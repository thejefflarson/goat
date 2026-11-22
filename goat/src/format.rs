//! The native host of the formatter (ADR 0041): `editor/format.goat` runs over
//! the editor vocabulary and answers an `Edited` event with whitespace edits,
//! which this applies. The program is the whole style; nothing here decides how
//! goat is laid out.

use crate::native::{Guest, HostEvent, Interactive};
use crate::{Host, HostInterface, SceneCommand, SceneHost, compile};
use std::time::Duration;

const FORMATTER: &str = include_str!("../../editor/format.goat");

/// Replace the bytes `from..to` of the text with `newlines` line breaks and
/// then `indent` spaces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edit {
    pub from: usize,
    pub to: usize,
    pub newlines: usize,
    pub indent: usize,
}

struct Edited(String);

impl HostEvent for Edited {
    fn tag(&self) -> &'static str {
        "Edited"
    }

    fn construct<H: Host + 'static>(
        &self,
        guest: &mut Guest<H>,
        constructor: &str,
    ) -> Result<i32, String> {
        let text = guest.string(&self.0)?;
        guest.call(constructor, (text, 0i64))
    }
}

/// The formatter, compiled and instantiated once and asked about any number of texts.
pub struct Formatter {
    editor: Interactive<SceneHost, Edited>,
}

impl Formatter {
    pub fn new() -> Result<Formatter, String> {
        let wasm = compile(FORMATTER, &HostInterface::editor()).map_err(|errors| {
            let rendered: Vec<_> = errors.iter().map(|e| e.render(FORMATTER)).collect();
            format!("the formatter does not compile:\n{}", rendered.join("\n"))
        })?;
        let editor =
            Interactive::with_timeout(&wasm, SceneHost::default(), Duration::from_secs(60))?;
        Ok(Formatter { editor })
    }

    /// The edits that lay `source` out in the house style, in order, each over
    /// whitespace. Empty when the text is already formatted or does not lex.
    pub fn edits(&mut self, source: &str) -> Result<Vec<Edit>, String> {
        let event = Edited(source.to_string());
        let editor = &mut self.editor;
        if !editor.send(&event)? {
            return Err("the formatter does not take an Edited event".to_string());
        }
        editor.draw()?;
        let commands = std::mem::take(&mut editor.sink_mut().commands);
        let frame = commands.iter().rposition(|c| *c == SceneCommand::Begin);
        let mut edits = Vec::new();
        for command in &commands[frame.ok_or("the formatter drew no frame")?..] {
            if let SceneCommand::Edit {
                from,
                to,
                newlines,
                indent,
            } = command
            {
                let field =
                    |n: i64| usize::try_from(n).map_err(|_| format!("a negative edit: {n}"));
                edits.push(Edit {
                    from: field(*from)?,
                    to: field(*to)?,
                    newlines: field(*newlines)?,
                    indent: field(*indent)?,
                });
            }
        }
        Ok(edits)
    }

    /// `source` laid out in the house style.
    pub fn format(&mut self, source: &str) -> Result<String, String> {
        let edits = self.edits(source)?;
        apply(source, &edits)
    }
}

/// `source` with `edits` applied. The edits must be in order, inside the text,
/// on character boundaries and over whitespace only: the formatter changes how
/// a program is laid out and never what it says.
pub fn apply(source: &str, edits: &[Edit]) -> Result<String, String> {
    let mut out = String::with_capacity(source.len());
    let mut at = 0;
    for edit in edits {
        let gap = source
            .get(edit.from..edit.to)
            .filter(|_| edit.from >= at)
            .ok_or_else(|| format!("an edit over {}..{} is out of place", edit.from, edit.to))?;
        if !gap.chars().all(char::is_whitespace) {
            return Err(format!(
                "an edit over {}..{} is not whitespace",
                edit.from, edit.to
            ));
        }
        out.push_str(&source[at..edit.from]);
        out.push_str(&"\n".repeat(edit.newlines));
        out.push_str(&" ".repeat(edit.indent));
        at = edit.to;
    }
    out.push_str(&source[at..]);
    Ok(out)
}
