//! The native host of the formatter (ADR 0041): `editor/format.goat` runs over
//! the editor vocabulary and answers an `Edited` event with whitespace edits,
//! which this applies. The program is the whole style; nothing here decides how
//! goat is laid out.

use crate::native::{Guest, HostEvent, Interactive};
use crate::{Host, HostInterface, SceneCommand, SceneHost, compile};
use goat_parser::lexer::{Token, TokenKind, lex};
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

/// The same bounds the web editor applies, so a wrong edit fails instead of
/// allocating without limit.
const MAX_NEWLINES: usize = 8;
const MAX_INDENT: usize = 256;

/// The lexer's whitespace (`parser/src/lexer.rs`); Unicode spaces such as
/// U+00A0 are `char::is_whitespace` but lex as unrecognized tokens.
const LEXER_WHITESPACE: [char; 4] = [' ', '\t', '\n', '\r'];

/// The conditions under which replacing a whitespace gap keeps every token
/// (ADR 0041, `gap_guard`): a gap after a comment keeps a line break, and a
/// gap after `start` is not made one space before `at`.
fn guard_gap(source: &str, tokens: &[Token], edit: &Edit) -> Result<(), String> {
    let Ok(before) = tokens.binary_search_by_key(&edit.from, |t| t.end) else {
        return Ok(());
    };
    let before = tokens[before];
    if before.kind == TokenKind::Comment && edit.newlines == 0 {
        return Err(format!(
            "an edit over {}..{} would join the line after a comment into it",
            edit.from, edit.to
        ));
    }
    let makes_start_at = edit.newlines == 0
        && edit.indent == 1
        && &source[before.start..before.end] == "start"
        && tokens
            .binary_search_by_key(&edit.to, |t| t.start)
            .is_ok_and(|i| &source[tokens[i].start..tokens[i].end] == "at");
    if makes_start_at {
        return Err(format!(
            "an edit over {}..{} would make `start at` out of two words",
            edit.from, edit.to
        ));
    }
    Ok(())
}

/// `source` with `edits` applied. The edits must be in order, inside the text,
/// on character boundaries and over the lexer's whitespace only, and must pass
/// `guard_gap`: the formatter changes how a program is laid out and never what
/// it says. Any other edit refuses the whole format.
pub fn apply(source: &str, edits: &[Edit]) -> Result<String, String> {
    let tokens = lex(source);
    let mut out = String::with_capacity(source.len());
    let mut at = 0;
    for edit in edits {
        let gap = source
            .get(edit.from..edit.to)
            .filter(|_| edit.from >= at)
            .ok_or_else(|| format!("an edit over {}..{} is out of place", edit.from, edit.to))?;
        if edit.newlines > MAX_NEWLINES || edit.indent > MAX_INDENT {
            return Err(format!(
                "an edit over {}..{} asks for {} line breaks and {} spaces",
                edit.from, edit.to, edit.newlines, edit.indent
            ));
        }
        if !gap.chars().all(|c| LEXER_WHITESPACE.contains(&c)) {
            return Err(format!(
                "an edit over {}..{} is not whitespace the lexer reads",
                edit.from, edit.to
            ));
        }
        guard_gap(source, &tokens, edit)?;
        out.push_str(&source[at..edit.from]);
        out.push_str(&"\n".repeat(edit.newlines));
        out.push_str(&" ".repeat(edit.indent));
        at = edit.to;
    }
    out.push_str(&source[at..]);
    Ok(out)
}
