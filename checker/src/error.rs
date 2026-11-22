//! Diagnostics produced by lowering and type inference, carrying a source span
//! so they can be rendered with a caret pointing at the offending text.

use crate::hir::Span;
use std::fmt;

/// What an error is about, for the callers that treat a class of errors
/// differently from the rest (the corpus reader skips them).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ErrorKind {
    #[default]
    Other,
    /// A method used as a plain function or the reverse: the dot or `::` met a
    /// field of the other flag, which the calculus does not track.
    MethodFlag,
    /// A "program too complex" diagnostic: a resource bound, not a type error.
    ResourceLimit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoatError {
    pub span: Span,
    pub message: String,
    pub kind: ErrorKind,
    /// Other places that explain the error, each with what it says there.
    pub labels: Vec<Label>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

impl GoatError {
    pub fn new(span: Span, message: impl Into<String>) -> GoatError {
        GoatError {
            span,
            message: message.into(),
            kind: ErrorKind::Other,
            labels: Vec::new(),
        }
    }

    pub fn of_kind(self, kind: ErrorKind) -> GoatError {
        GoatError { kind, ..self }
    }

    /// A resource-limit diagnostic.
    pub fn too_complex(span: Span, message: impl Into<String>) -> GoatError {
        GoatError::new(span, message).of_kind(ErrorKind::ResourceLimit)
    }

    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> GoatError {
        self.labels.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    /// Blame the user's `site` for an error raised inside the prelude, so the
    /// user is pointed at their own code rather than at text they never wrote.
    pub fn at_call_site(self, site: Span) -> GoatError {
        if self.span.in_prelude() {
            GoatError { span: site, ..self }
        } else {
            self
        }
    }

    /// Render the error against the source it came from: `line:col: message`,
    /// then the offending line with a caret underline. `source` is the user's
    /// program; an error still inside the prelude renders against that.
    pub fn render(&self, source: &str) -> String {
        let mut out = snippet(source, self.span, &self.message);
        for label in &self.labels {
            out.push('\n');
            out.push_str(&snippet(
                source,
                label.span,
                &format!("note: {}", label.message),
            ));
        }
        out
    }
}

/// `line:col: message`, then the line with a caret underline under `span`.
fn snippet(source: &str, span: Span, message: &str) -> String {
    let (source, origin) = if span.in_prelude() {
        (crate::PRELUDE, "in the prelude, ")
    } else {
        (source, "")
    };
    let (line, col, line_text) = locate(source, span.start);
    let caret_pad = " ".repeat(col.saturating_sub(1));
    let caret = "^".repeat(span.end.saturating_sub(span.start).max(1));
    format!("{origin}{line}:{col}: {message}\n  {line_text}\n  {caret_pad}{caret}")
}

impl fmt::Display for GoatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (at byte {})", self.message, self.span.start)
    }
}

/// Map a byte offset to a 1-based line and column and the text of that line.
fn locate(source: &str, offset: usize) -> (usize, usize, &str) {
    let offset = offset.min(source.len());
    let mut line_start = 0;
    let mut line_no = 1;
    for (i, b) in source.bytes().enumerate() {
        if i >= offset {
            break;
        }
        if b == b'\n' {
            line_no += 1;
            line_start = i + 1;
        }
    }
    let line_end = source[line_start..]
        .find('\n')
        .map(|n| line_start + n)
        .unwrap_or(source.len());
    let col = source[line_start..offset].chars().count() + 1;
    (line_no, col, &source[line_start..line_end])
}
