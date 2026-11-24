//! The control messages: the JSON `EngineMessage` the Swift side decodes
//! (`hosts/apple/GoatKit/Sources/GoatKit/EngineMessage.swift`), plus
//! `reloaded`.

use goat::native::{Reloaded, ResetReason};
use goat::{GoatError, Span};
use serde_json::{Value, json};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    Running,
    Finished,
    Failed,
}

pub fn ready() -> String {
    json!({"type": "ready"}).to_string()
}

pub fn state(state: State, message: Option<&str>) -> String {
    let name = match state {
        State::Running => "running",
        State::Finished => "finished",
        State::Failed => "failed",
    };
    let mut body = json!({"type": "state", "state": name});
    if let Some(message) = message {
        body["message"] = json!(message);
    }
    body.to_string()
}

pub fn output(lines: &[String]) -> String {
    json!({"type": "output", "lines": lines}).to_string()
}

pub fn reloaded(outcome: &Reloaded) -> String {
    match outcome {
        Reloaded::Refreshed => json!({"type": "reloaded", "outcome": "kept"}),
        Reloaded::Reset(ResetReason { kind, args }) => json!({
            "type": "reloaded",
            "outcome": "reset",
            "reason": {"kind": kind, "args": args},
        }),
    }
    .to_string()
}

/// `line` and `column` are 1-based and count characters; line 0 means the
/// message has no place in the user's source.
pub fn diagnostics(errors: &[GoatError], source: &str) -> String {
    let list: Vec<Value> = errors.iter().map(|e| diagnostic(e, source)).collect();
    json!({"type": "diagnostics", "diagnostics": list}).to_string()
}

fn diagnostic(error: &GoatError, source: &str) -> Value {
    if error.span.in_prelude() {
        return json!({"line": 0, "column": 0, "length": 0, "message": error.render(source)});
    }
    let (line, column, length) = locate(source, error.span);
    json!({"line": line, "column": column, "length": length, "message": error.message})
}

fn locate(source: &str, span: Span) -> (usize, usize, usize) {
    let start = floor_boundary(source, span.start);
    let before = &source[..start];
    let line = before.matches('\n').count() + 1;
    let column = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    let end = floor_boundary(source, span.end.max(start));
    (line, column, source[start..end].chars().count().max(1))
}

fn floor_boundary(text: &str, at: usize) -> usize {
    (0..=at.min(text.len()))
        .rev()
        .find(|&i| text.is_char_boundary(i))
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parsed(json: &str) -> Value {
        serde_json::from_str(json).unwrap()
    }

    #[test]
    fn a_state_carries_its_message_only_when_it_has_one() {
        assert_eq!(
            parsed(&state(State::Finished, None)),
            json!({"type": "state", "state": "finished"})
        );
        assert_eq!(
            parsed(&state(State::Failed, Some("boom"))),
            json!({"type": "state", "state": "failed", "message": "boom"})
        );
    }

    #[test]
    fn a_diagnostic_counts_characters_from_one() {
        let source = "héllo\nwörld + true";
        let at = source.find("true").unwrap();
        let error = GoatError::new(Span::new(at, at + 4), "no");
        let body = parsed(&diagnostics(&[error], source));
        assert_eq!(
            body["diagnostics"][0],
            json!({"line": 2, "column": 9, "length": 4, "message": "no"})
        );
    }

    #[test]
    fn a_span_inside_a_character_does_not_panic() {
        let error = GoatError::new(Span::new(1, 2), "no");
        let body = parsed(&diagnostics(&[error], "é"));
        assert_eq!(body["diagnostics"][0]["line"], 1);
    }

    #[test]
    fn a_reset_names_its_reason() {
        let reset = Reloaded::Reset(ResetReason::of(vec!["field_added".into(), "z".into()]));
        assert_eq!(
            parsed(&reloaded(&reset)),
            json!({"type": "reloaded", "outcome": "reset",
                   "reason": {"kind": "field_added", "args": ["z"]}})
        );
        assert_eq!(
            parsed(&reloaded(&Reloaded::Refreshed)),
            json!({"type": "reloaded", "outcome": "kept"})
        );
    }
}
