//! Semantic completion for the editor: the checker's answer at a cursor,
//! encoded for the wire (see `gw_complete`).

use goat_checker::query::{self, ItemKind};
use std::sync::OnceLock;

fn host() -> &'static goat::HostInterface {
    static HOST: OnceLock<goat::HostInterface> = OnceLock::new();
    HOST.get_or_init(goat::HostInterface::turtle)
}

const VARIABLE: u8 = 0;
const FUNCTION: u8 = 1;
const KEYWORD: u8 = 2;
const TAG: u8 = 3;
const FIELD: u8 = 4;

fn kind(kind: ItemKind) -> u8 {
    match kind {
        ItemKind::Variable => VARIABLE,
        ItemKind::Function => FUNCTION,
        ItemKind::Keyword => KEYWORD,
        ItemKind::Tag => TAG,
        ItemKind::Field => FIELD,
    }
}

/// Empty where nothing completes at the byte `cursor`. Otherwise `from: u32`,
/// the byte offset where the word being typed starts, then one entry per item,
/// best first: `kind: u8`, then the label and the detail, each a
/// little-endian `u32` byte length followed by UTF-8.
pub fn complete(source: &str, cursor: usize) -> Vec<u8> {
    let host = host();
    let Some(found) = query::complete(host.prelude(), host.vocab(), source, cursor) else {
        return Vec::new();
    };
    let mut out = u32::try_from(found.from)
        .unwrap_or(u32::MAX)
        .to_le_bytes()
        .to_vec();
    for item in &found.items {
        out.push(kind(item.kind));
        for text in [&item.label, &item.detail] {
            out.extend_from_slice(&(text.len() as u32).to_le_bytes());
            out.extend_from_slice(text.as_bytes());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(kind, label, detail)` per entry after the 4-byte header.
    fn entries(payload: &[u8]) -> Vec<(u8, String, String)> {
        let mut at = 4;
        let text = |at: &mut usize| {
            let len = u32::from_le_bytes(payload[*at..*at + 4].try_into().unwrap()) as usize;
            let value = String::from_utf8(payload[*at + 4..*at + 4 + len].to_vec()).unwrap();
            *at += 4 + len;
            value
        };
        let mut found = Vec::new();
        while at < payload.len() {
            let kind = payload[at];
            at += 1;
            let label = text(&mut at);
            let detail = text(&mut at);
            found.push((kind, label, detail));
        }
        found
    }

    #[test]
    fn a_field_after_a_dot_comes_back_with_its_type() {
        let source = "p = {x: 1, y: \"s\"}\np.";
        let payload = complete(source, source.len());
        assert_eq!(
            u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize,
            source.len()
        );
        assert_eq!(
            entries(&payload),
            [
                (FIELD, "x".into(), "Number".into()),
                (FIELD, "y".into(), "String".into())
            ]
        );
    }

    #[test]
    fn nothing_completes_in_a_comment() {
        assert!(complete("# hello", 7).is_empty());
    }

    #[test]
    fn a_cursor_inside_a_character_or_past_the_end_does_not_panic() {
        let source = "é = 1\né.";
        for cursor in 0..source.len() + 4 {
            let _ = complete(source, cursor);
        }
    }

    #[test]
    fn a_value_position_lists_the_hosts_names_with_their_signatures() {
        let payload = complete("x = ", 4);
        let found = entries(&payload);
        let forward = found.iter().find(|e| e.1 == "forward").expect("forward");
        assert_eq!(
            forward,
            &(FUNCTION, "forward".into(), "(Number) -> Unit".into())
        );
        assert!(found.iter().any(|e| e.0 == TAG && e.1 == "Tick"));
        assert!(found.iter().any(|e| e.0 == KEYWORD && e.1 == "match"));
    }
}
