//! The editor's highlighter is a goat program (`editor/highlight.goat`). It
//! must draw exactly the spans `parser::lexer` finds, byte for byte, on every
//! goat file in the repo: the lexer is the oracle (ADR 0018), and the program
//! only has to agree with it.
#![cfg(feature = "native")]

use goat::native::{Guest, HostEvent, Interactive};
use goat::{Host, HostInterface, SceneCommand, SceneHost, compile};
use goat_parser::lexer::{self, TokenKind};
use std::collections::HashSet;
use std::fs;
use std::time::Duration;

#[allow(dead_code)]
#[path = "../../parser/tests/corpus/mod.rs"]
mod corpus;

const HIGHLIGHTER: &str = include_str!("../../editor/highlight.goat");

#[derive(Clone, Debug, PartialEq)]
enum EditorEvent {
    Edited { text: String, cursor: i64 },
    Selected { anchor: i64, head: i64 },
    HostTags { names: String },
}

impl HostEvent for EditorEvent {
    fn tag(&self) -> &'static str {
        match self {
            EditorEvent::Edited { .. } => "Edited",
            EditorEvent::Selected { .. } => "Selected",
            EditorEvent::HostTags { .. } => "HostTags",
        }
    }

    fn construct<H: Host + 'static>(
        &self,
        guest: &mut Guest<H>,
        constructor: &str,
    ) -> Result<i32, String> {
        match self {
            EditorEvent::Edited { text, cursor } => {
                let text = guest.string(text)?;
                guest.call(constructor, (text, *cursor))
            }
            EditorEvent::Selected { anchor, head } => guest.call(constructor, (*anchor, *head)),
            EditorEvent::HostTags { names } => {
                let names = guest.string(names)?;
                guest.call(constructor, names)
            }
        }
    }
}

type Span = (i64, i64, String);

fn editor() -> Interactive<SceneHost, EditorEvent> {
    let wasm = compile(HIGHLIGHTER, &HostInterface::editor()).unwrap_or_else(|errors| {
        let rendered: Vec<_> = errors.iter().map(|e| e.render(HIGHLIGHTER)).collect();
        panic!("the highlighter does not compile:\n{}", rendered.join("\n"));
    });
    Interactive::with_timeout(&wasm, SceneHost::default(), Duration::from_secs(60)).unwrap()
}

fn edit(editor: &mut Interactive<SceneHost, EditorEvent>, text: &str) -> Vec<Span> {
    let event = EditorEvent::Edited {
        text: text.to_string(),
        cursor: 0,
    };
    assert!(editor.send(&event).unwrap());
    editor.draw().unwrap();
    let commands = std::mem::take(&mut editor.sink_mut().commands);
    let frame = commands.iter().rposition(|c| *c == SceneCommand::Begin);
    commands[frame.expect("draw begins a frame")..]
        .iter()
        .filter_map(|command| match command {
            SceneCommand::Span { from, to, kind } => Some((*from, *to, kind.clone())),
            _ => None,
        })
        .collect()
}

/// The names a host declares as tags: the prelude's `tag` declarations and the
/// vocabulary's events, shapes and keys, as `goat_web` hands them to its tokenizer.
fn host_tags(host: &HostInterface) -> HashSet<String> {
    let prelude = host.prelude();
    let mut tags: HashSet<String> = lexer::declared_tags(prelude, &lexer::tokenize(prelude))
        .into_iter()
        .map(String::from)
        .collect();
    let vocab = host.vocab();
    tags.extend(
        vocab
            .tag_names()
            .chain(vocab.key_tag_names())
            .map(String::from),
    );
    tags
}

fn declare_tags(editor: &mut Interactive<SceneHost, EditorEvent>, tags: &HashSet<String>) {
    let mut names: Vec<&str> = tags.iter().map(String::as_str).collect();
    names.sort_unstable();
    let event = EditorEvent::HostTags {
        names: names.join(" "),
    };
    assert!(editor.send(&event).unwrap());
}

/// The spans the lexer finds, as the web editor's `tok-<kind>` classes.
fn oracle(source: &str, tags: &HashSet<String>) -> Vec<Span> {
    lexer::highlight(source, tags)
        .into_iter()
        .filter_map(|token| {
            let kind = match token.kind {
                TokenKind::Comment => "comment",
                TokenKind::Keyword => "keyword",
                TokenKind::Literal => "literal",
                TokenKind::Number => "number",
                TokenKind::String => "string",
                TokenKind::Tag => "tag",
                TokenKind::Operator => "operator",
                TokenKind::Name | TokenKind::Punct | TokenKind::Whitespace | TokenKind::Unknown => {
                    return None;
                }
            };
            Some((token.start as i64, token.end as i64, kind.to_string()))
        })
        .collect()
}

fn assert_agrees(editor: &mut Interactive<SceneHost, EditorEvent>, name: &str, source: &str) {
    assert_agrees_with(editor, name, source, &HashSet::new());
}

fn assert_agrees_with(
    editor: &mut Interactive<SceneHost, EditorEvent>,
    name: &str,
    source: &str,
    tags: &HashSet<String>,
) {
    let (drawn, expected) = (edit(editor, source), oracle(source, tags));
    if drawn != expected {
        let at = drawn
            .iter()
            .zip(&expected)
            .position(|(a, b)| a != b)
            .unwrap_or(drawn.len().min(expected.len()));
        panic!(
            "{name}: {} spans, the lexer finds {}; first difference at span {at}: goat {:?}, lexer {:?}",
            drawn.len(),
            expected.len(),
            drawn.get(at),
            expected.get(at),
        );
    }
}

#[test]
fn the_highlighter_draws_the_spans_the_lexer_finds_on_every_goat_file() {
    let files = corpus::files_with("goat");
    assert!(files.len() > 25, "{} goat files", files.len());
    let mut editor = editor();
    for file in &files {
        let source = fs::read_to_string(file).unwrap();
        assert_agrees(&mut editor, &file.display().to_string(), &source);
    }
    let (_, leaked) = editor.finish().unwrap();
    assert_eq!(leaked, 0, "the highlighter leaked");
}

/// With the host's own tags declared, the spans still equal the lexer's, for
/// the turtle's names and the canvas host's.
#[test]
fn the_highlighter_marks_the_hosts_tags_as_the_lexer_does() {
    let files = corpus::files_with("goat");
    for (host, name) in [
        (HostInterface::turtle(), "turtle"),
        (goat_canvas::interface(), "canvas"),
    ] {
        let tags = host_tags(&host);
        let mut editor = editor();
        declare_tags(&mut editor, &tags);
        for file in &files {
            let source = fs::read_to_string(file).unwrap();
            assert_agrees_with(&mut editor, &file.display().to_string(), &source, &tags);
        }
        for source in [
            "update = program(m, e) do match e do Tick(dt) then m else m done done",
            "draw = program(m) do [Dot({x: 1, y: 2, r: 3, fill: \"red\"}), Line({x1: 1})] done",
            "KeyDown(Up) MouseMove Frame Empty Link \u{fc}n\u{ef}code Tickle Tick",
            "Tick tag Tick = Tock | Tick Tock Tick",
        ] {
            assert_agrees_with(&mut editor, source, source, &tags);
        }
        let marked = edit(&mut editor, "Link Empty x");
        assert_eq!(marked.len(), 2, "{name}: {marked:?}");
        assert!(marked.iter().all(|(_, _, kind)| kind == "tag"), "{name}");
        assert_eq!(editor.finish().unwrap().1, 0, "the highlighter leaked");
    }
}

#[test]
fn host_tags_replace_the_previous_names_and_keep_the_spans() {
    let mut editor = editor();
    let tags = HashSet::from(["Dot".to_string(), "Box".to_string()]);
    declare_tags(&mut editor, &tags);
    assert_eq!(edit(&mut editor, "Dot Box Line").len(), 2);
    declare_tags(&mut editor, &HashSet::from(["Line".to_string()]));
    editor.draw().unwrap();
    let frame = std::mem::take(&mut editor.sink_mut().commands);
    let kept = frame
        .iter()
        .filter(|c| matches!(c, SceneCommand::Span { .. }))
        .count();
    assert_eq!(kept, 2, "a HostTags event draws the spans it had");
    assert_eq!(edit(&mut editor, "Dot Box Line").len(), 1);
    editor.finish().unwrap();
}

/// The goat programs the Rust tests quote, and whatever else sits in a string
/// literal: more half-typed input for the scanner. Non-ASCII text is left to
/// the cases that name it, since the program approximates Unicode names.
#[test]
fn the_highlighter_agrees_with_the_lexer_on_the_strings_the_tests_quote() {
    let literals: Vec<String> = corpus::rust_sources()
        .iter()
        .flat_map(|source| corpus::string_literals(source))
        .filter(|text| text.is_ascii() && text.len() < 4000)
        .collect();
    assert!(literals.len() > 1000, "{} literals", literals.len());
    let mut editor = editor();
    for text in &literals {
        assert_agrees(&mut editor, &format!("{text:?}"), text);
    }
    assert_eq!(editor.finish().unwrap().1, 0, "the highlighter leaked");
}

#[test]
fn the_highlighter_agrees_with_the_lexer_on_the_corner_cases() {
    let cases = [
        "",
        "   \n\t\r\n",
        "# only a comment",
        "x = 1 # trailing\ny = 2",
        "\"unterminated",
        "\"escaped \\\" quote\" and \"back\\\\slash\"",
        "\"ends in backslash\\",
        "\"é\" # é\n1",
        "1 1.5 .5 5. 1e3 1E+3 2.5e-3 1e 1e+ 7.e2 0.5.5",
        "doner double ifx truthy true false truefalse",
        "start at start attention start  at",
        "== != <= < >= > -> // / % + * - = ! @ $ ?",
        "( ) { } [ ] : ; | , ... .",
        "_x x_y 9lives café",
        "for i from 1 to 10 do print(i) done",
        "for i in xs do print(i) done",
        "for (a) from 1 to f(2) do 0 done",
        "line.to {from: 1, to: 2} to from in foreign",
        "for from from from 1 to 2 do from done",
        "f = foreign \"m\" \"n\" (Number) -> Number\ng = foreign x\nh = foreign ;",
        "tag Shape = Circle(Number) | Dot | Square(Number, Number)\nCircle(1) Dot Shape Square",
        "tag Empty\ntag Link\nEmpty Link Other",
        "tag Pair = A((Number)) | B\ntag\ntag = C\nA B C",
        "tag Group = X(Number) Y\nX Y",
        "tag A | B\nA B",
        "tag",
        "tag Shape =",
        "tag Shape = Circle(Number",
        "p = program(x) do x done fn function",
        "ünïcode in a # comment\n\"and a string ünï\"",
    ];
    let mut editor = editor();
    for source in cases {
        assert_agrees(&mut editor, &format!("{source:?}"), source);
    }
    assert_eq!(editor.finish().unwrap().1, 0, "the highlighter leaked");
}

#[test]
fn spans_are_zero_based_byte_offsets_and_carry_roles_not_colors() {
    let mut editor = editor();
    let spans = edit(&mut editor, "é = 1 # n");
    assert_eq!(
        spans,
        [(5, 6, "number".to_string()), (7, 10, "comment".to_string())]
    );
    editor.finish().unwrap();
}

#[test]
fn a_new_edit_replaces_the_old_spans_and_other_events_change_nothing() {
    let mut editor = editor();
    assert_eq!(edit(&mut editor, "1").len(), 1);
    assert_eq!(edit(&mut editor, "if x then 1 done").len(), 4);
    assert!(
        !editor
            .send(&EditorEvent::Selected { anchor: 0, head: 3 })
            .unwrap()
    );
    editor.draw().unwrap();
    let frame = std::mem::take(&mut editor.sink_mut().commands);
    let spans = frame
        .iter()
        .filter(|c| matches!(c, SceneCommand::Span { .. }))
        .count();
    assert_eq!(spans, 4);
    assert_eq!(editor.finish().unwrap().1, 0);
}

#[test]
fn drawing_twice_gives_the_same_spans() {
    let mut editor = editor();
    let first = edit(&mut editor, "x = 1 + 2");
    editor.draw().unwrap();
    let again: Vec<_> = std::mem::take(&mut editor.sink_mut().commands)
        .into_iter()
        .filter_map(|c| match c {
            SceneCommand::Span { from, to, kind } => Some((from, to, kind)),
            _ => None,
        })
        .collect();
    assert_eq!(first, again);
    editor.finish().unwrap();
}

#[test]
fn the_editor_vocabulary_rejects_an_event_it_does_not_send() {
    let program = |event: &str| {
        format!(
            "init = {{n: 0}}\nupdate = program(m, e) do match e do {event} then m else m done done\ndraw = program(m) do [] done"
        )
    };
    let errors = compile(&program("Tick(dt)"), &HostInterface::editor()).unwrap_err();
    assert!(
        errors.iter().any(|e| e.message.contains("Tick")),
        "{errors:?}"
    );
    assert!(compile(&program("Edited(e)"), &HostInterface::editor()).is_ok());
    assert!(compile(&program("Selected(s)"), &HostInterface::editor()).is_ok());
    assert!(compile(&program("HostTags(h)"), &HostInterface::editor()).is_ok());
}

#[test]
fn the_editor_draws_spans_not_the_turtles_shapes() {
    let source = "init = {n: 0}\nupdate = program(m, e) do m done\ndraw = program(m) do [Line({x1: 0, y1: 0, x2: 1, y2: 1, color: \"red\"})] done";
    let errors = compile(source, &HostInterface::editor()).unwrap_err();
    assert!(
        errors.iter().any(|e| e.message.contains("Line")),
        "{errors:?}"
    );
}
