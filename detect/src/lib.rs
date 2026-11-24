//! Which host vocabulary a program is written in, read from the names it uses.
//! The `goat` command and the Apple engine both choose a host this way.

use goat::{GoatError, HostInterface, Span, Vocab};
use goat_parser::lexer::{Token, TokenKind, declared_tags, tokenize};
use std::collections::HashSet;

/// The vocabulary a program is written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vocabulary {
    Turtle,
    Canvas,
}

impl Vocabulary {
    pub fn interface(self) -> HostInterface {
        match self {
            Vocabulary::Turtle => HostInterface::turtle(),
            Vocabulary::Canvas => goat_canvas::interface(),
        }
    }
}

/// The names only one vocabulary knows: event and shape tags from its `Vocab`,
/// and for the turtle the calls its prelude declares. A name both know says
/// nothing about which is meant.
struct Names {
    turtle_tags: HashSet<String>,
    canvas_tags: HashSet<String>,
    turtle_calls: HashSet<String>,
}

impl Names {
    fn new() -> Names {
        let tags =
            |vocab: &Vocab| -> HashSet<String> { vocab.tag_names().map(str::to_string).collect() };
        let (turtle, canvas) = (tags(&Vocab::turtle()), tags(&goat_canvas::vocab()));
        Names {
            turtle_tags: turtle.difference(&canvas).cloned().collect(),
            canvas_tags: canvas.difference(&turtle).cloned().collect(),
            turtle_calls: declared_calls(goat_checker::TURTLE_VOCAB),
        }
    }
}

/// The names `source` binds to a `foreign` function: `forward = foreign ...`.
fn declared_calls(source: &str) -> HashSet<String> {
    let tokens = tokenize(source);
    tokens
        .windows(3)
        .filter(|w| w[0].kind == TokenKind::Name && is_punct(source, &w[1], "="))
        .filter(|w| text(source, &w[2]) == "foreign")
        .map(|w| text(source, &w[0]).to_string())
        .collect()
}

fn text<'a>(source: &'a str, token: &Token) -> &'a str {
    &source[token.start..token.end]
}

fn is_punct(source: &str, token: &Token, punct: &str) -> bool {
    token.kind == TokenKind::Punct && text(source, token) == punct
}

/// The vocabulary `source` is written in: the canvas's when it names a canvas
/// event or shape, the turtle's when it names a turtle one or calls a turtle
/// function, and the turtle's when it names neither. A program that names both
/// is an error at the first name of each.
pub fn detect(source: &str) -> Result<Vocabulary, GoatError> {
    let names = Names::new();
    let tokens = tokenize(source);
    let own_tags: HashSet<&str> = declared_tags(source, &tokens).into_iter().collect();
    let bound: HashSet<&str> = tokens
        .windows(2)
        .filter(|w| w[0].kind == TokenKind::Name && is_punct(source, &w[1], "="))
        .map(|w| text(source, &w[0]))
        .collect();
    let (mut turtle, mut canvas): (Vec<&Token>, Vec<&Token>) = (Vec::new(), Vec::new());
    for (i, token) in tokens.iter().enumerate() {
        let name = text(source, token);
        let after_dot = i > 0 && is_punct(source, &tokens[i - 1], ".");
        if token.kind != TokenKind::Name || own_tags.contains(name) || after_dot {
            continue;
        }
        let called = tokens
            .get(i + 1)
            .is_some_and(|after| is_punct(source, after, "("));
        if names.canvas_tags.contains(name) {
            canvas.push(token);
        } else if names.turtle_tags.contains(name)
            || (called && names.turtle_calls.contains(name) && !bound.contains(name))
        {
            turtle.push(token);
        }
    }
    let (Some(first_turtle), Some(first_canvas)) = (turtle.first(), canvas.first()) else {
        return Ok(if canvas.is_empty() {
            Vocabulary::Turtle
        } else {
            Vocabulary::Canvas
        });
    };
    let span = |token: &Token| Span::new(token.start, token.end);
    let list = |used: &[&Token]| -> String {
        let mut seen: Vec<&str> = Vec::new();
        for token in used {
            let name = text(source, token);
            if !seen.contains(&name) {
                seen.push(name);
            }
        }
        seen.iter()
            .map(|name| format!("`{name}`"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    Err(GoatError::new(
        span(first_turtle),
        format!(
            "this program uses the turtle's {} and the canvas's {}, which no one host knows; \
             pass --turtle or --canvas to say which you mean",
            list(&turtle),
            list(&canvas)
        ),
    )
    .with_label(span(first_canvas), "the canvas's vocabulary starts here"))
}
