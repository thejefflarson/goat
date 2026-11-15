//! Writes `proofs/GoatGrammar.v`: `grammar/goat.peg` as Coq data (ADR 0030).
//! Sequences and choices nest to the right, and recovery annotations are
//! dropped because they change nothing about valid input.
//!
//!     cargo run -q -p goat_parser --example emit_coq > proofs/GoatGrammar.v

use goat_parser::lexer::TokenKind;
use goat_parser::peg::{Expr, Grammar, Terminal};
use std::fmt::Write;

fn constructor(name: &str) -> String {
    format!("R_{name}")
}

fn terminal(t: &Terminal) -> String {
    match t {
        Terminal::Text(text) => format!("(E_term (T_text \"{}\"))", text.replace('"', "\"\"")),
        Terminal::Kind(TokenKind::Name) => "(E_term T_name)".into(),
        Terminal::Kind(TokenKind::Number) => "(E_term T_number)".into(),
        Terminal::Kind(TokenKind::String) => "(E_term T_string)".into(),
        Terminal::Kind(kind) => panic!("the grammar uses no {kind:?} terminal"),
        Terminal::EndOfInput => "(E_term T_eoi)".into(),
    }
}

fn nested(grammar: &Grammar, node: &str, items: &[Expr]) -> String {
    let (first, rest) = items.split_first().expect("a sequence has items");
    if rest.is_empty() {
        return expr(grammar, first);
    }
    format!(
        "({node} {} {})",
        expr(grammar, first),
        nested(grammar, node, rest)
    )
}

fn expr(grammar: &Grammar, e: &Expr) -> String {
    match e {
        Expr::Seq(items) => nested(grammar, "E_seq", items),
        Expr::Choice(items) => nested(grammar, "E_alt", items),
        Expr::Star(inner) => format!("(E_star {})", expr(grammar, inner)),
        Expr::Plus(inner) => format!("(E_plus {})", expr(grammar, inner)),
        Expr::Opt(inner) => format!("(E_opt {})", expr(grammar, inner)),
        Expr::Expect(inner) => format!("(E_expect {})", expr(grammar, inner)),
        Expr::Terminal(t) => terminal(t),
        Expr::Rule(id) => format!("(E_rule {})", constructor(&grammar.rule(*id).name)),
    }
}

fn main() {
    let grammar = Grammar::goat();
    let mut out = String::new();
    out.push_str(
        "(* Generated from grammar/goat.peg by parser/examples/emit_coq.rs; do not edit. *)\n\
         From Stdlib Require Import String.\n\
         Open Scope string_scope.\n\n\
         Inductive terminal : Type :=\n  | T_text (s : string)\n  | T_name\n  | T_number\n  | T_string\n  | T_eoi.\n\n\
         Inductive rule : Type :=\n",
    );
    for rule in &grammar.rules {
        writeln!(out, "  | {}", constructor(&rule.name)).unwrap();
    }
    out.push_str(
        ".\n\n\
         Inductive pexpr : Type :=\n  | E_term (t : terminal)\n  | E_rule (r : rule)\n  | E_seq (a b : pexpr)\n  | E_alt (a b : pexpr)\n  | E_star (a : pexpr)\n  | E_plus (a : pexpr)\n  | E_opt (a : pexpr)\n  | E_expect (a : pexpr).\n\n\
         Definition silent (r : rule) : bool :=\n  match r with\n",
    );
    for rule in grammar.rules.iter().filter(|r| r.silent) {
        writeln!(out, "  | {} => true", constructor(&rule.name)).unwrap();
    }
    out.push_str(
        "  | _ => false\n  end.\n\nDefinition body (r : rule) : pexpr :=\n  match r with\n",
    );
    for rule in &grammar.rules {
        writeln!(
            out,
            "  | {} =>\n    {}",
            constructor(&rule.name),
            expr(grammar, &rule.body)
        )
        .unwrap();
    }
    out.push_str("  end.\n");
    print!("{out}");
}
