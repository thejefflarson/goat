//! Every rule of `grammar/goat.peg` is classified against the core fragment of
//! `proofs/goat_ln.ott` (ADR 0030): `Core` names the Ott production the rule
//! takes part in (or `e`/`fs` for a rule that dispatches among them), and
//! `Outside` marks a rule the verified parser does not claim. Adding a rule
//! without classifying it, or leaving a stale entry, fails here.

use goat_parser::peg::Grammar;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

enum Class {
    Core(&'static str),
    Outside,
}
use Class::{Core, Outside};

const RULES: &[(&str, Class)] = &[
    ("goat", Core("e")),
    ("tag_decl", Outside),
    ("tag_kw", Outside),
    ("group_name", Outside),
    ("tag_case", Outside),
    ("expr", Core("e")),
    ("sequel", Outside),
    ("_part", Core("e_let")),
    ("_statement", Core("e")),
    ("_more_math", Outside),
    ("_operand", Core("e")),
    ("value", Core("e")),
    ("_infix", Outside),
    ("and_op", Outside),
    ("or_op", Outside),
    ("not_op", Outside),
    ("plus", Outside),
    ("minus", Outside),
    ("multiply", Outside),
    ("floor_divide", Outside),
    ("divide", Outside),
    ("remainder", Outside),
    ("equal", Outside),
    ("not_equal", Outside),
    ("lte", Outside),
    ("lt", Outside),
    ("gte", Outside),
    ("gt", Outside),
    ("_term", Core("e")),
    ("negation", Outside),
    ("_postfix", Core("e")),
    ("access", Core("e_proj")),
    ("call", Core("e_app")),
    ("arguments", Core("e_app")),
    ("_primary", Core("e")),
    ("number", Core("e_num")),
    ("string", Outside),
    ("boolean", Core("e")),
    ("true_lit", Core("e_true")),
    ("false_lit", Core("e_false")),
    ("name", Core("e_fvar")),
    ("record", Core("e_rec")),
    ("_record_item", Core("fs_cons")),
    ("spread", Outside),
    ("field", Core("fs_cons")),
    ("local", Core("e_let")),
    ("declaration", Core("e_let")),
    ("foreign_kw", Outside),
    ("foreign_decl", Outside),
    ("foreign_name", Outside),
    ("fn_type", Outside),
    ("_type_expr", Outside),
    ("list_type", Outside),
    ("record_type", Outside),
    ("field_type", Outside),
    ("type_name", Outside),
    ("destructure", Outside),
    ("record_pattern", Outside),
    ("list_pattern", Outside),
    ("rest_binding", Outside),
    ("function", Core("e_abs")),
    ("params", Core("e_abs")),
    ("_param", Core("e_abs")),
    ("conditional", Outside),
    ("_else_branch", Outside),
    ("list", Outside),
    ("match_expr", Outside),
    ("arm", Outside),
    ("pattern", Outside),
    ("labels", Outside),
    ("literal_pattern", Outside),
    ("repeat_loop", Outside),
    ("count_loop", Outside),
    ("each_loop", Outside),
    ("for_kw", Outside),
    ("from_kw", Outside),
    ("to_kw", Outside),
    ("in_kw", Outside),
];

/// The names `proofs/goat_ln.ott` gives the productions of `exp` and `fields`
/// (`e_abs`, `fs_cons`, ...), plus the two nonterminals.
fn ott_names() -> BTreeSet<String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../proofs/goat_ln.ott");
    let ott = fs::read_to_string(path).expect("proofs/goat_ln.ott is readable");
    let mut names: BTreeSet<String> = ["e".to_string(), "fs".to_string()].into();
    let mut prefix = "";
    for line in ott.lines() {
        let line = line.trim_start();
        if line.starts_with("exp, e ::") {
            prefix = "e_";
        } else if line.starts_with("fields, fs ::") {
            prefix = "fs_";
        } else if line.contains("::=") {
            prefix = "";
        } else if line.starts_with('|') && !prefix.is_empty() {
            let mut parts = line.split("::").skip(1);
            if let (Some(flag), Some(name)) = (parts.next(), parts.next())
                && flag.trim().is_empty()
                && let Some(name) = name.split_whitespace().next()
            {
                names.insert(format!("{prefix}{name}"));
            }
        }
    }
    names
}

#[test]
fn every_grammar_rule_is_classified_and_no_entry_is_stale() {
    let grammar: BTreeSet<&str> = Grammar::goat()
        .rules
        .iter()
        .map(|rule| rule.name.as_str())
        .collect();
    let mapped: BTreeSet<&str> = RULES.iter().map(|(name, _)| *name).collect();
    assert_eq!(mapped.len(), RULES.len(), "a rule is classified twice");
    let unclassified: Vec<_> = grammar.difference(&mapped).collect();
    let stale: Vec<_> = mapped.difference(&grammar).collect();
    assert!(
        unclassified.is_empty(),
        "unclassified rules: {unclassified:?}"
    );
    assert!(
        stale.is_empty(),
        "classified but not in the grammar: {stale:?}"
    );
}

#[test]
fn core_rules_name_real_ott_productions() {
    let ott = ott_names();
    for (rule, class) in RULES {
        if let Core(production) = class {
            assert!(
                ott.contains(*production),
                "`{rule}` maps to `{production}`, which goat_ln.ott lacks (has {ott:?})"
            );
        }
    }
}

#[test]
fn every_ott_production_is_reached_by_some_core_rule() {
    let reached: BTreeSet<&str> = RULES
        .iter()
        .filter_map(|(_, class)| match class {
            Core(production) => Some(*production),
            Outside => None,
        })
        .collect();
    for production in ott_names() {
        if !matches!(production.as_str(), "e" | "fs" | "fs_nil") {
            assert!(
                reached.contains(production.as_str()),
                "no rule takes part in `{production}`"
            );
        }
    }
}

/// `proofs/GoatShape.v` lists the core rules that make nodes; it must agree
/// with this map, or the Coq claim covers a different fragment than the Rust
/// side tests.
#[test]
fn coq_core_rule_list_matches_the_map() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../proofs/GoatShape.v");
    let coq = fs::read_to_string(path).expect("proofs/GoatShape.v is readable");
    let start = coq
        .find("Definition core_rule")
        .expect("GoatShape.v defines core_rule");
    let definition = &coq[start..];
    let definition = &definition[..definition.find("end.").expect("core_rule ends")];
    let in_coq: BTreeSet<&str> = definition
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter_map(|word| word.strip_prefix("R_"))
        .collect();
    let in_map: BTreeSet<&str> = RULES
        .iter()
        .filter(|(name, class)| matches!(class, Core(_)) && !name.starts_with('_'))
        .map(|(name, _)| *name)
        .collect();
    assert_eq!(in_coq, in_map);
}
