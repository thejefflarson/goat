//! Dual-run at the HIR: lowering the CST path's tree must give exactly the HIR
//! (spans, symbols and diagnostics included) that lowering pest's tree gives.

#[path = "../../parser/tests/corpus/mod.rs"]
mod corpus;

use corpus::{goat_programs, rust_sources, string_literals};
use goat_checker::PRELUDE;
use goat_checker::lower::{Lowered, lower_via_cst, lower_with_vocab};
use goat_checker::vocab::Vocab;

fn shown(lowered: &Lowered) -> String {
    format!(
        "{:#?}\n{:?}\n{:?}\n{:?}",
        lowered.root, lowered.errors, lowered.warnings, lowered.interactive
    )
}

/// Whether `source` parsed, after holding both paths to the same result.
fn assert_same_hir(prelude: &str, source: &str) -> bool {
    let vocab = Vocab::turtle();
    match (
        lower_with_vocab(prelude, &vocab, source),
        lower_via_cst(prelude, &vocab, source),
    ) {
        (Ok(pest), Ok(cst)) => {
            assert_eq!(shown(&cst), shown(&pest), "HIR differs on {source:?}");
            true
        }
        (Err(_), Err(_)) => false,
        (pest, cst) => panic!(
            "one path rejects what the other accepts (pest ok: {}, cst ok: {}): {source:?}",
            pest.is_ok(),
            cst.is_ok()
        ),
    }
}

#[test]
fn every_goat_file_lowers_to_the_same_hir_with_and_without_the_prelude() {
    let programs = goat_programs();
    for source in &programs {
        assert!(assert_same_hir("", source));
        assert!(assert_same_hir(PRELUDE, source));
    }
    eprintln!("{} .goat files, each lowered twice", programs.len());
}

#[test]
fn every_program_the_tests_quote_lowers_to_the_same_hir() {
    let (mut total, mut parsed) = (0, 0);
    for rust in rust_sources() {
        for literal in string_literals(&rust) {
            total += 1;
            parsed += usize::from(assert_same_hir("", &literal));
        }
    }
    eprintln!("string literals: {total} dual-run, {parsed} lowered");
    assert!(parsed > 1000, "the corpus must hold real programs");
}
