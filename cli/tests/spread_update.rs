//! A spread that updates keeps the record's type, so a model whose methods
//! return updated copies of itself runs through the interpreter and wasm
//! (ADR 0033).

#[allow(dead_code)]
mod support;

use support::run;

#[test]
fn a_spread_over_an_unknown_record_updates_or_extends() {
    let src = "set_x = program(r) do {...r, x: 1} done
        a = set_x({y: 7})
        b = set_x({x: 5, y: 8})
        print(a.x + a.y);
        print(b.x + b.y)";
    assert_eq!(run(src), "8\n9");
}

#[test]
fn a_recursive_spread_of_its_parameter_runs() {
    let src = "go = program(s, n) do if s.stop then n else go({...s, stop: true}, n + 1) done done
        print(go({stop: false}, 0))";
    assert_eq!(run(src), "1");
}
