//! Methods that return `{...self, …}` share one receiver type per record
//! literal (ADR 0034), so a model with several of them checks quickly instead
//! of tying a knot per method.

use goat_checker::check_with_prelude;
use std::time::{Duration, Instant};

const THREE_METHOD_MODEL: &str = "init = program() do {x: 0, y: 1,
        update: program(self) do {...self, x: self.x + 1} done,
        nudge: program(self) do {...self, y: self.y + 1} done,
        draw: program(self) do self.x done} done
    run = program(m, n) do if n == 0 then m else run(m.update(), n - 1) done done";

fn assert_checks_quickly(source: &str) {
    let start = Instant::now();
    let checked = check_with_prelude("", source);
    assert!(
        start.elapsed() < Duration::from_secs(2),
        "took {:?}",
        start.elapsed()
    );
    if let Err(errors) = checked {
        panic!("should check: {errors:?}");
    }
}

#[test]
fn a_chain_of_three_methods_checks() {
    assert_checks_quickly(&format!(
        "{THREE_METHOD_MODEL}\nm = init()\nm.nudge().update().draw()"
    ));
}

#[test]
fn a_looped_three_method_model_checks() {
    assert_checks_quickly(&format!(
        "{THREE_METHOD_MODEL}\nm = run(init(), 4)\nm.draw()"
    ));
}
