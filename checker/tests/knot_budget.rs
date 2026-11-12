//! Methods that return `{...self, …}` make receiver types that mention
//! themselves under several row prefixes. Checking such a program must end in
//! an answer or a plain error, never run away.

use goat_checker::check_with_prelude;
use std::time::{Duration, Instant};

fn error_of(source: &str) -> Option<String> {
    check_with_prelude("", source)
        .err()
        .map(|errors| errors[0].message.clone())
}

const THREE_METHOD_MODEL: &str = "init = program() do {x: 0, y: 1,
        update: program(self) do {...self, x: self.x + 1} done,
        nudge: program(self) do {...self, y: self.y + 1} done,
        draw: program(self) do self.x done} done
    run = program(m, n) do if n == 0 then m else run(m.update(), n - 1) done done";

fn assert_terminates_quickly(source: &str) {
    let start = Instant::now();
    let error = error_of(source);
    assert!(
        start.elapsed() < Duration::from_secs(2),
        "took {:?}",
        start.elapsed()
    );
    if let Some(message) = error {
        assert!(!message.contains('μ'), "{message}");
        assert!(
            message.contains("program too complex")
                || message.contains("infinite type")
                || message.contains("contain itself"),
            "{message}"
        );
        assert!(!message.contains("`t"), "{message}");
    }
}

#[test]
fn a_chain_of_three_methods_terminates() {
    assert_terminates_quickly(&format!(
        "{THREE_METHOD_MODEL}\nm = init()\nm.nudge().update().draw()"
    ));
}

#[test]
fn a_looped_three_method_model_terminates() {
    assert_terminates_quickly(&format!(
        "{THREE_METHOD_MODEL}\nm = run(init(), 4)\nm.draw()"
    ));
}
