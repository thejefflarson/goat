//! A record literal's methods share one receiver variable (ADR 0034), so a
//! record of many methods checks in time and type size that grow gently with
//! the method count, and methods may call each other through `self`.

use goat_checker::check_with_prelude;
use std::time::{Duration, Instant};

fn best_time(source: &str) -> Duration {
    (0..5)
        .map(|_| {
            let start = Instant::now();
            if let Err(errors) = check_with_prelude("", source) {
                panic!("should check: {source}\n{errors:?}");
            }
            start.elapsed()
        })
        .min()
        .expect("five runs")
}

/// `r = {x: 0, m0: …, m1: …}` and a call of the last method. With `callers`,
/// every odd method calls the even one before it through `self`; the rest
/// return `{...self, x: self.x + 1}`.
fn record_of_methods(count: usize, callers: bool) -> String {
    let mut fields = vec!["x: 0".to_string()];
    for i in 0..count {
        let body = if callers && i % 2 == 1 {
            format!("self.m{}()", i - 1)
        } else {
            "{...self, x: self.x + 1}".to_string()
        };
        fields.push(format!("m{i}: program(self) do {body} done"));
    }
    format!("r = {{{}}}\nr.m{}().x", fields.join(", "), count - 1)
}

#[test]
fn thirty_methods_half_of_them_calling_siblings_check() {
    let source = record_of_methods(30, true);
    let elapsed = best_time(&source);
    assert!(elapsed < Duration::from_secs(5), "{elapsed:?}");
}

#[test]
fn thirty_updating_methods_check() {
    let source = record_of_methods(30, false);
    let elapsed = best_time(&source);
    assert!(elapsed < Duration::from_secs(5), "{elapsed:?}");
}

#[test]
fn the_three_method_model_checks_in_a_few_milliseconds_in_release() {
    let source = "init = program() do {x: 0, y: 1,
            update: program(self) do {...self, x: self.x + 1} done,
            nudge: program(self) do {...self, y: self.y + 1} done,
            draw: program(self) do self.x done} done
        run = program(m, n) do if n == 0 then m else run(m.update(), n - 1) done done
        m = run(init(), 4)
        m.nudge().update().draw()";
    let elapsed = best_time(source);
    let limit = if cfg!(debug_assertions) { 2000 } else { 20 };
    assert!(elapsed < Duration::from_millis(limit), "{elapsed:?}");
}

#[test]
fn a_record_with_far_too_many_methods_is_refused_not_hung() {
    let source = record_of_methods(120, false);
    let start = Instant::now();
    let Err(errors) = check_with_prelude("", &source) else {
        panic!("a record of 120 methods should not check");
    };
    assert!(errors[0].message.starts_with("program too complex"));
    assert!(
        start.elapsed() < Duration::from_secs(10),
        "{:?}",
        start.elapsed()
    );
}

#[test]
fn a_method_called_on_a_siblings_result_is_refused_not_hung() {
    let source = "counter = {n: 0,
        bump: program(self) do {...self, n: self.n + 1} done,
        twice: program(self) do self.bump().bump() done,
        thrice: program(self) do self.twice().bump() done,
        total: program(self) do self.thrice().twice().n done}
        counter.total()";
    let start = Instant::now();
    assert!(check_with_prelude("", source).is_err());
    assert!(
        start.elapsed() < Duration::from_secs(10),
        "{:?}",
        start.elapsed()
    );
}
