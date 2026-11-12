//! A record literal's methods share one receiver type (ADR 0034), so the model
//! with several methods that return updated copies of itself runs through the
//! interpreter and wasm, which must print the same lines.

#[allow(dead_code)]
mod support;

use support::run;

const MODEL: &str = "init = program() do {x: 0, y: 1,
        update: program(self) do {...self, x: self.x + 1} done,
        nudge: program(self) do {...self, y: self.y + 1} done,
        draw: program(self) do self.x * 10 + self.y done} done
    run = program(m, n) do if n == 0 then m else run(m.update(), n - 1) done done\n";

#[test]
fn a_chain_of_three_methods_runs() {
    let src = format!("{MODEL}m = init()\nprint(m.nudge().update().draw())");
    assert_eq!(run(&src), "12");
}

#[test]
fn a_looped_three_method_model_runs() {
    let src = format!("{MODEL}m = run(init(), 4)\nprint(m.draw());\nprint(m.nudge().draw())");
    assert_eq!(run(&src), "41\n42");
}

#[test]
fn an_extension_of_a_record_with_methods_runs_its_methods() {
    let src = "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
        big = {...ball, size: 10}
        print(big.moved().size + big.moved().x)";
    assert_eq!(run(src), "12");
}

#[test]
fn a_method_added_in_a_spread_literal_runs() {
    let src = "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
        other = {...ball, twice: program(self, k) do self.x * k done}
        print(other.moved().twice(5))";
    assert_eq!(run(src), "10");
}

#[test]
fn methods_of_two_records_with_the_same_shape_run_in_a_list() {
    let src = "make = program(n) do {n: n, get: program(self) do self.n done} done
        pair = [make(1), make(2)]
        print(length(pair));
        print(make(7).get())";
    assert_eq!(run(src), "2\n7");
}

fn updating_record(methods: usize) -> String {
    let fields: Vec<String> = (0..methods)
        .map(|i| format!("m{i}: program(self) do {{...self, x: self.x + 1}} done"))
        .collect();
    format!("ball = {{x: 0, {}}}\n", fields.join(", "))
}

#[test]
fn twenty_updating_methods_run() {
    let chain: String = (0..20).map(|i| format!(".m{i}()")).collect();
    let src = format!("{}print(ball{chain}.x)", updating_record(20));
    assert_eq!(run(&src), "20");
}

#[test]
fn ten_methods_calling_siblings_run() {
    let fields: Vec<String> = (0..9)
        .map(|i| format!("m{i}: program(self) do self.m{}() done", i + 1))
        .collect();
    let src = format!(
        "ball = {{x: 0, {}, m9: program(self) do {{...self, x: self.x + 1}} done}}\n\
         print(ball.m0().x);\nprint(ball.m5().m0().x)",
        fields.join(", ")
    );
    assert_eq!(run(&src), "1\n2");
}
