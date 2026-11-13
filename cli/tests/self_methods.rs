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

const COUNTER: &str = "counter = {n: 0,
    bump: program(self) do {...self, n: self.n + 1} done,
    back: program(self) do {...self, n: self.n - 1} done,
    twice: program(self) do self.bump().bump() done,
    three: program(self) do self.bump().bump().bump() done,
    both: program(self) do self.bump().back() done,
    five: program(self) do self.twice().bump().twice() done,
    peek: program(self) do self.n done}\n";

#[test]
fn a_method_called_on_a_siblings_result_runs() {
    let src = format!(
        "{COUNTER}print(counter.twice().n);\nprint(counter.three().n);\nprint(counter.both().n);\n\
         print(counter.five().n);\nprint(counter.twice().twice().bump().n);\nprint(counter.five().peek())"
    );
    assert_eq!(run(&src), "2\n3\n0\n5\n5\n5");
}

#[test]
fn a_ten_call_chain_in_a_method_runs() {
    let src = format!(
        "counter = {{n: 0,
            bump: program(self) do {{...self, n: self.n + 1}} done,
            long: program(self) do self.{} done}}\nprint(counter.long().n);\nprint(counter.long().long().n)",
        ["bump()"; 10].join(".")
    );
    assert_eq!(run(&src), "10\n20");
}

#[test]
fn twenty_methods_some_of_them_chaining_run() {
    let mut fields = vec![
        "n: 0".to_string(),
        "bump: program(self) do {...self, n: self.n + 1} done".to_string(),
    ];
    for i in 0..19 {
        let body = match i % 3 {
            0 => "self.bump().bump()".to_string(),
            1 => format!("self.m{}().bump()", i - 1),
            _ => "{...self, n: self.n - 1}".to_string(),
        };
        fields.push(format!("m{i}: program(self) do {body} done"));
    }
    let src = format!(
        "r = {{{}}}\nprint(r.m18().n);\nprint(r.m16().n);\nprint(r.m17().m0().n)",
        fields.join(", ")
    );
    assert_eq!(run(&src), "2\n3\n1");
}

#[test]
fn a_method_declared_after_the_method_that_chains_on_it_runs() {
    let src = "counter = {n: 0,
        three: program(self) do self.twice().bump() done,
        twice: program(self) do self.bump().bump() done,
        bump: program(self) do {...self, n: self.n + 1} done}
        print(counter.three().n)";
    assert_eq!(run(src), "3");
}
