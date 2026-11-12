//! Methods on a receiver with no fixed record type (a parameter, a call
//! result, a spread copy) run through the interpreter and wasm, which must
//! print the same lines.

#[allow(dead_code)]
mod support;

use support::run;

const BALL: &str =
    "ball = {x: 1, speed: 2, moved: program(self) do {...self, x: self.x + self.speed} done}\n";

#[test]
fn a_function_calls_two_methods_on_its_parameter() {
    let src = "f = program(x) do x.do_thing(); x.do_another(5) done
        obj = {n: 10, do_thing: program(self) do print(self.n) done, do_another: program(self, k) do self.n + k done}
        print(f(obj))";
    assert_eq!(run(src), "10\n15");
}

#[test]
fn a_parameter_receiver_runs() {
    let src = format!("{BALL}step = program(p) do p.moved() done\nprint(step(ball).x)");
    assert_eq!(run(&src), "3");
}

#[test]
fn a_call_result_receiver_runs() {
    let src = format!("{BALL}b2 = ball.moved()\nb3 = b2.moved()\nprint(b3.x)");
    assert_eq!(run(&src), "5");
}

#[test]
fn a_spread_copy_receiver_runs() {
    let src = format!("{BALL}c = {{...ball, speed: 5}}\nc2 = c.moved()\nprint(c2.x)");
    assert_eq!(run(&src), "6");
}

#[test]
fn an_update_loop_over_a_model_with_methods_runs() {
    let src = "init = program() do {x: 0, speed: 3, update: program(self) do {...self, x: self.x + self.speed} done, draw: program(self) do self.x done} done
        run = program(m, n) do if n == 0 then m.draw() else run(m.update(), n - 1) done done
        print(run(init(), 4))";
    assert_eq!(run(src), "12");
}

#[test]
fn a_function_whose_type_mentions_itself_captures_its_parameter() {
    let src = "h = program(r) do
          stopped = program() do r.stop done
          if stopped() then 0 else 1 + (r.g)({stop: true, g: h}) done
        done
        print(h({stop: false, g: h}))";
    assert_eq!(run(src), "1");
}
