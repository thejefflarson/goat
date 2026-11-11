//! The embedded `blink` example against a recording host: a board's gpio,
//! timer and serial are host functions, so a host that notes each call shows
//! exactly what the board would have been told, under WAMR's fast interpreter.

use goat::Boundary::{Bool, Int, Str, Unit};
use goat::{Boundary, Host, HostInterface, HostValue, Profile};
use goat_wamr::{Interp, run_to_end_on};

#[derive(Debug, PartialEq)]
enum Call {
    Write(i64, bool),
    Delay(i64),
    Print(String),
}

#[derive(Default)]
struct Recording {
    calls: Vec<Call>,
    clock: i64,
}

impl Recording {
    fn writes(&self) -> Vec<(i64, bool)> {
        self.calls
            .iter()
            .filter_map(|call| match call {
                Call::Write(pin, on) => Some((*pin, *on)),
                _ => None,
            })
            .collect()
    }

    fn serial(&self) -> Vec<&str> {
        self.calls
            .iter()
            .filter_map(|call| match call {
                Call::Print(text) => Some(text.as_str()),
                _ => None,
            })
            .collect()
    }
}

impl Host for Recording {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        Some(match (module, name) {
            ("gpio", "write") => (vec![Int, Bool], Unit),
            ("timer", "delay") => (vec![Int], Unit),
            ("timer", "millis") => (vec![], Int),
            ("serial", "print") => (vec![Str], Unit),
            _ => return None,
        })
    }

    fn call(&mut self, module: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        use HostValue as V;
        Ok(match (module, name, args) {
            ("gpio", "write", [V::Int(pin), V::Bool(on)]) => {
                self.calls.push(Call::Write(*pin, *on));
                V::Unit
            }
            ("timer", "delay", [V::Int(ms)]) => {
                self.clock += ms;
                self.calls.push(Call::Delay(*ms));
                V::Unit
            }
            ("timer", "millis", []) => V::Int(self.clock),
            ("serial", "print", [V::Str(text)]) => {
                self.calls.push(Call::Print(text.clone()));
                V::Unit
            }
            _ => return Err(format!("bad call to {module}.{name}")),
        })
    }
}

fn record(src: &str) -> (Vec<String>, Recording) {
    let (wasm, _) = goat::compile_for(Profile::Embedded, src, &HostInterface::turtle())
        .unwrap_or_else(|e| panic!("embedded program compiles: {e:?}"));
    let finished = run_to_end_on(Interp::Fast, &wasm, Recording::default()).expect("module loads");
    let live = finished.result.expect("program finishes");
    assert_eq!(live, 0, "nothing left allocated after teardown");
    (finished.printed, finished.host)
}

#[test]
fn blink_toggles_the_led_three_times_and_reports_on_serial() {
    let (printed, host) = record(include_str!("../../examples/blink.goat"));
    assert!(printed.is_empty());
    let on_off = [(2, true), (2, false)];
    assert_eq!(host.writes(), on_off.repeat(3));
    assert_eq!(host.serial(), ["blinking"]);
    assert_eq!(host.clock, 3000);
    assert_eq!(
        host.calls[..3],
        [
            Call::Print("blinking".into()),
            Call::Write(2, true),
            Call::Delay(500)
        ]
    );
}

#[test]
fn a_host_clock_reads_back_through_the_boundary() {
    let src = "\
now = foreign \"timer\" \"millis\" () -> Int
delay = foreign \"timer\" \"delay\" (Int) -> Unit
delay(40); delay(2);
print(now())
";
    let (printed, host) = record(src);
    assert_eq!(printed, ["42"]);
    assert_eq!(host.calls, [Call::Delay(40), Call::Delay(2)]);
}

#[test]
fn a_foreign_name_the_host_lacks_is_refused_at_load() {
    let src = "led = foreign \"gpio\" \"toggle\" (Int) -> Unit\nled(1)";
    let (wasm, _) =
        goat::compile_for(Profile::Embedded, src, &HostInterface::turtle()).expect("compiles");
    let error = run_to_end_on(Interp::Fast, &wasm, Recording::default())
        .err()
        .expect("load fails");
    assert!(error.contains("gpio.toggle"), "{error}");
}
