//! Embed goat in a Rust program: describe what the host offers, compile a
//! script against it, and run it with a host that answers the script's calls.
//!
//!     cargo run -p goat --features native --example embed

use goat::native::run_to_end;
use goat::{Boundary, GoatError, Host, HostInterface, HostValue};

struct Logger(Vec<String>);

impl Host for Logger {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        (module == "log" && name == "line").then(|| (vec![Boundary::Str], Boundary::Unit))
    }

    fn call(&mut self, _: &str, _: &str, args: &[HostValue]) -> Result<HostValue, String> {
        if let [HostValue::Str(text)] = args {
            self.0.push(text.clone());
        }
        Ok(HostValue::Unit)
    }
}

fn first_message(errors: Vec<GoatError>) -> String {
    errors[0].message.clone()
}

fn main() -> Result<(), String> {
    let interface = HostInterface::with_stdlib("log = foreign \"log\" \"line\" (String) -> Unit");
    let script = "log(\"hello from goat\"); print(6 * 7)";
    let wasm = goat::compile(script, &interface).map_err(first_message)?;

    let finished = run_to_end(&wasm, Logger(Vec::new()))?;
    println!("printed: {:?}", finished.printed);
    println!("logged: {:?}", finished.host.0);
    Ok(())
}

#[cfg(test)]
mod tests {
    use goat::{GoatError, Group, HostInterface, Row, Ty, Vocab};

    #[test]
    fn the_facade_names_the_types_a_host_needs() {
        let vocab: Vocab = Vocab::turtle();
        let interface = HostInterface::with_vocab("", vocab);
        let (ty, _): (Ty, Vec<GoatError>) = goat::check("1", &interface).expect("checks");
        assert_eq!(ty.to_string(), "Number");
        let _: Option<(Row, Group)> = None;
    }

    #[test]
    fn runs() {
        super::main().expect("example runs");
    }
}
