//! Embed goat in a Rust program: describe what the host offers, compile a
//! script against it, and run it with a host that answers the script's calls.
//!
//!     cargo run -p goat --features native --example embed

use goat::HostInterface;
use goat::native::{Boundary, Host, HostValue, run_to_end};

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

fn main() -> Result<(), String> {
    let interface = HostInterface::with_stdlib("log = foreign \"log\" \"line\" (String) -> Unit");
    let script = "log(\"hello from goat\"); print(6 * 7)";
    let wasm = goat::compile(script, &interface).map_err(|errors| errors[0].message.clone())?;

    let finished = run_to_end(&wasm, Logger(Vec::new()))?;
    println!("printed: {:?}", finished.printed);
    println!("logged: {:?}", finished.host.0);
    Ok(())
}
