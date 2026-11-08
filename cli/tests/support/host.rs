//! A host with a handful of functions in module `test`, used by both the
//! interpreter and wasmtime so a program that calls them runs the same on each.
//! Every call is recorded in `log`, which is how a test sees the order and
//! count of calls whose result is `Unit`.

use goat_checker::hir::Boundary::{self, Bool, Int, Number, Str, Unit};
use goat_mir::{Host, HostValue};

#[derive(Default)]
pub struct TestHost {
    pub log: Vec<String>,
}

impl Host for TestHost {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        if module != "test" {
            return None;
        }
        Some(match name {
            "note" => (vec![Number], Unit),
            "double" => (vec![Number], Number),
            "count" => (vec![], Int),
            "bump" => (vec![Int], Int),
            "negate" => (vec![Bool], Bool),
            "say" => (vec![Str], Unit),
            "shout" => (vec![Str], Str),
            "greeting" => (vec![], Str),
            "nothing" => (vec![], Str),
            "mix" => (vec![Number, Bool, Str], Number),
            _ => return None,
        })
    }

    fn call(&mut self, _: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        use HostValue as V;
        let shown = |v: &V| match v {
            V::Number(x) => goat::format_number(*x),
            V::Int(n) => n.to_string(),
            V::Bool(b) => b.to_string(),
            V::Unit => "unit".into(),
            V::Str(s) => format!("{s:?}"),
        };
        let line: Vec<String> = args.iter().map(shown).collect();
        self.log.push(format!("{name}({})", line.join(", ")));
        Ok(match (name, args) {
            ("note", _) | ("say", _) => V::Unit,
            ("double", [V::Number(x)]) => V::Number(x * 2.0),
            ("count", []) => V::Int(7),
            ("bump", [V::Int(n)]) => V::Int(n + 1),
            ("negate", [V::Bool(b)]) => V::Bool(!b),
            ("shout", [V::Str(s)]) => V::Str(format!("{}!", s.to_uppercase())),
            ("greeting", []) => V::Str("hello from the host".into()),
            ("nothing", []) => V::Str(String::new()),
            ("mix", [V::Number(x), V::Bool(b), V::Str(s)]) => {
                V::Number(x + f64::from(*b) + s.len() as f64)
            }
            _ => return Err(format!("bad call to test.{name}")),
        })
    }
}
