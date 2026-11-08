// Full-pipeline panic-freedom: arbitrary source through parse → check → mono →
// wasm must never panic. It upholds "errors come only from the checker" — any
// ill-formed or ill-typed input is a `Vec<GoatError>`, never a mono/codegen
// crash. `check_never_panics` stops at the checker; this drives the whole
// `goat::compile` pipeline to the wasm bytes.
#[test]
fn compile_never_panics() {
    bolero::check!().for_each(|data: &[u8]| {
        if let Ok(source) = std::str::from_utf8(data) {
            let _ = goat::compile(source);
        }
    });
}
