// Full-pipeline panic-freedom: arbitrary source through parse → check → mono →
// wasm must never panic. It upholds "errors come only from the checker" — any
// ill-formed or ill-typed input is a `Vec<GoatError>`, never a mono/codegen
// crash. `check_never_panics` stops at the checker; this drives the whole
// `goat::compile` pipeline to the wasm bytes.
#[test]
fn compile_never_panics() {
    bolero::check!().for_each(|data: &[u8]| {
        if let Ok(source) = std::str::from_utf8(data) {
            let _ = goat::compile_turtle(source);
        } else {
            // Drive the lossy path: replacement characters (U+FFFD) are valid
            // UTF-8 that may reach all compiler phases, expanding coverage of
            // the diagnostic-formatting and character-handling code paths.
            let _ = goat::compile_turtle(&String::from_utf8_lossy(data));
        }
    });
}
