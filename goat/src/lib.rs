//! The goat compiler pipeline: source text to a WebAssembly module.

use goat_checker::GoatError;
use goat_checker::hir::Span;
pub use goat_mir::Profile;

#[cfg(feature = "native")]
pub mod native;

/// The vocabulary a host provides: the `foreign` functions a program may call,
/// declared in goat source ahead of the program. The events `update` receives
/// and the shapes `draw` returns are fixed by the checker's `vocab` (ADR 0015),
/// so they are not part of this value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostInterface {
    prelude: String,
}

impl HostInterface {
    /// A host whose complete prelude is `prelude`, standard library included
    /// or not.
    pub fn new(prelude: impl Into<String>) -> Self {
        HostInterface {
            prelude: prelude.into(),
        }
    }

    /// A host that offers the standard library plus `declarations`, goat
    /// source made of `foreign` bindings.
    ///
    /// `declarations` must not shadow any name already defined in the standard
    /// library; debug builds assert this to catch mistakes early.
    pub fn with_stdlib(declarations: &str) -> Self {
        debug_assert!(
            !shadows_stdlib(declarations),
            "declarations shadow a stdlib name"
        );
        Self::new(format!("{}\n{declarations}", goat_checker::STDLIB))
    }

    /// The turtle host the CLI and the web player implement.
    pub fn turtle() -> Self {
        Self::with_stdlib(goat_checker::TURTLE_VOCAB)
    }

    pub fn prelude(&self) -> &str {
        &self.prelude
    }
}

/// True if any top-level binding name in `declarations` is already defined in
/// the standard library. Uses a lightweight line scan: the first identifier on
/// a non-comment, non-empty, non-keyword line is treated as the binding name.
fn shadows_stdlib(declarations: &str) -> bool {
    use std::collections::HashSet;
    // Keywords that open a construct but are not binding names.
    const KW: &[&str] = &[
        "tag", "if", "then", "else", "done", "do", "program", "foreign", "match",
    ];
    fn binding_names(src: &str) -> HashSet<&str> {
        src.lines()
            .filter_map(|line| {
                let t = line.trim_start();
                if t.starts_with("//") || t.is_empty() {
                    return None;
                }
                let name = t.split(|c: char| !c.is_alphanumeric() && c != '_').next()?;
                if name.is_empty() || KW.contains(&name) {
                    None
                } else {
                    Some(name)
                }
            })
            .collect()
    }
    let stdlib = binding_names(goat_checker::STDLIB);
    binding_names(declarations)
        .iter()
        .any(|n| stdlib.contains(n))
}

/// Parse, type-check, monomorphize, and emit a wasm module for `source`
/// against the vocabulary of `host`.
pub fn compile(source: &str, host: &HostInterface) -> Result<Vec<u8>, Vec<GoatError>> {
    compile_with_warnings(source, host).map(|(wasm, _)| wasm)
}

/// [`compile`] against the turtle host.
pub fn compile_turtle(source: &str) -> Result<Vec<u8>, Vec<GoatError>> {
    compile(source, &HostInterface::turtle())
}

/// Like [`compile`], also returning the checker's non-fatal warnings.
pub fn compile_with_warnings(
    source: &str,
    host: &HostInterface,
) -> Result<(Vec<u8>, Vec<GoatError>), Vec<GoatError>> {
    compile_for(Profile::Desktop, source, host)
}

/// Like [`compile_with_warnings`], for the number widths of `profile`.
pub fn compile_for(
    profile: Profile,
    source: &str,
    host: &HostInterface,
) -> Result<(Vec<u8>, Vec<GoatError>), Vec<GoatError>> {
    compile_with(profile, source, host, goat_wasm::emit)
}

/// Like [`compile`] for an interactive program, emitting a module that imports
/// its memory and allocator state from the host, so a recompiled module can be
/// swapped in over the same heap (see `native::Interactive::reload`). A
/// run-once program is an error.
pub fn compile_reloadable(source: &str, host: &HostInterface) -> Result<Vec<u8>, Vec<GoatError>> {
    compile_with(Profile::Desktop, source, host, goat_wasm::emit_reloadable).map(|(wasm, _)| wasm)
}

fn compile_with(
    profile: Profile,
    source: &str,
    host: &HostInterface,
    emit: fn(&goat_mir::Program) -> Result<Vec<u8>, goat_wasm::EmitError>,
) -> Result<(Vec<u8>, Vec<GoatError>), Vec<GoatError>> {
    let mut checked = goat_checker::check_with_prelude(host.prelude(), source)?;
    let warnings = std::mem::take(&mut checked.typed.warnings);
    let program = goat_mir::mono_for(&checked, profile)?;
    verify_mir(&program)?;
    let wasm = emit(&program).map_err(|e| vec![GoatError::new(Span::new(0, 0), e.to_string())])?;
    Ok((wasm, warnings))
}

/// Verification costs about a tenth of mono, so it runs in release too: a
/// mono bug becomes a reported compiler error here instead of a module the
/// backend turns into something unsound.
fn verify_mir(program: &goat_mir::Program) -> Result<(), Vec<GoatError>> {
    goat_mir::verify(program).map_err(|errors| {
        vec![GoatError::new(
            Span::new(0, 0),
            format!(
                "internal compiler error: the generated program is malformed ({} problem(s), first: {:?})",
                errors.len(),
                errors[0]
            ),
        )]
    })
}

/// Format a number the way the program's `print` shows it: whole values within
/// ±1e18 as integers, everything else like C's `%.15g`.
pub fn format_number(x: f64) -> String {
    if x > -1e18 && x < 1e18 && x == x.trunc() {
        return (x as i64).to_string();
    }
    format_g15(x)
}

pub fn format_bool(b: bool) -> &'static str {
    if b { "true" } else { "false" }
}

#[cfg(kani)]
mod proofs {
    use super::format_bool;

    #[kani::proof]
    fn format_bool_matches_spec() {
        let b: bool = kani::any();
        let text = format_bool(b).as_bytes();
        if b {
            assert!(matches!(text, [b't', b'r', b'u', b'e']));
        } else {
            assert!(matches!(text, [b'f', b'a', b'l', b's', b'e']));
        }
    }
}

fn format_g15(x: f64) -> String {
    if x.is_nan() {
        return "nan".to_string();
    }
    if x.is_infinite() {
        return if x < 0.0 { "-inf" } else { "inf" }.to_string();
    }
    let sci = format!("{x:.14e}");
    let (mantissa, exp) = sci.split_once('e').expect("exponent form");
    let exp: i32 = exp.parse().expect("integer exponent");
    if (-4..15).contains(&exp) {
        let decimals = (14 - exp) as usize;
        return strip_zeros(&format!("{x:.decimals$}")).to_string();
    }
    let sign = if exp < 0 { '-' } else { '+' };
    format!("{}e{sign}{:02}", strip_zeros(mantissa), exp.abs())
}

fn strip_zeros(s: &str) -> &str {
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.')
    } else {
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_malformed_program_is_a_compiler_error_not_a_module() {
        let checked = goat_checker::check_with_prelude(HostInterface::turtle().prelude(), "1")
            .expect("checks");
        let mut program = goat_mir::mono_for(&checked, Profile::Desktop).expect("lowers");
        assert!(verify_mir(&program).is_ok());
        program.funcs.clear();
        let errors = verify_mir(&program).unwrap_err();
        assert!(errors[0].message.starts_with("internal compiler error"));
    }

    #[test]
    fn whole_numbers_print_as_integers() {
        assert_eq!(format_number(55.0), "55");
        assert_eq!(format_number(1_000_000.0), "1000000");
        assert_eq!(format_number(-0.0), "0");
        assert_eq!(format_number(-7.0), "-7");
    }

    #[test]
    fn fractions_use_fifteen_significant_digits() {
        assert_eq!(format_number(2.5), "2.5");
        assert_eq!(format_number(0.1 + 0.2), "0.3");
        assert_eq!(format_number(1.0 / 3.0), "0.333333333333333");
        assert_eq!(format_number(-0.0001), "-0.0001");
    }

    #[test]
    fn out_of_range_values_use_exponent_form() {
        assert_eq!(format_number(1e18), "1e+18");
        assert_eq!(format_number(1.5e300), "1.5e+300");
        assert_eq!(format_number(0.00001), "1e-05");
        assert_eq!(format_number(f64::INFINITY), "inf");
        assert_eq!(format_number(f64::NEG_INFINITY), "-inf");
        assert_eq!(format_number(f64::NAN), "nan");
    }

    #[test]
    fn compile_produces_a_wasm_module() {
        let bytes = compile_turtle("1 + 2 * 3").expect("compiles");
        assert_eq!(&bytes[..4], b"\0asm");
    }

    #[test]
    fn compile_returns_warnings_alongside_the_module() {
        let src = "tag Cirle tag Circle match Cirle(5) do Circle(r) then r else 0 done";
        let (wasm, warnings) =
            compile_with_warnings(src, &HostInterface::turtle()).expect("compiles");
        assert_eq!(&wasm[..4], b"\0asm");
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].message.contains("Cirle"));
    }

    #[test]
    fn compile_threads_check_errors() {
        assert!(compile_turtle("1 + true").is_err());
        assert!(compile_turtle("x").is_err());
    }

    #[test]
    fn the_turtle_host_is_the_built_in_prelude() {
        assert_eq!(HostInterface::turtle().prelude(), goat_checker::PRELUDE);
    }

    #[test]
    fn turtle_calls_compile_under_the_turtle_host_only() {
        let turn = "forward(10); left(90)";
        assert!(compile(turn, &HostInterface::turtle()).is_ok());
        assert!(compile(turn, &HostInterface::with_stdlib("")).is_err());
    }

    #[test]
    fn a_custom_host_compiles_a_program_that_uses_its_vocabulary() {
        let synth = HostInterface::with_stdlib(
            "beep = foreign \"synth\" \"beep\" (Number) -> Unit\n\
             volume = foreign \"synth\" \"volume\" () -> Number\n",
        );
        let program = "beep(volume() * 2)";
        let wasm = compile(program, &synth).expect("compiles");
        assert!(wasm.windows(4).any(|w| w == b"beep"));
        assert!(compile(program, &HostInterface::turtle()).is_err());
    }

    #[test]
    fn a_host_without_the_standard_library_lacks_its_definitions() {
        let bare = HostInterface::new("");
        assert!(compile("link(1, Empty)", &bare).is_err());
        assert!(compile("1 + 2", &bare).is_ok());
    }
}
