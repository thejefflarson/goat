//! The goat compiler pipeline: source text to a WebAssembly module.

use goat_checker::GoatError;
use goat_checker::hir::Span;

/// Parse, type-check, monomorphize, and emit a wasm module for `source`.
pub fn compile(source: &str) -> Result<Vec<u8>, Vec<GoatError>> {
    compile_with_prelude(goat_checker::PRELUDE, source)
}

/// Like [`compile`], with `prelude` standing in for the built-in one.
pub fn compile_with_prelude(prelude: &str, source: &str) -> Result<Vec<u8>, Vec<GoatError>> {
    compile_with_warnings(prelude, source).map(|(wasm, _)| wasm)
}

/// Like [`compile_with_prelude`], also returning the checker's non-fatal warnings.
pub fn compile_with_warnings(
    prelude: &str,
    source: &str,
) -> Result<(Vec<u8>, Vec<GoatError>), Vec<GoatError>> {
    let mut checked = goat_checker::check_with_prelude(prelude, source)?;
    let warnings = std::mem::take(&mut checked.typed.warnings);
    let program = goat_mir::mono(&checked)?;
    let wasm = goat_wasm::emit(&program)
        .map_err(|e| vec![GoatError::new(Span::new(0, 0), e.to_string())])?;
    Ok((wasm, warnings))
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
        let bytes = compile("1 + 2 * 3").expect("compiles");
        assert_eq!(&bytes[..4], b"\0asm");
    }

    #[test]
    fn compile_returns_warnings_alongside_the_module() {
        let src = "match Cirle(5) do Circle(r) then r else 0 done";
        let (wasm, warnings) = compile_with_warnings(goat_checker::PRELUDE, src).expect("compiles");
        assert_eq!(&wasm[..4], b"\0asm");
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].message.contains("Cirle"));
    }

    #[test]
    fn compile_threads_check_errors() {
        assert!(compile("1 + true").is_err());
        assert!(compile("x").is_err());
    }
}
