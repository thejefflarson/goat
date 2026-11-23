use goat::{HostInterface, Profile, compile_ll};

fn host() -> HostInterface {
    HostInterface::new("")
}

#[test]
fn arithmetic_source_compiles_to_ir() {
    let ir = compile_ll(
        Profile::Desktop,
        "if 1 < 2 then 3 * 4 - 5 else 0 done",
        &host(),
    )
    .unwrap();
    assert!(
        ir.contains("define tailcc i64 @goat_entry(ptr %inst) nounwind"),
        "{ir}"
    );
    assert!(ir.contains("@llvm.smul.with.overflow.i64"), "{ir}");
}

#[test]
fn embedded_source_uses_32_bit_ints() {
    let ir = compile_ll(Profile::Embedded, "6 * 7", &host()).unwrap();
    assert!(ir.contains("@llvm.smul.with.overflow.i32"), "{ir}");
}

#[test]
fn compiled_source_parses_with_clang() {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let Ok(mut child) = Command::new("clang")
        .args(["-x", "ir", "-c", "-o", "/dev/null", "-"])
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    else {
        eprintln!("skipping: clang is not on PATH");
        return;
    };
    let ir = compile_ll(
        Profile::Desktop,
        "if 1 < 2 then 7 // 2 + 7 % 2 else 0 done",
        &host(),
    )
    .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(ir.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn an_unsupported_construct_is_a_compiler_error() {
    let errors = compile_ll(
        Profile::Embedded,
        include_str!("../../examples/interactive.goat"),
        &HostInterface::new(goat_checker::PRELUDE),
    )
    .unwrap_err();
    assert!(
        errors[0]
            .to_string()
            .contains("not yet supported by the native backend")
    );
}
