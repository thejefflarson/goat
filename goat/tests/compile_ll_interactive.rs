use goat::{HostInterface, Profile, compile_ll};

#[test]
fn an_interactive_program_exports_the_contract_and_no_main() {
    let ir = compile_ll(
        Profile::Desktop,
        include_str!("../../examples/interactive.goat"),
        &HostInterface::turtle(),
    )
    .unwrap();
    for export in [
        "@goat_attach",
        "@goat_setup",
        "@goat_update",
        "@goat_draw",
        "@goat_release_model",
        "@goat_shutdown",
        "@goat_snapshot",
        "@goat_refresh",
        "@goat_reason_part",
        "@goat_free_static",
        "@goat_alloc",
        "@goat_event_Tick",
        "@goat_event_KeyDown",
        "@goat_subscriptions",
    ] {
        assert!(
            ir.contains(&format!("{export}(")) || ir.contains(&format!("{export} =")),
            "{export} in:\n{ir}"
        );
    }
    assert!(!ir.contains("@goat_main"), "{ir}");
    assert!(
        ir.contains("@goat.frame_present"),
        "draw presents one frame"
    );
}

#[test]
fn a_desktop_call_checks_the_stack_and_an_embedded_one_counts_depth() {
    let recursive = "f = program(n) do f(n) + 1 done\nf(1)";
    let host = HostInterface::new("");
    let desktop = compile_ll(Profile::Desktop, recursive, &host).unwrap();
    assert!(desktop.contains("@llvm.frameaddress.p0"), "{desktop}");
    let embedded = compile_ll(Profile::Embedded, recursive, &host).unwrap();
    assert!(!embedded.contains("frameaddress"), "{embedded}");
    assert!(embedded.contains("icmp ugt i32"), "{embedded}");
}
