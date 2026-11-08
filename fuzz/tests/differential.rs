#[path = "../../cli/tests/support/mod.rs"]
#[allow(dead_code)]
mod support;

#[test]
fn differential_interp_vs_wasm() {
    bolero::check!().for_each(|data: &[u8]| {
        support::agree_or_trap(&support::generate(data));
    });
}
