#[test]
fn check_never_panics() {
    bolero::check!().for_each(|data: &[u8]| {
        if let Ok(source) = std::str::from_utf8(data) {
            let _ = goat_checker::check(source);
        }
    });
}
