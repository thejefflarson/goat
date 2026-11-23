use goat::Profile;
use goat_mir::*;

/// What the program prints and leaves allocated under the interpreter.
pub fn interpreted(profile: Profile, source: &str) -> (Vec<String>, usize) {
    let checked = goat_checker::check(source).expect("type-checks");
    let program = goat_mir::mono_for(&checked, profile).expect("monomorphizes");
    assert_eq!(verify(&program), Ok(()), "{source}");
    let out = goat_mir::run(&program).expect("interprets");
    let mut printed = Vec::new();
    for line in &out.printed {
        printed.push(
            line.iter()
                .map(|piece| match piece {
                    Piece::Number(x) => goat::format_number(*x),
                    Piece::Int(n) => n.to_string(),
                    Piece::Text(bytes) => String::from_utf8_lossy(bytes).into_owned(),
                })
                .collect(),
        );
    }
    match out.value {
        Value::Int(n) => printed.push(n.to_string()),
        Value::Float(x) => printed.push(goat::format_number(x)),
        Value::Bool(b) => printed.push(goat::format_bool(b).to_string()),
        Value::Unit => {}
        Value::Ptr(_) => printed.push(String::from_utf8(out.root_string.unwrap()).unwrap()),
    }
    (printed, out.live_allocations)
}
