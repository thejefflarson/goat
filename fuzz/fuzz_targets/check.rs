#[macro_use]
extern crate afl;

// Fuzz the whole frontend: parse, name-resolve, and type-check. Any panic here
// (rather than a returned error) is a bug. Supersedes the old parser-only
// target, which exercised the now-removed AST/renamer.
fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(source) = std::str::from_utf8(data) {
            let _ = goat_checker::check(source);
        }
    });
}
