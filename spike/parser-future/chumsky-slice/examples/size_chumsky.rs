//! Links the parser into a standalone `.wasm` so its code size can be measured:
//! `cargo build --release --example size --target wasm32-unknown-unknown`.
fn main() {
    let src = std::hint::black_box(String::from("a = 1; match a do A then 2 done"));
    std::hint::black_box(chumsky_slice::parse_items(&src));
}
