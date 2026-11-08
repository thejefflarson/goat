fn main() {
    let src = std::path::Path::new("../tree-sitter-goat-slice/src");
    let mut build = cc::Build::new();
    build.include(src).file(src.join("parser.c"));
    // On wasm32-unknown-unknown there is no libc; tree-sitter-language ships the
    // headers and the tree-sitter runtime supplies the implementations.
    if let Ok(headers) = std::env::var("DEP_TREE_SITTER_LANGUAGE_WASM_HEADERS") {
        build.include(headers);
    }
    build.compile("tree-sitter-goat-slice");
    println!("cargo:rerun-if-changed={}", src.join("parser.c").display());
}
