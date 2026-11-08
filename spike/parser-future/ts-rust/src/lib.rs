//! SPIKE (throwaway): the tree-sitter Rust binding over the generated slice
//! grammar, to find out whether it builds for `wasm32-unknown-unknown`.

use tree_sitter::{Parser, Tree};
use tree_sitter_language::LanguageFn;

unsafe extern "C" {
    fn tree_sitter_goat_slice() -> *const ();
}

pub const LANGUAGE: LanguageFn = unsafe { LanguageFn::from_raw(tree_sitter_goat_slice) };

/// Parse `src`; error recovery is built in, so this returns a tree for any input.
pub fn parse(src: &str) -> Tree {
    let mut parser = Parser::new();
    parser
        .set_language(&LANGUAGE.into())
        .expect("grammar ABI matches the runtime");
    parser
        .parse(src, None)
        .expect("no timeout or cancellation set")
}

/// A minimal C ABI so the built `.wasm` can be driven from JS without
/// wasm-bindgen: `alloc` a buffer, write the source into it, call `has_error`.
#[cfg(target_arch = "wasm32")]
pub mod ffi {
    #[unsafe(no_mangle)]
    pub extern "C" fn alloc(len: usize) -> *mut u8 {
        let mut buf = Vec::<u8>::with_capacity(len);
        let ptr = buf.as_mut_ptr();
        std::mem::forget(buf);
        ptr
    }

    /// 1 if the recovered tree contains an ERROR or MISSING node, else 0.
    ///
    /// # Safety
    /// `ptr..ptr+len` must be a UTF-8 buffer from `alloc(len)` that the caller filled.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn has_error(ptr: *const u8, len: usize) -> u32 {
        let src = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len)) };
        u32::from(super::parse(src).root_node().has_error())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recovers_from_a_missing_done() {
        let tree = parse("match x do");
        assert!(tree.root_node().has_error());
        assert!(tree.root_node().to_sexp().contains("match_expr"));
    }
}
