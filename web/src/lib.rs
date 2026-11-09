//! C-ABI over [`goat::compile_turtle`], built as a `wasm32-unknown-unknown` module so a
//! browser can compile goat source. JS owns the buffers; every address is an
//! offset into this module's linear memory.
//!
//! Calling sequence:
//! 1. `p = gw_alloc(n)`; write `n` UTF-8 source bytes at `p`.
//! 2. `r = gw_compile(p, n)`; then `gw_free(p, n)`.
//! 3. Read the result record at `r`, then `gw_free_result(r)`.
//!
//! Result record: byte 0 is the tag (`TAG_OK` = wasm module bytes follow,
//! `TAG_ERR` = rendered diagnostics as UTF-8 follow), bytes 1..5 are the payload
//! length as a little-endian `u32`, bytes 5.. are the payload. The record is
//! owned by the caller until `gw_free_result`, which reads the length from the
//! header, so no length needs to be remembered. `gw_compile` never returns 0.
//!
//! Nothing here panics on any input; problems with the input become `TAG_ERR`
//! records. Diagnostics are the checker's own, rendered by `GoatError::render`.
//!
//! Two more entry points take the same source and return the same record, for
//! an editor:
//! - `gw_check` runs the same compile as `gw_compile` but reports structured
//!   diagnostics. `TAG_OK` has an empty payload; `TAG_ERR` has one entry per
//!   error: `start: u32`, `end: u32` (byte offsets into the source, little
//!   endian), `len: u32`, then `len` bytes of UTF-8 message.
//! - `gw_tokenize` lexes with the parser crate's hand-written lexer. The payload is
//!   one 9-byte entry per token: `kind: u8` (a `TOKEN_*` constant), then
//!   `start: u32` and `end: u32`, byte offsets. Names and punctuation are left
//!   out. `TAG_ERR` carries a message and no tokens.
//! - `gw_vocabulary` takes no source and returns `TAG_OK` with the words to
//!   complete (see `vocabulary::encode`): keywords, then the turtle host's
//!   functions and tags.

mod vocabulary;

use goat_parser::lexer::{self, TokenKind};
use std::alloc::{Layout, alloc, dealloc};
use std::collections::HashSet;
use std::sync::OnceLock;

pub const TAG_OK: u8 = 0;
pub const TAG_ERR: u8 = 1;
const HEADER: usize = 5;

pub const TOKEN_COMMENT: u8 = 0;
pub const TOKEN_KEYWORD: u8 = 1;
pub const TOKEN_LITERAL: u8 = 2;
pub const TOKEN_NUMBER: u8 = 3;
pub const TOKEN_STRING: u8 = 4;
pub const TOKEN_TAG: u8 = 5;
pub const TOKEN_OPERATOR: u8 = 6;

// 16 MiB is generous for source text; prevents a JS caller from triggering
// gigabyte allocations or multi-second compile jobs before control returns.
const MAX_SRC_LEN: u32 = 16 * 1024 * 1024;
// 4-byte size prefix prepended by gw_alloc so gw_free can recover the layout
// without trusting the caller-supplied length.
const ALLOC_HEADER: usize = 4;

#[cfg(test)]
fn buffer_layout(len: usize) -> Layout {
    // A zero-size layout is undefined for the allocator, so round up to one byte.
    Layout::from_size_align(len.max(1), 1).expect("byte layouts fit while len <= isize::MAX")
}

/// Allocate `len` bytes for the caller to fill. Returns 0 if `len` exceeds
/// `MAX_SRC_LEN` or allocation fails. The returned pointer points past a
/// 4-byte size header so `gw_free` can recover the layout without trusting
/// the caller-supplied length.
#[unsafe(no_mangle)]
pub extern "C" fn gw_alloc(len: u32) -> u32 {
    if len > MAX_SRC_LEN {
        return 0;
    }
    let total = len as usize + ALLOC_HEADER;
    let layout =
        Layout::from_size_align(total, 1).expect("byte layouts fit while len <= MAX_SRC_LEN");
    // SAFETY: layout has non-zero size (total >= ALLOC_HEADER).
    let base = unsafe { alloc(layout) };
    if base.is_null() {
        return 0;
    }
    // Store the data length so gw_free can reconstruct the layout.
    // SAFETY: base is valid with at least ALLOC_HEADER bytes.
    unsafe { (base as *mut u32).write_unaligned(len) };
    (base as usize + ALLOC_HEADER) as u32
}

#[cfg(test)]
fn alloc_buf(len: usize) -> *mut u8 {
    // SAFETY: the layout has non-zero size.
    unsafe { alloc(buffer_layout(len)) }
}

/// Free a buffer from `gw_alloc`. The caller-supplied `_len` is ignored; the
/// true allocation size is recovered from the header written by `gw_alloc`,
/// preventing a mismatched-layout dealloc when the caller passes a wrong length.
///
/// # Safety
/// `ptr` must come from one `gw_alloc` call not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn gw_free(ptr: u32, _len: u32) {
    let data_ptr = ptr as usize;
    if data_ptr < ALLOC_HEADER {
        return;
    }
    let base = (data_ptr - ALLOC_HEADER) as *mut u8;
    // SAFETY: ptr came from gw_alloc, so base[-ALLOC_HEADER] holds the stored len.
    let stored_len = unsafe { (base as *const u32).read_unaligned() };
    if stored_len > MAX_SRC_LEN {
        return; // corrupt header; leak rather than UB
    }
    let total = stored_len as usize + ALLOC_HEADER;
    let layout = Layout::from_size_align(total, 1)
        .expect("byte layouts fit while stored_len <= MAX_SRC_LEN");
    // SAFETY: base and layout match the gw_alloc allocation.
    unsafe { dealloc(base, layout) };
}

#[cfg(test)]
unsafe fn free_buf(ptr: *mut u8, len: usize) {
    if !ptr.is_null() {
        // SAFETY: `ptr` came from `alloc_buf(len)`.
        unsafe { dealloc(ptr, buffer_layout(len)) }
    }
}

/// Compile the `src_len` bytes at `src_ptr`; returns the result record's address.
///
/// # Safety
/// `src_ptr..src_ptr + src_len` must be readable memory.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn gw_compile(src_ptr: u32, src_len: u32) -> u32 {
    // SAFETY: forwarded from the caller's contract.
    unsafe { compile_at(src_ptr as usize as *const u8, src_len as usize) as usize as u32 }
}

/// Check the `src_len` bytes at `src_ptr`; returns the result record's address.
///
/// # Safety
/// `src_ptr..src_ptr + src_len` must be readable memory.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn gw_check(src_ptr: u32, src_len: u32) -> u32 {
    // SAFETY: forwarded from the caller's contract.
    unsafe { check_at(src_ptr as usize as *const u8, src_len as usize) as usize as u32 }
}

/// Tokenize the `src_len` bytes at `src_ptr`; returns the result record's address.
///
/// # Safety
/// `src_ptr..src_ptr + src_len` must be readable memory.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn gw_tokenize(src_ptr: u32, src_len: u32) -> u32 {
    // SAFETY: forwarded from the caller's contract.
    unsafe { tokenize_at(src_ptr as usize as *const u8, src_len as usize) as usize as u32 }
}

/// The words an editor completes: keywords, builtins and the host's names.
/// Returns the result record's address.
#[unsafe(no_mangle)]
pub extern "C" fn gw_vocabulary() -> u32 {
    vocabulary_record() as usize as u32
}

/// Free a record returned by `gw_compile`, `gw_check`, `gw_tokenize` or
/// `gw_vocabulary`.
///
/// # Safety
/// `ptr` must come from one `gw_compile` call not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn gw_free_result(ptr: u32) {
    // SAFETY: forwarded from the caller's contract.
    unsafe { free_record(ptr as usize as *mut u8) }
}

/// Address-width-neutral core of `gw_compile`, so host tests can call it with
/// native pointers.
///
/// # Safety
/// `ptr..ptr + len` must be readable memory (or `len` must be 0).
unsafe fn compile_at(ptr: *const u8, len: usize) -> *mut u8 {
    // SAFETY: forwarded from the caller's contract.
    let (tag, payload) = match unsafe { source_at(ptr, len) } {
        Ok(source) => match goat::compile_turtle(source) {
            Ok(module) => (TAG_OK, module),
            Err(errors) => (TAG_ERR, render_all(&errors, source).into_bytes()),
        },
        Err(problem) => (TAG_ERR, problem.into_bytes()),
    };
    make_record(tag, payload)
}

/// Like `compile_at`, with structured diagnostics instead of the rendered ones.
///
/// # Safety
/// `ptr..ptr + len` must be readable memory (or `len` must be 0).
unsafe fn check_at(ptr: *const u8, len: usize) -> *mut u8 {
    // SAFETY: forwarded from the caller's contract.
    let (tag, payload) = match unsafe { source_at(ptr, len) } {
        Ok(source) => match goat::compile_turtle(source) {
            Ok(_) => (TAG_OK, Vec::new()),
            Err(errors) => (TAG_ERR, encode_diagnostics(&errors)),
        },
        Err(problem) => (TAG_ERR, encode_diagnostic(0, 0, &problem)),
    };
    make_record(tag, payload)
}

/// # Safety
/// `ptr..ptr + len` must be readable memory (or `len` must be 0).
unsafe fn tokenize_at(ptr: *const u8, len: usize) -> *mut u8 {
    // SAFETY: forwarded from the caller's contract.
    let (tag, payload) = match unsafe { source_at(ptr, len) } {
        Ok(source) => (TAG_OK, encode_tokens(source)),
        Err(problem) => (TAG_ERR, problem.into_bytes()),
    };
    make_record(tag, payload)
}

/// The source text at `ptr`, or what is wrong with it.
///
/// # Safety
/// `ptr..ptr + len` must be readable memory (or `len` must be 0).
unsafe fn source_at<'a>(ptr: *const u8, len: usize) -> Result<&'a str, String> {
    if len > MAX_SRC_LEN as usize {
        return Err("source exceeds size limit".into());
    }
    let bytes: &[u8] = if len == 0 {
        &[]
    } else if ptr.is_null() {
        return Err("null source pointer".into());
    } else {
        // SAFETY: non-null, non-empty range, readable per the contract.
        unsafe { std::slice::from_raw_parts(ptr, len) }
    };
    std::str::from_utf8(bytes)
        .map_err(|e| format!("source is not valid UTF-8 (at byte {})", e.valid_up_to()))
}

fn encode_diagnostics(errors: &[goat_checker::GoatError]) -> Vec<u8> {
    errors
        .iter()
        .flat_map(|e| {
            // A span in the prelude indexes text the user never wrote.
            if e.span.in_prelude() {
                encode_diagnostic(0, 0, &format!("in the prelude, {}", e.message))
            } else {
                encode_diagnostic(e.span.start, e.span.end, &e.message)
            }
        })
        .collect()
}

fn word(n: usize) -> [u8; 4] {
    u32::try_from(n).unwrap_or(u32::MAX).to_le_bytes()
}

fn encode_diagnostic(start: usize, end: usize, message: &str) -> Vec<u8> {
    let mut entry = Vec::with_capacity(12 + message.len());
    entry.extend_from_slice(&word(start));
    entry.extend_from_slice(&word(end));
    entry.extend_from_slice(&word(message.len()));
    entry.extend_from_slice(message.as_bytes());
    entry
}

/// The names the host declares as tags: the prelude's `tag` declarations and
/// the vocabulary the checker accepts from the host (ADR 0015).
fn host_tags() -> &'static HashSet<String> {
    static TAGS: OnceLock<HashSet<String>> = OnceLock::new();
    TAGS.get_or_init(|| {
        let host = goat::HostInterface::turtle();
        let prelude = host.prelude();
        let mut tags: HashSet<String> = lexer::declared_tags(prelude, &lexer::tokenize(prelude))
            .into_iter()
            .map(String::from)
            .collect();
        let vocab = host.vocab();
        tags.extend(
            vocab
                .tag_names()
                .chain(vocab.key_tag_names())
                .map(String::from),
        );
        tags
    })
}

/// Address-width-neutral core of `gw_vocabulary`.
fn vocabulary_record() -> *mut u8 {
    static WORDS: OnceLock<Vec<u8>> = OnceLock::new();
    let words = WORDS
        .get_or_init(|| vocabulary::encode(&vocabulary::words(&goat::HostInterface::turtle())));
    make_record(TAG_OK, words.clone())
}

fn encode_tokens(source: &str) -> Vec<u8> {
    lexer::highlight(source, host_tags())
        .into_iter()
        .filter_map(|t| {
            let kind = match t.kind {
                TokenKind::Comment => TOKEN_COMMENT,
                TokenKind::Keyword => TOKEN_KEYWORD,
                TokenKind::Literal => TOKEN_LITERAL,
                TokenKind::Number => TOKEN_NUMBER,
                TokenKind::String => TOKEN_STRING,
                TokenKind::Tag => TOKEN_TAG,
                TokenKind::Operator => TOKEN_OPERATOR,
                TokenKind::Name | TokenKind::Punct | TokenKind::Whitespace | TokenKind::Unknown => {
                    return None;
                }
            };
            let mut entry = vec![kind];
            entry.extend_from_slice(&word(t.start));
            entry.extend_from_slice(&word(t.end));
            Some(entry)
        })
        .flatten()
        .collect()
}

fn render_all(errors: &[goat_checker::GoatError], source: &str) -> String {
    let rendered: Vec<String> = errors.iter().map(|e| e.render(source)).collect();
    rendered.join("\n\n")
}

fn make_record(tag: u8, payload: Vec<u8>) -> *mut u8 {
    let (tag, payload) = match u32::try_from(payload.len()) {
        Ok(_) => (tag, payload),
        Err(_) => (TAG_ERR, b"output exceeds 4 GiB".to_vec()),
    };
    let mut record = Vec::with_capacity(HEADER + payload.len());
    record.push(tag);
    record.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    record.extend_from_slice(&payload);
    Box::into_raw(record.into_boxed_slice()) as *mut u8
}

/// # Safety
/// `ptr` must come from `make_record` and not be freed already.
unsafe fn free_record(ptr: *mut u8) {
    if ptr.is_null() {
        return;
    }
    // SAFETY: a record starts with its header, and its total size is header + payload.
    unsafe {
        let len = u32::from_le_bytes(*(ptr.add(1) as *const [u8; 4])) as usize;
        // Guard: HEADER + len must not overflow usize. On wasm32, usize == u32,
        // so a maximum-valued payload length would wrap and produce a tiny slice.
        if len > usize::MAX - HEADER {
            return; // corrupt header; leak rather than UB
        }
        drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut(
            ptr,
            HEADER + len,
        )));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(source: &[u8]) -> (u8, Vec<u8>) {
        // SAFETY: `source` is a live slice; the record is read before it is freed.
        unsafe {
            let rec = compile_at(source.as_ptr(), source.len());
            let len = u32::from_le_bytes(*(rec.add(1) as *const [u8; 4])) as usize;
            let payload = std::slice::from_raw_parts(rec.add(HEADER), len).to_vec();
            let tag = *rec;
            free_record(rec);
            (tag, payload)
        }
    }

    fn record_of(entry: unsafe fn(*const u8, usize) -> *mut u8, source: &[u8]) -> (u8, Vec<u8>) {
        // SAFETY: `source` is a live slice; the record is read before it is freed.
        unsafe {
            let rec = entry(source.as_ptr(), source.len());
            let len = u32::from_le_bytes(*(rec.add(1) as *const [u8; 4])) as usize;
            let payload = std::slice::from_raw_parts(rec.add(HEADER), len).to_vec();
            let tag = *rec;
            free_record(rec);
            (tag, payload)
        }
    }

    /// `(start, end, message)` for each diagnostic entry in `payload`.
    fn diagnostics(payload: &[u8]) -> Vec<(u32, u32, String)> {
        let word = |at: usize| u32::from_le_bytes(payload[at..at + 4].try_into().unwrap());
        let mut found = Vec::new();
        let mut at = 0;
        while at < payload.len() {
            let len = word(at + 8) as usize;
            let message = &payload[at + 12..at + 12 + len];
            found.push((
                word(at),
                word(at + 4),
                String::from_utf8(message.to_vec()).unwrap(),
            ));
            at += 12 + len;
        }
        found
    }

    /// `(kind, text)` for each token entry in `payload`.
    fn tokens<'a>(source: &'a str, payload: &[u8]) -> Vec<(u8, &'a str)> {
        payload
            .chunks(9)
            .map(|entry| {
                let word = |at: usize| u32::from_le_bytes(entry[at..at + 4].try_into().unwrap());
                (entry[0], &source[word(1) as usize..word(5) as usize])
            })
            .collect()
    }

    #[test]
    fn check_of_good_source_is_ok_and_empty() {
        let (tag, payload) = record_of(check_at, b"1 + 2");
        assert_eq!((tag, payload.len()), (TAG_OK, 0));
    }

    #[test]
    fn check_reports_the_checkers_span_and_message() {
        let source = "x = 1\n1 + true";
        let (tag, payload) = record_of(check_at, source.as_bytes());
        assert_eq!(tag, TAG_ERR);
        let errors = goat::compile_turtle(source).unwrap_err();
        let found = diagnostics(&payload);
        assert_eq!(found.len(), errors.len());
        for ((start, end, message), error) in found.iter().zip(&errors) {
            assert_eq!(
                (*start as usize, *end as usize),
                (error.span.start, error.span.end)
            );
            assert_eq!(message, &error.message);
        }
        assert!(found[0].0 as usize >= "x = 1\n".len(), "{found:?}");
    }

    #[test]
    fn check_reports_a_syntax_error_with_a_span() {
        let (tag, payload) = record_of(check_at, b"if then");
        assert_eq!(tag, TAG_ERR);
        assert!(!diagnostics(&payload).is_empty());
    }

    #[test]
    fn check_agrees_with_compile_on_whether_source_is_good() {
        for source in [
            "",
            "1",
            "1 + true",
            "x",
            "if",
            "forward(10)",
            "forward(true)",
        ] {
            let (compiled, _) = run(source.as_bytes());
            let (checked, _) = record_of(check_at, source.as_bytes());
            assert_eq!(compiled, checked, "{source:?}");
        }
    }

    #[test]
    fn check_of_invalid_utf8_is_one_diagnostic() {
        let (tag, payload) = record_of(check_at, &[0xff]);
        assert_eq!(tag, TAG_ERR);
        let found = diagnostics(&payload);
        assert_eq!(found.len(), 1);
        assert!(found[0].2.contains("UTF-8"));
    }

    #[test]
    fn tokenize_reports_kinds_and_byte_offsets() {
        let source = "# hi\ntag Dot\nx = \"é\" + 1.5\nif true then Dot else Dot done";
        let (tag, payload) = record_of(tokenize_at, source.as_bytes());
        assert_eq!(tag, TAG_OK);
        assert_eq!(
            tokens(source, &payload),
            [
                (TOKEN_COMMENT, "# hi"),
                (TOKEN_KEYWORD, "tag"),
                (TOKEN_TAG, "Dot"),
                (TOKEN_STRING, "\"é\""),
                (TOKEN_OPERATOR, "+"),
                (TOKEN_NUMBER, "1.5"),
                (TOKEN_KEYWORD, "if"),
                (TOKEN_LITERAL, "true"),
                (TOKEN_KEYWORD, "then"),
                (TOKEN_TAG, "Dot"),
                (TOKEN_KEYWORD, "else"),
                (TOKEN_TAG, "Dot"),
                (TOKEN_KEYWORD, "done"),
            ]
        );
    }

    #[test]
    fn tokenize_knows_the_hosts_tags() {
        let source = "match e do KeyDown(Up) then Link(1, Empty) else 0 done";
        let (_, payload) = record_of(tokenize_at, source.as_bytes());
        let tags: Vec<_> = tokens(source, &payload)
            .into_iter()
            .filter(|(kind, _)| *kind == TOKEN_TAG)
            .map(|(_, text)| text)
            .collect();
        assert_eq!(tags, ["KeyDown", "Up", "Link", "Empty"]);
    }

    #[test]
    fn vocabulary_record_holds_keywords_and_host_names() {
        // SAFETY: the record is read before it is freed.
        let (tag, payload) = unsafe {
            let rec = vocabulary_record();
            let len = u32::from_le_bytes(*(rec.add(1) as *const [u8; 4])) as usize;
            let payload = std::slice::from_raw_parts(rec.add(HEADER), len).to_vec();
            let tag = *rec;
            free_record(rec);
            (tag, payload)
        };
        assert_eq!(tag, TAG_OK);
        let text = String::from_utf8_lossy(&payload);
        for word in ["repeat", "forward", "(Number) -> Unit", "KeyDown"] {
            assert!(text.contains(word), "{word}");
        }
    }

    #[test]
    fn tokenize_survives_a_syntax_error() {
        let source = "if x then )) \"oops";
        let (tag, payload) = record_of(tokenize_at, source.as_bytes());
        assert_eq!(tag, TAG_OK);
        assert!(tokens(source, &payload).contains(&(TOKEN_KEYWORD, "then")));
    }

    #[test]
    fn tokenize_of_invalid_utf8_is_an_error_record() {
        let (tag, payload) = record_of(tokenize_at, &[0xff]);
        assert_eq!(tag, TAG_ERR);
        assert!(String::from_utf8(payload).unwrap().contains("UTF-8"));
    }

    #[test]
    fn good_source_yields_a_wasm_module() {
        let (tag, payload) = run(b"1 + 2 * 3");
        assert_eq!(tag, TAG_OK);
        assert!(payload.starts_with(b"\0asm"));
    }

    #[test]
    fn type_error_is_rendered_with_a_caret() {
        let (tag, payload) = run(b"1 + true");
        assert_eq!(tag, TAG_ERR);
        let text = String::from_utf8(payload).unwrap();
        assert!(text.contains('^'), "{text}");
    }

    #[test]
    fn unbound_name_is_rendered() {
        let (tag, payload) = run(b"x");
        assert_eq!(tag, TAG_ERR);
        let text = String::from_utf8(payload).unwrap();
        assert!(!text.is_empty() && text.contains('^'), "{text}");
    }

    #[test]
    fn empty_source_does_not_panic() {
        let (tag, _) = run(b"");
        assert!(tag == TAG_OK || tag == TAG_ERR);
    }

    #[test]
    fn invalid_utf8_is_an_error_record() {
        let (tag, payload) = run(&[0xff, 0xfe, b'1']);
        assert_eq!(tag, TAG_ERR);
        assert!(String::from_utf8(payload).unwrap().contains("UTF-8"));
    }

    #[test]
    fn alloc_free_round_trip() {
        for len in [0usize, 1, 17, 4096] {
            let p = alloc_buf(len);
            assert!(!p.is_null());
            // SAFETY: `p` came from `alloc_buf(len)`.
            unsafe { free_buf(p, len) };
        }
        // SAFETY: null is accepted.
        unsafe {
            free_buf(std::ptr::null_mut(), 0);
            free_record(std::ptr::null_mut());
        }
    }
}
