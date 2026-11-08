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

use std::alloc::{Layout, alloc, dealloc};

pub const TAG_OK: u8 = 0;
pub const TAG_ERR: u8 = 1;
const HEADER: usize = 5;

// 16 MiB is generous for source text; prevents a JS caller from triggering
// gigabyte allocations or multi-second compile jobs before control returns.
const MAX_SRC_LEN: u32 = 16 * 1024 * 1024;
// 4-byte size prefix prepended by gw_alloc so gw_free can recover the layout
// without trusting the caller-supplied length.
const ALLOC_HEADER: usize = 4;

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
    let layout = Layout::from_size_align(total, 1).expect("byte layouts fit while len <= MAX_SRC_LEN");
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
    let layout = Layout::from_size_align(total, 1).expect("byte layouts fit while stored_len <= MAX_SRC_LEN");
    // SAFETY: base and layout match the gw_alloc allocation.
    unsafe { dealloc(base, layout) };
}

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

/// Free a record returned by `gw_compile`.
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
    if len > MAX_SRC_LEN as usize {
        return make_record(TAG_ERR, b"source exceeds size limit".to_vec());
    }
    let bytes: &[u8] = if len == 0 {
        &[]
    } else if ptr.is_null() {
        return make_record(TAG_ERR, b"null source pointer".to_vec());
    } else {
        // SAFETY: non-null, non-empty range, readable per the contract.
        unsafe { std::slice::from_raw_parts(ptr, len) }
    };
    let (tag, payload) = match std::str::from_utf8(bytes) {
        Ok(source) => match goat::compile_turtle(source) {
            Ok(module) => (TAG_OK, module),
            Err(errors) => (TAG_ERR, render_all(&errors, source).into_bytes()),
        },
        Err(e) => (
            TAG_ERR,
            format!("source is not valid UTF-8 (at byte {})", e.valid_up_to()).into_bytes(),
        ),
    };
    make_record(tag, payload)
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
