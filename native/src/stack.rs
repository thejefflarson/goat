//! The stack the calling thread runs on, so generated code can trap with goat's
//! stack-overflow message before it reaches the guard page (ADR 0042).

/// Bytes kept free below the limit for the host calls the program makes (print,
/// `scene.frame`, the sink behind it) and for the frame that trips the check.
pub const MARGIN: usize = 256 * 1024;

/// The lowest address generated code may run its stack down to on this thread,
/// or null when the thread's stack cannot be found, which turns the check off.
pub fn limit() -> *const u8 {
    thread_local! {
        // Finding the stack can read `/proc`, so each thread asks once.
        static LIMIT: usize = low().and_then(|low| low.checked_add(MARGIN)).unwrap_or(0);
    }
    LIMIT.with(|limit| *limit) as *const u8
}

#[cfg(target_os = "macos")]
fn low() -> Option<usize> {
    // SAFETY: both calls only read the calling thread's own attributes.
    let (top, size) = unsafe {
        let me = libc::pthread_self();
        (
            libc::pthread_get_stackaddr_np(me) as usize,
            libc::pthread_get_stacksize_np(me),
        )
    };
    top.checked_sub(size)
}

#[cfg(target_os = "linux")]
fn low() -> Option<usize> {
    // SAFETY: `attr` is initialized by `pthread_getattr_np` before it is read
    // and destroyed afterwards; the calls read the calling thread's attributes.
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return None;
        }
        let (mut addr, mut size) = (std::ptr::null_mut(), 0);
        let found = libc::pthread_attr_getstack(&attr, &mut addr, &mut size) == 0;
        libc::pthread_attr_destroy(&mut attr);
        found.then_some(addr as usize)
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn low() -> Option<usize> {
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_limit_is_below_the_current_frame_and_above_the_stack_floor() {
        let here = 0u8;
        let at = std::ptr::from_ref(&here) as usize;
        let limit = limit() as usize;
        assert_ne!(limit, 0, "this platform reports its stack");
        assert!(limit < at, "{limit:#x} is below {at:#x}");
        assert!(at - limit < 64 * 1024 * 1024);
    }
}
