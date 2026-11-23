//! `#[repr(C)]` mirrors of the structs the emitter declares (`goat_llvm`'s
//! `HOST_FUNCTIONS` and `INSTANCE_FIELDS`), so a host written in Rust builds the
//! table and the instance the generated code reads. `tests/layout.rs` checks
//! each field's offset against what clang computes for the emitted types.

use std::ffi::c_void;
use std::mem::{offset_of, size_of};

pub use goat_llvm::{HOST_VERSION, INSTANCE_VERSION};

/// The host's own pointer, passed back as the first argument of every table
/// function. A string argument is a pointer and a byte length.
pub type Ctx = *mut c_void;

macro_rules! host_table {
    ($($field:ident: fn($($arg:ty),*) $(-> $ret:ty)?),* $(,)?) => {
        /// The functions a host gives generated code. Every function takes the
        /// `ctx` the export received as its first argument, and the fields
        /// after `version` only grow at the end.
        #[repr(C)]
        #[derive(Clone, Copy)]
        pub struct GoatHost {
            pub version: u32,
            $(pub $field: unsafe extern "C" fn(Ctx $(, $arg)*) $(-> $ret)?,)*
        }

        /// Each field's name and offset, `version` first.
        pub fn host_offsets() -> Vec<(&'static str, usize)> {
            vec![("version", offset_of!(GoatHost, version))
                $(, (stringify!($field), offset_of!(GoatHost, $field)))*]
        }
    };
}

host_table! {
    print_number: fn(f64),
    print_bool: fn(i32),
    print_int: fn(i64),
    print_string: fn(*const u8, u64),
    write_number: fn(f64),
    write_string: fn(*const u8, u64),
    write_end: fn(),
    write_int: fn(i64),
    trap: fn(*const u8, u64) -> !,
    scene_begin: fn(),
    scene_end: fn(),
    scene_frame: fn(*const u8, u64),
    turtle_forward: fn(f64),
    turtle_back: fn(f64),
    turtle_left: fn(f64),
    turtle_right: fn(f64),
    turtle_pen_up: fn(),
    turtle_pen_down: fn(),
    turtle_color: fn(*const u8, u64),
    foreign: fn(*const u8, u64, *const u8, u64, *const GoatValue, u64, *mut GoatValue),
}

pub const VALUE_UNIT: u32 = 0;
pub const VALUE_NUMBER: u32 = 1;
pub const VALUE_INT: u32 = 2;
pub const VALUE_BOOL: u32 = 3;
pub const VALUE_STR: u32 = 4;

/// An argument or result of a `foreign` call: `a` holds the `f64` bits, the
/// `i64`, the bool (0 or 1) or the string's pointer, and `b` the string's length.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct GoatValue {
    pub tag: u32,
    pub a: u64,
    pub b: u64,
}

/// What the generated code keeps for one running program instead of globals.
/// The host allocates it, sets `version`, `heap` and `heap_size`, and leaves the
/// rest as [`Instance::new`] does.
#[repr(C)]
pub struct GoatInstance {
    pub version: u32,
    pub live: u32,
    pub depth: u32,
    pub site_start: u32,
    pub site_end: u32,
    pub heap: *mut u8,
    pub heap_size: u64,
    pub host: *const GoatHost,
    pub ctx: Ctx,
    pub spill: [u64; 8],
}

pub fn instance_offsets() -> Vec<(&'static str, usize)> {
    vec![
        ("version", offset_of!(GoatInstance, version)),
        ("live", offset_of!(GoatInstance, live)),
        ("depth", offset_of!(GoatInstance, depth)),
        ("site_start", offset_of!(GoatInstance, site_start)),
        ("site_end", offset_of!(GoatInstance, site_end)),
        ("heap", offset_of!(GoatInstance, heap)),
        ("heap_size", offset_of!(GoatInstance, heap_size)),
        ("host", offset_of!(GoatInstance, host)),
        ("ctx", offset_of!(GoatInstance, ctx)),
        ("spill", offset_of!(GoatInstance, spill)),
    ]
}

/// A `goat_instance` with a heap it owns. The instance is boxed, so the pointer
/// the generated code keeps stays valid when this moves.
pub struct Instance {
    raw: Box<GoatInstance>,
    _heap: Vec<u128>,
}

impl Instance {
    pub fn new(heap_bytes: usize) -> Instance {
        let mut heap = vec![0u128; heap_bytes.div_ceil(size_of::<u128>())];
        let raw = Box::new(GoatInstance {
            version: INSTANCE_VERSION,
            live: 0,
            depth: 0,
            site_start: u32::MAX,
            site_end: 0,
            heap: heap.as_mut_ptr().cast(),
            heap_size: (heap.len() * size_of::<u128>()) as u64,
            host: std::ptr::null(),
            ctx: std::ptr::null_mut(),
            spill: [0; 8],
        });
        Instance { raw, _heap: heap }
    }

    pub fn as_ptr(&mut self) -> *mut GoatInstance {
        &mut *self.raw
    }

    pub fn set_version(&mut self, version: u32) {
        self.raw.version = version;
    }

    pub fn live(&self) -> u32 {
        self.raw.live
    }

    /// The source range the program last named as the user's code running, as
    /// byte offsets, or `None` if it named none.
    pub fn site(&self) -> Option<(usize, usize)> {
        (self.raw.site_start != u32::MAX)
            .then_some((self.raw.site_start as usize, self.raw.site_end as usize))
    }
}

/// `[size, offset of each field]` for `goat_host`, then for `goat_instance`,
/// in the order `goat_llvm::layout_probe` stores them.
pub fn expected_layout() -> Vec<u64> {
    let mut layout = vec![size_of::<GoatHost>() as u64];
    layout.extend(host_offsets().iter().map(|(_, at)| *at as u64));
    layout.push(size_of::<GoatInstance>() as u64);
    layout.extend(instance_offsets().iter().map(|(_, at)| *at as u64));
    layout
}
