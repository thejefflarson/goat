//! Serves a `goat_host` table from a Rust [`Host`]: `scene_*`, `turtle_*` and
//! `foreign` reach `Host::call` under the module they are named for, and
//! printing follows `goat::format_number`, so the output reads as the wasm
//! runtime's does.

use crate::abi::*;
use goat::{Host, HostValue};
use std::ffi::c_void;

/// What `ctx` points at while a program runs.
pub struct Adapter<H> {
    pub host: H,
    /// The lines the program has printed, and the one it is still writing.
    pub lines: Vec<String>,
    line: String,
    trap: unsafe extern "C" fn(Ctx, *const u8, u64) -> !,
    /// The message of a trap the host raised, kept alive for the trap call.
    halt: String,
}

impl<H: Host> Adapter<H> {
    /// `trap` is the host library's never-returning way out of generated code.
    pub fn new(host: H, trap: unsafe extern "C" fn(Ctx, *const u8, u64) -> !) -> Adapter<H> {
        Adapter {
            host,
            lines: Vec::new(),
            line: String::new(),
            trap,
            halt: String::new(),
        }
    }

    pub fn ctx(&mut self) -> Ctx {
        (self as *mut Adapter<H>).cast::<c_void>()
    }

    /// The table whose entries are this adapter's.
    pub fn table(&self) -> GoatHost {
        GoatHost {
            version: HOST_VERSION,
            print_number: print_number::<H>,
            print_bool: print_bool::<H>,
            print_int: print_int::<H>,
            print_string: print_string::<H>,
            write_number: write_number::<H>,
            write_string: write_string::<H>,
            write_end: write_end::<H>,
            write_int: write_int::<H>,
            trap: self.trap,
            scene_begin: scene_begin::<H>,
            scene_end: scene_end::<H>,
            scene_frame: scene_frame::<H>,
            turtle_forward: turtle_forward::<H>,
            turtle_back: turtle_back::<H>,
            turtle_left: turtle_left::<H>,
            turtle_right: turtle_right::<H>,
            turtle_pen_up: turtle_pen_up::<H>,
            turtle_pen_down: turtle_pen_down::<H>,
            turtle_color: turtle_color::<H>,
            foreign: foreign::<H>,
        }
    }

    fn finish_line(&mut self) {
        self.lines.push(std::mem::take(&mut self.line));
    }

    fn call(&mut self, module: &str, name: &str, args: &[HostValue]) -> HostValue {
        match self.host.call(module, name, args) {
            Ok(value) => value,
            Err(message) => self.stop(message),
        }
    }

    fn stop(&mut self, message: String) -> ! {
        self.halt = message;
        let (trap, ptr, len) = (self.trap, self.halt.as_ptr(), self.halt.len() as u64);
        let ctx = self.ctx();
        // SAFETY: `trap` is the host library's, which does not return and
        // reads `len` bytes at `ptr`, which `halt` keeps alive.
        unsafe { trap(ctx, ptr, len) }
    }
}

/// SAFETY: `ctx` is the `Adapter<H>` the driver passed to the export, and the
/// generated code calls the table one function at a time.
unsafe fn adapter<'a, H>(ctx: Ctx) -> &'a mut Adapter<H> {
    unsafe { &mut *ctx.cast::<Adapter<H>>() }
}

/// SAFETY: the generated code passes a pointer and the byte length it holds.
unsafe fn text(ptr: *const u8, len: u64) -> String {
    if len == 0 {
        return String::new();
    }
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len as usize) };
    String::from_utf8_lossy(bytes).into_owned()
}

macro_rules! printing {
    ($($name:ident($($arg:ident: $ty:ty),*) => |$a:ident| $body:expr;)*) => {$(
        unsafe extern "C" fn $name<H: Host>(ctx: Ctx $(, $arg: $ty)*) {
            let $a = unsafe { adapter::<H>(ctx) };
            $body
        }
    )*};
}

printing! {
    print_number(x: f64) => |a| {
        a.line.push_str(&goat::format_number(x));
        a.finish_line();
    };
    print_bool(b: i32) => |a| {
        a.line.push_str(goat::format_bool(b != 0));
        a.finish_line();
    };
    print_int(n: i64) => |a| {
        a.line.push_str(&n.to_string());
        a.finish_line();
    };
    write_number(x: f64) => |a| a.line.push_str(&goat::format_number(x));
    write_int(n: i64) => |a| a.line.push_str(&n.to_string());
    write_end() => |a| a.finish_line();
}

unsafe extern "C" fn print_string<H: Host>(ctx: Ctx, ptr: *const u8, len: u64) {
    let a = unsafe { adapter::<H>(ctx) };
    a.line.push_str(&unsafe { text(ptr, len) });
    a.finish_line();
}

unsafe extern "C" fn write_string<H: Host>(ctx: Ctx, ptr: *const u8, len: u64) {
    let a = unsafe { adapter::<H>(ctx) };
    a.line.push_str(&unsafe { text(ptr, len) });
}

/// A table entry that hands its arguments to `Host::call` under `$module`.
macro_rules! hosted {
    ($($name:ident, $module:literal, $call:literal($($arg:ident: $ty:ty),*) => [$($value:expr),*];)*) => {$(
        unsafe extern "C" fn $name<H: Host>(ctx: Ctx $(, $arg: $ty)*) {
            let a = unsafe { adapter::<H>(ctx) };
            a.call($module, $call, &[$($value),*]);
        }
    )*};
}

fn number(x: f64) -> HostValue {
    HostValue::Number(x)
}

fn string(ptr: *const u8, len: u64) -> HostValue {
    HostValue::Str(unsafe { text(ptr, len) })
}

hosted! {
    scene_begin, "scene", "begin"() => [];
    scene_end, "scene", "end"() => [];
    turtle_forward, "turtle", "forward"(x: f64) => [number(x)];
    turtle_back, "turtle", "back"(x: f64) => [number(x)];
    turtle_left, "turtle", "left"(x: f64) => [number(x)];
    turtle_right, "turtle", "right"(x: f64) => [number(x)];
    turtle_pen_up, "turtle", "pen_up"() => [];
    turtle_pen_down, "turtle", "pen_down"() => [];
    turtle_color, "turtle", "color"(p: *const u8, n: u64) => [string(p, n)];
}

/// A frame's bytes, replayed by the host's `Host::frame`.
unsafe extern "C" fn scene_frame<H: Host>(ctx: Ctx, ptr: *const u8, len: u64) {
    let a = unsafe { adapter::<H>(ctx) };
    let bytes = if len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(ptr, len as usize) }
    };
    if let Err(message) = a.host.frame(bytes) {
        a.stop(message);
    }
}

/// Any other host function, by module and name. A string result needs the
/// program's allocator, which the native backend does not have yet, so it is a
/// trap.
#[allow(clippy::too_many_arguments)]
unsafe extern "C" fn foreign<H: Host>(
    ctx: Ctx,
    module: *const u8,
    module_len: u64,
    name: *const u8,
    name_len: u64,
    args: *const GoatValue,
    arg_count: u64,
    result: *mut GoatValue,
) {
    let a = unsafe { adapter::<H>(ctx) };
    let (module, name) = unsafe { (text(module, module_len), text(name, name_len)) };
    let raw = if arg_count == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(args, arg_count as usize) }
    };
    let mut values = Vec::with_capacity(raw.len());
    for value in raw {
        values.push(match value.tag {
            VALUE_UNIT => HostValue::Unit,
            VALUE_NUMBER => HostValue::Number(f64::from_bits(value.a)),
            VALUE_INT => HostValue::Int(value.a as i64),
            VALUE_BOOL => HostValue::Bool(value.a != 0),
            VALUE_STR => string(value.a as *const u8, value.b),
            tag => a.stop(format!("{module}.{name} was given a value tagged {tag}")),
        });
    }
    let returned = match a.call(&module, &name, &values) {
        HostValue::Unit => GoatValue::default(),
        HostValue::Number(x) => GoatValue {
            tag: VALUE_NUMBER,
            a: x.to_bits(),
            b: 0,
        },
        HostValue::Int(n) => GoatValue {
            tag: VALUE_INT,
            a: n as u64,
            b: 0,
        },
        HostValue::Bool(b) => GoatValue {
            tag: VALUE_BOOL,
            a: u64::from(b),
            b: 0,
        },
        HostValue::Str(_) => a.stop(format!(
            "{module}.{name} returned a string, which the native backend cannot take yet"
        )),
    };
    unsafe { *result = returned };
}

#[cfg(test)]
mod tests {
    use super::*;
    use goat::Boundary;

    #[derive(Default)]
    struct Recorder(Vec<String>);

    impl Host for Recorder {
        fn signature(&self, _: &str, _: &str) -> Option<(Vec<Boundary>, Boundary)> {
            None
        }

        fn frame(&mut self, bytes: &[u8]) -> Result<(), String> {
            self.0.push(format!("frame{bytes:?}"));
            Ok(())
        }

        fn call(
            &mut self,
            module: &str,
            name: &str,
            args: &[HostValue],
        ) -> Result<HostValue, String> {
            self.0.push(format!("{module}.{name}{args:?}"));
            Ok(match name {
                "twice" => match args {
                    [HostValue::Int(n)] => HostValue::Int(n * 2),
                    _ => HostValue::Unit,
                },
                _ => HostValue::Unit,
            })
        }
    }

    unsafe extern "C" fn no_trap(_: Ctx, _: *const u8, _: u64) -> ! {
        std::process::abort()
    }

    fn text(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn printing_follows_the_runtimes_formats() {
        let mut a = Adapter::new(Recorder::default(), no_trap);
        let (table, ctx) = (a.table(), a.ctx());
        let (hi, len) = text("hi");
        unsafe {
            (table.print_int)(ctx, -3);
            (table.print_number)(ctx, 2.5);
            (table.print_bool)(ctx, 1);
            (table.write_string)(ctx, hi, len);
            (table.write_int)(ctx, 7);
            (table.write_end)(ctx);
            (table.print_string)(ctx, hi, len);
        }
        assert_eq!(a.lines, ["-3", "2.5", "true", "hi7", "hi"]);
    }

    #[test]
    fn scene_and_turtle_entries_reach_the_host_under_their_modules() {
        let mut a = Adapter::new(Recorder::default(), no_trap);
        let (table, ctx) = (a.table(), a.ctx());
        let (red, len) = text("red");
        unsafe {
            (table.scene_begin)(ctx);
            (table.scene_frame)(ctx, [1u8, 0].as_ptr(), 2);
            (table.turtle_forward)(ctx, 10.0);
            (table.turtle_pen_up)(ctx);
            (table.turtle_color)(ctx, red, len);
        }
        assert_eq!(
            a.host.0,
            [
                "scene.begin[]",
                "frame[1, 0]",
                "turtle.forward[Number(10.0)]",
                "turtle.pen_up[]",
                "turtle.color[Str(\"red\")]",
            ]
        );
    }

    #[test]
    fn a_foreign_call_carries_tagged_values_both_ways() {
        let mut a = Adapter::new(Recorder::default(), no_trap);
        let (table, ctx) = (a.table(), a.ctx());
        let (module, module_len) = text("test");
        let (name, name_len) = text("twice");
        let args = [GoatValue {
            tag: VALUE_INT,
            a: 21,
            b: 0,
        }];
        let mut result = GoatValue::default();
        unsafe {
            (table.foreign)(
                ctx,
                module,
                module_len,
                name,
                name_len,
                args.as_ptr(),
                1,
                &mut result,
            );
        }
        assert_eq!((result.tag, result.a), (VALUE_INT, 42));
        assert_eq!(a.host.0, ["test.twice[Int(21)]"]);
    }
}
