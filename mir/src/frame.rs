//! The frame encoding (ADR 0015, second addendum): the bytes a compiled `draw`
//! hands the host's `scene.frame` once per frame. A frame says which scene
//! calls it makes before it makes them, so a host needs no per-vocabulary
//! table.
//!
//! ```text
//! frame  = version:u8  ncalls:u8  call{ncalls}  record*
//! call   = name_len:u8  name:utf8  nparams:u8  wire:u8{nparams}
//! record = call_index:u8  value{nparams of that call}
//! value  = Int: i64 LE | Float: f64 LE | Bool: u8 | Str: len:u32 LE, utf8
//! ```
//!
//! A wire is `i`, `f`, `b` or `s`. A record is one scene call, so replaying
//! a frame is making the calls in order.

use crate::host::HostValue;
use goat_checker::ty::Ty;

pub const VERSION: u8 = 1;

/// The most bytes one frame may hold before the program traps.
pub const LIMIT: usize = 1 << 24;

pub const TOO_BIG: &str = "this picture is too big";

/// The type of one value in a record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Wire {
    Int,
    Float,
    Bool,
    Str,
}

impl Wire {
    pub fn of(ty: &Ty) -> Option<Wire> {
        match ty {
            Ty::Int => Some(Wire::Int),
            Ty::Float => Some(Wire::Float),
            Ty::Bool => Some(Wire::Bool),
            Ty::Str => Some(Wire::Str),
            _ => None,
        }
    }

    fn code(self) -> u8 {
        match self {
            Wire::Int => b'i',
            Wire::Float => b'f',
            Wire::Bool => b'b',
            Wire::Str => b's',
        }
    }

    fn from_code(code: u8) -> Option<Wire> {
        match code {
            b'i' => Some(Wire::Int),
            b'f' => Some(Wire::Float),
            b'b' => Some(Wire::Bool),
            b's' => Some(Wire::Str),
            _ => None,
        }
    }
}

/// The scene calls a frame makes, numbered in the order they were first used.
#[derive(Debug, Default)]
pub struct Calls(Vec<(String, Vec<Wire>)>);

impl Calls {
    /// The index of the call `name` over `params`, declaring it first if new.
    pub fn index(&mut self, name: &str, params: &[Wire]) -> u8 {
        let at = self
            .0
            .iter()
            .position(|(n, p)| n == name && p == params)
            .unwrap_or_else(|| {
                self.0.push((name.to_string(), params.to_vec()));
                self.0.len() - 1
            });
        u8::try_from(at).expect("a vocabulary declares at most 255 scene calls")
    }

    /// The version byte and call declarations every frame starts with.
    pub fn header(&self) -> Vec<u8> {
        let byte = |n: usize| u8::try_from(n).expect("a scene call fits the frame header");
        let mut out = vec![VERSION, byte(self.0.len())];
        for (name, params) in &self.0 {
            out.push(byte(name.len()));
            out.extend(name.as_bytes());
            out.push(byte(params.len()));
            out.extend(params.iter().map(|w| w.code()));
        }
        out
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        let end = self
            .at
            .checked_add(n)
            .filter(|&end| end <= self.bytes.len());
        let end = end.ok_or("the frame ends in the middle of a value")?;
        let out = &self.bytes[self.at..end];
        self.at = end;
        Ok(out)
    }

    fn byte(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], String> {
        Ok(self.take(N)?.try_into().expect("take returns N bytes"))
    }
}

fn read_header<'a>(r: &mut Reader<'a>) -> Result<Vec<(&'a str, Vec<Wire>)>, String> {
    let version = r.byte()?;
    if version != VERSION {
        return Err(format!("the frame is version {version}, not {VERSION}"));
    }
    let mut calls = Vec::new();
    for _ in 0..r.byte()? {
        let name_len = r.byte()?;
        let name = std::str::from_utf8(r.take(name_len.into())?)
            .map_err(|_| "a scene call name in the frame is not text")?;
        let nparams = r.byte()?;
        let params = r
            .take(nparams.into())?
            .iter()
            .map(|&code| Wire::from_code(code).ok_or("the frame has an unknown value type"))
            .collect::<Result<Vec<_>, _>>()?;
        calls.push((name, params));
    }
    Ok(calls)
}

/// The scene calls a frame's header declares, in index order.
pub fn declared(header: &[u8]) -> Result<Vec<(String, Vec<Wire>)>, String> {
    let mut r = Reader {
        bytes: header,
        at: 0,
    };
    let calls = read_header(&mut r)?;
    Ok(calls
        .into_iter()
        .map(|(name, params)| (name.to_string(), params))
        .collect())
}

/// Make each scene call `bytes` encodes, in order, through `call`. A frame
/// that is truncated, is of a version this host does not know, or names a
/// wire or a call index it did not declare is an error, never a panic: the
/// bytes are the guest's.
pub fn replay(
    bytes: &[u8],
    mut call: impl FnMut(&str, &[HostValue]) -> Result<(), String>,
) -> Result<(), String> {
    let mut r = Reader { bytes, at: 0 };
    let calls = read_header(&mut r)?;
    let mut args = Vec::new();
    while r.at < bytes.len() {
        let index = usize::from(r.byte()?);
        let (name, params) = calls
            .get(index)
            .ok_or("the frame calls a scene call it did not declare")?;
        args.clear();
        for wire in params {
            args.push(match wire {
                Wire::Int => HostValue::Int(i64::from_le_bytes(r.array()?)),
                Wire::Float => HostValue::Number(f64::from_le_bytes(r.array()?)),
                Wire::Bool => HostValue::Bool(r.byte()? != 0),
                Wire::Str => {
                    let len = u32::from_le_bytes(r.array()?);
                    let text = r.take(usize::try_from(len).map_err(|_| "string too long")?)?;
                    HostValue::Str(String::from_utf8_lossy(text).into_owned())
                }
            });
        }
        call(name, &args)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const CIRCLE: [Wire; 4] = [Wire::Float, Wire::Float, Wire::Float, Wire::Str];

    fn frame() -> Vec<u8> {
        let mut calls = Calls::default();
        let circle = calls.index("circle", &CIRCLE);
        let mut bytes = calls.header();
        bytes.push(circle);
        for x in [1.0_f64, 2.0, 3.0] {
            bytes.extend(x.to_le_bytes());
        }
        bytes.extend(3_u32.to_le_bytes());
        bytes.extend(b"red");
        bytes
    }

    fn replayed(bytes: &[u8]) -> Result<Vec<(String, Vec<HostValue>)>, String> {
        let mut seen = Vec::new();
        replay(bytes, |name, args| {
            seen.push((name.to_string(), args.to_vec()));
            Ok(())
        })?;
        Ok(seen)
    }

    #[test]
    fn a_frame_replays_the_calls_it_declares() {
        let seen = replayed(&frame()).unwrap();
        assert_eq!(
            seen,
            [(
                "circle".to_string(),
                vec![
                    HostValue::Number(1.0),
                    HostValue::Number(2.0),
                    HostValue::Number(3.0),
                    HostValue::Str("red".into())
                ]
            )]
        );
    }

    #[test]
    fn a_truncated_frame_is_rejected_whatever_the_cut() {
        let whole = frame();
        let record = whole.len() - (1 + 24 + 4 + 3);
        for len in 0..whole.len() {
            let cut = replayed(&whole[..len]);
            assert_eq!(cut.is_ok(), len == record, "cut at {len}");
        }
    }

    #[test]
    fn a_string_longer_than_the_frame_is_rejected() {
        let mut bytes = frame();
        let at = bytes.len() - 7;
        bytes[at..at + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(replayed(&bytes).is_err());
    }

    #[test]
    fn an_undeclared_call_an_unknown_wire_and_a_wrong_version_are_rejected() {
        let mut bytes = frame();
        let record = bytes.len() - (1 + 24 + 4 + 3);
        bytes[record] = 9;
        assert!(replayed(&bytes).unwrap_err().contains("did not declare"));

        let mut bytes = frame();
        let wire = bytes.iter().position(|&b| b == b'f').unwrap();
        bytes[wire] = b'?';
        assert!(replayed(&bytes).unwrap_err().contains("unknown value type"));

        let mut bytes = frame();
        bytes[0] = 2;
        assert!(replayed(&bytes).unwrap_err().contains("version 2"));
        assert!(replayed(&[]).is_err());
    }

    #[test]
    fn a_call_name_that_is_not_text_is_rejected() {
        let mut bytes = frame();
        bytes[3] = 0xFF;
        assert!(replayed(&bytes).is_err());
    }

    #[test]
    fn a_header_with_more_calls_than_bytes_is_rejected() {
        assert!(replayed(&[VERSION, 200]).is_err());
    }
}
