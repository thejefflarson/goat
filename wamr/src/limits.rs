//! Which WAMR interpreter a module needs (ADR 0025). The fast interpreter
//! encodes a function's frame in 16-bit offsets, so it refuses at load any
//! function whose locals, operand stack and constants add up to more than
//! 32767 cells. The classic interpreter has no such cap.

use wasmparser::{CompositeInnerType, Parser, Payload, ValType};

use crate::Interp;

/// The most cells one function may use under the fast interpreter.
pub const FAST_INTERP_CELL_LIMIT: u32 = 32767;

fn cells(ty: ValType) -> u32 {
    match ty {
        ValType::I64 | ValType::F64 => 2,
        ValType::V128 => 4,
        _ => 1,
    }
}

/// `Classic` when some function might exceed the fast interpreter's cell
/// limit, `Fast` otherwise. A function's cells are bounded by its parameters
/// and locals plus two per operator (each pushes at most one value, or one
/// constant, of at most two cells), so a function is oversized when that bound
/// passes the limit. The bound errs toward `Classic`, which runs everything
/// the fast interpreter does, only slower.
pub fn interp_for(wasm: &[u8]) -> Result<Interp, String> {
    let bad = |e: wasmparser::BinaryReaderError| format!("invalid module: {e}");
    let mut param_cells = Vec::new();
    let mut signatures = Vec::new();
    let mut next = 0;
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.map_err(bad)? {
            Payload::TypeSection(reader) => {
                for group in reader {
                    for ty in group.map_err(bad)?.into_types() {
                        param_cells.push(match ty.composite_type.inner {
                            CompositeInnerType::Func(f) => {
                                f.params().iter().map(|&p| cells(p)).sum()
                            }
                            _ => 0,
                        });
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                for index in reader {
                    signatures.push(index.map_err(bad)?);
                }
            }
            Payload::CodeSectionEntry(body) => {
                let params = signatures
                    .get(next)
                    .and_then(|&ty| param_cells.get(ty as usize))
                    .copied()
                    .ok_or("function has no type")?;
                next += 1;
                let mut bound = params;
                for local in body.get_locals_reader().map_err(bad)? {
                    let (count, ty) = local.map_err(bad)?;
                    bound = bound.saturating_add(count.saturating_mul(cells(ty)));
                }
                let operators = body.get_operators_reader().map_err(bad)?;
                for op in operators {
                    op.map_err(bad)?;
                    bound = bound.saturating_add(2);
                }
                if bound > FAST_INTERP_CELL_LIMIT {
                    return Ok(Interp::Classic);
                }
            }
            _ => {}
        }
    }
    Ok(Interp::Fast)
}
