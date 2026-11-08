//! What a module imports, read before it loads: WAMR links a module's host
//! functions while loading it, so they must be registered first.

use wasmparser::{CompositeInnerType, Parser, Payload, TypeRef, ValType};

pub struct Import {
    pub module: String,
    pub name: String,
    pub params: Vec<ValType>,
    pub result: Option<ValType>,
}

/// The function imports of `wasm`, in order. Any other kind of import is an
/// error: goat's modules import only host functions.
pub fn function_imports(wasm: &[u8]) -> Result<Vec<Import>, String> {
    let bad = |e: wasmparser::BinaryReaderError| format!("invalid module: {e}");
    let mut types = Vec::new();
    let mut imports = Vec::new();
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.map_err(bad)? {
            Payload::TypeSection(reader) => {
                for group in reader {
                    for ty in group.map_err(bad)?.into_types() {
                        types.push(match ty.composite_type.inner {
                            CompositeInnerType::Func(f) => Some(f),
                            _ => None,
                        });
                    }
                }
            }
            Payload::ImportSection(reader) => {
                for import in reader.into_imports() {
                    let import = import.map_err(bad)?;
                    let TypeRef::Func(index) = import.ty else {
                        return Err(format!(
                            "unsupported import {}.{}: only host functions can be linked",
                            import.module, import.name
                        ));
                    };
                    let ty = types
                        .get(index as usize)
                        .and_then(Option::as_ref)
                        .ok_or("import has no function type")?;
                    imports.push(Import {
                        module: import.module.to_string(),
                        name: import.name.to_string(),
                        params: ty.params().to_vec(),
                        result: ty.results().first().copied(),
                    });
                }
            }
            _ => {}
        }
    }
    Ok(imports)
}
