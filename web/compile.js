// Drives goat_web.wasm; the record layout is documented in src/lib.rs.
const OK = 0;

export async function loadCompiler(url) {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`could not load compiler: HTTP ${response.status}`);
  return WebAssembly.compile(await response.arrayBuffer());
}

export async function compile(compiler, source) {
  const instance = await WebAssembly.instantiate(compiler, {});
  const { memory, gw_alloc, gw_free, gw_compile, gw_free_result } = instance.exports;
  const text = new TextEncoder().encode(source);
  const src = gw_alloc(text.length);
  new Uint8Array(memory.buffer, src, text.length).set(text);
  const rec = gw_compile(src, text.length);
  gw_free(src, text.length);
  const view = new DataView(memory.buffer);
  const tag = view.getUint8(rec);
  const payload = new Uint8Array(memory.buffer, rec + 5, view.getUint32(rec + 1, true)).slice();
  gw_free_result(rec);
  return tag === OK
    ? { ok: true, module: payload }
    : { ok: false, diagnostics: new TextDecoder().decode(payload) };
}
