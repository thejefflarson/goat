// Drives goat_web.wasm; the record layout is documented in src/lib.rs.
const OK = 0;

interface CompilerExports {
  memory: WebAssembly.Memory;
  gw_alloc(len: number): number;
  gw_free(ptr: number, len: number): void;
  gw_compile(ptr: number, len: number): number;
  gw_free_result(rec: number): void;
}

export type CompileResult =
  | { ok: true; module: Uint8Array<ArrayBuffer> }
  | { ok: false; diagnostics: string };

export async function loadCompiler(url: string | URL): Promise<WebAssembly.Module> {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`could not load compiler: HTTP ${response.status}`);
  return WebAssembly.compile(await response.arrayBuffer());
}

export async function compile(compiler: WebAssembly.Module, source: string): Promise<CompileResult> {
  const instance = await WebAssembly.instantiate(compiler, {});
  const { memory, gw_alloc, gw_free, gw_compile, gw_free_result } =
    instance.exports as unknown as CompilerExports;
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
