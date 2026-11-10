# Embedding goat

goat is a library first. The `goat` crate compiles a script against a **host
interface** (the functions and the event and shape vocabulary your application
offers) into a WebAssembly module. Your application runs that module in a wasm
runtime and answers the script's calls. The CLI (`goat_cli`), the web player
(`goat_web`) and the Apple shells are clients of this surface; none of them has
a private way in. Decisions behind it: ADR 0015 (host-owned event loop), ADR
0020 (host vocabulary), ADR 0024 (the facade owns the host boundary).

Nothing here is promised yet. Every item below is **experimental** unless it is
marked **stable**. Experimental means the name or signature may change in any
release; stable means a change needs an ADR.

## The model

```
 your source ──► compile(source, &HostInterface) ──► wasm bytes
                                                        │
 your app: instantiate, answer `foreign` calls ◄────────┘
```

- The script never touches the outside world except through functions you
  declare with `foreign`. That is the sandbox: a script with no declarations can
  compute and print, and nothing else.
- The host interface is the only type annotation in the system. Script code
  carries none; the checker infers everything else from your `foreign`
  signatures.
- Compilation needs no wasm runtime, so the compiler crates build for
  `wasm32-unknown-unknown`. Running does, and lives behind the `native` feature
  (wasmtime) so it stays out of that build.

## Public surface

Everything is imported from the `goat` crate root, except the runner in
`goat::native`.

| Item | Status | What it is |
|---|---|---|
| `HostInterface::with_stdlib(decls)` | stable | The standard library plus your `foreign` declarations. Declarations may not shadow stdlib names (debug builds assert). |
| `HostInterface::new(prelude)` | experimental | Your whole prelude, stdlib included or not, with the turtle's vocabulary. |
| `HostInterface::with_vocab(prelude, vocab)` | experimental | Your own events, shapes and keys (ADR 0020). |
| `Vocab`, `Ty`, `Row`, `Group`, `GoatError`, `Span` | experimental | Re-exported from the checker, so a host names every type `compile`, `check` and `with_vocab` use with only a `goat` dependency. |
| `check(source, &host)` | experimental | Type-check without emitting code; returns the program's `Ty` and the warnings. `goat check` calls it. |
| `HostInterface::turtle()` | experimental | The turtle host's interface; the reference client. |
| `HostInterface::prelude()`, `vocab()` | experimental | Read back what the interface carries. |
| `compile(source, &host)` | stable | Source to wasm bytes, or the checker's errors. |
| `compile_with_warnings` | experimental | Also returns non-fatal warnings. |
| `compile_for(profile, ..)`, `Profile` | experimental | `Profile::Desktop` (`Int` is `i64`, `Float` is `f64`) or `Profile::Embedded` (`i32`, `f32`). |
| `compile_reloadable(source, &host)` | experimental | An interactive program whose memory the host owns, so `Interactive::reload` can swap it in. |
| `compile_turtle(source)` | experimental | `compile` against the turtle. |
| `Host`, `HostValue`, `Boundary`, `NoHost` | stable | The `foreign` boundary: implement `Host` to answer calls. Values crossing are `Number`, `Int`, `Bool`, `Unit` and `Str`; a string is copied. |
| `SceneSink`, `Scene`, `SceneCommand`, `SceneHost`, `check_color` | experimental | Where an interactive program's frames go. |
| `format_number`, `format_bool` | experimental | Format values the way `print` does. |
| `native::run_to_end`, `run_to_end_within` | experimental | Run a run-once program against a `Host`; a trap becomes `Finished.result`'s `Err(Stopped)`, with the source range to blame. |
| `native::Interactive` | experimental | Drive `init`/`update`/`draw`: `new`, `with_timeout`, `send`, `draw`, `reload`, `subscriptions`, `finish`. |
| `native::Event` | experimental | The turtle vocabulary's events: `Tick`, `KeyDown`, `KeyUp`, `PointerMove`, `PointerDown`, `PointerUp`. |
| `native::Guest` | experimental | The raw wasmtime instance the runners are built on. |

Known gaps in the facade, each a reason not to mark more as stable:

- `Interactive` sends the turtle's `Event` enum and draws through the fixed
  `scene.*` calls. A custom `Vocab` compiles, but today only a host that
  implements those imports itself (a `Guest` with its own `Host`) can drive it.

## Tutorial: embed goat in a Rust app

The code below is `goat/examples/embed.rs`. It is a complete program, compiled
and run by `cargo test`, and it uses a host with no turtle in it: one logging
function.

```console
cargo run -p goat --features native --example embed
```

### 1. Declare what the host offers

A `foreign` binding names a host module and function and gives its type. The
types are `Number`, `Int`, `Bool`, `Unit` and `String`, plus function arrows.

```rust
let interface = HostInterface::with_stdlib("log = foreign \"log\" \"line\" (String) -> Unit");
```

The script now has a function `log`. Its name is whatever you bind it to; its
signature is what the checker enforces at every call.

### 2. Compile the script

```rust
let script = "log(\"hello from goat\"); print(6 * 7)";
let wasm = goat::compile(script, &interface).map_err(|errors| errors[0].message.clone())?;
```

Errors carry a source span (byte range) for your editor to underline. A script
that calls a function you did not declare fails here, never at run time.

### 3. Implement `Host`

`signature` tells the runtime the types of your functions (compiled code only
carries wasm value types, so it cannot tell a `Bool` from a string pointer);
`call` runs one. Returning `Err` traps the script.

```rust
struct Logger(Vec<String>);

impl Host for Logger {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        (module == "log" && name == "line").then(|| (vec![Boundary::Str], Boundary::Unit))
    }

    fn call(&mut self, _: &str, _: &str, args: &[HostValue]) -> Result<HostValue, String> {
        if let [HostValue::Str(text)] = args {
            self.0.push(text.clone());
        }
        Ok(HostValue::Unit)
    }
}
```

`signature` must agree with the declaration from step 1; the checker cannot see
your Rust, so a mismatch is yours to avoid.

### 4. Run it

```rust
let finished = run_to_end(&wasm, Logger(Vec::new()))?;
println!("printed: {:?}", finished.printed);
println!("logged: {:?}", finished.host.0);
```

```
printed: ["42"]
logged: ["hello from goat"]
```

`finished.result` is `Ok(live_blocks)` on a clean finish (zero for a correct
program) or `Err(Stopped)` if the script trapped; `printed` holds the output
either way. Use `run_to_end_within` to stop a script that runs too long.

### 5. Interactive programs and hot reload

A script that defines `init`, `update` and `draw` is not run once; the host
drives it (ADR 0015). `goat/examples/embed_live.rs` sends three `Tick`
events, draws, recompiles an edited script, and reloads it:

```console
cargo run -p goat --features native --example embed_live
```

```
Kept: circles [(3.0, 9.0)], 0 heap blocks leaked
```

The steps, in order:

1. Compile with `compile_reloadable`, not `compile`.
2. `Interactive::new(&wasm, sink)` instantiates and runs `init`. The sink is
   your `SceneSink`; `draw` calls it with `begin`, each shape, then `end`.
3. `send(&Event)` runs `update`. It returns `false` and does nothing if the
   script does not handle that event (`subscriptions()` lists those it does).
4. `reload(&new_wasm)` swaps in the recompiled program over the same heap. It
   returns `Reloaded::Kept` when the model's layout is unchanged (the ticks
   above survived the edit) and `Reloaded::Reset` when it changed and the model
   restarted from the new `init`. If the new program cannot start, the old one
   keeps running.
5. `finish()` tears down and returns the sink and the number of leaked heap
   blocks.

A trap stops an `Interactive` for good, except that a reload rescues it.
`Interactive::with_timeout` bounds each call into the script.

## The reference clients

The turtle is the first client: `HostInterface::turtle()` supplies its
`forward`, `left` and pen declarations and its events and shapes, and the CLI
(`cli/src/main.rs`) answers them with a `Host`. The web player compiles with
`goat::compile_turtle` in a `wasm32-unknown-unknown` module and implements the
same imports in JavaScript. Both go through the calls in this guide. The
turtle's declarations are ordinary goat source (`prelude/turtle.goat`), so any
embedder can read them as a worked host interface. The canvas host will be the
second reference client; it is not documented here until it lands.

## What is not here

Reading a host's WIT file to generate the `foreign` declarations is not built.
Today you write the declarations by hand, as in step 1.
