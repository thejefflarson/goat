# goat

A small, statically typed programming language that compiles to WebAssembly —
built to be simple enough for a kid to read, with a real type system underneath
so it can grow into something serious. The eventual goal is a turtle-graphics
language for making drawings.

```
# examples/fib.goat
fib = program(n) do
  if n < 2 then n
  else fib(n - 1) + fib(n - 2)
  done
done

fib(10)
```

```console
$ goat run examples/fib.goat
55
```

## The language today

- Numbers, booleans, strings, and the unit value.
- `name = value  rest` — bindings, which may be recursive.
- `program(a, b) do ... done` — first-class functions; `f(x, y)` calls them.
  `function` is an accepted synonym for `program`.
- `if c then a else b done` — conditionals.
- `{x: 1, y: 2}` — records, with field access `point.x`.
- Arithmetic `+ - * /` and comparisons `< <= > >=`.
- `a and b`, `a or b`, `not a` — booleans; `and`/`or` skip the right side when the
  left decides.
- `a; b` — run `a`, drop its value, then run `b`.
- `repeat n times do ... done`, `for i from 1 to 10 do ... done` and
  `for x in xs do ... done` — loops, which are `Unit` expressions.

Types are inferred — you never write a type annotation. The checker is
Hindley-Milner with **row-polymorphic records** (scoped labels), so a function
like `program(p) do p.x done` works on *any* record that has an `x`.

To have a language model read or write goat, give it [`docs/llm.md`](docs/llm.md)
— the whole language as it runs today, written for a model with no training data
on goat.

A `(…)` immediately after an expression is a **call** — `f(x)` calls `f`. A
grouped expression therefore can't start a new statement right after another
one; `1 (2)` reads as "call `1` with `2`" (and `1` is not a function, so you get
a clear error saying so). Separate statements with `;` — `print(1); (2)` — which
is also how a bare call or a loop stands as a statement.

To embed goat in your own application, see [`docs/embedding.md`](docs/embedding.md).

## Toolchain

```console
$ goat check FILE        # parse and type-check; prints the program's type
$ goat build FILE -o OUT # compile to a WebAssembly module
$ goat run FILE          # compile and run
```

The one backend emits WebAssembly. `goat build` writes the module; `goat run`
executes it under wasmtime with the turtle as its host.

## Layout

| Crate | Role |
|---|---|
| `parser` | the grammar (pest) |
| `checker` | lowering, name resolution, and type inference |
| `mir` | monomorphization and the mid-level IR |
| `wasm` | the WebAssembly backend, emitted from MIR |
| `goat` | the facade: compile, check and run for embedders |
| `cli` | the `goat` command |

See [`docs/plan.md`](docs/plan.md) for the roadmap.
