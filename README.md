# goat

A small, statically typed programming language that compiles to native code —
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

Types are inferred — you never write a type annotation. The checker is
Hindley-Milner with **row-polymorphic records** (scoped labels), so a function
like `program(p) do p.x done` works on *any* record that has an `x`.

To have a language model read or write goat, give it [`docs/llm.md`](docs/llm.md)
— the whole language as it runs today, written for a model with no training data
on goat.

A `(…)` immediately after an expression is a **call** — `f(x)` calls `f`. A
grouped expression therefore can't start a new statement right after another
one; `1 (2)` reads as "call `1` with `2`" (and `1` is not a function, so you get
a clear error saying so).

## Toolchain

```console
$ goat check FILE        # parse and type-check; prints the program's type
$ goat build FILE -o OUT # compile to a native executable
$ goat run FILE          # compile and run
```

The backend is [Cranelift](https://cranelift.dev); `goat build` links the
generated object against a tiny C runtime using the system `cc`.

## Layout

| Crate | Role |
|---|---|
| `parser` | the grammar (pest) |
| `checker` | lowering, name resolution, and type inference |
| `compiler` | the Cranelift native backend |
| `cli` | the `goat` command |

## Status

Working: the full frontend (parse → type-check) for everything above, and a
native backend for numbers, booleans, functions (including recursion and
higher-order calls), conditionals, and arithmetic.

Not yet compiled (they type-check, but the backend rejects them for now):
records and strings at runtime, and closures that capture local variables.
Next up: compiling records, then the drawing runtime (a live window) and loop
syntax.
