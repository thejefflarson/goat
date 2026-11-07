# goat for language models

goat is a new language, so a model has never seen it in training. This file is
the whole language as it runs **today** — paste it into context before asking a
model to read or write goat. It describes what actually compiles and runs on the
current build, and marks clearly what is planned but not yet usable, so a model
does not generate code the compiler rejects.

If a feature is under "Not yet", the compiler will reject it with a clear error.
Prefer the forms under "What runs today".

## In one paragraph

goat is a typed, garbage-collector-free scripting language that compiles to
WebAssembly and runs under a wasm runtime (the CLI uses wasmtime). It is
functional and immutable: there are no variables to reassign — a program is one
expression, and its value is the program's output. Statements are expressions
joined with `;`, and loops are expressions of type `Unit`.
Types are inferred (Hindley-Milner), so you never write a type annotation.

## Running a program

```
goat run program.goat      # compile to wasm and run it, printing the result
goat build program.goat -o out.wasm   # just emit the wasm module
goat check program.goat    # type-check only
```

The program's result is its **final expression**. The runtime prints that value
when it is a number or a boolean. (A record or function result prints nothing
yet — end a program on a number or boolean to see output.)

## What runs today

### Numbers, booleans, operators

```
1 + 2 * 3        # 7   — usual precedence, left-associative
10 / 4           # 2.5 — numbers are floating point
-x               # negation
1 < 2            # true   — comparisons: <  <=  >  >=  give a boolean
true    false    # booleans
```

There is one number type (`Number`). Arithmetic is `+ - * /`. Comparisons
produce booleans. There is no `==` yet, and no boolean `and`/`or` yet.

### Bindings: `name = value`

A binding names a value, then the rest of the program follows. Bindings are
expressions; the last expression is the result.

```
x = 10
y = x + 5
y                # 15
```

Value bindings are **sequential and shadow**: a later binding of the same name
replaces the earlier one for the code after it.

```
score = 1
score = score + 1   # the right-hand `score` is the old 1
score               # 2
```

### Sequencing: `a; b`

`a; b` runs `a`, drops its value, then runs `b`; it is `b`'s value. A trailing
`print(1);` is `Unit`. Bindings scope over the statements after them.

```
print(1); print(2); 3     # prints 1, 2; value 3
```

A statement ends only at `;`: `print(1) (2)` is a call of `print(1)` and
`print(1) -2` is a subtraction, so write `print(1); (2)`. A loop or a bare call
that is not the last thing in a block needs the `;`.

### Booleans: `and`, `or`, `not`

```
x > 1 and x < 10 or x == 100
not done
```

`and`/`or` skip the right side when the left decides. Loosest first: `or`,
`and`, `not`, `==`, comparisons, `+ -`, `* /` — so `not a == b` is
`not (a == b)`.

### Loops

```
repeat 3 times do print("hi") done;
for i from 1 to 5 do print(i * i) done;      # 1 to 5, both included
for x in [3, 1, 2] do print(x) done;
```

A loop is a `Unit` expression; the body's value is dropped. The counter is a
`Number`. `for` counts up only (`from 5 to 1` runs zero times). `from`, `to` and
`in` are words only in a `for` header; `for`, `and`, `or`, `not` are reserved.

### Conditionals: `if … then … else … done`

```
if n < 2 then n else n - 1 done
```

`then` and `else` branches must have the same type. The whole `if` is an
expression. (An `if` with no `else` is allowed only when the `then` branch has
the unit type — rare today; prefer the full form.)

### Functions: `program(params) do body done` (or `function(...)`)

`program` and `function` are the same keyword — two spellings of one thing. Use
whichever reads better; `program` is the kid-facing default.

```
double = program(n) do n * 2 done
double(21)       # 42
```

```
fib = function(n) do
  if n < 2 then n
  else fib(n - 1) + fib(n - 2)
  done
done
fib(10)          # 55
```

Functions are **first-class values**: pass them as arguments, return them, store
them in record fields.

```
apply = program(f, x) do f(x) done
apply(double, 21)   # 42
```

Functions defined together in a scope are **mutually recursive** — order does
not matter; each can call the others and itself.

### Records: `{field: value, …}` and `record.field`

```
origin = {x: 0, y: 0}
spot = {x: 3, y: 4, z: 5}
spot.x           # 3
```

Field access is **row-polymorphic**: a function that reads `.x` and `.y` works
on any record that has at least those fields, whatever else it carries.

```
sum = program(p) do p.x + p.y done
sum(origin) + sum(spot)   # 0 + 7 = 7
```

Records nest, and field access chains: `{point: {x: 1}}.point.x` is `1`.

### Comments

```
# everything after a # to the end of the line is a comment
```

## Types, in brief

Types are fully inferred; you never annotate. The inferencer is Hindley-Milner
with row-polymorphic records. A binding made with `=` is generalized, so a
generic function bound with `=` can be used at several types:

```
id = program(x) do x done
id(1)            # OK
id(true)         # OK — id is generic
```

One sharp edge to know (standard HM): a function **passed as a parameter** is
monomorphic inside the body — it cannot be used at two different types there.

```
both = program(f) do a = f(1)  f(true) done   # ERROR: Number vs Bool
```

Bind the generic function with `=` and call it directly, or pass it once per
type, instead.

## Not yet (the compiler will reject these)

These are planned but **do not run on the current build**. Do not generate them.

- **Capturing closures.** A `program(...)` that refers to a binding from an
  enclosing scope is rejected today ("closures are not supported yet"). A nested
  function may use its own parameters and any top-level function, but not a
  variable captured from an outer function. (This is Phase 4, landing now.)
- **Strings.** String literals parse (`"hi"`) but there is no string runtime, so
  a program that produces or prints a string will not run yet. (Phase 5.)
- **`return`.** A reserved word with no syntax; a function's value is its body.
- **Variants and `match`** (`Circle(5)`, `Empty`), **lists**, and the
  **turtle/drawing** builtins. (Phases 7–8.)
- **Field-wise record arithmetic** (`{x:1} + {x:2}`) and **named types**.
  (Later.)

## Complete worked examples

Each of these runs today with `goat run`.

```
# Recursion — the tenth Fibonacci number. Prints 55.
fib = program(n) do
  if n < 2 then n
  else fib(n - 1) + fib(n - 2)
  done
done
fib(10)
```

```
# Functions as values. Prints 42.
apply = program(f, x) do f(x) done
double = function(n) do n * 2 done
apply(double, 21)
```

```
# Records and row-polymorphic field access. Prints 7.
origin = {x: 0, y: 0}
spot = {x: 3, y: 4, z: 5}
sum = program(p) do p.x + p.y done
sum(origin) + sum(spot)
```

## Checklist before handing goat back

- The program ends on a **number or boolean** expression (so it prints).
- No capturing of outer-scope variables inside a nested `program`/`function`.
- No strings, loops, `==`, `and`/`or`, variants, `match`, or lists.
- Recursion, not iteration, for repetition.
- No type annotations anywhere.
