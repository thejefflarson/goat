# Differential test: the proven algorithm against the Rust checker

ADR 0037 (decision 6) ties the inference algorithm proved in `proofs/` to
`checker/src/infer.rs` by running both on the same programs.

- `proofs/GoatInfer.v` is the algorithm (Hindley-Milner algorithm W with Leijen
  row unification, and a sort on each type variable). `proofs/GoatInferSound.v`
  proves it sound: every type it infers is derivable in `typing`, in the kinding
  environment it returns (`infer_closed_sound`, no admits, no axioms).
- `proofs/GoatExtract.v` extracts it to OCaml (`goat_infer.ml`).
- `checker/examples/core_corpus.rs` collects programs and writes, for each one
  in the core fragment, its term (locally nameless s-expression) and the Rust
  checker's verdict (`ERR`, or `OK` and the type).
- `driver.ml` runs the extracted algorithm on each term and exits non-zero if
  acceptance differs or the types differ up to renaming of variables.

Run it with `make -C proofs differential` (it is part of `make -C proofs ci`
and of the `coq` workflow).

## Which programs are compared

Every goat source the repository holds: `examples/*.goat`, the `goat` blocks of
`docs/llm.md`, every string literal of the Rust sources under `checker/` and
`parser/` (tests included), a short list of hand-written programs, 4000
programs from a fixed-seed generator of the core, and 6000 from a fixed-seed
typed generator of the phase-1 forms, and 8000 from a fixed-seed generator of
blocks of functions that call themselves and each other. A program is compared when it is in the
fragment of `proofs/goat_ln.ott`: numerals, Float literals, strings, unit,
booleans, functions, calls, `if` with an `else`, the twelve binary operators on
Int, Float, String and Bool, `let` of any value, `letrec` groups of
functions, record literals with distinct labels, and field access, binding every
name it uses. Anything else (the prelude, tags, `::`, dot calls, `self`, an operator on records or on Unit) is outside the
calculus and skipped.

The generic operators are compared. `+ - *` on operands the checker leaves as
type variables (`program(x) do x * 2 done`, `add = program(a, b) do a + b done`),
a numeral at `Float` (`1 + 1.5`, written as the bare numeral), and a generic
function used at `Int` and at `Float` are all in the corpus. Five kinds of
program are skipped, each because the calculus and the checker differ on it:

- a comparison, or a `/`, on an operand whose type only a later use settles
  (`program(x) do x > x done("a")`): a generic comparison waits for the `Eq` and
  `Ordered` sorts, and `/` on an open operand is typed `Ordered` by the checker
  and `Numeric` by the calculus;
- a `let` of a syntactic value with a numeral in it (`n = 3`, `r = {a: 1}`): the
  calculus generalizes it (`numeral_binding_is_generic`), the checker generalizes
  a numeral's variable only in a function's type, so
  `n = 3  {a: n + 1.5, b: n // 2}` types in the calculus and not in the checker;
- a program with `+ - *` on open operands that passes a record to a call: the
  checker applies them to a record field by field, and the calculus has no
  operator on records;
- a record that holds a function of a recursive group by name
  (`{stop: true, g: h}` inside `h`): the checker accepts a type with no finite
  derivation;
- the cases the README already listed: the prelude, tags, `::`, dot calls,
  `self`.

## Where `float(e)` goes

The calculus has no implicit Int-to-Float widening, so the corpus writer
elaborates it from the checker's node types and the driver then requires the
proven algorithm to accept the result. It writes `float(e)` around

- the Int operand of `< <= > >= == !=` whose other operand is a Float, and the
  Int operand of `+ - *` in the same position;
- each operand of `/`, Int or Float (a quotient takes Floats, and `float(e)` is
  the identity on a Float);
- an Int argument to a call whose callee's parameter is a Float;
- a numeral inside an operand of a comparison whose type is Float.

An Int literal whose node type is Float anywhere else is written as the bare
numeral, which the calculus types at `Float` (`T_Num`); the checker settled the
literal there rather than widening it. A numeral inside a comparison is written
`float(n)` because the algorithm has no derivation of a comparison at a variable
and takes `Int` for a numeral's variable there, so a numeral that a later use
makes a `Float` would be rejected. If the checker widened anywhere else, the
elaborated program would be rejected and the driver would report a mismatch. A
rejected program has no node types and is written with no coercions. This is a
differential check, not a theorem: a full proof would need a model of the
checker's elaborator.

The calculus is curried, so a program whose functions and calls all take one
parameter or argument (`U` lines) is compared in both directions. A program with
several (`N` lines) is compared only when the Rust checker accepts it, since the
Rust checker rejects a partial call that the curried calculus accepts.

A `let` of a computed value is compared (`T_LetMono`). A function that calls
itself, or that is in a group with functions that mention each other, is read
as a `letrec` (`T_Letrec`) of the group, which the checker generalizes after
typing all its members (`Infer::settle`); the corpus writer groups the
members with the same rule. A group whose functions are not next to each other
in their block, with a value binding between them, is skipped. The group
generator writes blocks of such functions, with computed values around them, at
any depth.

## Types up to renaming

Both sides print the type in one form: functions curried, record fields in
label order (labels numbered by first occurrence in the program; a stable sort,
so repeated labels keep their order), type and row variables numbered by first
occurrence. Rust's `Int` is the calculus's `Number`.

A program's type can leave variables free, and the algorithm returns the kinding
environment that gives each its sort (`infer_closed_env`). The calculus has no
defaulting rule (ADR 0038), so the driver defaults when it prints: a free
`Literal` variable prints as `Number`, which is what the checker does to a
variable that nothing decided (`default_numbers`: a number in no function's
type is `Int`). A free `Numeric` or `Any` variable prints as a numbered
variable, as the checker's does. So `program(x) do x * 2 done` prints
`(Number -> Number)` on both sides and `program(a, b) do a + b done` prints
`(v0 -> (v0 -> v0))`.

## What it does not show

A disagreement is caught only on a tested program. The generator and the
corpus are finite, which is the gap ADR 0037 accepts.
