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

## Recursive types

A program in which the checker gives some node a recursive type (`Ty::Rec`) is
a mode `R` line, or a mode `K` line when a `Rec` body holds a record with an
open row (a row variable that must itself be tied into the knot). Its verdict
is the root type written with `(mu mK. T)` for a recursive type, `mK` naming the
binder by its depth. The driver reads that text and the algorithm's type as
regular trees and compares them by bisimulation with assumed pairs: a pair of
recursive types met again is taken as equal, and the variables of the two sides
correspond one to one. A program the algorithm refuses is counted, not compared:
a recursive group whose members need a knot (`g = program(p) do {a: p, b: g(p)}
done`; the algorithm unifies the members of a group with `unify_t`) and a row
that must knot (a `K` line). Any other difference is a mismatch and fails the
run.

## Which programs are compared

Every goat source the repository holds: `examples/*.goat`, the `goat` blocks of
`docs/llm.md`, every string literal of the Rust sources under `checker/` and
`parser/` (tests included), a short list of hand-written programs, 4000
programs from a generator of the core, 6000 from a typed generator of the
phase-1 forms, and 8000 from a generator of blocks of functions that call
themselves and each other, each run with three fixed seeds so that a change to
one random stream cannot hide or reveal a mismatch by chance. A program is compared when it is in the
fragment of `proofs/goat_ln.ott`: numerals, Float literals, strings, unit,
booleans, functions, calls, `if` with an `else`, the twelve binary operators on
Int, Float, String and Bool, `let` of any value, `letrec` groups of
functions, record literals with distinct labels, and field access, binding every
name it uses. Dot calls, `::` and `self` are read as the `proj`, `app` and `let` lowering rewrote them to, and the method flag
is erased from the type column. A function with `self` first, written directly as a field of a record literal, is a
method: the reader writes it `(meth e)`, the calculus's `fs_meth`, and a literal with a method is typed by `T_Obj`, which gives
all its methods one receiver (ADR 0034 decision 2). The checker ties a method's receiver to its record
(`{x: 0, bump: program(self) do {...self, x: self.x + 1} done}` is `mu m. {x: Number, bump: (m -> m) | v}`), and the
algorithm does the same by giving every method one record of slots for the literal's fields and a row variable for what a
use adds, unified with the fields' types afterwards (`tie_obj`); so these programs are compared, and a literal whose
methods need different receivers is rejected by both (`lit = {a: program(self) do self.x done, b: program(self) do self.y done}`
then `lit.a()`). Anything else (the prelude, tags, an operator on records or on Unit) is outside the
calculus and skipped.

The generic operators are compared. `+ - *` on operands the checker leaves as
type variables (`program(x) do x * 2 done`, `add = program(a, b) do a + b done`),
a numeral at `Float` (`1 + 1.5`, written as the bare numeral), and a generic
function used at `Int` and at `Float` are all in the corpus, and so is a call that
passes a record of numbers to such a function (`add({x: 1}, {x: 2})`: the
calculus applies `+ - * // %` to records field by field, `GoatRecArith.v`).
A `let` of a record or a name with a numeral in it is compared too
(`r = {a: 1}  {x: r.a + 1.5, y: r.a // 2}` is an error in both): the algorithm
generalizes a function and a bare numeral over every variable of its type, and
any other syntactic value over every variable but the `Literal` ones, which stay
shared and open to `Float`, as the checker does (ADR 0038). A spread of
syntactic values is one too, as in the checker's `is_syntactic_value`.
A few kinds of
program are skipped, each because the calculus and the checker differ on it:

- a comparison at a parameter's generic type (`program(a, b) do a == b done`,
  or `same` of that used at `Int` and at `String`): the checker leaves the
  parameter a variable with an `Eq` or `Ordered` kind, and the calculus has no
  such sort, so the algorithm takes one concrete type and cannot type both
  uses. A comparison on a variable a later use settles is compared: the first run
  of the algorithm leaves it open and the second settles it at what the program
  forced (`v = 71 // 88` then `if v <= v then v - 3.1 else 4.0 done` is
  `Float`), and `/` on an open operand is compared too. The reader skips a
  comparison whose operand type is a checker variable outside `number_vars`; the
  checker does not record a `Numeric` variable there (`x == x % x` in a function),
  so `FORCED` in `core_corpus.rs` pins such programs as compared anyway;
- a rest pattern with no fields (`program({...r}) do r done`): the checker types
  it as a record, and the calculus has no way to say that without a label;
- a program the checker rejects over the method flag (a dot call on a plain
  function, `::` on a method or on a data field, a field a method in one record
  and plain in the other), which the calculus does not track; the checker marks
  these errors with `ErrorKind::MethodFlag`, and the reader skips them under their
  own count;
- a program the checker gives up on as too complex (`ErrorKind::ResourceLimit`),
  which a budget decides and not the types;
- the cases the README already listed: the prelude, tags.

A further kind is counted apart from these. When the checker types a program in
the fragment with a recursive type (a `Ty::Rec` anywhere, `Ty::is_recursive`, as for `(p.moved)(p)`), the
corpus writes it as an `R` line and the driver prints it as "skipped for a
recursive type", with no comparison, and says for how many of them the
algorithm infers a type. The algorithm ties a knot where a variable meets a
type that mentions it and writes the head `fold` or `unfold` a mu type that
meets its unrolling needs (`proofs/GoatCoerce.v`, `proofs/GoatInferW.v`); a
difference below a function type or a record field would need an
eta-expansion, so it refuses the program (a deep coercion), and a recursive
group whose members need a recursive type is outside what it elaborates yet.
The canonical type cannot write a `mu`, so the two sides are not compared; the
count tells the reader whether the fragment still reaches recursive types and
how far the algorithm follows it.

## Where `float(e)` goes

The calculus has no implicit Int-to-Float widening, so the corpus writer
elaborates it from the checker's node types and the driver then requires the
proven algorithm to accept the result. It writes `float(e)` around

- the Int operand of `< <= > >= == !=` whose other operand is a Float, and the
  Int operand of `+ - *` in the same position;
- each operand of `/`, Int or Float (a quotient takes Floats, and `float(e)` is
  the identity on a Float);
- an Int argument to a call whose callee's parameter is a Float, including a
  parameter the checker settled as a Float by joining the call's arguments
  (`f(7 // 2, 2.5)` for `f = program(a, b) do a + b done`);
- an Int branch of an `if` whose result is a Float (ADR 0040);
- a numeral inside an operand of a comparison whose type is Float.

An Int literal whose node type is Float anywhere else is written as the bare
numeral, which the calculus types at `Float` (`T_Num`); the checker settled the
literal there rather than widening it. A numeral inside a comparison is written
`float(n)` because the checker widens a numeral beside a Float there. If the checker widened anywhere else, the
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

`core_corpus` prints on stderr how many programs it wrote and how many it
skipped, by reason, and a pinned program it had to skip is reported as
`FORCED SKIP`. The driver prints how many programs it compared and how many
mismatched.

A program outside the calculus is counted under one feature it uses, the first
in this fixed order, which is the order of the proof phases that bring each in:
a foreign host call; tags and `match`; a spread
onto a row variable that lacks the label (below); `print` or `trap`; `and`, `or`, `not`; a loop (a binding named `loop`,
which lowering gives every `repeat` and `for`); a comparison, then arithmetic,
on operands that are not `Int`, `Float`, `String` or `Bool`. After those come
the reasons that are about the shape of a program and not a missing feature: a
recursive group that a value binding uses before the group's last member (the
checker types the use at the member's monomorphic type, the hoisted `letrec` at
its generalized one), a rest pattern with no fields, an inferred type the corpus cannot write, an `if` without an `else`, a function or call with no parameters,
a program that ends in a binding, a numeral of 2^30 or more, and `none of the
above`. A program using two features counts only under the earlier, so when a
phase lands its count falls to 0 and its programs either join the compared set
or appear under the next feature they use.

## Spread and restrict

`{...p, x: v}` is read as `(spread E l e)` and a rest pattern `{x, ...r} = p`
as `(restrict E l)`, one per label, nested. The algorithm infers both
(`proofs/GoatInfer.v`: unification surfaces a label through a presence entry
`l ^ P : T`, binds `P` to `Unit` or `Bool`, and a row variable to
`l ^ p : a ; r`). A presence entry prints as `l3^v2: T`; a `Unit` entry prints as
a field and a `Bool` entry is dropped, as the checker's resolved rows read.

The 222 programs once counted as "a method or presence row" held method flag
variables, none a presence entry: an open row that field access made
(`program(r) do r.x done`) carries a flag variable that only a dot call or a
`METHOD` settles. The calculus has no flag, so the reader ignores a flag
variable and skips only a field flagged `METHOD`.

One kind of program is skipped because the calculus is stricter than the
checker. The calculus's `l # R` holds only of a closed row, so a spread of `l`
onto a record whose row ends in a row variable the checker knows lacks `l` (the
remainder of a rest pattern, put back: `{x, ...r} = p` then `{...r, x: 2}`) has
no derivation, and a program that puts a record with `x` in the remainder's
place is rejected by the checker (`was taken out of this record`) and accepted
by the algorithm. These count under `LacksOnTail`. A `lacks` sort on row
variables in the kinding environment would remove the skip; it extends `sat`,
`kres` and `inst` from type variables to row variables.

## Tag groups (waiting for the checker's groups)

`infer` types `con` and `match` and `unify_t` unifies `grp` types
(`proofs/GoatInfer.v`; both are proved sound), but the corpus and the driver do
not exercise them: the checker's tag groups (#517) are not on master. Once they
are, the corpus writer and the driver need the following, and nothing in
`proofs/` changes.

- **Terms the driver reads** (`driver.ml`, `exp_of`), locally nameless like the
  rest: `(con W TG E)` and `(match W E ARS)`, where `W` is the group's
  declaration (a list of tags, each a list of slot codes) and `ARS` a list of
  `(arm TG E)` ending in nothing or `(else E)`. An arm body binds its payload as
  `(b 0)`, opened one level deeper than the arms around it; an `else` body binds
  nothing, and is opened at the same level as the scrutinee (see
  `open_arms_wrt_exp_rec` in `Goat_ott.v`).
- **Slot codes** (`GoatDefs.v`, `slot_ty`): `0` is the group itself, `1` to `5`
  are `Int`, `Float`, `Bool`, `Unit`, `String`, and `6 + j` is parameter `j`.
  The parameters are numbered by the order of the `_` slots across the whole
  declaration, left to right, and the printed type lists them in that order. A
  tag with no slots carries `Unit`; one with slots carries the closed record
  `{0: s0, 1: s1, ...}` of them, so `Tag(a, b)` is `(con W TG (rec (l 0 a) (l 1
  b)))` and an arm reads a slot as a projection of its binder.
- **What to skip, with a counted reason**: a group with a slot that is a record,
  a list or a function (the slot codes cannot name them yet); a `match` with a
  literal or list pattern, or destructuring (not calculus forms); a `match` on a
  host event or shape family (open rows in the checker, not groups).
- **The type printer** needs a `Typ_Grp (w, a)` case: print the group by its
  name (the corpus can write the name beside the term, or the driver can number
  groups by first occurrence of `w`) followed by the parameters read off the
  spine `a`, each as `canonical_type` prints it, in order. The checker's
  printer for a group type must agree on the parameter order and on an
  unconstrained parameter: `Empty` has type `List(v0)` on both sides, one free
  variable per parameter the program leaves undecided.
- **Verdicts to compare both ways**: a missing tag, a repeated arm and a tag
  outside the group have no derivation; an `else` with full cover has one. The
  checker's verdict must agree on each.
- **Widening** (#506): an `Int` payload where the declaration says `Float`, and
  an `Int` arm joined with a `Float` arm, are elaborated with `float(e)` the way
  the other join sites are (see "Where `float(e)` goes"); the algorithm has no
  implicit widening.
- **Generators**: a typed generator of groups (declarations with parameters,
  recursive groups such as `List`, and matches that use `else`), run with the
  same three fixed seeds as the others.
