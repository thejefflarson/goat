# goat for language models

goat is a new language, so a model has never seen it in training. This file is
the whole language as it runs **today** — paste it into context before asking a
model to read or write goat. It describes what actually compiles and runs on the
current build, and marks clearly what is not usable, so a model does not
generate code the compiler rejects.

If a feature is under "Not yet", the compiler will reject it with a clear error.
Prefer the forms under "What runs today".

A test (`cli/tests/llm_doc.rs`) type-checks every ```` ```goat ```` block in this
file, and checks that every ```` ```goat error ```` block is rejected, so the
examples cannot drift from the compiler. Plain ```` ``` ```` blocks are fragments
and are not checked.

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
when it is a number or a boolean. (A record, list or function result prints
nothing yet — end a program on a number or boolean, or call `print`, to see
output.)

## What runs today

### Numbers, booleans, operators

```goat
print(1 + 2 * 3);   # 7   — usual precedence, left-associative
print(10 / 4)       # 2.5 — numbers are floating point
```

```goat
n = 4
print(-n);          # -4
print(1 < 2)        # true — comparisons: <  <=  >  >=  give a boolean
```

Arithmetic is `+ - * /`. `true` and `false` are booleans. `print` shows any
value and returns it.

Whole numbers have their own type, `Int`. `a // b` divides and rounds down,
`a % b` is the remainder (it takes the sign of `b`), and `round`, `floor`,
`ceil` and `truncate` turn a decimal into an `Int`. `sqrt` takes a number;
`sin`, `cos` and `tan` take degrees.

```goat
print(17 // 5);              # 3
print(17 % 5);               # 2
print(round(2.5));           # 3
print(sqrt(16))              # 4
```

### Bindings: `name = value`

A binding names a value, then the rest of the program follows. Bindings are
expressions; the last expression is the result.

```goat
x = 10
y = x + 5
y                # 15
```

Value bindings are **sequential and shadow**: a later binding of the same name
replaces the earlier one for the code after it.

```goat
score = 1
score = score + 1   # the right-hand `score` is the old 1
score               # 2
```

### Sequencing: `a; b`

`a; b` runs `a`, drops its value, then runs `b`; it is `b`'s value. A trailing
`print(1);` is `Unit`. Bindings scope over the statements after them.

```goat
print(1); print(2); 3     # prints 1, 2; value 3
```

A statement ends only at `;`: `print(1) (2)` is a call of `print(1)` and
`print(1) -2` is a subtraction, so write `print(1); (2)`. A loop or a bare call
that is not the last thing in a block needs the `;`.

### Booleans and equality: `and`, `or`, `not`, `==`, `!=`

```goat
x = 7
print(x > 1 and x < 10 or x == 100);
print(not x == 8);
print(x != 3)
```

`==` and `!=` compare numbers, strings, booleans, records, tags and lists —
anything with no function inside. `and`/`or` skip the right side when the left
decides. Loosest first: `or`, `and`, `not`, `==`, comparisons, `+ -`, `* /` — so
`not a == b` is `not (a == b)`.

### Loops

```goat
repeat 3 times do print("hi") done;
for i from 1 to 5 do print(i * i) done;      # 1 to 5, both included
for x in [3, 1, 2] do print(x) done;
```

A loop is a `Unit` expression; the body's value is dropped. The counter is a
`Number`. `for` counts up only (`from 5 to 1` runs zero times). `from`, `to` and
`in` are words only in a `for` header; `for`, `and`, `or`, `not` are reserved.

### Conditionals: `if … then … else … done`

```goat
n = 5
if n < 2 then n else n - 1 done
```

`then` and `else` branches must have the same type. The whole `if` is an
expression. (An `if` with no `else` is allowed only when the `then` branch has
the unit type — rare today; prefer the full form.)

### Functions: `program(params) do body done` (or `function(...)`)

`program` and `function` are the same keyword — two spellings of one thing. Use
whichever reads better; `program` is the kid-facing default.

```goat
double = program(n) do n * 2 done
double(21)       # 42
```

```goat
fib = function(n) do
  if n < 2 then n
  else fib(n - 1) + fib(n - 2)
  done
done
fib(10)          # 55
```

A function's value is its body; there is no `return`.

Functions are **first-class values**: pass them as arguments, return them, store
them in record fields.

```goat
double = program(n) do n * 2 done
apply = program(f, x) do f(x) done
apply(double, 21)   # 42
```

Functions defined together in a scope are **mutually recursive** — order does
not matter; each can call the others and itself.

### Closures

A function can use a variable from the scope around it; it captures the value
when the function is made.

```goat
make_adder = program(a) do program(b) do a + b done done
add_ten = make_adder(10)
add_ten(5)       # 15
```

### Records: `{field: value, …}` and `record.field`

```goat
origin = {x: 0, y: 0}
spot = {x: 3, y: 4, z: 5}
spot.x           # 3
```

Field access is **row-polymorphic**: a function that reads `.x` and `.y` works
on any record that has at least those fields, whatever else it carries.

```goat
origin = {x: 0, y: 0}
spot = {x: 3, y: 4, z: 5}
add_up = program(p) do p.x + p.y done
add_up(origin) + add_up(spot)   # 0 + 7 = 7
```

Records nest, and field access chains: `{point: {x: 1}}.point.x` is `1`.

`+ - * /` work on records of numbers field by field. `{...p, x: 3}` copies `p`
with `x` replaced, and `{a, b} = p` or `program({a, b})` takes a record apart by
field name (`...rest` keeps whatever is left).

```goat
step = {x: 1, y: 2} + {x: 10, y: 20}
moved = {...step, x: 0}
distance_squared = program({x, y}) do x * x + y * y done
distance_squared(moved)   # 0 + 22 * 22 = 484
```

A spread **updates** a field `p` has and **extends** `p` with one it lacks, so a
misspelled name adds a field instead of changing one. It never changes a
field's type: `{...p, x: "hi"}` is an error when `x` is a number.

```goat
ball = {x: 1, y: 2}
moved = {...ball, x: 5}          # update: x is 5
tagged = {...ball, color: "red"} # extend: a new field
oops = {...ball, z: 5}           # a typo for x adds z; x is still 1
moved.x + tagged.y + oops.x
```

```goat error
ball = {x: 1, y: 2}
{...ball, x: "hi"}
```

### Methods: `self`, `.` and `::`

A function written inside a record can take `self` as its first parameter. That
makes it a *method*, and the record is handed to it as `self`.

`ball.moved()` calls `moved` and hands it `ball` as `self`. A method gives back
something new, and `ball` itself doesn't change, so keep the result:
`ball2 = ball.moved()`. Methods chain, and the receiver can be a parameter.

```goat
ball = {
  x: 1,
  moved: program(self) do {...self, x: self.x + 1} done,
  at: program(self, x) do {...self, x: x} done
}
ball2 = ball.moved()
step = program(b) do b.moved().x done
ball2.x + ball.moved().moved().x + step(ball)   # 2 + 3 + 2 = 7
```

A record can't hold its own constructor, because that would make the record
refer to itself and goat values are acyclic. To make another one, use any of:

- a prototype copy, `{...ball, x: 5}`, which has exactly `ball`'s type, so it
  goes in the same list;
- a method that returns a modified copy, like `at` above: `ball.at(5)`;
- a top-level function, `make_ball(5)`.

```goat
ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
make_ball = program(x) do {x: x, moved: program(self) do {...self, x: self.x + 1} done} done
balls = [ball, {...ball, x: 5}, make_ball(9)]
sum(change_each(balls, program(b) do b.moved().x done))   # 2 + 6 + 10 = 18
```

`::` takes a function out of a record without handing it the record. Use it for
plain functions, the ones without `self`: `tools::double(5)`. `.` means "record,
do this", and `::` means "borrow the record's tool".

```goat
math = {
  double: program(n) do n * 2 done,
  clamp: program(x, low, high) do
    if x < low then low else if x > high then high else x done done
  done
}
math::clamp(math::double(7), 0, 10)   # 10
```

The two do not mix. `.` on a function without `self` is an error, and so is `::`
on a method (`ball::moved()`; write `ball.moved()`).

```goat error
tools = {double: program(n) do n * 2 done}
tools.double(5)
```

The checker says: "`double` has no `self`, so `tools.double(5)` can't hand it
`tools`. Call it with `tools::double(5)`. If `double` is meant to work on
`tools`, make it a method by writing `self` first: `program(self, n)`." For the
other direction it says: "`moved` has `self`, so call it with a dot:
`ball.moved()`. `::` is for functions without `self`, like `math::double(5)`."

```goat error
ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
ball::moved()
```

Two other mistakes have their own messages. `self` only works in a function
written right inside a record, and it has to be the first parameter. Records in
one list must agree on which fields are methods: "`f` is a method in one record
and a plain function in the other, so they don't have the same shape. Start both
with `self`, or neither."

```goat error
add = program(self, n) do n done
1
```

### Tags and `match`

A tag is declared with `tag` and builds a variant when it is called with a
payload. `match` takes a value apart by its tag. A `match` over numbers or
strings needs an `else`, since they can never be exhausted.

```goat
tag Circle
tag Square

area = program(shape) do
  match shape do
    Circle(r) then 3 * r * r
    Square(side) then side * side
  done
done

print(area(Circle(2)));
print(area(Square(3)));
match 5 do
  0 then "zero"
  else "other"
done
```

A grouped declaration closes its tags into one type, so a `match` must handle
every tag and needs no `else`. A group that names itself can hold itself in a
payload.

```goat
tag Light = Red | Green | Amber
tag Tree = Leaf | Node({left: Tree, right: Tree})

seconds = program(light) do
  match light do
    Red then 30
    Green then 25
    Amber then 5
  done
done

size = program(tree) do
  match tree do
    Leaf then 0
    Node(n) then 1 + size(n.left) + size(n.right)
  done
done

print(seconds(Green));
print(size(Node({left: Leaf, right: Leaf})))
```

### Lists

`[1, 2, 3]` is a list; `[]` is the empty list. A list pattern takes one apart.

```goat
sum_all = program(xs) do
  match xs do
    [] then 0
    [first, ...rest] then first + sum_all(rest)
  done
done
sum_all([1, 2, 3, 4])    # 10
```

Lists come with a toolbox, no setup needed: `length`, `first`, `rest`, `item`
(counts from 1), `add`, `join`, `reverse`, `sort`, `sum`, `biggest`, `smallest`,
`has`, `each`, `change_each`, `keep` and `count`.

```goat
scores = [7, 1, 9, 4]
big = program(n) do n > 3 done
double = program(n) do n * 2 done
print(sort(scores));                          # [1, 4, 7, 9]
print(change_each(keep(scores, big), double)); # [14, 18, 8]
print(item(scores, 2));                       # 1
print(join(scores, [5, 6]));                  # [7, 1, 9, 4, 5, 6]
print(has(scores, 4));                        # true
sum(scores)                                   # 21
```

### Comparing and sorting: `<`, `<=`, `>`, `>=`

`<`, `<=`, `>` and `>=` order any two values of the same type, as long as the
type holds no function. The rules, by kind of value:

- **Numbers** compare by value, and an `Int` compares with a `Float`.
- **Strings** compare in dictionary order by Unicode code point, so a shorter
  prefix is smaller: `"app" < "apple" < "apply"`. Capitals come before
  lowercase letters.
- **Bools**: `false < true`.
- **Tags** go in declaration order, leftmost lowest. `tag Level = Low | Medium
  | High` gives `Low < Medium < High`. Two values of the same tag compare by
  payload: `Hit(1) < Hit(2)`.
- **Lists** compare element by element from the left. The first difference
  decides, and a list that runs out first is smaller: `[1, 2] < [1, 3]`,
  `[1, 9] < [2]`, `[1, 2] < [1, 2, 0]`, `[] < [1]`.
- **Records** compare field by field in label order, which is alphabetical,
  not the order written, because `{x, y}` and `{y, x}` are the same type. The
  first unequal field decides. To rank by another field first, compare a list
  or a tag payload instead.
- **Functions** can't be compared; it is an error.

```goat
tag Level = Low | Medium | High
tag Shot = Miss | Hit(Int)
a = "app" < "apple"                  # true
b = false < true                     # true
c = Low < High                       # true
d = Hit(1) < Hit(2)                  # true
e = [1, 9] < [2]                     # true: 1 < 2 decides
f = [1, 2] < [1, 2, 0]               # true: the shorter list runs out first
g = {name: "Zed", age: 3} < {name: "Amy", age: 9}   # true: age is compared before name
h = [[2, "b"], [1, "z"], [2, "a"]]
sort(h)                              # [[1, "z"], [2, "a"], [2, "b"]]
```

`sort`, `biggest`, `smallest` and `insert_sorted` use the same order, so they
work on strings, records and lists too: `sort(["pear", "apple", "fig"])`.

```goat error
f = program(n) do n done
f < f
```

The checker says: "can't compare functions with `<`". Details are in
`docs/adr/0036-structural-ordering.md`; `examples/ordering.goat` walks through
every rule.

### Turtle drawing

`forward`, `back`, `left`, `right` take a number (degrees for turns), `pen_up`
and `pen_down` take nothing, and `color` takes a name or a `"#rrggbb"` code. The
turtle starts in the middle facing up. `goat run` needs `-o FILE.svg` to save
the drawing.

```goat
color("purple");
for side from 1 to 60 do
  forward(side * 3);
  right(89)
done
```

### Interactive programs: `init`, `update`, `draw`

A program that defines `init`, `update` and `draw` is run by its host, not once
through. The host calls `update(model, event)` for each event, which returns the
new model, and `draw(model)`, which returns a list of shapes. Only the events
`update` names are sent. See `examples/interactive.goat`, `examples/shapes.goat`
and `examples/canvas/` for the events and shapes each host knows.

```goat
init = {ticks: 0}

update = program(model, event) do
  match event do
    Tick(dt) then {...model, ticks: model.ticks + 1}
    else model
  done
done

draw = program(model) do
  [Line({x1: 0, y1: 0, x2: model.ticks, y2: 10, color: "red"})]
done
```

### Reading a string: `byte_length` and `byte_at`

A string is UTF-8, and these two builtins count **bytes**, not characters.

```goat
print(byte_length("goat"));     # 4
print(byte_length("é"));        # 2: one character, two bytes
print(byte_at("goat", 1))       # 103, the byte for "g"
```

`byte_at(s, i)` counts from 1, like `item(xs, 1)`, and gives an `Int` from 0 to
255. A position below 1 or past `byte_length(s)` stops the program with a
trap pointing at the call. Neither builtin allocates. See
`examples/vowels.goat`.

### Reading a string by character: `char_count` and `char_at`

These two count Unicode **code points**, which is not always what you see as
one character.

```goat
print(char_count("goat"));       # 4
print(char_count("é"));          # 1 (byte_length says 2)
print(char_count("日本"));        # 2
print(char_at("goat", 1));       # "g", a new one-character String
print(char_at("日本", 2));        # "本"
print(char_at("goat", 1) == "g") # true
```

`char_at(s, i)` counts from 1, like `item(xs, 1)`. A position below 1 or past
`char_count(s)` stops the program with a trap pointing at the call. Both read
the whole string up to the position, so use them for short words, not in a hot
loop over a long text.

Some emoji and accented letters are several code points: a thumbs-up with a skin
tone (`"👍🏽"`) is 2, and a family emoji joined with zero-width joiners is 5.
`char_count` says 2 and 5, and `char_at` hands back the pieces. Grapheme
clusters (what a reader sees as one character) are not supported. `char_count`
does not allocate; `char_at` allocates the new string, which the program frees
when it is no longer used. See `examples/letters.goat`.

### Comments

```goat
# everything after a # to the end of the line is a comment
1
```

## Types, in brief

Types are fully inferred; you never annotate. The inferencer is Hindley-Milner
with row-polymorphic records. A binding made with `=` whose value is a function,
a literal, a name, or a record or spread (`{...r, k: v}`) of such values is generalized, so a generic
function bound with `=` can be used at several types. A *computed* binding (a
call, a `match`, an `if`, a field access) has one type; use it at two types and
the checker suggests writing it as a function so it re-specializes per use:

```goat
id = program(x) do x done
print(id(1));            # OK
print(id(true))          # OK — id is generic
```

One sharp edge to know (standard HM): a function **passed as a parameter** is
monomorphic inside the body — it cannot be used at two different types there.

```goat error
both = program(f) do a = f(1)  f(true) done   # ERROR: Number vs Bool
1
```

Bind the generic function with `=` and call it directly, or pass it once per
type, instead.

## Not yet (the compiler will reject these)

Do not generate these; each one fails on the current build.

- **Building strings.** A string literal can be printed, compared with `==`,
  and read with `byte_length`, `byte_at`, `char_count` and `char_at`.
  `char_at` is the only way to make a new string at run time; `+` and `join`
  do not work on strings.

```goat error
greeting = "hello, " + "goat"
print(greeting)
```

- **`::` as a namespace.** `::` only takes a function out of a record you
  have: no `math::sqrt` from a module, no `Shape::Circle`.

```goat error
tools = {double: program(n) do n * 2 done}
math::double(5)
```

- **Assigning a field.** Fields are never assigned; `self.x = 5` doesn't exist.
  Write `{...self, x: 5}` and keep the result.
- **Methods on strings or lists.** `"hi".length()` and `[1, 2].sum()` don't
  exist; call `length("hi")` or `sum([1, 2])`.
- **`return`.** A reserved word with no syntax; a function's value is its body.

```goat error
f = program(n) do return n done
f(1)
```

- **Named types** (`type Point = {x: Number}`). Only `tag` declares a type.

```goat error
type Point = {x: Number}
1
```

- **Type annotations of any kind.** goat will not get them.

## Complete worked examples

Each of these runs today with `goat run`.

```goat
# Recursion — the tenth Fibonacci number. Prints 55.
fib = program(n) do
  if n < 2 then n
  else fib(n - 1) + fib(n - 2)
  done
done
fib(10)
```

```goat
# Functions as values. Prints 42.
apply = program(f, x) do f(x) done
double = function(n) do n * 2 done
apply(double, 21)
```

```goat
# Records and row-polymorphic field access. Prints 7.
origin = {x: 0, y: 0}
spot = {x: 3, y: 4, z: 5}
add_up = program(p) do p.x + p.y done
add_up(origin) + add_up(spot)
```

```goat
# A closure and a list. Prints 6.
scale = program(k) do program(n) do n * k done done
triple = scale(3)
sum(change_each([1, 2, 3], triple)) / 3
```

## Changing the editor's colours

The web editor's syntax colours are a goat program, `editor/theme.goat`. Press
"Edit editor theme" to open it in the editor, change a colour in a line like
`Swatch({role: "keyword", light: "#4a2fb8", dark: "#b4a3ff"})`, and press "Save
theme" (or leave Live on and just type): the editor re-colours at once, with no
reload. The roles are `keyword`, `literal`, `number`, `string`, `comment` and
`tag`; `light` is the colour on a light page and `dark` on a dark one. A colour
is a basic name like `"purple"` or a code like `"#4a2fb8"`. Anything else is
ignored and that colour keeps its default.

The editor refuses a colour that is hard to read (under 4.5:1 contrast on the
editor's background or selection) and says which one. A theme with a mistake
keeps the last good colours. Your theme is remembered in this browser; "Reset
theme" brings the default back. goat only says which colours; the page decides
how to paint them.

## Checklist before handing goat back

- The program ends on a **number or boolean** expression (so it prints), or
  calls `print`.
- Repeat with `repeat`, `for` or recursion; there is no `while`.
- Take a variant or list apart with `match`; a `match` over numbers or strings
  needs an `else`.
- Compare with `==` and `!=`; combine with `and`, `or`, `not`.
- No string concatenation, no `return`, no named types.
- Call a method with `.` (`ball.moved()`) and a plain function from a record
  with `::` (`tools::double(5)`); never `ball::moved()` or `tools.double(5)`.
- Keep the result of a method: `ball2 = ball.moved()`. A method never changes
  `ball`.
- No field assignment, no `::` namespaces, no methods on strings or lists.
- No type annotations anywhere.
