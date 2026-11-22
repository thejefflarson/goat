# ADR 0041 — The formatter is a goat program with one style

- Status: accepted (2026-11-22)
- Builds on: [ADR 0015](0015-host-owned-event-loop-contract.md) and
  [ADR 0020](0020-host-vocabulary.md) (the editor host's vocabulary),
  [ADR 0018](0018-native-first-test-drivers.md) (one Rust suite, thin drivers).
- Context: #539.

## Context

goat had no formatter. The owner decided two things: there is one style and
nothing to configure (as with gofmt), and the formatter is written in goat, like
`editor/highlight.goat`, not in Rust.

goat cannot build strings at run time (`char_at` is the only way to see text;
there is no `+` or `join` on strings), so a goat program cannot return formatted
text. It can return data.

## Decision

1. **The formatter changes whitespace only, and returns edits.** `editor/format.goat`
   is an interactive program over the editor vocabulary. It receives the text on
   an `Edited` event and `draw` returns a list of `Edit({from, to, newlines,
   indent})`: replace the bytes `from..to` (0-based, `to` exclusive, always
   whitespace or empty) with `newlines` line breaks and then `indent` spaces. A
   one-space gap is `newlines: 0, indent: 1`; deleting a gap is `0, 0`. Only gaps
   that differ from the style are listed, so a formatted text yields no edits.
   Hosts apply the edits: the CLI, and the web editor as one CodeMirror
   transaction. The host `goat::format::apply` refuses an edit that is out of
   order, out of range or over a non-whitespace byte, so a wrong program cannot
   change what a program says.
2. **The scanner is copied from `highlight.goat`.** goat programs cannot import
   one another. The copy keeps unrecognized bytes as tokens, and the formatter
   returns no edits for a text that has any. `goat/tests/format.rs` checks the
   formatter's output against `parser::lexer` on every goat file in the repo and
   every string the Rust tests quote: the same tokens, comments included, the
   same parse tree, the same checker result, and a second pass that changes
   nothing. A scanner that drifts from the lexer breaks those tests.
3. **The style is what the formatter does, and the tests enforce it.**
   - Indent is 2 spaces per level. A level is opened by `do`, by `if`, and by an
     opening bracket; each closes at `done` or its bracket. Blocks opened on the
     same line indent their contents once, so `x = program(a) do` and
     `f({` followed by lines indent one level.
   - A line that starts with a closer (`done`, `)`, `]`, `}`) takes the indent
     of the line that opened the block.
   - `match` arms and the `else` arm share the indent of the first arm. A `then`
     or `else` that ends a line indents the lines that follow, once.
   - An `if` whose `then` is on the `if` line puts `else` (and `else if`) at the
     indent of that line. An `if` whose head runs on to several lines indents its
     `then` and `else` one level.
   - An `else if` chain adds no level per link; each link still needs its `done`.
   - A line that continues an expression (it starts with, or the line before it
     ends with, a binary operator, `and`, `or`, `=` or `|`) is indented one more
     level.
   - One space between tokens; none after `(`, `[`, `{`, before `)`, `]`, `}`,
     `,`, `;` and `:`, around `.`, and between a name and its `(`; one after `,`,
     `;` and `:`; one around every binary operator and `=`. A `-` that is a sign
     keeps its number. `::` and a `.` beside a number are left as written, since
     removing the gap could change what the lexer reads.
   - Blank lines: at most one, none just after `do` or an opening bracket, none
     just before a closer, none at the start of the text. The text ends in one
     line break; `\r\n` becomes `\n`; trailing whitespace goes.
   - Comments are kept as written. A comment on its own line is indented like
     the line after the previous token; a trailing comment keeps the spaces
     before it when they are spaces, or becomes one space.
4. **Long records and lists break; nothing else does.** A record `{...}` or
   list `[...]` literal whose one-line form would end past column 80 is laid out
   one field or item per line: `{` stays on its line, each item sits on its own
   line two spaces past the line that holds `{`, each `,` stays at the end of its
   line, and `}` (or `]`) takes its own line at the indent of the line that holds
   the opener. The grammar allows a trailing comma, but adding one would not be a
   whitespace edit, so the last item gets none (one the author wrote stays).
   - Width is counted in characters (a byte that is not a UTF-8 continuation
     byte), from the start of the line, indent included, to the closing bracket.
   - A broken record is checked again field by field: an inner record that fits
     stays on one line, and one that does not breaks in turn.
   - A record or list the author already wrote across lines, or with a comment
     inside, stays broken, and is laid out one item to a line. The formatter
     never joins lines, so a deliberate layout survives and a second pass changes
     nothing.
   - Call arguments, parameter lists and everything else are never broken, and
     there is no other line-width rule: a long call stays on its line.
5. **Hosts.** `goat fmt FILE...` rewrites each file in place; `goat fmt --check
   FILE...` changes nothing and fails if any file is not formatted. The web editor
   has a Format command and a shortcut. The Apple editor is a follow-up.
6. **The repo is formatted.** Every `.goat` file in the repo is a fixed point of
   the formatter, and the corpus test fails when one is not.

## Consequences

- The style is changed by editing `editor/format.goat`; the corpus test then
  shows which repo files move.
- The editor vocabulary gains an `Edit` shape and a `scene.edit` host call, which
  hosts without text ignore.
- Two goat programs carry a copy of the scanner until goat can share code.
