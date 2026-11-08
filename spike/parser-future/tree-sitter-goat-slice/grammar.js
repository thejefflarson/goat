// SPIKE (throwaway): the same grammar slice as rowan-slice / chumsky-slice,
// as a tree-sitter grammar. Tree-sitter generates its own error recovery
// (ERROR / MISSING nodes); there is nothing recovery-specific written here.
module.exports = grammar({
  name: "goat_slice",

  extras: ($) => [/\s/, $.comment],
  word: ($) => $.name,

  rules: {
    source_file: ($) => optional($.expr),

    comment: (_) => token(seq("#", /[^\n]*/)),

    // expr = part (';' part)* ';'?
    expr: ($) =>
      prec.right(seq($._part, repeat(seq(";", $._part)), optional(";"))),

    // part = declaration+ statement? | statement
    _part: ($) =>
      prec.right(choice(seq(repeat1($.declaration), optional($._statement)), $._statement)),

    // declaration = name '=' value ';'?
    declaration: ($) =>
      prec.right(seq($.name, "=", $._statement, optional(";"))),

    _statement: ($) => choice($.operation, $._operand),

    // A flat run `operand (infix operand)*`; precedence is resolved after
    // parsing, as lower.rs does today.
    operation: ($) =>
      prec.left(1, seq($._operand, repeat1(seq($.infix, $._operand)))),

    infix: (_) =>
      choice("+", "-", "*", "//", "/", "%", "==", "!=", "<=", "<", ">=", ">", "and", "or"),

    _operand: ($) => choice($.negation, $._term),

    negation: ($) => prec(3, seq(choice("-", "not"), $._operand)),

    _term: ($) => choice($._primary, $.call, $.access),

    call: ($) =>
      prec(2, seq($._term, "(", optional(seq($.expr, repeat(seq(",", $.expr)), optional(","))), ")")),

    access: ($) => prec(2, seq($._term, ".", $.name)),

    _primary: ($) =>
      choice($.number, $.string, $.boolean, $.name, $.paren, $.match_expr),

    paren: ($) => seq("(", $.expr, ")"),

    // match_expr = 'match' expr 'do' arm* ('else' expr)? 'done'
    match_expr: ($) =>
      seq("match", $.expr, "do", repeat($.arm), optional(seq("else", $.expr)), "done"),

    arm: ($) => seq($.pattern, "then", $.expr),

    pattern: ($) =>
      choice(
        seq($.name, optional(seq("(", optional(seq($.name, repeat(seq(",", $.name)))), ")"))),
        $.number,
        $.string,
        $.boolean,
      ),

    boolean: (_) => choice("true", "false"),
    number: (_) => /\d+(\.\d*)?/,
    string: (_) => /"([^"\\\n]|\\.)*"/,
    name: (_) => /[\p{XID_Start}][\p{XID_Continue}]*/u,
  },
});
