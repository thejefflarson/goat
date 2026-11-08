//! SPIKE (throwaway): the same grammar slice as `rowan-slice`, written with
//! chumsky combinators. Produces an AST (not a lossless CST) and recovers with
//! `recover_with(via_parser(..))`. Not wired into the real compiler.

use chumsky::prelude::*;

pub type Span = SimpleSpan;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Num(String),
    Str(String),
    Bool(bool),
    Name(String),
    Neg(Box<Expr>),
    Not(Box<Expr>),
    Bin(Box<Expr>, String, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Access(Box<Expr>, String),
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<Arm>,
        otherwise: Option<Box<Expr>>,
    },
    /// Placeholder left where recovery skipped over invalid input.
    Error,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub pattern: String,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Let(String, Expr),
    Expr(Expr),
}

const KEYWORDS: [&str; 10] = [
    "match", "do", "done", "then", "else", "not", "and", "or", "true", "false",
];

type Err<'a> = extra::Err<Rich<'a, char>>;

pub fn parser<'a>() -> impl Parser<'a, &'a str, Vec<Item>, Err<'a>> {
    let ident = text::ident()
        .filter(|s: &&str| !KEYWORDS.contains(s))
        .map(str::to_string)
        .padded();
    let kw = |k: &'static str| text::keyword(k).ignored().padded();
    // Succeeds without consuming when the next thing is a binding start
    // (`name =`) or the end: the points where an open construct should close.
    let at_decl = ident.then(just('=').and_is(just("==").not())).rewind();
    let close_point = at_decl.ignored().or(end());

    let expr = recursive(|expr: Recursive<_>| {
        let num = text::int(10)
            .then(just('.').then(text::digits(10)).or_not())
            .to_slice()
            .map(|s: &str| Expr::Num(s.to_string()));
        let string = just('"')
            .ignore_then(none_of('"').repeated().to_slice())
            .then_ignore(just('"'))
            .map(|s: &str| Expr::Str(s.to_string()));
        let boolean = kw("true")
            .to(Expr::Bool(true))
            .or(kw("false").to(Expr::Bool(false)));

        let pattern = ident
            .then(
                ident
                    .separated_by(just(',').padded())
                    .collect::<Vec<_>>()
                    .delimited_by(just('('), just(')'))
                    .or_not(),
            )
            .map(|(head, _)| head)
            .or(num
                .or(string)
                .or(boolean.clone())
                .to_slice()
                .map(str::to_string)
                .padded());
        let body_missing = kw("done").or(kw("else")).rewind().to(Expr::Error);
        let arm = at_decl
            .not()
            .ignore_then(pattern)
            .then_ignore(kw("then").recover_with(via_parser(empty())))
            .then(expr.clone().recover_with(via_parser(body_missing)))
            .map(|(pattern, body)| Arm { pattern, body });

        let matches = kw("match")
            .ignore_then(expr.clone())
            .then_ignore(kw("do"))
            .then(arm.repeated().collect::<Vec<_>>())
            .then(kw("else").ignore_then(expr.clone()).or_not())
            .then_ignore(kw("done").recover_with(via_parser(close_point)))
            .map(|((scrutinee, arms), otherwise)| Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms,
                otherwise: otherwise.map(Box::new),
            });

        let paren = expr
            .clone()
            .delimited_by(just('(').padded(), just(')').padded())
            .recover_with(via_parser(nested_delimiters('(', ')', [], |_| Expr::Error)));

        let atom = choice((
            num.padded(),
            string.padded(),
            boolean,
            matches,
            paren,
            ident.map(Expr::Name),
        ));

        enum Post {
            Call(Vec<Expr>),
            Access(String),
        }
        let call = expr
            .clone()
            .separated_by(just(',').padded())
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just('(').padded(), just(')').padded())
            .map(Post::Call);
        let access = just('.').padded().ignore_then(ident).map(Post::Access);
        let postfix = atom.foldl(call.or(access).repeated(), |e, p| match p {
            Post::Call(args) => Expr::Call(Box::new(e), args),
            Post::Access(name) => Expr::Access(Box::new(e), name),
        });

        let unary = choice((just('-').padded().to(true), kw("not").to(false)))
            .repeated()
            .foldr(postfix, |is_neg, e| {
                if is_neg {
                    Expr::Neg(Box::new(e))
                } else {
                    Expr::Not(Box::new(e))
                }
            });

        let op = choice((
            just("//"),
            just("=="),
            just("!="),
            just("<="),
            just(">="),
            just("+"),
            just("-"),
            just("*"),
            just("/"),
            just("%"),
            just("<"),
            just(">"),
        ))
        .padded()
        .or(kw("and").to("and"))
        .or(kw("or").to("or"))
        .map(str::to_string);

        // Each place an operand can be missing needs its own recovery point;
        // without this one, `x = 1 + ;` loses the whole parse.
        let rhs = unary.clone().recover_with(via_parser(
            choice((just(';'), just(')'), just(',')))
                .padded()
                .ignored()
                .or(end())
                .rewind()
                .to(Expr::Error),
        ));
        unary.clone().foldl(op.then(rhs).repeated(), |l, (op, r)| {
            Expr::Bin(Box::new(l), op, Box::new(r))
        })
    });

    // A value that is missing before `;` or the end becomes `Expr::Error`
    // without consuming, so the rest of the file still parses.
    let missing_value = just(';').padded().ignored().or(end()).rewind();
    let binding = ident
        .then_ignore(just('=').padded())
        .then(
            expr.clone()
                .recover_with(via_parser(missing_value.to(Expr::Error))),
        )
        .then_ignore(just(';').padded().or_not())
        .map(|(name, value)| Item::Let(name, value));

    let item = binding.or(expr
        .map(Item::Expr)
        .then_ignore(just(';').padded().or_not()));
    item.recover_with(skip_then_retry_until(
        any().ignored(),
        just(';').ignored().or(end()),
    ))
    .repeated()
    .collect()
    .then_ignore(end())
}

/// Parse and return the (possibly partial) items and every error found.
pub fn parse_items(src: &str) -> (Vec<Item>, Vec<(Span, String)>) {
    let (out, errs) = parser().parse(src).into_output_errors();
    (
        out.unwrap_or_default(),
        errs.into_iter()
            .map(|e| (*e.span(), e.to_string()))
            .collect(),
    )
}
