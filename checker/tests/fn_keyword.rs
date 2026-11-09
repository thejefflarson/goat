//! `fn`, `function` and `program` introduce the same function literal.

use goat_checker::check;

fn type_of(source: &str) -> Result<String, String> {
    match check(source) {
        Ok(checked) => Ok(checked.typed.root_ty.to_string()),
        Err(errors) => Err(errors[0].message.clone()),
    }
}

fn twice_with(keyword: &str) -> Result<String, String> {
    type_of(&format!(
        "twice = {keyword}(f, x) do f(f(x)) done\ntwice({keyword}(n) do n + 1 done, 1)"
    ))
}

#[test]
fn fn_checks_exactly_like_function_and_program() {
    assert_eq!(twice_with("fn"), Ok("Number".to_string()));
    assert_eq!(twice_with("fn"), twice_with("function"));
    assert_eq!(twice_with("fn"), twice_with("program"));
}

#[test]
fn a_mistake_in_an_fn_body_is_still_reported() {
    assert!(type_of("f = fn(n) do n + true done\nf(1)").is_err());
}

#[test]
fn fn_is_reserved_so_it_cannot_name_anything() {
    assert!(type_of("fn = 1\nfn").is_err());
    assert!(type_of("f = program(fn) do fn done\nf(1)").is_err());
}
