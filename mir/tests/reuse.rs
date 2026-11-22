//! A record's cell is written in place when nothing else holds it: derived
//! record arithmetic reuses an unshared operand, and a record read only
//! through its fields is released as soon as they are loaded, so the fields it
//! held are unshared too. These count allocations (the interpreter's, which
//! the wasm backend matches) and check where the release lands.

use goat_mir::*;

/// Records built from constants alone are shared immortal cells, which are
/// never overwritten; these tests build theirs through a call.
const MK: &str = "mk = program(x, y) do {x: x, y: y} done\n";

fn lower(src: &str) -> Program {
    let p = mono(&goat_checker::check(src).expect("checks")).expect("lowers");
    assert_eq!(verify(&p), Ok(()), "{src}");
    p
}

fn outcome(src: &str) -> Outcome {
    let out = run(&lower(src)).expect("runs");
    assert_eq!(out.live_allocations, 0, "{src}");
    out
}

#[test]
fn a_sum_of_unshared_records_is_written_into_the_first() {
    let out = outcome(&format!(
        "{MK}a = mk(1.0, 2.0)\nb = mk(3.0, 4.0)\nc = a + b\nc.x + c.y"
    ));
    assert_eq!(out.value, Value::Float(10.0));
    assert_eq!(out.allocations, 2);
}

#[test]
fn a_shared_operand_gets_a_fresh_result_and_is_not_written_into() {
    let src = format!("{MK}a = mk(1.0, 2.0)\nb = mk(3.0, 4.0)\nc = a + b\nd = a + b\n");
    // `c` has to be fresh because `a` is needed again; `d` is the last use.
    let out = outcome(&format!("{src}c.x + c.y + d.x + d.y"));
    assert_eq!(out.value, Value::Float(20.0));
    assert_eq!(out.allocations, 3);
}

#[test]
fn a_record_added_to_itself_is_not_unshared() {
    let out = outcome(&format!("{MK}a = mk(1.0, 2.0)\nb = a + a\nb.x + a.x"));
    assert_eq!(out.value, Value::Float(3.0));
    assert_eq!(out.allocations, 2);
}

#[test]
fn a_nested_sum_reuses_the_outer_record_and_leaves_a_shared_inner_one() {
    let src = format!(
        "{MK}inner = mk(1.0, 2.0)\n\
         a = {{p: inner, n: 1.0}}\n\
         b = {{p: mk(10.0, 20.0), n: 2.0}}\n\
         c = a + b\n\
         c.p.x + inner.x + a.n"
    );
    let out = outcome(&src);
    assert_eq!(out.value, Value::Float(13.0));
}

#[test]
fn a_function_sums_fields_read_out_of_a_record_it_owns_in_place() {
    let src = format!(
        "{MK}f = program(q) do q.p + q.v done\n\
         r = f({{p: mk(1.0, 2.0), v: mk(3.0, 4.0)}})\n\
         r.x + r.y"
    );
    let p = lower(&src);
    let out = run(&p).expect("runs");
    assert_eq!(out.value, Value::Float(10.0));
    // Three literals; the sum lands in `p`'s cell, which only the loads share
    // until the record is released.
    assert_eq!(out.allocations, 3);

    let calls = |f: &Func| {
        let mut n = 0;
        f.body
            .for_each_node(&mut |e| n += usize::from(matches!(e, Expr::CallDirect(..))));
        n
    };
    let f = p
        .funcs
        .iter()
        .find(|f| f.params.len() == 1 && calls(f) == 1)
        .expect("the step function");
    let (mut drop_at, mut call_at, mut at) = (None, None, 0);
    f.body.for_each_node(&mut |e| {
        match e {
            Expr::Drop(_) => drop_at = drop_at.or(Some(at)),
            Expr::CallDirect(..) => call_at = call_at.or(Some(at)),
            _ => {}
        }
        at += 1;
    });
    assert!(
        drop_at < call_at,
        "the record is released before the sum: {f:#?}"
    );
}

const SPAWN: &str = "spawn = program(i, acc) do
  if i == 0 then acc else
    spawn(i - 1, link({p: {x: i * 0.4, y: i * 0.3}, v: {x: 1.5 - i * 0.003, y: 0.7 + i * 0.002}}, acc))
  done
done
step = program(q) do
  p = q.p + q.v
  v = q.v * {x: 0.999, y: 0.999}
  {p: p, v: {x: v.x, y: v.y}}
done
";

/// Allocations `change_each(ps, step)` makes per particle: the benchmark's
/// update step. Each particle costs a new velocity, a new particle and two list
/// cells. The `+` and `*` results come from the particle's own records, and the
/// damping literal is one shared cell.
#[test]
fn a_particle_step_allocates_four_records_not_seven() {
    const N: usize = 50;
    let allocations =
        |body: &str| outcome(&format!("{SPAWN}ps = spawn({N}, [])\n{body}")).allocations;
    let per_particle = (allocations("change_each(ps, step)") - allocations("ps")) as f64 / N as f64;
    assert!((4.0..4.5).contains(&per_particle), "{per_particle}");
}

const LOOP: &str = "loop = program(i, acc) do
  if i == 0 then acc else loop(i - 1, acc + BODY) done
done
";

fn loop_allocations(body: &str) -> usize {
    let src = format!("{}loop(100, 0.0)", LOOP.replace("BODY", body));
    outcome(&src).allocations
}

#[test]
fn a_record_of_constants_is_built_once_however_often_it_is_evaluated() {
    assert_eq!(loop_allocations("{x: 1.0, y: 2.0}.x"), 0);
}

#[test]
fn a_record_with_a_computed_field_is_built_each_time() {
    assert_eq!(loop_allocations("{x: i * 1.0, y: 2.0}.x"), 100);
}

#[test]
fn a_constant_record_is_never_written_into() {
    let src = "f = program(i) do
  c = {x: 1.0, y: 2.0} + {x: 3.0, y: 4.0}
  s = {...{x: 1.0, y: 2.0}, x: 9.0}
  c.x + s.x + s.y
done
f(0) + f(1)";
    assert_eq!(outcome(src).value, Value::Float(2.0 * (4.0 + 9.0 + 2.0)));
}
