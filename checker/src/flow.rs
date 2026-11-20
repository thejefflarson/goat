//! The pure core of numeric widening (ADR 0040): given the flows `producer =>
//! slot` recorded at a binding's scalar join sites, decide what each variable
//! is. It knows nothing of types beyond `Int < Float`, so it is tested alone.

use std::collections::HashMap;

use crate::ty::TypeVar;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scalar {
    Int,
    Float,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum End {
    Fixed(Scalar),
    Var(TypeVar),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edge {
    pub producer: End,
    pub slot: End,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Solution {
    /// The scalar each decided variable takes.
    pub bound: Vec<(TypeVar, Scalar)>,
    /// Variables no concrete end reaches, grouped: each group is one type.
    pub joined: Vec<Vec<TypeVar>>,
    /// Indices of the edges that carry a `Float` into an `Int`.
    pub narrowed: Vec<usize>,
}

enum Node {
    Fixed(Scalar),
    Var(usize),
}

pub fn solve(edges: &[Edge]) -> Solution {
    let mut index: HashMap<TypeVar, usize> = HashMap::new();
    let mut vars: Vec<TypeVar> = Vec::new();
    let mut node = |end: End| match end {
        End::Fixed(s) => Node::Fixed(s),
        End::Var(v) => Node::Var(*index.entry(v).or_insert_with(|| {
            vars.push(v);
            vars.len() - 1
        })),
    };
    let nodes: Vec<(Node, Node)> = edges
        .iter()
        .map(|e| (node(e.producer), node(e.slot)))
        .collect();
    let n = vars.len();
    let mut out: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut into: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, (p, s)) in nodes.iter().enumerate() {
        if let Node::Var(p) = p {
            out[*p].push(i);
        }
        if let Node::Var(s) = s {
            into[*s].push(i);
        }
    }

    let determined = reached_from_fixed(&nodes, &out, n);
    let mut value: Vec<Option<Scalar>> = vec![None; n];
    let mut queue: Vec<usize> = Vec::new();
    fn raise(value: &mut [Option<Scalar>], queue: &mut Vec<usize>, v: usize, to: Scalar) {
        if value[v] < Some(to) {
            value[v] = Some(to);
            queue.push(v);
        }
    }
    for (p, s) in &nodes {
        match (p, s) {
            (Node::Fixed(c), Node::Var(s)) => raise(&mut value, &mut queue, *s, *c),
            (Node::Var(p), Node::Fixed(c)) if !determined[*p] => {
                raise(&mut value, &mut queue, *p, *c)
            }
            _ => {}
        }
    }
    while let Some(v) = queue.pop() {
        let here = value[v].expect("a queued variable has a value");
        for &i in &out[v] {
            if let Node::Var(s) = nodes[i].1 {
                raise(&mut value, &mut queue, s, here);
            }
        }
        for &i in &into[v] {
            if let Node::Var(p) = nodes[i].0
                && !determined[p]
            {
                raise(&mut value, &mut queue, p, here);
            }
        }
    }

    let of = |n: &Node| match n {
        Node::Fixed(s) => Some(*s),
        Node::Var(v) => value[*v],
    };
    let narrowed = nodes
        .iter()
        .enumerate()
        .filter(|(_, (p, s))| of(p) == Some(Scalar::Float) && of(s) == Some(Scalar::Int))
        .map(|(i, _)| i)
        .collect();
    let bound = (0..n).filter_map(|v| Some((vars[v], value[v]?))).collect();
    Solution {
        bound,
        joined: undecided_groups(&nodes, &value, &vars),
        narrowed,
    }
}

/// The variables a fixed end reaches by following edges forward.
fn reached_from_fixed(nodes: &[(Node, Node)], out: &[Vec<usize>], n: usize) -> Vec<bool> {
    let mut reached = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    for (p, s) in nodes {
        if let (Node::Fixed(_), Node::Var(s)) = (p, s)
            && !std::mem::replace(&mut reached[*s], true)
        {
            stack.push(*s);
        }
    }
    while let Some(v) = stack.pop() {
        for &i in &out[v] {
            if let Node::Var(s) = nodes[i].1
                && !std::mem::replace(&mut reached[s], true)
            {
                stack.push(s);
            }
        }
    }
    reached
}

/// The connected groups, of two or more, among variables nothing decided.
fn undecided_groups(
    nodes: &[(Node, Node)],
    value: &[Option<Scalar>],
    vars: &[TypeVar],
) -> Vec<Vec<TypeVar>> {
    let mut parent: Vec<usize> = (0..vars.len()).collect();
    fn find(parent: &mut [usize], v: usize) -> usize {
        let mut root = v;
        while parent[root] != root {
            root = parent[root];
        }
        let mut at = v;
        while parent[at] != root {
            at = std::mem::replace(&mut parent[at], root);
        }
        root
    }
    for (p, s) in nodes {
        if let (Node::Var(p), Node::Var(s)) = (p, s)
            && value[*p].is_none()
            && value[*s].is_none()
        {
            let (a, b) = (find(&mut parent, *p), find(&mut parent, *s));
            parent[a] = b;
        }
    }
    let mut groups: HashMap<usize, Vec<TypeVar>> = HashMap::new();
    for v in (0..vars.len()).filter(|v| value[*v].is_none()) {
        groups
            .entry(find(&mut parent, v))
            .or_default()
            .push(vars[v]);
    }
    let mut groups: Vec<Vec<TypeVar>> = groups.into_values().filter(|g| g.len() > 1).collect();
    groups.iter_mut().for_each(|g| g.sort_unstable());
    groups.sort();
    groups
}

#[cfg(test)]
mod tests {
    use super::*;
    use End::{Fixed, Var};
    use Scalar::{Float, Int};

    fn flow(producer: End, slot: End) -> Edge {
        Edge { producer, slot }
    }

    fn bound(solution: &Solution, var: TypeVar) -> Option<Scalar> {
        solution
            .bound
            .iter()
            .find(|(v, _)| *v == var)
            .map(|(_, s)| *s)
    }

    #[test]
    fn a_slot_takes_the_join_of_its_producers() {
        let solution = solve(&[flow(Fixed(Int), Var(0)), flow(Fixed(Float), Var(0))]);
        assert_eq!(bound(&solution, 0), Some(Float));
        assert!(solution.narrowed.is_empty());
    }

    #[test]
    fn the_answer_does_not_depend_on_the_order_of_the_flows() {
        let edges = [
            flow(Var(1), Var(0)),
            flow(Fixed(Float), Var(1)),
            flow(Fixed(Int), Var(0)),
            flow(Var(0), Var(2)),
        ];
        let mut reversed = edges;
        reversed.reverse();
        let (a, b) = (solve(&edges), solve(&reversed));
        for var in 0..3 {
            assert_eq!(bound(&a, var), Some(Float));
            assert_eq!(bound(&b, var), Some(Float));
        }
    }

    #[test]
    fn a_free_producer_takes_what_its_slot_is() {
        let solution = solve(&[flow(Var(0), Fixed(Float))]);
        assert_eq!(bound(&solution, 0), Some(Float));
        let solution = solve(&[flow(Var(0), Fixed(Int)), flow(Fixed(Int), Fixed(Int))]);
        assert_eq!(bound(&solution, 0), Some(Int));
    }

    #[test]
    fn a_free_producer_beside_an_int_and_a_float_is_a_float() {
        let solution = solve(&[
            flow(Fixed(Int), Var(1)),
            flow(Var(0), Var(1)),
            flow(Var(0), Var(2)),
            flow(Fixed(Float), Var(2)),
        ]);
        assert_eq!(bound(&solution, 0), Some(Float));
        assert_eq!(bound(&solution, 1), Some(Float));
    }

    #[test]
    fn an_int_slot_stays_an_int_when_only_its_own_producers_say_so() {
        let solution = solve(&[
            flow(Fixed(Int), Var(0)),
            flow(Fixed(Int), Var(0)),
            flow(Var(0), Var(1)),
            flow(Fixed(Float), Var(1)),
        ]);
        assert_eq!(bound(&solution, 0), Some(Int));
        assert_eq!(bound(&solution, 1), Some(Float));
        assert!(solution.narrowed.is_empty());
    }

    #[test]
    fn free_variables_with_no_concrete_end_are_joined() {
        let solution = solve(&[
            flow(Var(0), Var(2)),
            flow(Var(1), Var(2)),
            flow(Var(5), Var(6)),
        ]);
        assert!(solution.bound.is_empty());
        assert_eq!(solution.joined, vec![vec![0, 1, 2], vec![5, 6]]);
    }

    #[test]
    fn a_float_into_an_int_is_narrowing() {
        let solution = solve(&[flow(Fixed(Float), Fixed(Int)), flow(Var(0), Fixed(Int))]);
        assert_eq!(solution.narrowed, vec![0]);
        let solution = solve(&[flow(Fixed(Float), Var(0)), flow(Var(0), Fixed(Int))]);
        assert_eq!(solution.narrowed, vec![1]);
    }

    #[test]
    fn a_free_producer_wanted_as_int_and_float_is_a_float_and_narrows() {
        let solution = solve(&[flow(Var(0), Fixed(Int)), flow(Var(0), Fixed(Float))]);
        assert_eq!(bound(&solution, 0), Some(Float));
        assert_eq!(solution.narrowed, vec![0]);
    }

    #[test]
    fn a_cycle_terminates() {
        let solution = solve(&[
            flow(Var(0), Var(1)),
            flow(Var(1), Var(0)),
            flow(Fixed(Int), Var(0)),
        ]);
        assert_eq!(bound(&solution, 0), Some(Int));
        assert_eq!(bound(&solution, 1), Some(Int));
    }

    #[test]
    fn a_long_chain_is_solved_in_linear_time() {
        let n = 200_000u32;
        let mut edges: Vec<Edge> = (0..n).map(|v| flow(Var(v), Var(v + 1))).collect();
        edges.push(flow(Fixed(Float), Var(0)));
        let solution = solve(&edges);
        assert_eq!(solution.bound.len(), n as usize + 1);
    }
}
