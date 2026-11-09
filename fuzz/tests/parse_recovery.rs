use goat_parser::cst::{Child, Node};
use goat_parser::interp::{parse, parse_recovering};

fn assert_tiles(node: Node) {
    let mut at = node.span().start;
    for child in node.elements() {
        let (start, end) = match child {
            Child::Token(t) => (t.start, t.end),
            Child::Node(n) => {
                assert_tiles(n);
                (n.span().start, n.span().end)
            }
        };
        assert_eq!(start, at, "a gap or overlap inside {}", node.kind());
        at = end;
    }
    assert_eq!(
        at,
        node.span().end,
        "{} ends where its pieces do",
        node.kind()
    );
}

#[test]
fn parse_recovery_holds_its_invariants() {
    bolero::check!().for_each(|data: &[u8]| {
        let Ok(source) = std::str::from_utf8(data) else {
            return;
        };
        let recovered = parse_recovering(source);
        let root = recovered.cst.root();
        let text: String = root
            .tokens()
            .iter()
            .map(|t| &source[t.start..t.end])
            .collect();
        assert_eq!(text, source, "the tree reproduces the source");
        assert_eq!(root.span(), 0..source.len());
        assert_tiles(root);
        assert_eq!(
            recovered.diagnostics.is_empty(),
            parse(source).is_ok(),
            "no diagnostics iff the strict parse accepts: {source:?}"
        );
    });
}
