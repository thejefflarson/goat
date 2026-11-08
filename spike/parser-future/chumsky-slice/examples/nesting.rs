//! Time the parser on `(((...1...)))` (valid) and `(((...` (unclosed) as depth
//! grows, to expose backtracking blowup.
use std::time::Instant;

fn main() {
    for depth in [100, 400, 1000, 2000] {
        let valid = format!("{}1{}", "(".repeat(depth), ")".repeat(depth));
        let open = "(".repeat(depth);
        for (label, src) in [("valid", &valid), ("unclosed", &open)] {
            let t = Instant::now();
            let (_, errs) = chumsky_slice::parse_items(src);
            println!(
                "depth {depth:>3} {label:<8} {:>10.2?} errors={}",
                t.elapsed(),
                errs.len()
            );
        }
    }
}
