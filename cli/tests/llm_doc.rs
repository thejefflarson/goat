//! `docs/llm.md` is pasted into a model's context, so its examples must match
//! the compiler. A ```` ```goat ```` block must type-check and a
//! ```` ```goat error ```` block must be rejected; other fences are fragments.

use std::fs;
use std::process::Command;

struct Block {
    line: usize,
    expect_error: bool,
    source: String,
}

fn goat_blocks(doc: &str) -> Vec<Block> {
    let mut blocks = Vec::new();
    let mut open: Option<Block> = None;
    for (index, text) in doc.lines().enumerate() {
        let text = text.trim_end();
        match (&mut open, text) {
            (None, "```goat" | "```goat error") => {
                open = Some(Block {
                    line: index + 1,
                    expect_error: text.ends_with("error"),
                    source: String::new(),
                });
            }
            (Some(_), "```") => blocks.extend(open.take()),
            (Some(block), _) => {
                block.source.push_str(text);
                block.source.push('\n');
            }
            (None, _) => {}
        }
    }
    assert!(open.is_none(), "unterminated goat block");
    blocks
}

#[test]
fn llm_doc_examples_match_the_compiler() {
    let doc = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../docs/llm.md")).unwrap();
    let blocks = goat_blocks(&doc);
    assert!(blocks.len() > 20, "found only {} goat blocks", blocks.len());
    assert!(blocks.iter().any(|b| b.expect_error), "no error blocks");

    let dir = tempfile::tempdir().expect("temp dir");
    let mut wrong = Vec::new();
    for block in blocks {
        let path = dir.path().join(format!("line{}.goat", block.line));
        fs::write(&path, &block.source).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_goat"))
            .args(["check", path.to_str().unwrap()])
            .output()
            .expect("run goat");
        if out.status.success() == block.expect_error {
            let want = if block.expect_error {
                "should be rejected but compiled"
            } else {
                "should compile but failed"
            };
            wrong.push(format!(
                "docs/llm.md:{} {want}\n{}{}",
                block.line,
                block.source,
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
