//! `cargo run --release -p goat_pulley_spike --example bench [pulley|cranelift] [frames]`

fn main() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let pulley = args.next().as_deref() != Some("cranelift");
    let frames = args
        .next()
        .map_or(Ok(600), |n| n.parse().map_err(|e| format!("{e}")))?;
    print!("{}", goat_pulley_spike::bench(pulley, frames)?);
    Ok(())
}
