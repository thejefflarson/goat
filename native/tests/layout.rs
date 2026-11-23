use goat_native::abi::{expected_layout, host_offsets, instance_offsets};
use goat_native::{Library, clang_available};

#[test]
fn the_mirrors_name_the_emitters_fields_in_order() {
    let host: Vec<_> = host_offsets().into_iter().map(|(name, _)| name).collect();
    let mut emitted = vec!["version"];
    emitted.extend(goat_llvm::HOST_FUNCTIONS);
    assert_eq!(host, emitted);

    let instance: Vec<_> = instance_offsets()
        .into_iter()
        .map(|(name, _)| name)
        .collect();
    let emitted: Vec<_> = goat_llvm::INSTANCE_FIELDS
        .iter()
        .map(|(name, _)| *name)
        .collect();
    assert_eq!(instance, emitted);
}

#[test]
fn both_structs_start_with_their_version() {
    assert_eq!(host_offsets()[0], ("version", 0));
    assert_eq!(instance_offsets()[0], ("version", 0));
}

#[test]
fn the_rust_layout_is_the_layout_the_emitter_writes() {
    if !clang_available() {
        eprintln!("skipping: clang is not available");
        return;
    }
    let lib = Library::build(&goat_llvm::layout_probe()).unwrap();
    assert_eq!(lib.probe_layout().unwrap(), expected_layout());
}
