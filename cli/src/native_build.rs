//! `goat build --native`: compile a program to LLVM IR, then have clang link it
//! with the standalone runtime in `libgoat_native.a` (ADR 0042).

use goat::{HostInterface, Profile};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

const STATIC_LIB: &str = "libgoat_native.a";
const CLANG_CANDIDATES: [&str; 3] = ["clang-23", "clang-17", "clang"];

#[cfg(target_os = "macos")]
const SYSTEM_LIBS: &[&str] = &["-liconv", "-Wl,-dead_strip"];
#[cfg(not(target_os = "macos"))]
const SYSTEM_LIBS: &[&str] = &["-lpthread", "-ldl", "-lm", "-Wl,--gc-sections"];

#[cfg(target_os = "macos")]
const MISSING_CLANG: &str = "run `xcode-select --install` to get Apple's clang";
#[cfg(not(target_os = "macos"))]
const MISSING_CLANG: &str =
    "install clang with your package manager (for example `apt install clang`)";

/// The vocabulary a program is written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vocabulary {
    Turtle,
    Canvas,
}

impl Vocabulary {
    pub fn interface(self) -> HostInterface {
        match self {
            Vocabulary::Turtle => HostInterface::turtle(),
            Vocabulary::Canvas => goat_canvas::interface(),
        }
    }
}

/// The program's LLVM IR, or why the backend has none.
pub fn emit_ir(source: &str, vocabulary: Vocabulary) -> Result<String, Vec<goat::GoatError>> {
    goat::compile_ll(Profile::Desktop, source, &vocabulary.interface())
}

/// Whether `ll` is an interactive program, which has no `goat_main` for a
/// standalone binary to run.
pub fn is_interactive(ll: &str) -> bool {
    ll.contains("@goat_attach(")
}

/// The labels of the `goat_event_<Label>` exports `ll` defines, which an
/// interactive program's host calls to build the events it sends.
#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
fn event_labels(ll: &str) -> Vec<&str> {
    const EXPORT: &str = "@goat_event_";
    ll.lines()
        .filter(|line| line.starts_with("define "))
        .filter_map(|line| {
            let after = &line[line.find(EXPORT)? + EXPORT.len()..];
            Some(&after[..after.find('(')?])
        })
        .collect()
}

/// The clang to run: `$GOAT_CLANG`, else the first of `clang-23`, `clang-17`
/// and `clang` that runs.
pub fn find_clang() -> Result<String, String> {
    if let Ok(named) = std::env::var("GOAT_CLANG") {
        return if runs(&named) {
            Ok(named)
        } else {
            Err(format!("GOAT_CLANG is {named}, which does not run"))
        };
    }
    CLANG_CANDIDATES
        .iter()
        .find(|name| runs(name))
        .map(|name| name.to_string())
        .ok_or_else(|| {
            format!("goat build --native needs clang, which is not installed: {MISSING_CLANG}")
        })
}

fn runs(clang: &str) -> bool {
    Command::new(clang)
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
}

/// The runtime library the `goat` binary carries, set once at startup. Empty
/// when the build script could not build it.
static EMBEDDED_LIB: OnceLock<&'static [u8]> = OnceLock::new();

pub fn embed_static_lib(bytes: &'static [u8]) {
    let _ = EMBEDDED_LIB.set(bytes);
}

/// The runtime library: `$GOAT_NATIVE_LIB`, else one beside this executable,
/// else the copy the binary carries, written into `scratch`.
pub fn find_static_lib(scratch: &Path) -> Result<PathBuf, String> {
    if let Some(path) = std::env::var_os("GOAT_NATIVE_LIB") {
        let path = PathBuf::from(path);
        return if path.is_file() {
            Ok(path)
        } else {
            Err(format!(
                "GOAT_NATIVE_LIB is {}, which is not a file",
                path.display()
            ))
        };
    }
    let beside = std::env::current_exe()
        .map_err(|e| format!("cannot find the goat executable: {e}"))?
        .with_file_name(STATIC_LIB);
    if beside.is_file() {
        return Ok(beside);
    }
    match EMBEDDED_LIB.get() {
        Some(bytes) if !bytes.is_empty() => {
            let path = scratch.join(STATIC_LIB);
            std::fs::write(&path, bytes)
                .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
            Ok(path)
        }
        _ => Err(format!(
            "{} not found and this goat carries no copy; build it with `cargo build -p goat_native`, or point GOAT_NATIVE_LIB at it",
            beside.display()
        )),
    }
}

/// The C file that holds the program's source for trap reports and starts the
/// runtime.
fn entry_c(source: &str) -> String {
    let bytes: Vec<String> = source
        .bytes()
        .chain([0])
        .map(|byte| byte.to_string())
        .collect();
    format!(
        "#include <stdint.h>\n\
         int32_t goat_main(const void *, void *, void *);\n\
         int goat_standalone_main(int, char **, int32_t (*)(const void *, void *, void *), const uint8_t *, uint64_t);\n\
         static const uint8_t source[] = {{{}}};\n\
         int main(int argc, char **argv) {{\n    \
         return goat_standalone_main(argc, argv, goat_main, source, sizeof source - 1);\n}}\n",
        bytes.join(",")
    )
}

/// The bundle identifier of the app named `name`: `local.goat.` and the name
/// in lowercase ASCII letters, digits and hyphens.
#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
fn bundle_identifier(name: &str) -> String {
    let slug: Vec<String> = name
        .to_ascii_lowercase()
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|part| !part.is_empty())
        .map(str::to_string)
        .collect();
    let slug = if slug.is_empty() {
        "app".to_string()
    } else {
        slug.join("-")
    };
    format!("local.goat.{slug}")
}

#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
fn xml_escape(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// The `Info.plist` of the app `name`.
#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
fn info_plist(name: &str) -> String {
    let (id, name) = (bundle_identifier(name), xml_escape(name));
    format!(
        r#"<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
	<key>CFBundleExecutable</key>
	<string>{name}</string>
	<key>CFBundleIdentifier</key>
	<string>{id}</string>
	<key>CFBundleName</key>
	<string>{name}</string>
	<key>CFBundleDisplayName</key>
	<string>{name}</string>
	<key>CFBundlePackageType</key>
	<string>APPL</string>
	<key>CFBundleIconFile</key>
	<string>AppIcon</string>
	<key>LSMinimumSystemVersion</key>
	<string>13.0</string>
	<key>NSHighResolutionCapable</key>
	<true/>
</dict>
</plist>
"#
    )
}

/// Whether `out` names an app bundle.
pub fn is_app_path(out: &Path) -> bool {
    out.extension().is_some_and(|ext| ext == "app")
}

#[cfg(not(target_os = "macos"))]
pub fn bundle(_: &str, _: &str, _: &Path) -> Result<(), String> {
    Err("goat build --native writes .app bundles on macOS only".to_string())
}

/// Writes the interactive program `ll` as the app bundle `app`: the executable,
/// an `Info.plist`, the default icon, all signed ad hoc so macOS will run it.
#[cfg(target_os = "macos")]
pub fn bundle(ll: &str, source: &str, app: &Path) -> Result<(), String> {
    use goat_native::appkit;
    if !is_interactive(ll) {
        return Err(
            "a .app needs an interactive program (one with init, update and draw); \
             a run-once program builds as a plain executable, so drop the .app from -o"
                .to_string(),
        );
    }
    let name = app
        .file_stem()
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.is_empty())
        .ok_or_else(|| format!("{} has no name to give the app", app.display()))?;
    const CODESIGN: &str = "/usr/bin/codesign";
    if !Path::new(CODESIGN).is_file() {
        return Err(format!(
            "goat build --native needs {CODESIGN} to sign a .app, which is missing"
        ));
    }
    if app.is_dir() {
        std::fs::remove_dir_all(app)
            .map_err(|e| format!("cannot replace {}: {e}", app.display()))?;
    }
    let (macos, resources) = (app.join("Contents/MacOS"), app.join("Contents/Resources"));
    for dir in [&macos, &resources] {
        std::fs::create_dir_all(dir).map_err(|e| format!("cannot make {}: {e}", dir.display()))?;
    }
    link_interactive(ll, source, &macos.join(name))?;
    for (path, bytes) in [
        (
            app.join("Contents/Info.plist"),
            info_plist(name).into_bytes(),
        ),
        (resources.join("AppIcon.icns"), appkit::ICON.to_vec()),
    ] {
        std::fs::write(&path, bytes)
            .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    run(
        Command::new(CODESIGN)
            .args(["--force", "--sign", "-"])
            .arg(app),
        "codesign",
    )
}

/// Links `ll`, the IR of `source`, into the executable `out`.
pub fn link(ll: &str, source: &str, out: &Path) -> Result<(), String> {
    if is_interactive(ll) {
        return link_interactive(ll, source, out);
    }
    let clang = find_clang()?;
    let dir = tempfile::tempdir().map_err(|e| format!("cannot make a temporary directory: {e}"))?;
    let lib = find_static_lib(dir.path())?;
    let (ll_path, c_path) = (dir.path().join("program.ll"), dir.path().join("entry.c"));
    for (path, text) in [(&ll_path, ll), (&c_path, &entry_c(source))] {
        std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    let output = Command::new(&clang)
        .args(["-O2", "-x", "ir"])
        .arg(&ll_path)
        .args(["-x", "c"])
        .arg(&c_path)
        .args(["-x", "none"])
        .arg(&lib)
        .args(SYSTEM_LIBS)
        .arg("-o")
        .arg(out)
        .output()
        .map_err(|e| format!("cannot run {clang}: {e}"))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "{clang} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}

#[cfg(not(target_os = "macos"))]
fn link_interactive(_: &str, _: &str, _: &Path) -> Result<(), String> {
    Err(
        "goat build --native does not support interactive programs on this platform yet: \
         their window host is AppKit, so they build on macOS only"
            .to_string(),
    )
}

/// The C file that defines the program's exports and source for the window
/// host to start.
#[cfg(target_os = "macos")]
fn interactive_entry_c(source: &str, events: &[&str]) -> String {
    let mut bytes: Vec<String> = source.bytes().map(|byte| byte.to_string()).collect();
    bytes.push("0".to_string());
    let mut c = String::from(
        "#include \"goat_host.h\"\n\
         int32_t goat_attach(const void *, void *, void *);\n\
         void *goat_setup(const void *, void *, void *);\n\
         void *goat_update(const void *, void *, void *, void *, void *);\n\
         void goat_draw(const void *, void *, void *, void *);\n\
         void *goat_alloc(const void *, void *, void *, uint32_t);\n",
    );
    for label in events {
        c += &format!("void *goat_event_{label}();\n");
    }
    c += "static const GoatEvent events[] = {\n";
    for label in events {
        c += &format!("    {{\"{label}\", (const void *)goat_event_{label}}},\n");
    }
    c += &format!(
        "    {{0, 0}}\n}};\n\
         const GoatProgram goat_program = {{goat_attach, goat_setup, goat_update, goat_draw, \
         goat_alloc, events, {}}};\n\
         static const uint8_t source[] = {{{}}};\n\
         const GoatSource goat_source = {{source, sizeof source - 1}};\n",
        events.len(),
        bytes.join(",")
    );
    c
}

/// The Swift compiler: `$GOAT_SWIFTC`, else `swiftc`.
#[cfg(target_os = "macos")]
fn find_swiftc() -> Result<String, String> {
    let swiftc = std::env::var("GOAT_SWIFTC").unwrap_or_else(|_| "swiftc".to_string());
    if runs(&swiftc) {
        Ok(swiftc)
    } else {
        Err(format!(
            "an interactive goat build needs {swiftc} for its AppKit host, which does not run: {MISSING_CLANG}"
        ))
    }
}

#[cfg(target_os = "macos")]
fn run(command: &mut Command, name: &str) -> Result<(), String> {
    let output = command
        .output()
        .map_err(|e| format!("cannot run {name}: {e}"))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "{name} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}

/// Links an interactive program with the AppKit host (`goat_native::appkit`):
/// clang compiles the program and its entry code, and `swiftc` compiles the
/// host and links all of it with the runtime library.
#[cfg(target_os = "macos")]
fn link_interactive(ll: &str, source: &str, out: &Path) -> Result<(), String> {
    use goat_native::appkit;
    let (clang, swiftc) = (find_clang()?, find_swiftc()?);
    let dir = tempfile::tempdir().map_err(|e| format!("cannot make a temporary directory: {e}"))?;
    let lib = find_static_lib(dir.path())?;
    let at = |name: &str| dir.path().join(name);
    let (header, header_text) = appkit::HEADER;
    let mut files = vec![
        (at("program.ll"), ll.to_string()),
        (
            at("entry.c"),
            interactive_entry_c(source, &event_labels(ll)),
        ),
        (at(header), header_text.to_string()),
    ];
    files.extend(
        appkit::SWIFT
            .iter()
            .map(|(name, text)| (at(name), text.to_string())),
    );
    for (path, text) in &files {
        std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    run(
        Command::new(&clang)
            .args(["-O2", "-c", "-x", "ir"])
            .arg(at("program.ll"))
            .arg("-o")
            .arg(at("program.o")),
        &clang,
    )?;
    run(
        Command::new(&clang)
            .args(["-O2", "-c", "-I"])
            .arg(dir.path())
            .arg(at("entry.c"))
            .arg("-o")
            .arg(at("entry.o")),
        &clang,
    )?;
    run(
        Command::new(&swiftc)
            .args(["-O", "-swift-version", "5", "-module-name", "GoatHost"])
            .arg("-import-objc-header")
            .arg(at(header))
            .args(appkit::SWIFT.iter().map(|(name, _)| at(name)))
            .args([at("program.o"), at("entry.o")])
            .arg(&lib)
            .args([
                "-framework",
                "AppKit",
                "-liconv",
                "-Xlinker",
                "-dead_strip",
                "-o",
            ])
            .arg(out),
        &swiftc,
    )
}
