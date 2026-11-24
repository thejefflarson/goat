#!/bin/sh
# Builds goat_apple as a static library for every Apple slice and packages
# Frameworks/GoatEngine.xcframework, the module Swift imports as `GoatEngine`.
# Needs cargo with the Apple targets (rustup target add aarch64-apple-darwin
# x86_64-apple-darwin aarch64-apple-ios aarch64-apple-ios-sim) and Xcode.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/../.." && pwd)
out="$here/Frameworks"
work="$root/target/goat_engine_xcframework"

# Keep in step with deploymentTarget in project.yml.
export MACOSX_DEPLOYMENT_TARGET=13.0
export IPHONEOS_DEPLOYMENT_TARGET=17.0

cd "$root"
for target in aarch64-apple-darwin x86_64-apple-darwin aarch64-apple-ios aarch64-apple-ios-sim; do
  cargo build -j "${GOAT_JOBS:-2}" -p goat_apple --release --target "$target"
done

lib() { echo "$root/target/$1/release/libgoat_apple.a"; }

rm -rf "$work" "$out/GoatEngine.xcframework"
mkdir -p "$work/headers" "$work/macos" "$out"
cp "$here/engine/include/goat_engine.h" "$work/headers/"
cat > "$work/headers/module.modulemap" <<'MAP'
module GoatEngine {
    header "goat_engine.h"
    export *
}
MAP

lipo -create "$(lib aarch64-apple-darwin)" "$(lib x86_64-apple-darwin)" -output "$work/macos/libgoat_apple.a"

xcodebuild -create-xcframework \
  -library "$work/macos/libgoat_apple.a" -headers "$work/headers" \
  -library "$(lib aarch64-apple-ios)" -headers "$work/headers" \
  -library "$(lib aarch64-apple-ios-sim)" -headers "$work/headers" \
  -output "$out/GoatEngine.xcframework"
