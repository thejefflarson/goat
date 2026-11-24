#!/bin/sh
# Xcode pre-build check: the app is useless without its staged engine library.
xcf="$SRCROOT/Frameworks/GoatEngine.xcframework"
if [ ! -f "$xcf/Info.plist" ]; then
  echo "error: Frameworks/GoatEngine.xcframework is not staged. Run hosts/apple/scripts/stage-engine.sh first." >&2
  exit 1
fi
if [ -n "$(find "$SRCROOT/engine/src" "$SRCROOT/engine/include" "$SRCROOT/engine/Cargo.toml" -newer "$xcf/Info.plist" -print -quit)" ]; then
  echo "error: GoatEngine.xcframework is older than hosts/apple/engine. Run hosts/apple/scripts/stage-engine.sh again." >&2
  exit 1
fi
