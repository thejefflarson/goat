#!/bin/sh
# Xcode pre-build check: the app is useless without its staged drawing engine.
if [ ! -f "$SRCROOT/Resources/web/embed.html" ] || [ ! -f "$SRCROOT/Resources/web/goat_web.wasm" ]; then
  echo "error: Resources/web is not staged. Run hosts/apple/scripts/stage-web.sh first." >&2
  exit 1
fi
