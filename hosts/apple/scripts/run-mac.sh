#!/usr/bin/env bash
# Build and launch the goat macOS app from the command line — no Xcode UI.
#
#   hosts/apple/scripts/run-mac.sh
#
# Restages the engine library on every run, so the app always carries the current
# compiler. Signs with
# the team in Local.xcconfig; -allowProvisioningUpdates is only slow the first time.
set -euo pipefail
cd "$(dirname "$0")/.."

./scripts/stage-engine.sh         # build Frameworks/GoatEngine.xcframework (the app links it)
xcodegen generate                 # (re)generate Goat.xcodeproj from project.yml + Local.xcconfig

# ENABLE_USER_SCRIPT_SANDBOXING=NO: the "Check staged engine" build phase runs
# scripts/check-staged.sh, which Xcode's per-script sandbox otherwise blocks from
# reading its own script. CI passes the same flag.
xcodebuild -project Goat.xcodeproj -scheme Goat-macOS -configuration Debug \
  -destination 'platform=macOS' -derivedDataPath build \
  -allowProvisioningUpdates ENABLE_USER_SCRIPT_SANDBOXING=NO build

open build/Build/Products/Debug/Goat.app
