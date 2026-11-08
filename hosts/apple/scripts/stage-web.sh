#!/bin/sh
# Builds the compiler wasm and the embed page, and stages them where both app
# targets bundle them (Resources/web). Needs cargo (with the wasm32 target) and npm.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/../.." && pwd)

cd "$root"
cargo build -p goat_web --target wasm32-unknown-unknown --release
npm ci --prefix web
npm run build --prefix web
node web/bundle.ts --embed "$here/Resources/web"
