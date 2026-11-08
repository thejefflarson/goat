#!/usr/bin/env bash
# Re-vendors the slice of WAMR that goat_wamr builds: the fast interpreter, the
# loader, and the posix platform layers. Pass a checkout of the pinned tag:
#
#   git clone --depth 1 --branch WAMR-2.4.5 \
#     https://github.com/bytecodealliance/wasm-micro-runtime.git /tmp/wamr
#   wamr/vendor.sh /tmp/wamr
#
# Bump the tag and the commit recorded in vendor/VERSION together.
set -euo pipefail

src="${1:?usage: vendor.sh <wasm-micro-runtime checkout>}"
here="$(cd "$(dirname "$0")" && pwd)"
dst="$here/vendor/wasm-micro-runtime"

rm -rf "$dst"
mkdir -p "$dst/core/iwasm/common/arch" "$dst/core/iwasm/interpreter" \
  "$dst/core/shared/platform/common"

cp "$src/LICENSE" "$dst/"
cp "$src/core/config.h" "$src/core/version.h" "$dst/core/"
cp -R "$src/core/iwasm/include" "$dst/core/iwasm/"
cp "$src"/core/iwasm/common/*.c "$src"/core/iwasm/common/*.h "$dst/core/iwasm/common/"
cp "$src/core/iwasm/common/arch/invokeNative_general.c" "$dst/core/iwasm/common/arch/"
mkdir -p "$dst/core/iwasm/aot" "$dst/core/iwasm/compilation"
cp "$src"/core/iwasm/aot/*.h "$dst/core/iwasm/aot/"
cp "$src"/core/iwasm/compilation/aot.h "$dst/core/iwasm/compilation/"
cp "$src"/core/iwasm/interpreter/*.h "$dst/core/iwasm/interpreter/"
cp "$src/core/iwasm/interpreter/wasm_loader.c" \
  "$src/core/iwasm/interpreter/wasm_runtime.c" \
  "$src/core/iwasm/interpreter/wasm_interp_fast.c" "$dst/core/iwasm/interpreter/"
cp -R "$src/core/shared/utils" "$src/core/shared/mem-alloc" "$dst/core/shared/"
cp -R "$src/core/shared/platform/include" "$src/core/shared/platform/darwin" \
  "$src/core/shared/platform/linux" "$dst/core/shared/platform/"
cp -R "$src/core/shared/platform/common/posix" \
  "$src/core/shared/platform/common/memory" "$dst/core/shared/platform/common/"
find "$dst" \( -name '*.cmake' -o -name SConscript \) -delete
