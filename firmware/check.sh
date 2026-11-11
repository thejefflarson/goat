#!/usr/bin/env bash
# The firmware CI gate: WAMR links for each board architecture with tail calls
# and bulk memory on, and a build with either flag off is rejected.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"

for arch in riscv32imc thumbv6m; do
  "$here/build.sh" "$arch"
  for flag in WAMR_BUILD_TAIL_CALL WAMR_BUILD_BULK_MEMORY; do
    if env "$flag=0" "$here/build.sh" "$arch" >/dev/null 2>&1; then
      echo "$arch built with $flag=0; the floor check did not fire" >&2
      exit 1
    fi
    echo "$arch rejects $flag=0"
  done
done
