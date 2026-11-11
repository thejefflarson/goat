#!/usr/bin/env bash
# Cross-builds the vendored WAMR interpreter for a board architecture and links
# it with link_check.c, so a build that links proves the runtime resolves
# against the board's C library. wamr/csrc/floor.c fails the build unless tail
# calls and bulk memory are on (docs/adr/0019).
#
#   firmware/build.sh riscv32imc|thumbv6m
#
# The host-only wamr crate never builds this; see docs/adr/0029.
set -euo pipefail

arch="${1:?usage: build.sh riscv32imc|thumbv6m}"
here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"
core="$root/wamr/vendor/wasm-micro-runtime/core"
out="$root/target/firmware/$arch"

case "$arch" in
  riscv32imc)
    cc="${CC:-riscv64-unknown-elf-gcc}"
    cflags=(-march=rv32imc -mabi=ilp32 -DBUILD_TARGET_RISCV32_ILP32 '-DBUILD_TARGET="RISCV32_ILP32"')
    ldflags=(-march=rv32imc -mabi=ilp32 -nostartfiles)
    specs=(--specs=picolibc.specs)
    ;;
  thumbv6m)
    cc="${CC:-arm-none-eabi-gcc}"
    cflags=(-mcpu=cortex-m0plus -mthumb -DBUILD_TARGET_THUMB '-DBUILD_TARGET="THUMB"')
    ldflags=(-mcpu=cortex-m0plus -mthumb)
    specs=(--specs=nosys.specs)
    ;;
  *) echo "unknown architecture $arch" >&2; exit 2 ;;
esac

# Mirrors SOURCES in wamr/build.rs, with this directory's platform in place of
# the posix one.
sources=(
  iwasm/common/wasm_application.c
  iwasm/common/wasm_blocking_op.c
  iwasm/common/wasm_c_api.c
  iwasm/common/wasm_exec_env.c
  iwasm/common/wasm_loader_common.c
  iwasm/common/wasm_memory.c
  iwasm/common/wasm_native.c
  iwasm/common/wasm_runtime_common.c
  iwasm/common/wasm_shared_memory.c
  iwasm/common/arch/invokeNative_general.c
  iwasm/interpreter/wasm_loader.c
  iwasm/interpreter/wasm_runtime.c
  iwasm/interpreter/wasm_interp_fast.c
  shared/mem-alloc/ems/ems_alloc.c
  shared/mem-alloc/ems/ems_gc.c
  shared/mem-alloc/ems/ems_hmu.c
  shared/mem-alloc/ems/ems_kfc.c
  shared/mem-alloc/mem_alloc.c
  shared/utils/bh_assert.c
  shared/utils/bh_bitmap.c
  shared/utils/bh_common.c
  shared/utils/bh_hashmap.c
  shared/utils/bh_leb128.c
  shared/utils/bh_list.c
  shared/utils/bh_log.c
  shared/utils/bh_queue.c
  shared/utils/bh_vector.c
  shared/utils/runtime_timer.c
)

# WAMR_BUILD_TAIL_CALL and WAMR_BUILD_BULK_MEMORY default to the floor; the CI
# negative check sets one to 0 and expects floor.c to reject the build.
defines=(
  -DBH_MALLOC=wasm_runtime_malloc -DBH_FREE=wasm_runtime_free
  -DWASM_ENABLE_INTERP=1 -DWASM_ENABLE_FAST_INTERP=1 -DWASM_ENABLE_MINI_LOADER=0
  -DWASM_ENABLE_AOT=0 -DWASM_ENABLE_JIT=0 -DWASM_ENABLE_FAST_JIT=0
  "-DWASM_ENABLE_TAIL_CALL=${WAMR_BUILD_TAIL_CALL:-1}"
  "-DWASM_ENABLE_BULK_MEMORY=${WAMR_BUILD_BULK_MEMORY:-1}"
  -DWASM_ENABLE_REF_TYPES=1 -DWASM_ENABLE_SIMD=0 -DWASM_ENABLE_SHARED_MEMORY=0
  -DWASM_ENABLE_MULTI_MODULE=0 -DWASM_ENABLE_LIBC_BUILTIN=0 -DWASM_ENABLE_LIBC_WASI=0
  -DWASM_DISABLE_HW_BOUND_CHECK=1 -DWASM_DISABLE_STACK_HW_BOUND_CHECK=1
)

includes=(
  -I"$here/platform"
  -I"$core" -I"$core/iwasm/include" -I"$core/iwasm/common" -I"$core/iwasm/interpreter"
  -I"$core/shared/utils" -I"$core/shared/mem-alloc" -I"$core/shared/platform/include"
)

mkdir -p "$out"
rm -f "$out"/*.o
objs=()
compile() {
  local src="$1" obj
  obj="$out/$(basename "$(dirname "$src")")_$(basename "$src").o"
  "$cc" "${specs[@]}" "${cflags[@]}" "${defines[@]}" "${includes[@]}" -Os -ffunction-sections \
    -fdata-sections -w -c "$src" -o "$obj"
  objs+=("$obj")
}

for s in "${sources[@]}"; do compile "$core/$s"; done
compile "$here/platform/platform.c"
compile "$root/wamr/csrc/floor.c"
compile "$here/link_check.c"

"$cc" "${specs[@]}" "${ldflags[@]}" -Wl,--gc-sections "${objs[@]}" -lm \
  -o "$out/link_check.elf"
echo "linked $out/link_check.elf"
