#!/bin/sh
# Spike: how many programs the checker accepts and the algorithm refuses only
# because a sort does not reach a variable inside a type (docs/design/phase6-proof-plan.md,
# 2.4), and how many only because a row variable has no sort (#564).
#
#     differential/sort_gap.sh   (after `make -C proofs differential`)
#
# Patches a scratch copy of the extracted algorithm so that `sat_b` accepts a
# variable of any sort inside a type (`len_t`) and `rsat_b` accepts a row
# variable (`len_r`), then reruns every checker-accepted program the algorithm
# refuses (sort_gap_main.ml).  The lenient runs are unsound and read only for
# acceptance.  Nothing it writes is part of the build.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
diff_dir=$here/../proofs/_differential
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

{
  echo 'let len_t = ref false'
  echo 'let len_r = ref false'
  sed -e 's/^| Typ_Var a -> finer_b (d a) k$/| Typ_Var a -> !len_t || finer_b (d a) k/' \
      -e 's/^| Row_Ext (_, t0, r'"'"') -> (&&) (sat_b d k t0) (rsat_b d k r'"'"')$/&\n| Row_Var _ when !len_r -> true/' \
      "$diff_dir/goat_infer.ml"
} > "$work/goat_infer.ml"
grep -q '!len_t' "$work/goat_infer.ml" && grep -q '!len_r' "$work/goat_infer.ml"

{ sed -n '1,/^let fuel = /p' "$here/driver.ml" | sed '$d'; cat "$here/sort_gap_main.ml"; } > "$work/sort_gap.ml"
(cd "$work" && ocamlfind ocamlopt -w -a goat_infer.ml sort_gap.ml -o sort_gap)
"$work/sort_gap" "$diff_dir/corpus.tsv"
