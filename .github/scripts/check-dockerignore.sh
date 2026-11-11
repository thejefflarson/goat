#!/usr/bin/env bash
# The editor image's build context is allowlist-only (web/Dockerfile.dockerignore).
# A workspace member or Dockerfile COPY source missing from it fails the image
# build on master only, after merge. Fail here instead.
set -euo pipefail
cd "$(dirname "$0")/../.."

ignore=web/Dockerfile.dockerignore
status=0

require() {
  grep -qxF "!$1" "$ignore" || {
    echo "::error file=$ignore::'$1' ($2) is not allowlisted; add '!$1'" >&2
    status=1
  }
}

members=$(awk '/^members *= *\[/{on=1;next} on&&/\]/{exit} on{gsub(/[ ",]/,"");if($0)print}' Cargo.toml)
[ -n "$members" ] || { echo "no workspace members parsed from Cargo.toml" >&2; exit 1; }
for m in $members; do require "${m%%/*}" "workspace member"; done

srcs=$(awk 'toupper($1)=="COPY" && !/--from/{for(i=2;i<NF;i++) if($i !~ /^--/) print $i}' web/Dockerfile)
for src in $srcs; do
  case "$src" in .|./) continue ;; esac
  require "${src%%/*}" "web/Dockerfile COPY source"
done

exit $status
