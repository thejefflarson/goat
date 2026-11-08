#!/usr/bin/env bash
# Fail-soft sccache backend selection for the CI Rust jobs (`lint` and `test` in
# .github/workflows/rust.yml — the two jobs that install sccache and set it as
# RUSTC_WRAPPER). The CI-side twin of scripts/start-sccache-docker.sh: same shape,
# different transport for the config — this one reads the runner pod's env
# directly; the Docker twin reads BuildKit build secrets mounted at /run/secrets.
#
# The runner pod injects the R2 config -- SCCACHE_BUCKET / SCCACHE_ENDPOINT /
# SCCACHE_REGION / SCCACHE_S3_KEY_PREFIX / SCCACHE_S3_USE_SSL plus the bucket-scoped
# AWS_* token -- from the `sccache-r2` Secret via envFrom (cluster repo:
# charts/actions/runners/values-protector.yaml). Nothing about the backend is set in
# the workflow, and no credential is committed here.
#
# WHY THIS SCRIPT EXISTS. sccache's S3/R2 backend is EAGER, exactly like the redis
# one it replaced: `sccache --start-server` FAILS outright when the bucket is
# unreachable, and the first rustc-through-sccache call then dies with "sccache:
# Timed out waiting for server startup", killing the whole job. Measured against
# sccache 0.16.0 (cluster repo, JEF-564 R2 cutover):
#
#   S3 configured, endpoint unreachable    -> --start-server FAILS
#   empty SCCACHE_BUCKET + SCCACHE_DIR set -> "Cache location: Local disk"
#
# So an R2 outage would otherwise be a HARD CI OUTAGE, not a slow build -- the same
# blast radius the redis backend had, now pointed at an off-cluster dependency.
#
# On success: leave the pod's S3 env alone and exit 0.
# On failure: fall back to a LOCAL disk cache. GITHUB_ENV cannot *unset* a variable,
# so the fallback exports an EMPTY SCCACHE_BUCKET (sccache then treats the backend as
# unconfigured -- the measurement above) alongside SCCACHE_DIR. Exporting SCCACHE_DIR
# alone would not work: a non-empty SCCACHE_BUCKET still wins.
#
# Usage:
#   bash .github/scripts/start-sccache.sh              # start a server, never fail
#   bash .github/scripts/start-sccache.sh --selftest   # run the built-in fixtures
set -uo pipefail

LOCAL_CACHE_DIR="${HOME}/.cache/sccache"

fall_back_to_local_disk() {
  {
    echo "SCCACHE_BUCKET="
    echo "SCCACHE_DIR=${LOCAL_CACHE_DIR}"
  } >>"${GITHUB_ENV}"
  sccache --stop-server >/dev/null 2>&1 || true
  SCCACHE_BUCKET= SCCACHE_DIR="${LOCAL_CACHE_DIR}" sccache --start-server >/dev/null 2>&1 || true
}

start_sccache() {
  # Start clean -- no server should be running yet (no earlier step compiles), but
  # make the backend switch deterministic if one lingered.
  sccache --stop-server >/dev/null 2>&1 || true

  if [ -z "${SCCACHE_BUCKET:-}" ]; then
    # The `sccache-r2` Secret never reached the pod (Secret missing, or an overlay
    # that re-enumerates the runner container dropped the envFrom). Say so loudly:
    # silently compiling against a cold local cache is how a broken cutover reads
    # as fine.
    echo "::warning::sccache: no R2 config in the pod env (sccache-r2 Secret missing?) — using a local disk cache"
    fall_back_to_local_disk
    return 0
  fi

  for attempt in 1 2 3; do
    if sccache --start-server >/dev/null 2>&1; then
      echo "sccache: R2 backend up (bucket=${SCCACHE_BUCKET}, attempt ${attempt})"
      return 0
    fi
    echo "sccache: R2 backend not ready (attempt ${attempt}/3); retrying in 3s" >&2
    sccache --stop-server >/dev/null 2>&1 || true
    sleep 3
  done

  echo "::warning::sccache: R2 backend unreachable — falling back to local disk cache"
  fall_back_to_local_disk
}

# ── Self-test ────────────────────────────────────────────────────────────────
# Drives the three states a job can be in against stub `sccache`/`sleep` binaries,
# so a regression in the fail-soft logic (in particular the load-bearing empty
# SCCACHE_BUCKET in the GITHUB_ENV fallback) is caught by CI in seconds instead of
# by an R2 outage taking every Rust job down with it. Mirrors the fixture shape in
# scripts/start-sccache-docker.sh's selftest.
selftest() {
  _tmp="$(mktemp -d)"
  trap 'rm -rf "${_tmp}"' EXIT
  mkdir -p "${_tmp}/bin"

  cat >"${_tmp}/bin/sccache" <<'STUB'
#!/bin/sh
if [ "${1:-}" = "--start-server" ]; then
  echo "start bucket=[${SCCACHE_BUCKET:-}] dir=[${SCCACHE_DIR:-}]" >>"${STUB_LOG}"
  [ "${STUB_START_FAILS:-0}" = "1" ] && exit 1
fi
exit 0
STUB
  # Stub out the real sleep so the "unreachable" fixture doesn't burn 6s of retry
  # backoff every CI run.
  cat >"${_tmp}/bin/sleep" <<'STUB'
#!/bin/sh
exit 0
STUB
  chmod +x "${_tmp}/bin/sccache" "${_tmp}/bin/sleep"
  PATH="${_tmp}/bin:${PATH}"
  export PATH STUB_LOG

  _fails=0
  expect() { # expect <label> <grep-pattern> <file>
    if grep -q "$2" "$3"; then
      echo "  ok   $1"
    else
      echo "  FAIL $1 — no line matching /$2/ in:" >&2
      sed 's/^/       /' "$3" >&2
      _fails=$((_fails + 1))
    fi
  }

  # 1. No R2 config in the pod env (sccache-r2 Secret missing/dropped): local
  #    disk, and NOT a hard failure.
  unset SCCACHE_BUCKET
  GITHUB_ENV="${_tmp}/env1"; : >"${GITHUB_ENV}"
  STUB_LOG="${_tmp}/log1"; : >"${STUB_LOG}"
  STUB_START_FAILS=0 start_sccache >/dev/null 2>&1 || _fails=$((_fails + 1))
  expect "no bucket -> local disk fallback exported" "^SCCACHE_BUCKET=$" "${GITHUB_ENV}"
  expect "no bucket -> SCCACHE_DIR exported" "^SCCACHE_DIR=${LOCAL_CACHE_DIR}$" "${GITHUB_ENV}"
  expect "no bucket -> local disk server started" "bucket=\[\] dir=\[${LOCAL_CACHE_DIR}\]" "${STUB_LOG}"

  # 2. Bucket configured and R2 answers: S3 backend, GITHUB_ENV untouched, no
  #    fallback.
  export SCCACHE_BUCKET="a-bucket"
  GITHUB_ENV="${_tmp}/env2"; : >"${GITHUB_ENV}"
  STUB_LOG="${_tmp}/log2"; : >"${STUB_LOG}"
  STUB_START_FAILS=0 start_sccache >/dev/null 2>&1 || _fails=$((_fails + 1))
  if [ -s "${GITHUB_ENV}" ]; then
    echo "  FAIL R2 reachable -> GITHUB_ENV left untouched" >&2
    _fails=$((_fails + 1))
  else
    echo "  ok   R2 reachable -> GITHUB_ENV left untouched"
  fi
  expect "R2 reachable -> S3 backend, exactly one start" "^start bucket=\[a-bucket\] dir=\[\]$" "${STUB_LOG}"

  # 3. Bucket configured, R2 unreachable: retried 3x, THEN degraded to local
  #    disk with an empty bucket — the exact fallback this probe exists for.
  GITHUB_ENV="${_tmp}/env3"; : >"${GITHUB_ENV}"
  STUB_LOG="${_tmp}/log3"; : >"${STUB_LOG}"
  STUB_START_FAILS=1 start_sccache >/dev/null 2>&1 || _fails=$((_fails + 1))
  expect "R2 down -> local disk fallback exported" "^SCCACHE_BUCKET=$" "${GITHUB_ENV}"
  expect "R2 down -> SCCACHE_DIR exported" "^SCCACHE_DIR=${LOCAL_CACHE_DIR}$" "${GITHUB_ENV}"
  if [ "$(grep -c 'bucket=\[a-bucket\]' "${STUB_LOG}")" != "3" ]; then
    echo "  FAIL R2 down -> 3 attempts before degrading" >&2
    _fails=$((_fails + 1))
  else
    echo "  ok   R2 down -> 3 attempts before degrading"
  fi
  expect "R2 down -> fallback started with empty bucket" "bucket=\[\] dir=\[${LOCAL_CACHE_DIR}\]" "${STUB_LOG}"

  if [ "${_fails}" -ne 0 ]; then
    echo "selftest: ${_fails} failure(s)" >&2
    return 1
  fi
  echo "selftest: all fixtures passed"
}

if [ "${1:-}" = "--selftest" ]; then
  selftest
else
  start_sccache
fi
