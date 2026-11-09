# ADR 0024 — The `goat` facade owns the public host boundary

- Status: accepted (2026-11-08)
- Context: ADR 0020 (host vocabulary), `docs/plan.md` ("library first": the
  `goat` crate is the embedding API), issue #296.

## Context

The host boundary — `Host`, `HostValue`, `NoHost`, the scene types (`Scene`,
`SceneCommand`, `SceneHost`, `SceneSink`) and the `Boundary` type a foreign
signature is written in — is a runtime concern. It is defined in `goat_mir`
because the MIR interpreter needs it, and `Boundary` in `goat_checker`. Every
client therefore reached past the `goat` facade and named `goat_mir` or
`goat_checker` to implement a host, so the facade did not describe what an
embedder depends on.

## Decision

The `goat` crate re-exports the host boundary at its root: `Host`, `HostValue`,
`NoHost`, `Boundary`, `Scene`, `SceneCommand`, `SceneHost`, `SceneSink` and `check_color` (the one color allowlist every host
shares).
Clients (the CLI, `goat_wamr`, `goat::native`, examples) import host types from
`goat`, not from `goat_mir` or `goat_checker`.

The types stay defined where they are. Moving them into `goat` would make
`goat_mir` depend on `goat`, a cycle with `goat -> goat_mir`; a new
`goat_host` crate would add a crate for a handful of types. A re-export gives
clients one import path and keeps the crate graph acyclic. Tests that exercise
compiler internals (`mono`, `verify`, the interpreter) still name `goat_mir`.

## Consequences

- The host surface can move crates later without touching clients.
- `goat::native` no longer re-exports these types; they live at the root.
- The color allowlist and the scene wire protocol still have two homes each;
  those are separate tickets.
