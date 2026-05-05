# hex — agent-specific conventions

Conventions specifically for LLM agents working on this project.
General project doctrine (Mathlib-free split, SPEC/PLAN structure,
key files) lives in `SPEC/` and `PLAN.md`; start there for
orientation.

## Style

Don't add "research completed" timestamps, progress notes, or
meta-commentary about the history of our research process to any
file. The git history tracks that. SPEC files and `PLAN/` contain
the current state of the design, not a journal of how we got there.

## Per-turn progress files

Start of turn: read the most recent file in `progress/` (ISO-8601
timestamps sort chronologically). If only `progress/0000-init.md`
exists, the repo is freshly initialised — proceed with Phase 0.

End of turn: write `progress/<UTC-timestamp>.md` with sections
**Accomplished** / **Current frontier** / **Next step** / **Blockers**.
Scope these to *your* session — what you touched, where you stopped,
what you think comes next for your corner of the project.
Commits made during the turn should mention the progress file.

## Lean

Check diagnostics after every step; don't continue past errors. Build
via `lake build`, not `lean` directly. `native_decide` is banned (see
SPEC).

Never introduce an `axiom`. This includes converting an existing
`theorem`/`def`/`example` into an `axiom` when a refactor breaks its
proof — fix the proof or fix the API. For unfinished proofs use
`sorry`, which is grep-able and produces a warning; `axiom` is silent.
