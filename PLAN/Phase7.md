# Phase 7: User-facing Documentation

**Coupling:** local. Library L can start Phase 7 once
`libraries.yml[L].done_through ≥ 6`. Deps need not be at Phase 7.

Every library has Phase 7 work: a Verso chapter in the `HexManual`
aggregator documenting the library's API with live, typechecked Lean
code blocks.

## Tool: Verso

[Verso](https://github.com/leanprover/verso) is the Lean-native
authoring system used for the Lean Language Reference. Chosen over
plain Markdown or raw doc-gen4 because Verso embeds live Lean code
blocks that typecheck against the real library, so signatures,
examples, and cross-references stay in sync with the code
automatically — the right fit for a verified computational algebra
library where readers should see both the algorithmic exposition and
the actual Lean API.

## Structure: `HexManual` lean_lib

The manual is a single `lean_lib HexManual` in the root
`lakefile.lean` (set up during Phase 0). It depends on Verso and on
every `hex-*` library.

- Verso's dependency on Mathlib (if any) flows only through
  `HexManual`, not into the computational libraries.
- The manual sits at the top of the DAG — it is the aggregator that
  depends on everything else.
- A single document cross-references definitions and theorems across
  every library.

Per-library chapter content lives at
`HexManual/Chapters/<LibraryName>.lean` (e.g.
`HexManual/Chapters/HexArith.lean`). The top-level `HexManual.lean`
imports all chapters.

## Authoring style (Verso manual tricks)

A chapter is narrative prose walking the reader through the library,
with docstrings and type signatures of the significant defs/theorems
embedded *programmatically* at the points the narrative reaches them
— the chapter pulls canonical text from the source rather than
duplicating it, so signatures and docs stay in sync with the library
automatically. Same pattern used by the Lean Language Reference.

Each chapter should cover:

1. A short introduction (what the library is for, what downstream
   users get from it).
2. The core data types, with their signatures pulled from source.
3. The principal operations, with worked examples that compile.
4. Key correctness theorems, with statements pulled from source and
   prose explaining their meaning.
5. Cross-references to the corresponding Mathlib bridge library (for
   computational libs) or to the computational counterpart (for
   `hex-*-mathlib` libs).

Three Verso constraints bite chapter authors and only surface at
build time:

- A `{ref "tag"}[text]` (or `{name}`/`{docstring}`) directive must sit
  on a **single line** — breaking `{ref` from its `"tag"}[text]` across
  a newline is a parse error.
- Lean code blocks (```` ```lean ````) are capped at **60 columns**;
  longer lines warn. Lift wide `example`/`theorem` binders into a
  `variable` block above the block to fit.
- `{docstring StructName}` errors unless **every field** of the
  structure is documented (`'Foo.bar' is not documented`). To embed a
  structure's docstring, first add a `/-- … -/` field docstring to each
  field in the source `structure`, or fall back to `{name StructName}`.
  Likewise, `#eval`/`#guard` on an `@[extern]` def fails in the manual's
  evaluator (no native binding) — document those by signature/law and
  keep evaluated example blocks to the pure-Lean surface.

## Additional Phase 7 work: tutorials

Some libraries have extra Phase 7 scope beyond the reference chapter —
authoring the tutorial pages specified in
[SPEC/tutorials.md](../SPEC/tutorials.md), which also live in
`HexManual/Tutorials/` as Verso chapters. Each tutorial is anchored to
a single library for Phase 7 bookkeeping (even if it draws on several):

| Tutorial | Anchor library |
|----------|---------------|
| AES byte arithmetic (GF(2^8)) | `hex-gf2` |
| AES modulus irreducibility | `hex-berlekamp` |
| Prime splitting (Kummer-Dedekind) | `hex-gfq` |
| LLL in cryptanalysis (Coppersmith toy) | `hex-lll` |

Phase 7 for an anchor library is not "done" until both its reference
chapter *and* its anchored tutorials are complete.

## Exit criteria for library `L`

- `L`'s reference chapter at `HexManual/Chapters/<L>.lean` exists and
  builds inside the `HexManual` `lean_lib`;
- all embedded Lean code blocks in the chapter typecheck;
- computational vs. proof boundary is stated where relevant;
- cross-references to deps resolve (if a chapter for a dep exists, the
  cross-reference goes to it; otherwise, a stub link is acceptable and
  resolves later);
- any tutorials anchored to `L` (see table above) exist and build.

Record completion by bumping `libraries.yml[L].done_through` to `7`.

## Full-manual render as a release artifact

Rendering the complete manual — with all cross-references resolved and
all tutorials linked from the release entry point — is a release-level
concern handled in [Releases.md](Releases.md), not a per-library
Phase 7 exit criterion. A release requires every library in its scope
at `done_through ≥ 7`, at which point the full manual renders cleanly.
