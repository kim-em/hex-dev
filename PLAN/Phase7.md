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

Several Verso syntax constraints bite chapter authors and only surface
at build time:

- A `{ref "tag"}[text]` (or `{name}`/`{docstring}`) directive must sit
  on a **single line** — breaking `{ref` from its `"tag"}[text]` across
  a newline is a parse error.
- Lean code blocks (```` ```lean ````) are capped at **60 columns**;
  longer lines warn. Lift wide `example`/`theorem` binders into a
  `variable` block above the block to fit.
- `{name X}` requires `X` to be a **constant** (def/theorem/structure),
  not a namespace. Referring to a namespace like `GramSchmidt.Int` errors
  with `Unknown constant`; name a real declaration in it, or use a plain
  `` `code span` `` in prose.
- `#eval`/`#guard` on an `@[extern]` def fails in the manual's
  evaluator (no native binding) — document those by signature/law and
  keep evaluated example blocks to the pure-Lean surface.
- When the library is an `abbrev` over a more generic type
  (`ZPoly = DensePoly Int`, `FpPoly p = DensePoly (ZMod64 p)`), a
  worked-example `#guard` over an op defined in *both* namespaces
  (`content`, `primitivePart`, …) is ambiguous under
  `open Hex Hex.DensePoly`. Qualify the specialized op explicitly
  (`ZPoly.content f`, not `content f`). Validate `#guard` values in a
  throwaway file importing the fast Mathlib-free library before the
  slow `HexManual` build. Build that throwaway file *through* `lake`
  (e.g. as a temporary module, or trust the values pinned by the
  library's `Conformance.lean`): a standalone `lake env lean file.lean`
  has no precompiled native binding, so `#guard`s over `@[extern]` ops
  (any `ZMod64` arithmetic) error with "Could not find native
  implementation" even when the values are correct. Those same extern
  `#guard`s *do* evaluate green inside the real `HexManual` build, which
  precompiles — so an elaboration-clean throwaway run with only
  native-impl runtime errors at the `#guard` lines is a pass, not a
  failure.
- `{docstring T}` on a `structure`/`inductive`/`class` requires **every
  field to have its own docstring**, not just the type — an undocumented field
  errors with `'…' is not documented` (and cascades into a misleading
  "declaration uses `sorry`" warning on the `#doc`). Add a `/-- … -/` to
  each field in the source library before referencing the type, or embed
  it with `{name}` and describe the fields in prose instead.
- Prose containing a literal `[` (e.g. a formula like `Fₚ[x]`) parses as
  a markdown link target and errors with `expected link target '(url)'
  or '[ref]'`. Wrap such formulas in a code span (`` `Fₚ[x] / (f)` ``) or
  escape the bracket as `\[`.

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

## Additional Phase 7 work: released-repo README

Every library released as a split repo also carries a root `README.md`,
authored here as `<L>/README.md` and published to the released repo's
root by the sync. This is the short landing-page reference for the
released package, distinct from the Verso chapter. Its required shape —
intro, `Quickstart`, `Functionality`, `Verification`, `Contributing` —
and its style rules are specified in [SPEC/readme.md](../SPEC/readme.md).
The quickstart code must build-check against the monorepo.

## Exit criteria for library `L`

- `L`'s reference chapter at `HexManual/Chapters/<L>.lean` exists and
  builds inside the `HexManual` `lean_lib`;
- all embedded Lean code blocks in the chapter typecheck;
- computational vs. proof boundary is stated where relevant;
- cross-references to deps resolve (if a chapter for a dep exists, the
  cross-reference goes to it; otherwise, a stub link is acceptable and
  resolves later);
- any tutorials anchored to `L` (see table above) exist and build;
- if `L` is published as a split repo, `<L>/README.md` exists and
  conforms to [SPEC/readme.md](../SPEC/readme.md), and its quickstart
  code build-checks.

Record completion by bumping `libraries.yml[L].done_through` to `7`.

## Full-manual render as a release artifact

Rendering the complete manual — with all cross-references resolved and
all tutorials linked from the release entry point — is a release-level
concern handled in [Releases.md](Releases.md), not a per-library
Phase 7 exit criterion. A release requires every library in its scope
at `done_through ≥ 7`, at which point the full manual renders cleanly.
