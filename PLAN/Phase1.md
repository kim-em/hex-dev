# Phase 1: Scaffolding

**Coupling:** dep-coupled. Library L can start Phase 1 once every
`d ∈ L.deps` has `libraries.yml[d].done_through ≥ 1`.

Create Lean files implementing each library's API as declared in the
SPEC. Parallelizable in DAG order (a library can be scaffolded once
its dependencies are scaffolded).

## What to scaffold

Read `SPEC/Libraries/hex-foo.md`. The SPEC contains explicit Lean
code blocks with `structure`, `def`, `theorem`, and `class`
declarations, and some newer library specs also give explicit API
contracts in prose with named suggested declarations. These stable
declarations and record shapes are the scaffolding targets. Prose
discussion of proof strategies, alternatives, heuristics, and
examples is context for later phases, not a scaffolding obligation,
unless it explicitly fixes the public API or theorem split.

## Rules

- **Read the SPEC prose for each declaration before writing its
  body.** The signature alone is not the contract. Locate the SPEC
  prose that describes *what algorithm* the declaration computes,
  read it end to end, and make sure your body implements that
  algorithm. If the SPEC gives explicit update formulas, case
  analysis, or a pseudocode sketch, your body must follow it. If
  you cannot find such prose, or cannot understand it, do not
  commit the declaration.

- Every `def`, data-carrying `structure` field, `class`, and
  `instance` MUST have a body that the author *believes*
  correctly implements the SPEC contract for that declaration.
  There is no acceptable placeholder form:
  - NOT wrong-but-plausible bodies
    (`def rowReduce M := { rank := 0, echelon := M, transform := 1 }`).
  - NOT `sorry` bodies (`noncomputable def rowReduce ... := sorry`).
  - NOT `axiom rowReduce : ...`.
  - NOT trivial returns (`Matrix.identity`, `none`, the input
    unchanged, an identity cast).
  - NOT alternative implementations with the wrong algorithmic
    complexity. **In particular**: a function whose name or
    signature promises a *native-typed* algorithm (`UInt64`,
    `UInt32`, `Float`, `Fin n`, ...) but whose body is `f a.toNat
    b.toNat` followed by `.ofNat` of the result is a wrong-shape
    scaffold — it moves all the work into bignum `Nat` arithmetic,
    which is the wrong asymptotic and the wrong algorithm. Native
    type signatures must perform native arithmetic.
  - NOT a body marked "honest placeholder", "Phase 1 scaffold
    returns <trivial>", "scaffold for the eventual <X> bridge",
    "for now", or any equivalent phrase in its docstring or
    comments. Such phrases are meta-commentary about implementation
    history, not documentation; their presence is itself the bug.
  - NOT a fake `@[extern "name"]` whose C body delegates straight
    back to the Lean fallback. An `@[extern]` whose only effect is
    to call `l_Hex_*___boxed` (or otherwise re-enter the Lean
    runtime to do the actual work) is not a valid extern boundary.
    Either the C side does work native to C (calling GMP, CLMUL,
    `__uint128_t`, etc.), or the `@[extern]` attribute and its C
    file must not be committed yet.

  If you cannot implement the function correctly in this PR: **do
  not commit the declaration**. Leave it out of Lean entirely. The
  SPEC file is the record of what's *designed*; the Lean surface
  is the record of what's *implemented correctly so far*. Any bad
  definitions will poison all downstream conformance testing,
  benchmarking, and theorem proving. We need to get definitions
  right, and if we ever discover they are wrong, fix them
  immediately rather than working around them.

- **`sorry`'d theorem proofs are expected.** The point of scaffolding
  is to get the API surface compiling, not to fill in proofs. This
  rule applies to `theorem` bodies and propositional `structure`
  fields — those produce `Prop` values, and a `sorry` proof doesn't
  propagate into computation. It does **not** extend an escape
  valve for data-level bodies — see the rule above.

- **Helper definitions** not in the SPEC are fine if needed to state
  the API. Note them in the PR. The same "correctly implemented or
  not committed" rule applies.

- **Verify:** `lake build` must succeed after each scaffolding PR.

## Work unit granularity (Phase 1)

Phase 1 issues are typically one-per-major-structure or
one-per-SPEC-subsection — whichever matches the shape of the SPEC
file. A single structure definition plus its basic API lemmas is
often the right size. Every library will need many PRs across many
agent sessions.

General issue-writing conventions (narrow issues, canonical body
shape, decomposition, partial progress) live in
[Conventions.md](Conventions.md).

## Exit criteria

For library `hex-foo`, Phase 1 is done when:

- every SPEC declaration that has been implemented in Lean has a
  signature matching the SPEC, and a body that correctly implements
  the SPEC contract (no `sorry`, no `axiom`, no wrong-but-plausible
  trivial body);
- SPEC declarations that have *not* yet been correctly implemented
  are not present in Lean — the PR description records which ones
  are deferred to follow-ups, and a follow-up issue exists for each;
- `lake build <HexFooLib>` succeeds;
- each new `.lean` file carries a module docstring summarising the
  library contents;
- no `TODO`, `FIXME`, or `...` placeholder remains in the scaffolded
  code (other than `sorry` in proofs).

Record completion by bumping `libraries.yml[L].done_through` to `1`.
