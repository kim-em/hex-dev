# Design principles

1. **Many small libraries** in a single monorepo, each its own Lake
   library target.

2. **No Mathlib in the computational core.** Every library that computes
   something is Mathlib-free. Where full correctness requires results
   from analysis (e.g. the Mignotte bound), the computational
   library proves conditional correctness and the corresponding
   `-mathlib` library discharges the hypothesis. The `-mathlib`
   libraries also prove correspondence with Mathlib's mathematical
   definitions (e.g. `ZMod64 p ≃+* ZMod p`).

   The procedural consequence — "before filing or claiming an issue,
   verify which side of this boundary the deliverable sits on" — is
   captured in [PLAN/Conventions.md, "Library placement is a hard
   precondition"](../PLAN/Conventions.md#library-placement-is-a-hard-precondition).
   A proof whose shortest path uses Mathlib's `adjugate`, universal
   polynomial rings, or any Mathlib-only structure does not live in a
   Mathlib-free library, regardless of which file the issue happens
   to name.

3. **Performant by default.** Dense array-backed representations, `UInt64`
   coefficients for `F_p`, Barrett/Montgomery reduction for modular
   arithmetic. New GMP `@[extern]` primitives where Lean's runtime
   doesn't yet expose what we need (notably extended GCD for big
   integers). FLINT is used for conformance testing, not as a runtime
   dependency.

4. **Lean algorithms from the start.** All algorithms are implemented and
   run in Lean natively. No external CAS in the loop. Certificate
   structures exist for compact proof witnesses, but the algorithms that
   generate and check certificates are both in Lean.

5. **Clear DAG structure.** Libraries can be developed in parallel. LLL has
   no dependency on polynomial arithmetic. Hensel lifting is independent of
   LLL. Everything meets at the top (Berlekamp-Zassenhaus).

6. **`Hex` namespace.** All definitions live under `Hex` to avoid
   collisions with Mathlib's root-namespace types (`Matrix`,
   `Polynomial`, etc.).

7. **Scaffolding applies only to proofs.** A proof skeleton may carry
   `sorry` placeholders, where allowed. Every `def`, data-carrying
   `structure` field, `class`, and `instance` ships with its
   intended-final implementation on the first commit — the *real*
   algorithm with the *intended* complexity, not a wrong-but-plausible
   stand-in. If you cannot write that implementation in the current
   session, do not commit the declaration; leave it out of Lean
   entirely and open a follow-up issue. This rule is enforced at
   three points: when a library is scaffolded
   ([PLAN/Phase1.md](../PLAN/Phase1.md)), when its scaffolding is
   reviewed ([PLAN/Phase2.md](../PLAN/Phase2.md)), and when its
   benchmarks run ([benchmarking.md](benchmarking.md)). If
   benchmarking later reveals that a committed `def` was scaffolding
   in disguise — wrong shape, wrong complexity — the response is to
   roll back the affected library's `done_through` and re-enter the
   relevant phase, not to weaken the benchmark.

   *"Intended complexity"* means the canonical fast algorithm for
   the operation — square-and-multiply for `pow`, Newton iteration
   for floor square root, the multiplicative formula for binomial
   coefficients, Euclidean for `gcd`. If a library SPEC doesn't
   mention performance requirements for an operation, assume the
   implementation needs to be optimal.

   Proof-level placeholders use `sorry`, never `axiom`. `sorry`
   produces a compile-time warning that surfaces in CI; `axiom` is
   silent. If a refactor breaks an existing proof, fix the proof,
   fix the API the proof depends on, or roll back the refactor —
   never axiomatise the conclusion. The same rollback path that
   applies to a benchmark-discovered scaffolding `def` applies to a
   proof a refactor would silently axiomatise.

8. **Fallback discipline for total forms of partial helpers.** A
   close relative of principle 7. Pipelines sometimes contain a
   helper of shape

   ```lean
   def helper (f : T) : U :=
     match helperOpt f with
     | some x => x
     | none => fallback f
   ```

   where the `Option`-returning `helperOpt` is the natural
   mathematical object and `helper`'s total form exists for
   downstream type-signature convenience. The `none` branch is a
   **fallback**.

   A total form of a partial helper is admissible **only** when
   the SPEC text classifies the fallback under exactly one of the
   following:

   - **`unreachable-by-pipeline-invariant`** — the bridge file
     proves a theorem `helperOpt?_isSome_of_<precondition>`
     showing the `none` branch is unreachable on inputs that the
     public API passes downstream. The SPEC text cites the theorem
     by name and states the pipeline invariant it relies on. The
     `none` branch may then return an arbitrary value;
     semantically it is dead code.
   - **`audited-emergency-value`** — the fallback's behaviour is
     mathematically safer than crashing (e.g. a verifiable
     identity element, an explicit failure record that downstream
     consumers inspect), every call site explicitly audits this,
     and the SPEC text states the rationale and lists the call
     sites that accept the fallback. This mode is rare.

   A total form of a partial helper without one of these two
   classifications is a SPEC violation. The remedy is to either
   prove the unreachability theorem, document the audit (and pass
   each call site's audit), or **remove the total form** by
   propagating the `Option` upward through the pipeline until the
   public API takes explicit responsibility for the `none` case.
   *"Refactor later"* is not an admissible classification; it is
   principle 7 restated.

   This rule applies retroactively: existing total forms of
   partial helpers must be either proved unreachable, documented
   and audited, or removed before any `done_through` bump past
   the phase in which the helper lives. The same rollback path
   that applies under principle 7 applies here.

## Lakefile

Use `precompileModules := true` only on libraries that export
`@[extern]` functions. Don't use it otherwise, and in particular
libraries importing Mathlib must not use `precompileModules`.

## Fully autonomous execution

The project runs without human interaction after launch. Lean, Mathlib,
and this SPEC are fixed inputs. Agents resolve every issue they
encounter:

- If a needed result is not in Mathlib, prove it locally.
- If a tactic misbehaves, work around it.

There is no human escalation channel. "Stop and flag" is not an
option; "decide and proceed" is.

### Scope of autonomous SPEC edits

Agents may edit the SPEC only to fix clauses that are ill-typed,
internally contradictory, or clearly mathematically impossible. Every
such edit is accompanied by an explicit rationale in the PR
description citing the offending clause and the project goal that
breaks the tie. Changes to public APIs or release goals are
exceptional and should be called out as such, even though no human
approves them. Routine refactoring and "I would have written it
differently" are not grounds for SPEC edits.

### Push sorries earlier

When a proof is hard, replace it with a proof outline that cites new, clearly-stated lemmas
(which may themselves be `sorry`) one level closer to the
foundations. Repeat until the remaining sorries are individually
plausible. This keeps the proof graph reviewable even when the
leaves are incomplete, and lets later workers attack foundational
lemmas in isolation.

## Naming and documentation

**Namespaces.** New types, functions, and theorems introduced by this
project live under `Hex` (e.g. `Hex.FpPoly`, `Hex.GF2n`). Additions to
existing Lean/Mathlib datatypes live in the original namespace
(`Nat.foo`, `Array.polyProduct`, `UInt64.mulHi`). Subnamespaces like
`Hex.GramSchmidt.Int` are fine when they aid discoverability.

**Docstrings.** All public `def`/`structure`/`class`/`inductive`
declarations carry a docstring. Non-obvious private helpers — anything
encoding an invariant, a subtle algorithmic choice, or a non-trivial
specification — also carry one. Routine private plumbing (unfolding
lemmas, `_aux` helpers, trivial getters) is exempt. Every theorem
another file could reasonably import carries a docstring stating what
it proves and why the caller cares.
