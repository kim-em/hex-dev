# Design principles

1. **Many small libraries** in a single monorepo, each its own Lake
   library target. Split a large library along its dependency seams into
   one-subject units — the matrix stack is `hex-matrix` (dense base) with
   `hex-row-reduce`, `hex-determinant`, and `hex-bareiss` on top — and
   give each computational library a matching `*-mathlib` bridge.

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

   A Mathlib-free library also depends only on Lean core and other
   Mathlib-free Hex libraries — not on Batteries. Where it needs a
   Batteries lemma, it reproduces that lemma in a small Mathlib-free
   shim, keeping the upstream name and signature, marked for removal
   once the lemma lands in Lean core.

   Mathlib *typeclass instances* on an executable type — algebraic
   structures like `Ring` or `Module` — also live in the `*-mathlib`
   bridge, transported along the equivalence so the operations stay the
   executable ones.

3. **Performant by default.** Dense array-backed representations, `UInt64`
   coefficients for `F_p`, Barrett/Montgomery reduction for modular
   arithmetic. New GMP `@[extern]` primitives where Lean's runtime
   doesn't yet expose what we need (notably extended GCD for big
   integers). FLINT is used for conformance testing, not as a runtime
   dependency.

   Hot data transforms use their container linearly, so the compiler
   mutates the backing store in place: prefer `Vector.swap` /
   `Vector.modify` / `Vector.map`, which reuse a uniquely-owned buffer,
   over reading with `getElem` and writing back with `set`, which forces
   a copy.

4. **Lean algorithms from the start.** All algorithms are implemented and
   run in Lean natively, and the native algorithm is always the default and
   carries the correctness guarantee. No *trusted* external CAS in the loop:
   no result whose correctness the project relies on may come from outside
   Lean. Certificate structures exist for compact proof witnesses, and the
   algorithms that generate and check certificates are both in Lean.

   A *checked* external oracle is admissible and is not "external CAS in the
   loop" in the sense this rule forbids. An untrusted external implementation
   may propose a candidate result, provided a verified Lean checker validates
   it on every call and the native algorithm runs whenever the candidate is
   absent or rejected. Correctness then depends only on the verified checker
   and the native fallback, never on the external oracle, so the trusted
   computing base is unchanged. The checker's soundness theorem, the
   fallback, and the dispatch are all in Lean; the external oracle supplies
   only a hint.

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

9. **Performance-led implementation; proofs adapt to it.** Where a
   library competes with a verified external reference (e.g.
   `hex-berlekamp-zassenhaus` vs the AFP `Berlekamp_Zassenhaus`), the
   *shape* of the data-level implementation is chosen for performance
   and validated by **conformance** (differential testing against the
   reference / an oracle) and **benchmarking** (match the reference on
   easy inputs, beat it where the reference is asymptotically worse).
   These two gates are required and **merge-blocking** before the
   correctness proofs are completed; the formal proofs then adapt to the
   committed executable invariants. Do **not** weaken a spec, or modify a
   committed `def`, to make a proof go through — that inverts the
   dependency and has repeatedly produced churn. Freeze the proof-shaped
   invariant surface early (state the contracts, check them in
   conformance) so the proofs have a stable target, but let correctness
   be *established* by the gates first and *certified* by the proofs
   last. This does not relax principle 7 (no data-level scaffolding) or
   the no-`axiom` rule; it orders the work, it does not lower the bar.

10. **Encapsulate representations.** Expose a core datatype as an opaque
    type with an API, not as a transparent alias, so its representation
    can change without touching consumers. `Hex.Matrix` is a one-field
    structure; consumers construct and read it through its API (`ofFn`,
    `ofRows`, `getRow`, `rows`, and entry access `M[(i, j)]`) and never
    its backing store, so a later switch (e.g. to a flat
    `Vector R (n*m)`) stays invisible.

11. **Kernel-facing specification, `@[csimp]` runtime implementation.**
    Always-on cross-checks discharge concrete identities with `decide`,
    so definitions on that path must reduce cheaply in the kernel: no
    `dite` plumbing on the value path, no per-access `Array` list
    traversal inside a loop. When the fast executable shape conflicts
    with this, the public name carries the kernel-friendly
    specification and the optimized body moves to a `*Impl` twin
    registered by a proved `@[csimp]` equality (never
    `@[implemented_by]`, which is unverified). Mark the specification
    `noncomputable`: the kernel still reduces its body for `decide`
    (`noncomputable` suppresses only code generation, not kernel
    reduction), while the `@[csimp]` proof redirects each occurrence
    that reaches code generation to the `*Impl`, so the slow reference
    body is never emitted as dead compiled code. Proof-mode and kernel
    `decide` uses still see the public specification. Spec-level views
    without a runtime twin (e.g. `DensePoly.toList`) are likewise
    `noncomputable`, so runtime code cannot silently round-trip through
    them. Characterising lemmas stay on the public name. Precedents: `DensePoly.trimTrailingZeros`, `DensePoly.mul`,
    `ZMod64.add`/`sub`, `Matrix.mul`, `Vector.dotProduct`.

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

### Proof debt does not cross the layer boundary

A `*-mathlib` proof term must not depend, directly or
transitively, on any Mathlib-free theorem whose proof contains
`sorry`, regardless of channel (direct citation, wrapper, rename,
helper, `simp`/`rw`/`simpa`, typeclass instance, imported chain,
or a Mathlib-side lemma whose own proof routes through such a
dependency). Mathlib-free definitions and Mathlib-free lemmas
with complete proof terms are admissible.

When a bridge proof needs an operational invariant from the
Mathlib-free layer, the admissible moves are: factor the
invariant into a sorry-free Mathlib-free lemma; close the
Mathlib-free `sorry` first; or prove the bridge statement
directly from Mathlib infrastructure (adjugate, cofactor,
Desnanot–Jacobi, and the determinant equivalence the relevant
`*-mathlib` SPEC requires). A wrapper, rename, or separate
decomposition does not change the proof-term dependency graph.

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

**Coined words.** Don't invent vocabulary. Name things with a standard
mathematical term, a standard programming term, or a plain description
of what they do — check Mathlib and the literature first. Two failure
modes: invented `-ise`/`-ify` verbs for operations that already have a
name (the transform making a polynomial monic is `ZPoly.toMonic`, not
`monicise`), and issue/PR process words as identifiers ("umbrella",
"transport package", "consumer", "Gap N", "HO-N") — these record how a
proof was scheduled, not what it is. A name a reader can't decode
without finding its originating issue is a defect.
