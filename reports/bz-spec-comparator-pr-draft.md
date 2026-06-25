# Draft PR: hex-berlekamp-zassenhaus SPEC — comparator, headline
correctness theorem, no-fallback discipline

**Purpose of this draft.** Captures the SPEC-level changes that
[reports/bz-vs-isabelle-investigation.md](bz-vs-isabelle-investigation.md)
identifies as the orchestration gaps that allowed the `isGoodPrime` /
`fallbackPrimeChoiceData` cascade to ship. The draft is structured as a
single PR (four coupled changes); review notes at the bottom flag
which clauses are load-bearing for the post-mortem and which are
project-hygiene cleanup.

This is an *interactive-Claude SPEC-clarification PR* per the
[`spec-driven-development`](../../../.claude/skills/spec-driven-development/SKILL.md)
skill — the clauses introduced here resolve orchestration gaps that
worker agents (per
[`PLAN/Conventions.md §"SPEC immutability"`](../PLAN/Conventions.md))
cannot address on their own. Human review by Kim is the merge gate.

This PR is **SPEC text + libraries.yml metadata only**. It does not
touch Lean code. The rollback issue
([reports/bz-rollback-issue-draft.md](bz-rollback-issue-draft.md))
dispatches the implementation work the new SPEC clauses require.

---

## Title

```
spec: BZ Phase-4 requires AFP comparator, headline correctness theorem, no-fallback discipline
```

## Body

This PR codifies four orchestration requirements for
`hex-berlekamp-zassenhaus` that the project did not have when the
current Phase-4 bench scaffolding landed under HO-3 (#2566). All four
trace to a single live regression — hex BZ's `factor` returns
mathematically wrong output on `(x-1)…(x-n)` for several `n ∈ [11, 24]`
and is 200–2,400× slower than the AFP Isabelle BZ extracted-Haskell
binary even when correct — investigated in
[reports/bz-vs-isabelle-investigation.md](../reports/bz-vs-isabelle-investigation.md).
The investigation traces the bug to:

1. No external comparator was declared for BZ, so the wall-time blow-up
   could not be distinguished from "schedule too short".
2. The Mathlib bridge proved per-function soundness lemmas but no
   end-to-end pipeline theorem, so the wrong-output bug had nowhere to
   surface.
3. `choosePrimeData` fell through to a hard-coded `p = 3` via
   `fallbackPrimeChoiceData` when no candidate prime passed an overly
   strict `isGoodPrime`, with no theorem guarding the fallback.

This PR is the spec change. Worker issues for the implementation work
land separately (see linked issues below).

### Change 1: `SPEC/Libraries/hex-berlekamp-zassenhaus.md` — add a
`## External comparators` section

Add the following section between the existing `## Conformance
fixtures` and `## References` sections:

```markdown
## External comparators

Phase 4 for `hex-berlekamp-zassenhaus` declares one **gating** external
comparator:

- **`verified Isabelle BZ (AFP Berlekamp_Zassenhaus; Haskell extraction
  of `factor_int_poly` via `Factorization_External_Interface.thy`)`**.
  Build via a sibling of
  [scripts/oracle/setup_lll_isabelle.sh](https://github.com/kim-em/hex-lll/blob/main/scripts/oracle/setup_lll_isabelle.sh)
  that targets the AFP `Berlekamp_Zassenhaus` session instead of the
  Zenodo LLL deposit. Set-up: `isabelle build -b Berlekamp_Zassenhaus`
  using the AFP release matching the pinned Isabelle, then
  `isabelle export -d <wrapper-session> -x '*:code/**'` on a
  wrapper theory that re-exports `factor_int_poly` to Haskell. The
  generated module is compiled with `ghc -O2` against a persistent
  stdin/stdout driver per
  [SPEC/benchmarking.md §External comparators — Process call](../benchmarking.md#external-comparators).

  **Gating goal: `hex/isabelle ≤ 1×` at the largest eligible scaling
  rung of every registered scientific bench target.** Justification:
  both implementations are pure-functional verified code extracted to
  a strict runtime with native integer arithmetic. The
  `hex-lll` row in [reports/hex-lll-performance.md](https://github.com/kim-em/hex-lll/blob/main/reports/hex-lll-performance.md)
  already demonstrates parity is achievable across the dimension
  ladder against the analogous AFP-extracted LLL binary (hex within
  ±10%, faster at small `n`). There is no architectural reason hex
  should require concessional headroom against the BZ comparator.

  *Algorithm-class caveat.* The 1× gate presumes the comparator
  implements an algorithm of the same class or weaker than hex's.
  Isabelle's `Berlekamp_Zassenhaus.berlekamp_zassenhaus_factorization`
  uses classical exhaustive lifted-factor recombination; hex's spec
  mandates the BHKS van Hoeij CLD construction (see §"Recombination"),
  which is strictly more sophisticated and asymptotically better on
  adversarial inputs, so parity holds without algorithmic-class
  concession. If a future comparator implements a fundamentally
  stronger algorithm, this clause must be explicitly amended to
  loosen the goal or reclassify the comparator.

The fpLLL/python-flint comparators that adjacent libraries declare for
their LLL or polynomial-arithmetic surfaces are *informational only*
at the BZ level; the verified-Isabelle path is the only same-class
(verified-to-verified) comparator and so is the only one classified
as gating here.
```

### Change 2: `libraries.yml` — add `phase4.comparators`

In the `HexBerlekampZassenhaus` block, add:

```yaml
      comparators:
        - tool: "verified Isabelle BZ (AFP Berlekamp_Zassenhaus, Haskell extraction of factor_int_poly via Factorization_External_Interface)"
          class: gating
          goal: "wallclock ratio hex/isabelle ≤ 1× at the largest eligible scaling rung of every registered scientific bench target; algorithm-class caveat per the SPEC §External comparators clause"
```

This is structurally identical to `HexLLL`'s `verified Isabelle LLL`
entry except for the tool/source pointer and the tighter 1× goal.

### Change 3: `SPEC/Libraries/hex-berlekamp-zassenhaus.md` — add a `##
Headline correctness theorem` section after the existing `## Proof
obligations Group C` section

```markdown
## Headline correctness theorem

`HexBerlekampZassenhausMathlib` must carry, and the `done_through ≥ 4`
bump is blocked on, an end-to-end theorem with the following
**semantic shape**:

> For every nonzero `f : Hex.ZPoly`, the public-API output
> `φ := Hex.factor f : Hex.Factorization` satisfies all five clauses:
>
> 1. **Product preservation.** `Hex.Factorization.product φ = f`.
> 2. **Primitive irreducibility.** Every `entry ∈ φ.factors` is
>    primitive and `Polynomial.Irreducible
>    (HexPolyZMathlib.toPolynomial entry.1)` holds in the Mathlib sense.
> 3. **Positive multiplicities.** Every `entry ∈ φ.factors` has
>    `entry.2 > 0`.
> 4. **No factor associates.** For any two distinct positions in
>    `φ.factors`, the underlying polynomials are not associates of
>    each other.
> 5. **Scalar carries sign and content.** `φ.scalar` equals the signed
>    integer content of `f` (sign × content per `ZPoly.content` and
>    `ZPoly.leadingCoeff` conventions).

The final Lean name (e.g. `factor_correct`,
`factor_irreducible_factorisation`) may differ from this prose, and
intermediate predicates such as `IsIrreducibleFactorization` may
abbreviate the conjunction, but the five-clause shape is binding.

This is the post-condition of the public API and the contract the
combinator advertises in its docstring. **The headline theorem is
the critical-path artefact for `done_through ≥ 4`.** Intermediate
lemmas are admissible when they are either

- (a) load-bearing for some proof of the headline theorem, or
- (b) independently justified as public API, executable checker, or
  regression guard with stated rationale.

Lemmas that satisfy neither are dead weight and should be removed
or refactored until they earn their place.

A bridge file that proves an arbitrary collection of intermediate
lemmas but does not prove the headline correctness theorem is
incomplete by SPEC: the orchestrator must not bump `done_through` to
4 in that state. The local realisation of this clause for the open
BZ architectural directive is rewritten in the dispatched rollback
issue.
```

### Change 4: `SPEC/design-principles.md` — add a `### Fallback
discipline for total forms of partial helpers` clause **next to
§"Placeholders are for proofs only"**

Insert immediately after the existing §"Placeholders are for proofs
only":

```markdown
### Fallback discipline for total forms of partial helpers

A close relative of the no-placeholder rule. Pipelines sometimes
contain a helper of shape

```lean
def helper (f : T) : U :=
  match helperOpt f with
  | some x => x
  | none => fallback f
```

where the `Option`-returning `helperOpt` is the natural mathematical
object and `helper`'s total form exists for downstream
type-signature convenience. The `none` branch is a **fallback**.

A total form of a partial helper is admissible **only** when the SPEC
text classifies the fallback under exactly one of the following:

- **`unreachable-by-pipeline-invariant`**: the bridge file proves a
  theorem `helperOpt?_isSome_of_<precondition>` showing the `none`
  branch is unreachable on inputs that the public API passes
  downstream. The SPEC text cites the theorem by name and states the
  pipeline invariant it relies on. The `none` branch may then return
  an arbitrary value; semantically it is dead code.
- **`audited-emergency-value`**: the fallback's behaviour is
  mathematically safer than crashing (e.g. a verifiable identity
  element, an explicit failure record that downstream consumers
  inspect), every call site explicitly audits this, and the SPEC text
  states the rationale and lists the call sites that accept the
  fallback. This mode is rare.

A total form of a partial helper without one of these two
classifications is a SPEC violation. The remedy is to either prove
the unreachability theorem, document the audit (and pass each call
site's audit), or **remove the total form** by propagating the
`Option` upward through the pipeline until the public API takes
explicit responsibility for the `none` case. *"Refactor later"* is
not an admissible classification; it is the no-placeholder rule
restated.

This rule applies retroactively: existing total forms of partial
helpers must be either proved unreachable, documented and audited,
or removed before any `done_through` bump past the phase in which
the helper lives.
```

### Change 5: `PLAN/Conventions.md` — append cross-reference paragraph

In the §"Hard rules" section, after the existing §"Placeholders are
for proofs only" subsection, append a one-paragraph cross-reference
to the two new SPEC clauses, modelled on the existing reference to
`design-principles.md §7` for the placeholder rule. The wording
points workers at:

1. `SPEC/design-principles.md` §"Fallback discipline for total forms
   of partial helpers" — sibling of the placeholder rule, applies
   project-wide.
2. The per-library `## Headline correctness theorem` requirement —
   per-library SPECs at `done_through ≥ 4` must state and discharge
   such a theorem; intermediate lemmas earn their place by being
   load-bearing for it or independently justified per the
   admissibility test in the per-library SPEC clause.

---

## Review notes

- **Change 1 + Change 2 are the post-mortem critical-path.** Without
  them the comparator gap (gap 1 of the investigation report) is not
  closed and the wallclock regression can re-occur on any future BZ
  rewrite.
- **Change 3 is the deeper fix.** Per-function soundness lemmas don't
  compose into end-to-end correctness on their own; the orchestrator
  needs to dispatch the headline theorem as the critical-path
  artefact, with intermediate lemmas as consequences of the proof's
  decomposition (or independently justified as public-API surface).
- **Change 4 generalises the fallback-smell post-mortem** and lives
  in `SPEC/design-principles.md`, not benchmarking — it is a
  data-body coding rule, sibling to the no-placeholder rule.
  Project-wide, prospective and retroactive.
- **Change 5 is hygiene** — workers re-read `PLAN/Conventions.md`
  every session; both new rules need to be findable from there or
  they don't actually constrain behaviour.

## Related

- Post-mortem: [reports/bz-vs-isabelle-investigation.md](../reports/bz-vs-isabelle-investigation.md)
- Rollback issue (drafted): [reports/bz-rollback-issue-draft.md](../reports/bz-rollback-issue-draft.md)
- HO-1 (open): https://github.com/kim-em/hex/issues/2564
- HO-2 (closed): https://github.com/kim-em/hex/issues/2565
- HO-3 (closed): https://github.com/kim-em/hex/issues/2566

🤖 Prepared with Claude Code
