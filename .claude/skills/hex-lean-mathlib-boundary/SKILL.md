---
name: hex-lean-mathlib-boundary
description: Gotchas for the Mathlib-free/Mathlib boundary in HexBerlekampZassenhausMathlib and similar *Mathlib Lean layers (ZMod64, FpPoly, DensePoly, ZPoly). Read before proving lemmas that mix the executable types with Mathlib Polynomial / ZMod algebra, OR before verifying any change to a *Mathlib bridge file — CI does not build those libraries, so a whole-library `lake build` failure may be pre-existing on main (see "The Mathlib layer is not CI-built").
allowed-tools: Bash, Read, Grep, Glob
---

# Mathlib-free / Mathlib boundary in the hex Lean layers

The executable types (`Hex.ZMod64 p`, `Hex.FpPoly p = Hex.DensePoly (ZMod64 p)`,
`Hex.ZPoly = Hex.DensePoly Int`) carry **only `Lean.Grind` ring instances and a
custom `Dvd`** — *not* Mathlib's `CommRing`/`Field`/`Monoid`/`AddGroup`
typeclasses. Mathlib homomorphism lemmas therefore fail to synthesize instances
on these types. Do arithmetic with `grind`, and cross to the Mathlib
`Polynomial (ZMod p)` / `ZMod p` side through the project's bridges.

## Concrete rules

- **The `*_semiring`/`*_ring`-specialized `DensePoly` coeff `@[simp]` lemmas
  do not match a goal term built with the canonical instances.**
  `DensePoly.coeff_derivative_semiring` / `coeff_add_semiring` / `coeff_sub_ring`
  restate `derivative`/`add`/`sub` through the `Lean.Grind.Semiring`-derived
  `NatCast`/`Mul` (the `attribute [local instance 1100] Semiring.natCast`), a
  *different instance path* than the canonical `NatCast (ZMod64 p)` /
  `Mul (ZMod64 p)` that a `DensePoly.derivative f` term in a Mathlib-layer goal
  carries. So `rw`/`simp only [coeff_derivative_semiring]` silently fails to fire
  (reported "unused" / "did not find pattern") even though the statement looks
  right. Use the **general** lemma with the explicit zero hypothesis instead —
  `rw [Hex.DensePoly.coeff_derivative f n (Lean.Grind.Semiring.mul_zero _)]` — it
  matches the goal's operation exactly, then `toZMod_mul`/`toZMod_natCast` +
  `push_cast; ring` finish the transport against `Polynomial.coeff_derivative`.
- **`grind`, not `ring`, for `ZMod64`/`FpPoly` arithmetic.** Ring lemmas
  (`mul_one`, `neg_add_cancel`, `ring`) need Mathlib instances these types lack.
  `grind` uses the `Lean.Grind.CommRing` instance; prime-inverse facts
  (`ZMod64.inv_mul_eq_one_of_prime`, `mul_inv_eq_one_of_prime`) are `@[grind]`.
- **Transporting `FpPoly` multiplication to `Polynomial (ZMod p)`
  (`map_mul'`-shaped goals): push `toZMod` through the executable List-fold,
  *then* convert to a Finset sum on the `ZMod p` side — you cannot meet in the
  middle.** `ZMod64 p` has no Mathlib `AddCommMonoid`, so a `Finset.antidiagonal`
  sum (and `HexPolyMathlib.toPolynomial`, which needs Mathlib `Semiring`) does
  **not** typecheck over `ZMod64`; the furthest multiplication form expressible
  over `ZMod64` is the diagonal *List.foldl* of `Hex.DensePoly.mulCoeffSum_eq_diagonal`
  (`HexPoly/Euclid.lean`, over `Lean.Grind.CommRing`). Recipe for
  `toZMod (mulCoeffSum f g n) = ∑ x ∈ Finset.antidiagonal n, …`: (1) rewrite to
  the diagonal fold; (2) a small induction `toZMod ((range m).foldl (·+·) 0) =
  ∑ i ∈ range m, toZMod (term i)` via `toZMod_add` + `Finset.sum_range_succ`
  (state it abstractly over `term : Nat → ZMod64 p`, see next bullet); (3)
  `toZMod` the per-term `if`-guard via `toZMod_zero`/`toZMod_mul`; (4) match the
  `f.size` range against `range (n+1)` through a `max`-bridge `Finset.sum_subset`
  (terms vanish by support / degree guard) and finish with
  `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, mirroring
  `HexPolyMathlib.toPolynomial_mul`. (Landed: `HexBerlekampMathlib.fpPolyEquiv`,
  #7729.)
- **The `coeff_*_semiring` instance-path mismatch also bites `mulCoeffSum` and
  `mulCoeffSum_eq_diagonal`.** A `mulCoeffSum f g n` you write in an
  `FpPoly`-context goal carries ZMod64-direct `Add`/`Mul`; the
  `[Lean.Grind.CommRing]` lemma `mulCoeffSum_eq_diagonal` carries the
  CommRing-derived ones, so `rw [mulCoeffSum_eq_diagonal …]` reports "did not
  find pattern" on a goal that visibly contains the term. Fix: bind the equation
  through a `have hdiag : <state with the goal's instances> :=
  mulCoeffSum_eq_diagonal f g n` (the proof unifies the instances by defeq during
  elaboration), then `rw [hdiag]`. Same trick for any `[Grind.CommRing]`-stated
  `DensePoly` lemma applied to an `FpPoly` goal. `exact` (defeq-tolerant) needs
  no such wrapper, so per-term closers like `exact toZMod_diagonalMulCoeffTerm …`
  match through the instance gap directly.
- **No `map_neg` / `map_one` / `map_zero` / `map_dvd` on `ZMod64`/`FpPoly`.**
  These need `ZeroHomClass`/`AddMonoidHomClass`/`Monoid` that the executable
  types don't have. To compute e.g. `toZMod (-1) = -1`: prove `(-1)+1 = 0` in
  `ZMod64` by `grind`, push through `toZMod_add`/`toZMod_one`/`toZMod_zero`
  (the real bridge lemmas), and finish in `ZMod p` with
  `eq_neg_of_add_eq_zero_left`.
- **`FpPoly`/`DensePoly` `∣` is custom** (`a ∣ b := ∃ r, b = a * r`), so
  `map_dvd` does not apply and `dvd_trans` is replaced by `fpPoly_dvd_trans`.
  Transport divisibility to Mathlib by destructuring and re-multiplying:
  `obtain ⟨r, hr⟩ := h; ⟨toMathlibPolynomial r, by rw [hr, toMathlibPolynomial_mul]⟩`.
  (`HexBerlekampZassenhausMathlib/Basic.lean` exposes `toMathlibPolynomial_dvd`
  and `self_dvd_monicModPImage` for exactly this.)
- **`ZPoly = DensePoly Int` ring identities: `grind` is unreliable; use the
  `equiv`/`toPolynomial` bridge.** `grind` is advertised for `ZMod64`/`FpPoly`
  arithmetic, but on `ZPoly` it *fails* on basics like `factor * 0 = 0` and
  `p * C c = C c * p` (commutativity) — the `Lean.Grind.CommRing` facts it
  needs are not all reachable. Prove such equalities by
  `apply HexPolyZMathlib.equiv.injective` then
  `rw [HexPolyZMathlib.equiv_apply, …, HexPolyZMathlib.toPolynomial_mul,
  HexPolyZMathlib.toPolynomial_C]` and finish with `ring` in `Polynomial ℤ`
  (which *does* have the Mathlib `CommRing`). For ZPoly self-divisibility
  `p ∣ p`, `dvd_refl` does not apply (custom `Dvd`); use
  `Hex.DensePoly.dvd_refl_poly` (`HexPoly/Euclid.lean`). Note `primitivePart`
  divides by the *nonnegative* content and does **not** sign-normalize
  (`primitivePart_eq_self_of_primitive` holds for any-sign primitive), so a
  `primitivePart (dilate (lc core) g) = factor` goal needs both
  `0 < leadingCoeff factor` (from `normalizeFactorSign factor = factor`) *and*
  `0 < leadingCoeff core` — the latter is a genuine extra hypothesis, not
  derivable from sign-normalising the factor (see #7365).
- **`ZMod64` zero has two representations** (`Zero.zero` vs `OfNat 0`); a `rw`
  on `toZMod 0` / `(0 : FpPoly).coeff n` may report "did not find pattern" or
  leave an unclosed `0 = 0`. Close with `exact`/`show` (defeq-tolerant), not
  `rw`/`simp`.
- **`HexPolyMathlib.toPolynomial` vs `HexPolyZMathlib.toPolynomial`:**
  `HexPolyZMathlib.toPolynomial` is an `abbrev` specializing the general
  `HexPolyMathlib.toPolynomial` to `R = Int`. They are defeq but **not
  syntactically equal**, so `rw [hk]` fails when `hk` was produced by a
  `HexPolyMathlib`-namespace lemma against a `HexPolyZMathlib` goal. This also
  bites when you `rw` the lemma *directly* (e.g.
  `rw [← HexPolyMathlib.leadingCoeff_toPolynomial]`): the chained rewrite
  leaves a `HexPolyMathlib.toPolynomial` term that a later
  `rw [hg_toPolynomial : HexPolyZMathlib.toPolynomial g = …]` then cannot
  match. Bind the result with an explicit `HexPolyZMathlib.toPolynomial …`
  type ascription first (`have hlc : (HexPolyZMathlib.toPolynomial g).leadingCoeff
  = … := HexPolyMathlib.leadingCoeff_toPolynomial g`), then `rw [← hlc, …]`.

## Proving *inside* the Mathlib-free files

Lemmas that live in the executable files themselves (`HexPoly/*`,
`HexPolyZ/*`, `HexBerlekampZassenhaus/Basic.lean`) cannot use Mathlib tactics
or `Monoid`/`CommRing` lemmas — those modules don't import Mathlib.

- **`by_contra`, `ring`, `omega`-via-Mathlib are out.** `by_contra` reports
  "unknown tactic"; replace with `rcases Nat.eq_zero_or_pos n` or
  `rcases Nat.lt_trichotomy a b`. `omega`/`simp`/`rcases`/`conv` are core and
  available.
- **Integer `^` has no `pow_add`/`pow_succ`/`pow_one`/`one_pow` (Mathlib).**
  Use `Lean.Grind.Semiring.pow_succ` (`a^(n+1) = a^n * a`) and
  `Lean.Grind.Semiring.pow_zero`; `Int.one_pow`, `Int.mul_assoc`,
  `Int.mul_comm`, `Int.mul_zero`, `Int.one_mul` are core and fine. For
  `a^(m+k) = a^m * a^k`, write a one-line induction on `k` with `pow_succ`.
- **`omega` does not see through `Int.ofNat`.** It normalizes the `↑n` /
  `Nat.cast` coercion but treats the explicit constructor `Int.ofNat n` as an
  opaque atom — so `0 ≤ Int.ofNat n` and `Int.ofNat n.natAbs = n` (with
  `0 < n`) both fail with a bogus counterexample. `content`/`contentNat`
  (`HexPoly/Euclid.lean`) are defined via `Int.ofNat`, so Gauss/content proofs
  hit this. Either restate the goal as `(n : Int)` (Nat.cast, which `omega`
  handles) and close by `exact` up to defeq, or use core lemmas directly:
  `Int.natAbs_of_nonneg`, `Int.mul_pos`, `Nat.pos_of_ne_zero`. Note
  `Int.ofNat_pos` does **not** exist.
- **Array/List core lemma names differ from intuition:** the lemma for
  `(l.toArray).toList = l` is `List.toList_toArray` (not `Array.toList_toArray`).
  For `(xs.push a).getD`, `HexBerlekampZassenhaus/Basic.lean` already has
  `array_getD_push_lt`/`array_getD_push_size`/`array_toList_getD` — reuse them.

## Signature gotcha

A hypothesis whose type mentions `toMathlibPolynomial`/`monicModPImage`/`modP`
at `primeData.p` is elaborated **before** any `letI := primeData.bounds`, so an
implicit `[Bounds primeData.p]` cannot be synthesized and the type silently
becomes `sorry`. Write the instance explicitly in such signatures:
`@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds (…)`.

## `Nat.choose` / `Nat.Prime` resolve to the executable shadows inside `Hex`

The Mathlib-free arithmetic layer defines its own `Hex.Nat.choose` (Pascal
recursion, `HexArith/Nat/Prime.lean`) and `Hex.Nat.Prime`. So a `def` written
inside `namespace Hex` (e.g. `bhksCoeffBound = Nat.choose (n-1) j * …` in
`HexBerlekampZassenhaus/Basic.lean`) elaborates `Nat.choose` to
**`Hex.Nat.choose`**, NOT Mathlib's `Nat.choose` — even though they are the
same recursion. Symptom in the Mathlib layer: `rfl`/`simp [theDef]` against a
RHS you wrote with dot-notation `(n-1).choose j` (= Mathlib `Nat.choose`) fails
with a "type mismatch" or "unsolved goal" whose two sides look identical except
one reads `Hex.Nat.choose`. The fix is a one-line bridge proved by induction on
the shared recurrence, e.g.

```lean
theorem hex_choose_eq (n k : Nat) : Hex.Nat.choose n k = Nat.choose n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih => cases k with
    | zero => simp
    | succ k => rw [Hex.Nat.choose_succ_succ, Nat.choose_succ_succ, ih, ih]
```

then `simp_rw [hex_choose_eq]` before reaching for any Mathlib `Nat.choose`
lemma (`Nat.sum_range_choose`, etc.). Same pattern for `Hex.Nat.Prime`.

## Fast-BHKS raw irreducibility ≠ slow-path raw irreducibility (scheduled-loop determinism)

The slow-path raw irreducibility (`slowModularRaw_irreducible_of_fast_none`,
#7665) is *unconditional* because the slow path runs a single fixed-precision
`exhaustiveCoreFactorsWithBound` at `exhaustiveLiftBound` — one deterministic
array, so `hraw : … = some rawFactors` pins it directly and the irreducibility
producer applies at that one precision. **Do not assume the fast path is the same
shape.** `factorFastCoreWithBound` is a *schedule loop* (`Basic.lean:6935`): it
starts at `Hex.initialHenselPrecision a`, walks `henselPrecisionSchedule`, and
returns the array of the **first** precision where `bhksRecoverClassified`
returns `.success`. A `ForwardRecoveryInputs` package sits at the cap `target`
(the *last* schedule element), so the loop's actual output need not equal the
package's `expectedFactors` — an earlier schedule precision could exit `.success`
with a different array.

Consequences for any fast-BHKS irreducibility / `h_raw` work:

- The existing `factorFastCore*_of_forwardInputs` wrappers force loop-start =
  package precision = cut precision (the same `k`). They **cannot** apply to the
  executable run, where `start = initialHenselPrecision a ≠ target = cap`. Use
  the decoupled `…_of_forwardInputs_on_schedule` wrappers
  (`PartitionRefinement.lean`, #7666): the count argument routes through
  `factorFastCoreWithBound_some_factor_count_eq_of_cut`, whose loop-result params
  (`k`,`fuel`) and cut-precision param (`L`) are already independent.
- Those decoupled wrappers still take `h : factorFastCoreWithBound core B
  primeData start fuel = some hinputs.expectedFactors` as a hypothesis. Producing
  that `h` for the real `start = initialHenselPrecision a` is the **scheduled-loop
  determinism obligation** (loop's first success returns the cap recovery). It is
  *not* derivable from the cap package: `factorFastCoreWithBound_isSome_of_
  recovery_on_schedule` (`Basic.lean:7105`) proves existence, not factor
  identity, and `bhksRecoverClassified_success_*` (`Basic.lean:11238-11322`) give
  product/dvd/sign for any success but neither irreducibility nor equality to the
  cap recovery. Closing it needs "recovery fails below the Mignotte precision" (a
  BHKS precision-soundness theorem) or a universal "recovery success ⟹ irreducible
  at arbitrary precision" — neither is in the tree. Before claiming a fast-BHKS
  "expose the loop array" / unconditional `h_raw` issue, confirm a determinism
  producer exists, else land the decoupled bridges + diagnose (#7664).

## `Matrix` / `Vector` resolve to Mathlib's inside the Mathlib layer

The mirror of the shadow above. In a Mathlib-layer file (namespace
`HexBerlekampZassenhausMathlib.*`, importing Mathlib), bare `Matrix`/`Vector`
resolve to **Mathlib's** `Matrix` (index *types*) / `Vector`, NOT the
executable `Hex.Matrix Int n m` (Nat-indexed dense rows) / `Hex.Vector`. When a
lemma signature must name an executable matrix — e.g. the reduced BHKS basis
fed to `Hex.bhksCutPrefixCount` — write `Hex.Matrix Int n m` and
`Hex.Vector.normSq` explicitly. Symptom of getting it wrong: a type-mismatch on
the dimension argument, `L.factorCount + L.coeffWidth` "has type ℕ … of sort
outParam Type but is expected to have type Type", because Mathlib's `Matrix`
wants its first two arguments to be index types, not `Nat`.

## The Mathlib layer *models* executable definitions

The bridge does not just prove lemmas about the executable types; it carries
**model definitions that mirror the shape of executable functions** —
e.g. `scaledRecombinationCandidate` / `scaledLiftedFactorProduct` /
`RepresentsIntegerFactorAtLift` (`HexBerlekampZassenhausMathlib/Basic.lean`)
mirror the per-step candidate built inside `Hex.scaledRecombinationSearchModAux`
/ `bhksIndicatorCandidate?`. Before changing an executable definition's *shape*
(the candidate expression, the recombination target, the lift transform),
grep the Mathlib layer for proofs that `unfold` it or restate its body, and
size that surface first — it is often far larger than the executable proofs.

Two directions behave very differently under such a change:

- **Product / divisibility direction survives.** Proofs like `*_product` rest
  on the `exactQuotient? target candidate` recursion, which is blind to how the
  candidate was built, so they need only mechanical `let`-expression updates
  (mirror the new candidate text) — never a new argument.
- **Recovery / coverage direction does not.** Proofs that identify the emitted
  candidate against an expected factor (the `RepresentsIntegerFactorAtLift`
  recovery chain, the coverage proof in `Basic.lean`) *encode* the old shape;
  changing it is a structural remodel needing new math, not a token swap. These
  feed the still-`sorry` headline `factor_irreducible_of_nonUnit`, but they are
  proven (not sorried) lemmas, so they must still compile.

Consequence: a soundness fix to the executable recombination is **not**
independently landable green — the executable change and the Mathlib remodel
must land in one PR. Scope accordingly (see #6799 / #6801 for the
`DensePoly.scale` → `ZPoly.dilate` example).

**Build the target module first to get the real in-scope error set — it is
usually a handful of errors, not the whole conceptual chain.** Before hand-
tracing a scale→dilate (or similar) cascade through dozens of wrapper
theorems, run `lake build HexBerlekampZassenhausMathlib.<Module>` and grep the
log for `error:`. A conceptually huge cascade often surfaces as only 2-3 red
declarations, because most wrappers typecheck against the *signature* of a
broken callee and only the body fails. Separate the in-scope errors from any
known out-of-scope group (e.g. the #7122 `factorFast_ne_none_of_forwardInputs_on_schedule`
heartbeat/unknown-constant cluster) up front, then read only what those few
errors touch. This right-sizes the work and avoids burning context reading
wrappers that already compile.

**Size the migration before deep-reading proofs.** When a predicate like
`RepresentsIntegerFactorAtLift` flips from being *defeq* to a recovery equality
(e.g. the scaled `reduceModPow` congruence) to wrapping a *structure*
(`Nonempty (RecoveredAtLift …)`), every consumer that fed `hrep` into a recovery
lemma breaks, and the dilate bridge (`RecoveredAtLift.candidate_eq_of_monic_dvd`)
needs a *different precision/bound model* than the consumers carry — the bound
moves from the factor to the monic-coordinate witness (`(toMonic core).monic`),
plus `hmonic_ne` / `hfactor_norm`. That new hypothesis cascades through every
caller up to the top driver (where `(toMonic core).monic = core` collapses it).
So before sinking a session into per-theorem reads: for each erroring consumer,
`grep -n "<name>_of_bound\b"` the **caller fan-out**. If a forced signature
change hits more than a handful of callers (each re-cascading), it is a
multi-session remodel with no intermediate green state — land the cascade-free
fixes (e.g. a `2 ≤ d.p^k` derivable straight from precision +
`defaultFactorCoeffBound_pos_of_ne_zero`, not from a recovery lemma), then
partial + scope the rest in one accurately-sized follow-up rather than
attempting the whole cascade blind. Watch for a hidden soundness signal too:
the new `RecoveredAtLift.dilate_eq` carries no `normalizeFactorSign`, so a
`0 < leadingCoeff factor` conclusion is only valid for sign-normalised factors —
the consumer must gain `hfactor_norm`, which callers do supply.

When you reroute the broken scale-model consumers off the removed scale
congruence, **do not target the `hdilated` exact-equality chain**
(`candidatesOfDilatedCenteredLift` / `ofMignottePrecisionCandidateProducts`),
even though the issue body may name it. That chain's `hdilated` wants the
*exact* `dilate (lc f) (centeredLiftPoly …) = expectedFactor` with **no**
`primitivePart`, but `RecoveredAtLift.dilate_eq` only ever gives the
`primitivePart (dilate (lc core) monicFactor) = factor` form, and that
`primitivePart` is load-bearing: `coeff_dilate` is `coeff n = c^n · p.coeff n`
(`HexPolyZ/Basic.lean:70`), so `dilate 4 (x+2) = 4·x + 2` has `content = 2`.
Hence `content (dilate (lc core) monicFactor) = 1` is **false** whenever
`leadingCoeff core` is a non-unit — i.e. the generic non-monic-core regime the
monic transform exists for. Reroute to the primitivePart-aware
`liftedRecoveryCandidate` / `RecoveredAtLift.candidate_eq_of_monic_dvd`
(`Basic.lean:2781`) path instead. Note the linchpin: the base `RecoveredAtLift`
producer from a successful `bhksIndicatorCandidate?` is the carrier the whole
reroute consumes. For the **monic-core** case it now exists and compiles —
`bhksIndicatorCandidate?_representsIntegerFactorAtLift` (`Recovery.lean:1125`,
landed by #7121 deliverable 1 / PR #7196): with `leadingCoeff core = 1` it sets
`monicFactor := candidate` and closes all four fields from
`bhksIndicatorCandidate?_reduceModPow_eq_of_monic` (`congr`, via `scale 1 = id`),
`dilate_one` + `Hex.bhksIndicatorCandidate?_primitive` (`dilate_eq`), and
`Hex.bhksIndicatorCandidate?_dvd` + `toMonic_monic_eq_core_of_leadingCoeff_eq_one`
(`monic_dvd`). The two executable lemmas were `private`; #7196 drops that. So a
scale→dilate **consumer** reroute is no longer blocked on a missing producer —
it is blocked on the cascade work itself (rerouting
`productCongruence_of_representsIntegerFactorAtLift` and the `productCongruences*`
chain consumed at `Recovery.lean:4075`, the `hproduct`/`product_congr`
scale-congruence in `ForwardRecoveryInputs.ofMignottePrecision…` /
`CanonicalRecoveryInputs`, and IntReductionMod's `scaled_recovery_of_bound`, all
of which force `hmonic_ne`/`hfactor_norm`/`hprecision` up to the top driver).
The **non-monic-core** producer (where `primitivePart`/`dilate` do not collapse)
is still the harder monic-transform recovery direction owned by the
fast-BHKS-monic-lift migration issue.

### "Final integration" issues: confirm the substrate *producer* exists, not just that the feeder issue closed

A `feature` issue that says "instantiate `SlowPathHenselSubstrate` / `…Evidence`
constructed by the prerequisite issues" is only a token-swap if a theorem
*concludes* that structure. A closed feeder issue does **not** prove its
producer landed: these substrate issues are sometimes closed COMPLETED on a
replan-triage comment whose claim contradicts the source (e.g. #6773 was closed
asserting `liftedFactorSubsetPartition_of_choosePrimeData` "does not assume" the
evidence, but it takes `hinitial : InitialLiftedFactorSubsetPartitionEvidence`
as a hypothesis and only projects fields out of it). Before claiming such an
integration, grep for an actual producer: `grep -rn ": <StructureName>"` should
find a `theorem … : <StructureName> …` whose body builds it (or a `{ field := … }`
literal), not just `(h : <StructureName>)` binders and `…_fields h` projections.
If every occurrence is a hypothesis or destructor, the substrate is unproduced —
diagnose on the issue (per the CLAUDE.md "Directives are hypotheses" rule) and
`coordination skip` rather than attempting the integration. Substrate producers
still missing as of this writing: `HenselLiftDescentHypotheses` and the
`toMonicLiftData` modP→lift transport. `InitialLiftedFactorSubsetPartitionEvidence`
now *has* one — `initialLiftedFactorSubsetPartitionEvidence_of_toMonicChoosePrimeData`
(`IntReductionMod.lean`, #7362). Note where it landed: not next to its natural
consumer (`slowPathHenselSubstrate_*` in `Basic.lean`) but downstream in
`IntReductionMod.lean`, because its `pairwise_disjoint` field needs the mod-`p`
squarefreeness datum (`modPFactorSubset_disjoint_of_choosePrimeData` /
`squarefree_toMathlibPolynomial_monicModPImage_of_choosePrimeData`) that lives
there, below `Basic.lean`. Building a producer whose fields straddle this boundary
forces it into the lowest file that sees every datum, which in turn forces
de-privatising any `private` `Basic.lean` helpers it calls (visibility-only, safe).
Wiring it back up into the upstream slow-path substrate is a separate follow-up
(the substrate cannot import downstream modules). That follow-up landed (#7584):
`IntReductionMod.lean` now carries carrier-free toMonic producers that need only a
`toMonicPrimeData?` selection witness plus core facts (lc>0, deg>0, primitive,
squarefree, B≠0, the monic-correspondent bound) — `liftedFactorSubsetPartition_of_toMonicPrimeData_complete`
and `slowPathHenselSubstrate_of_toMonicPrimeData`, both discharging `hinitial` via
the #7362 producer above and `hcorr` via the new Basic.lean
`henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData` (the carrier-free
correspondence: at `True True`, `MonicDescentHypotheses`' only consumed fields
`lift_eq`/`successful_lift` are `rfl`/`trivial`, so no descent carrier is needed —
there is still no `MonicDescentHypotheses` *producer*, but the partition/substrate
chain no longer needs one). So when wiring #6771/#7561, **do not re-derive these** —
consume `slowPathHenselSubstrate_of_toMonicPrimeData` / `…_complete` directly. They
have no in-tree consumer yet; the slow-exhaustive branch
(`liftedFactorSubsetPartition_outerBound_of_choosePrimeData`) is keyed on the
different `choosePrimeData? squareFreeCore` selection, not `toMonicPrimeData?`.

A distinct, sharper failure mode than "no producer": the hypothesis the
directive asks you to *produce* is not merely unproduced but **provably false**,
so no producer can ever exist. The recurring instance is the bare lift-coverage
quantifier `hexists_lifted` / `HenselSubsetCorrespondenceRest.exists_subset`
(`Basic.lean:3325`, inherited by `LiftedFactorSubsetPartition` at
`Basic.lean:3460`): `∀ {factor}, Irreducible (toPolynomial factor) → factor ∣
core → ∃ S, RepresentsIntegerFactorAtLift core d factor S`. This universal is
**unsatisfiable** under the standard core side conditions, because
`normalizeFactorSign_eq_of_representsAtLift` (`Basic.lean:13646`) proves every
*represented* factor is sign-normalized (`normalizeFactorSign factor = factor`,
i.e. `0 ≤ leadingCoeff factor`) given `hcore_lc_pos`, monic lifted factors, and
the precision bound — all of which are the substrate's own hypotheses
(`hbound`/`hcore_lc_pos`, + `toMonicLiftData_liftedFactor_monic_*`). So any
negative-leading-coefficient irreducible divisor (e.g. `1−x ∣ x²−1`, with
`toPolynomial` `1−X` irreducible) has **no** representing subset, and the bare
`∀`-factor existence is false for every positive-degree core. The landed
recovery producer `toMonicLiftData_represents_lifted_of_modP` (`Basic.lean:19885`)
matches this exactly — it only covers factors carrying
`hsign : normalizeFactorSign factor = factor`. **Before attempting any
"produce the coverage hypothesis from core facts" issue, sanity-check the factor
quantifier: if it ranges over all irreducible factors with no sign guard, it is
unsatisfiable — diagnose (counterexample + the `normalizeFactorSign_eq_of_*`
cite) and skip.** The sound fix is a structural narrowing of the `exists_subset`
quantifier to `normalizeFactorSign factor = factor` across the
`HenselSubsetCorrespondence*` / `LiftedFactorSubsetPartition` structures, which
is a shared-`Prop` refactor, not a core-facts assembly. (#7550 was skipped on
exactly this.)

The same check applies one level down to a "reduce X via the existing
`*_of_recovery` lemmas" directive: the named recovery lemma existing is not
enough — verify its *hypotheses* are obtainable from the representation predicate
in scope. The scaled chain is the trap. `scaledRecombinationCandidate` is
**scale-based** (`scale lc q = lc·q`) while `RepresentsIntegerFactorAtLift` /
`RecoveredAtLift` carry only the **dilate** recovery (`dilate lc q` has
`coeff n = lc^n·q.coeff n` — deliberately *not* `scale`, `HexPolyZ/Basic.lean:63`).
Every `scaledRecombinationCandidate_eq_factor_of_recovery` lemma needs
`hscaled : reduceModPow (scaledLiftedFactorProduct …) = reduceModPow factor` as a
hypothesis, and **nothing produces it** (`grep` finds `scaledLiftedFactorProduct
… reduceModPow` only in hypothesis position). So a non-circular scaled support
field (`support_subset_of_dvd_scaledRecombinationCandidate`) cannot be built as a
thin wrapper over the lifted-product support theorem — the dilate carrier feeds
the dilate reflection (`toPolynomial_dvd_of_primitivePart_dilate_dvd`, monic-only)
but not the scaled candidate. Mod p the obstruction is the dilation automorphism
`σ : q(x) ↦ q(lc·x)`: `f ~ σ(lfp S)` but the scaled candidate `~ lfp T`, and the
clean half needs the undilated `lfp S ∣ lfp T`. This was #7479 deliverable 2;
the dilate equality/support wrappers (deliverables 1/3, #7491 / `toMonicLiftData_
liftedRecoveryCandidate_eq`) are the unblocked ones.

The same #7479 gap is what currently blocks the **whole slow-modular toMonic
capstone** (#7561 / `factorSlowModularFactorsWithBound_factor_irreducible_of_fast_none`):
its irreducibility producer needs a `LiftedFactorSubsetPartition core d Finset.univ
core`, whose required field `support_subset_of_dvd_recombinationCandidate`
(`Basic.lean:3547`) is the **unscaled** support `S ⊆ T` over
`liftedFactorProductCandidate` (`Basic.lean:2527`). *Every* partition producer
(`Basic.lean:17918/19131/20790`, `IntReductionMod.lean:3102`) takes it as the
open `hunscaled` hypothesis; the only landed `S ⊆ T` lemma
(`toMonicLiftData_subset_of_dvd_liftedRecoveryCandidate`) is over the **scaled**
`liftedRecoveryCandidate` (`Basic.lean:2540`), which coincides with the unscaled
one **only at `leadingCoeff core = 1`** (`liftedRecoveryCandidate.eq_productCandidate_of_lc_one`)
— and the re-key runs on non-monic cores. Disambiguation for #7561's Notes: the
`MonicDescentHypotheses` / `hexists_lifted` adapter is **not** the blocker — `hcorr`
and `hinitial` are producible from core facts now
(`henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData_success_descent`,
`initialLiftedFactorSubsetPartitionEvidence_of_toMonicChoosePrimeData`), and the
heavy `descends` field is not consumed when building the correspondence (only
`lift_eq = rfl` / `successful_lift = trivial`). Land the unscaled-support
producer first, then #7561 is the thin composition.

**But "no producer" only blocks a transport that genuinely needs a bridge
between two concrete defs.** Before skipping a `henselLiftData → toMonicLiftData`
(or similar) transport, check whether the consumer chain is *generic in the
`LiftData`*: if the structure/lemma you feed (`ForwardRecoveryInputs f d`,
`bhksRecover_eq_some_of_forwardInputs f d h`) quantifies over an arbitrary
`d : Hex.LiftData`, no bridge is needed — you just **restate** the Mathlib-side
theorem over whichever lift data the executable consumer already uses (grep the
executable consumer's `hrecover`/`hd` hypothesis for the concrete def it
expects). #7122 was exactly this: the five concrete `henselLiftData` sites in
`Recovery.lean` swapped to `toMonicLiftData` with no bridge, because everything
downstream routes through a `private abbrev` (`factorFastCapLiftData`) that is
never unfolded. Confirm genericity by grepping that the feeder takes
`(d : Hex.LiftData)` as a parameter, not a fixed `henselLiftData …`.

### Applying a `henselLiftData`-form lemma to a `toMonicLiftData` goal

`Hex.ZPoly.toMonicLiftData core B primeData` is **definitionally**
`Hex.henselLiftData (toMonic core).monic (precisionForCoeffBound B primeData.p)
primeData`, but **not syntactically equal** — `toMonicLiftData` is a plain
(non-reducible) `def`. So the cluster of `henselLiftData_*` lemmas
(`_liftedSubset_complement_isCoprime_mod_p`, `_liftedFactor_modP_eq_modPFactor`,
`_liftedFactors_size_eq`, …) does not match a `toMonicLiftData` goal under `rw`,
`subst`, or `simp` keyed matching, even though `exact`/`convert` will eventually
unify via `isDefEq`. Recipe that works:

- **Restate the goal in `henselLiftData` form with `show`** (set
  `monicCore := (toMonic core).monic`, `precision := precisionForCoeffBound B
  primeData.p` first), then every `henselLiftData_*` lemma and every
  `liftedSubsetOfModPSubset`/`hsize` rewrite applies syntactically. `set d :=
  toMonicLiftData …` does **not** help — it does not fold the goal's
  `toMonicLiftData` occurrences, and a later `rw [← hS]`/`subst hS` then fails
  with "did not find pattern" / leaves the goal untouched.
- **Never `set d := toMonicLiftData …` when `d` appears in a hypothesis/goal
  TYPE** (`S T : LiftedFactorSubset d`, `hrep : RepresentsIntegerFactorAtLift
  core d f S`). `set` reverts and reintroduces those, renaming `S`/`T` to
  inaccessible `S✝`/`T✝`, so your later `S`/`T` references mismatch
  (`… core (toMonicLiftData …) S✝ … but expected … core d S`). Worse, the
  let-bound `d` makes every later `LiftData`-projection defeq unfold `d` and
  evaluate the expensive `liftedFactors` field, blowing the `whnf` heartbeat
  limit (the error surfaces as a "(deterministic) timeout at `whnf`" pinned to
  the declaration's first line, *masking* the real type mismatches until you
  raise `maxHeartbeats`). Write the `toMonicLiftData core B primeData` term out
  explicitly so all defeqs stay syntactic. A value-level `set lc :=
  leadingCoeff core` / `set pk := (toMonicLiftData …).p ^ (toMonicLiftData …).k`
  is fine (no dependent types, no `liftedFactors` eval).
- **Prove `.p`/`.k` projections of `toMonicLiftData` via `unfold`, not `rfl`
  or `simp`.** `have hp : (toMonicLiftData core B primeData).p = primeData.p :=
  by unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _`
  (likewise `henselLiftData_k`). Bare `rfl` forces a `whnf` of the whole
  structure (heartbeat blowup); `simp [Hex.ZPoly.toMonicLiftData]` unfolds the
  `liftedFactors`/`multifactorLiftQuadratic` field and tries to normalise it
  (same blowup).
- **Defeq `liftedFactor` rewrite:** `liftedFactor (toMonicLiftData …) i =
  liftedFactor (henselLiftData monicCore precision …) (liftedIndexOfModPIndex …
  ⟨i.val, _⟩)` holds by `rfl`. Use a `calc` with explicit terms rather than
  `rw [← toMathlibPolynomial_modP_eq_map_intCast_zmod]` — the backward rewrite
  builds a `toMathlibPolynomial`-at-inferred-`p` motive that is not type
  correct.
- **Transport a `Fin` bound across the size eq at the `Nat` level**, never by
  rewriting the size inside the `<`: `i.isLt.trans_eq
  (henselLiftData_liftedFactors_size_eq monicCore precision primeData) :
  i.val < primeData.factorsModP.size`. Rewriting the size in `i.isLt` directly
  fails with "motive is not type correct" because `↑i`'s type depends on it.
- The invariant inputs (`QuadraticMultifactorLiftInvariant`, `factorsModP`
  monic/irreducible/nodup/product-congr) discharge from `toMonicPrimeData? core =
  some primeData` by the block in
  `Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData` — copy it
  (`toMonicPrimeData?_factorsModP_berlekamp_form` /`_isGoodPrime` /`_prime`,
  then `factorsModP_*_of_factorsModPBerlekampForm` and
  `QuadraticMultifactorLiftInvariant_of_choosePrimeData`).

## The Mathlib layer is not CI-built — establish a baseline first

CI builds only bench + conformance targets (`ci.yml`, `conformance.yml`);
it does **not** build `HexBerlekampZassenhausMathlib`. So that layer can be
**hard-red on main** — a real elaboration error, not just the known
`sorry`s — whenever an executable→Mathlib split is mid-flight (e.g. the
dilation remodel left `Basic.lean` failing at `:15990` while #6804/#6772 were
open), and merges keep flowing because nothing gates it.

Because nothing gates it, a green CI rollup does **not** mean a Mathlib-layer
file compiles — a reviewer of such a PR must build it locally to verify it at
all. A fresh worktree has no built Mathlib, so run `lake exe cache get` first
(fetches prebuilt oleans in minutes; a from-scratch Mathlib compile is hours).
Only the project's own files then rebuild.

When you verify against a Mathlib-layer module with a throwaway scratch file
(`lake env lean Scratch.lean` importing e.g. `HexBerlekampZassenhausMathlib.Lattice`),
`lake env lean` loads that import's **prebuilt olean**, not its source. A
reused worktree's olean can predate decls added in later commits, so a
genuinely-present definition shows as `unknown identifier` (and autoImplicit
then treats it as a free variable, cascading confusing errors) even though the
source clearly declares it — fully-qualifying the name does not help. Before
blaming a namespace, `ls -la` the module's `.olean` under `.lake/build/lib/` and
check its mtime against the source: if stale, `lake build <Module>` to refresh
it, then re-run the scratch verifier. Delete the scratch file before finishing.

Before attributing a Mathlib-layer build failure to your own change, build the
**unmodified** target on a clean tree to get a red/green baseline
(`lake build HexBerlekampZassenhausMathlib.<Module>`), and `git diff origin/main
-- <file>` to confirm the failing file is untouched by you. When you capture
that build with `| tee <log>`, the pipeline's exit status is `tee`'s, so a
`run_in_background` completion notification reports **exit 0 even on a failed
build** — judge red/green by grepping the log for `error:` / `build failed`,
never by the reported exit code. Grep only *after* the build has finished: a
still-running background build's log shows zero `error:` lines simply because
elaboration has not yet reached the broken file, so a premature grep reads
false-green. Wait for the `Built <target>` / process-exit signal (or an
`error: build failed` line) before concluding, and do not launch overlapping
`lake build`s to "confirm" — they serialize on the worktree lock and muddy
attribution. A faster
single-build attribution when your change is purely additive *within* the same
file: Lean reports every per-declaration error and keeps elaborating past a
failed declaration, so if the build log's only `error:` line numbers fall
**outside** the line range of your additions (a warning emitted *after* the
failing line but *before* your code confirms elaboration reached you), your
declarations compiled — no clean-tree rebuild needed. But that passive read
gives **no signal when the failing line is the highest line in the whole log**:
proof-only theorems emit no warning (only `sorry` does), so additions *below*
the pre-existing breakage produce no later diagnostic to confirm elaboration
even reached them. In that case add a temporary `#check @yourTheorem` probe
right after each addition and rebuild: if it prints the full type (an `info` at
that line), you have proved both that elaboration ran past the earlier errors
*and* that the theorem typechecks; if the name failed it errors "unknown
identifier" instead. Remove the probes before committing. This is the reliable
way to verify additive wrappers stranded in a file that is red from a separate
mid-flight migration (e.g. adding cap-bound wrappers to `Recovery.lean` while
its recovery-direction proofs are red from a partial monic-lift migration): the
full-module build never goes green, but the wrappers are still verifiably
correct, so land them and name the owning migration issue in the PR body. If
your target's
file (or a file it imports, like `Basic.lean`) is already red and your additions
*depend on* the broken declarations, they cannot be verified at all. Land the
parts that *do* build in isolation, and preserve the blocked parts (source in
the issue comment) for a follow-up gated on the remodel issue rather than
merging unverified Lean.

The inverse also bites: **fixing a red dependency unmasks pre-existing breakage
in files downstream of it.** If `Basic.lean` is red on main, every module that
imports it (`Recovery.lean`, `IntReductionMod.lean`, `PartitionRefinement.lean`)
is never reached by a full-target build — so a clean-`origin/main`
`lake build HexBerlekampZassenhausMathlib` is **not** a valid baseline for those
downstream files; it stops at `Basic.lean` and reports zero downstream errors
purely because elaboration never got there. When your PR makes `Basic.lean`
green, the full target proceeds and surfaces those downstream errors for the
first time — they look like regressions but are not. Confirm by grepping that
the failing downstream file uses none of the declarations your diff touched
(`grep -ln <changed-lemma-names> <downstream>.lean`) and that the error shapes
are internal to it (e.g. `unfold <unchanged-def>` failures, a kernel cascade on
some `…_ne_none_…` constant from a separate mid-flight migration). Then verify
your deliverable with the **module** build (`lake build
HexBerlekampZassenhausMathlib.Basic`), note the unmasked downstream breakage in
the PR body as pre-existing/out-of-scope (name the owning migration issue), and
do **not** try to fix it — that is a different issue's remodel.

## Pre-existing sorries

`HexBerlekampMathlib/Basic.lean` and `HexHenselMathlib/Correctness.lean` ship
`sorry`s (the `toMathlibPolynomial` coeff bridge etc.). Those warnings are not
from your file; building on them is the established project state. Only check
that *your added lines* are `sorry`/`axiom`/`native_decide`-free
(`git diff -U0 <file> | grep '^+' | grep -iE 'sorry|axiom|native_decide'`).

## Heartbeat timeouts in heavy assembly proofs

`maxHeartbeats` is a **per-declaration** budget, not per-tactic. In big proofs
over large terms (full Sylvester-of-products matrices, `degreeLT` reprs), a
`(deterministic) timeout at whnf`/`isDefEq`/`tactic execution` error names the
line where the *shared* budget hit zero — **not** the pathological tactic. Don't
restructure around the reported line first; it is usually a cheap `omega` or
`exact` that simply ran last.

- First remedy: `set_option maxHeartbeats 400000 in` on the declaration (the
  common Mathlib value; raise further only if needed). **Placement: the
  `set_option … in` line must come *before* the declaration's docstring, not
  between the `/-- … -/` and the `structure`/`def`/`theorem` keyword** — a doc
  comment binds to the declaration it is adjacent to, so the wrong order gives a
  parse error (`unexpected token 'set_option'; expected 'lemma'`). Order is
  `set_option … in` → `/-- doc -/` → `structure …`. Once the budget is large
  enough, the *real* error often surfaces (e.g. an inline `by omega` whose
  target type wasn't yet determined because it sat under `lt_of_le_of_lt _ (by
  omega)` — fix by giving the bound an explicitly-typed `have h2 : … := by
  omega` so its goal is fully concrete before `omega` runs). A timeout can also
  mask a genuine type mismatch the unifier is churning on (e.g. `isDefEq` trying
  to unify two distinct `LiftData`s over large terms); raising the budget lets
  the real `Application type mismatch` appear, so don't assume a timeout means
  "just needs more heartbeats." Conversely, if even a large budget (e.g.
  `1000000`, 5×) still times out at `whnf`/`isDefEq`, it is a genuine
  heavy-defeq problem, not a tight budget — stop raising and factor the heavy
  sub-step into a thin lemma instead.
- Swapping a reducible `abbrev` to a def that unfolds to a *larger* term can tip
  previously-green declarations over the budget without any logic change. #7122
  repointed a `private abbrev` from `henselLiftData core …` to
  `toMonicLiftData core …` (which unfolds to `henselLiftData (toMonic core).monic
  …`); three cap input *structures* whose field types whnf that lift via
  `projectedRowsOfLiftData … .factorCount` then needed `maxHeartbeats 1000000`
  (400k was not enough, 1M was). The structures' *consumers* elaborated fine at
  the default 200k — only the field-type elaboration of the structures
  themselves was on the boundary, so bump the structure defs, not the whole
  cascade.
- Keep the capstone thin: factor heavy sub-steps (column-formula computations,
  `repr` evaluations) into their own lemmas. Each gets a fresh budget, and the
  capstone only pays for delegating.
- A `let`/`set`-bound abbreviation of a huge term in the *goal or context* makes
  `omega` and defeq checks whnf that term — avoid binding the matrix; write it
  out or `clear_value` only when the value is genuinely unneeded downstream.

## Verifying executable-layer changes: build the module, not the target

`lake build HexBerlekampZassenhaus` (the whole target) drags in
`CrossCheck` (~11 min, external oracle) and `Conformance` (~2 min) — it is a
~15-minute build, not a fast check. For iterating on a lemma, verify the
specific module (`lake build HexBerlekampZassenhaus.Basic`,
`lake build HexPolyZ.Basic`); that elaborates your declarations in seconds and
is the real correctness signal for theorem-only additions, which never affect
the `#guard`/oracle steps. Run the full target once at the end.

Do **not** launch a second `lake build` in the same worktree while one is still
running its tail jobs — they serialize on lake's per-worktree build lock, so the
second just blocks and looks "stuck". (This machine also runs concurrent builds
from *other* pod worktrees; `pgrep lake` showing many processes is normal and
not your build.)

**Numerically checking executable behavior in a scratch file: `#eval`/`#guard`
inside a lake-built module, not `lake env lean Scratch.lean`.** To sanity-check a
premise by *running* the executable functions (e.g. comparing
`defaultFactorCoeffBound f` against `defaultFactorCoeffBound (toMonic core).monic`
to test a precision claim), be aware that any code path touching the `@[extern]`
arithmetic (`Hex.ZMod64.mul`, anything pulling in `choosePrimeData?` /
`factorSlowModularFactorsWithBound` / mod-`p` work) fails under the interpreter
with `Could not find native implementation of external declaration
'Hex.ZMod64.mul'`. The `--load-dynlib=.lake/build/lib/*.dylib` workaround then
dies on flat-namespace symbol errors (`symbol not found '_lp_Hex_Hex_ZMod64_mul'`)
— do not sink time into it. Two reliable routes: (1) restrict the scratch to the
*pure-integer* `ZPoly`/`Nat` ops (`defaultFactorCoeffBound`, `toMonic`,
`precisionForCoeffBound`, `coeffNormSq`), which need no extern and run fine under
`lake env lean Scratch.lean` — for a primitive squarefree `f`, `squareFreeCore f`
is `f`, so you can take `core := f` and avoid the modular `normalizeForFactor`
path entirely; (2) if you genuinely need the ZMod64 path, put the `#eval`/`#guard`
in a module the package builds (`precompileModules := true` is set, so build-time
`#eval` resolves the native symbols) rather than running a standalone file.

## The BHKS tight CLD column bound is an *aggregation* phenomenon, not per-factor

The tight `2·|col j| ≤ factorCount` estimate (BHKS Lemma 5.7, packaged as
`TightColumnBound` in `Lattice.lean`, consumed by `tightNormBound_of_lift`) is
**not** provable per-factor through `Hex.abs_cldCoeffs_le_bhksCoeffBound`. That
lemma is the *loose* bound `|cldCoeffs f p a gᵢ .getD j| ≤ bhksCoeffBound f j`;
the individual high-bit cuts `psiCut p a b ((cldQuotientMod f gᵢ p a).coeff j)`
are genuinely large (verified: `±7` for `f=(x-1)(x²+1)`, `p=5`, `a=4` with
`factorCount=3`, so `2·7=14 > 3`) and only become small after **cancellation
over the support sum**. Do not try to bound the column term-by-term.

Why the cancellation is exact: `TrueFactorLift.support_product_eq :
supportProduct L S = factor` uses the **raw** `Array.polyProduct` (no mod-`p^a`
reduction), so it forces `∏_{i∈S} gᵢ = factor` **exactly over ℤ**. The selected
lifted factors are therefore exact monic integer *divisors* of `f` (cofactor
`f/gᵢ` is a genuine integer polynomial), so the log-derivative identity
`Σ_{i∈S} phi(f, gᵢ) = phi(f, factor)` holds exactly (`phi f g = f·g'/g`), and the
per-factor coefficient bound routes through the **unconditional**
`BHKS.abs_phi_coeff_le_of_monic_factor` (`CLDColumnBound.lean`) — it discharges
its own Mahler hypothesis, unlike the conditional `abs_phi_coeff_le`. The carry
cancellation itself is `BHKS.two_mul_natAbs_sum_psiCut_le` (the BHKS 5.7 high-bit
estimate, landed by #7651's carry-core PR): feed it per-element exact ambient
residues (`centeredResiduePow p a (z i) = w i`) whose support sum is a small
integer (`|y| ≤ B`, `2B < p^b`). Sanity-check any "tight CLD column" directive
that points at `abs_cldCoeffs`: that is the loose route and will not close the
`factorCount` shape.
