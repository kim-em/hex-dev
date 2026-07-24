---
name: hex-lean-mathlib-boundary
description: Gotchas for the Mathlib-free/Mathlib boundary in HexBerlekampZassenhausMathlib and similar *Mathlib Lean layers (ZMod64, FpPoly, DensePoly, ZPoly). Read before proving lemmas that mix the executable types with Mathlib Polynomial / ZMod algebra, OR before adding/proving ANY lemma in the Mathlib-free executable layer (`HexBerlekampZassenhaus/`, `HexLLL/`, etc. — NOT the `*Mathlib` libs), where Mathlib tactics like `by_contra`/`push_neg`/`ring`/`set` and lemmas like `lt_of_lt_of_le` are unavailable (see "Proving inside the Mathlib-free files"), OR before verifying any change to a *Mathlib bridge file — `ci.yml` builds the whole `HexBerlekampZassenhausMathlib` library (and transitively `HexBerlekampMathlib`), so those layers are merge-gating and must stay green (see "The Mathlib layer IS CI-gated").
allowed-tools: Bash, Read, Grep, Glob
---

# Mathlib-free / Mathlib boundary in the hex Lean layers

## Repo-generation caveat (read first)

Parts of this skill describe an older incarnation of the BHKS Mathlib layer
(files like `Recovery.lean`/`TerminationBound.lean`/`BadVector.lean` with the
`SeparationHypotheses`/`BadVectorBridgeData` cluster). In the current tree
those were deleted (6bf20977, #8411) and the surviving `W ⊆ L'` half was
resurrected by #8519 into `SignatureClasses.lean`, `Lattice.lean`,
`CLDColumnBound.lean`, `Recovery.lean`, `PartitionRefinement.lean` (namespace
`HexBerlekampZassenhausMathlib.BHKS`), keyed on `Matrix.rowReduce`, `vecMul`,
and `lllNative`. Key #8519 facts that supersede older notes below:

- **The CLD lattice runs in the monic (`M2`) coordinate**:
  `bhksRecoverClassified` / `bhksSingleAllOnesPartition` build
  `bhksLatticeBasis (ZPoly.toMonic f).monic …`, and the lattice tier
  (`factorLatticeFactorsWithBound`) selects `ZPoly.toMonicPrimeData?` — so the
  toMonic partition producers (`liftedFactorSubsetPartition_of_toMonicPrimeData_complete`)
  and the monic-regime short-vector producer
  (`BHKS.supportShortVectorData_of_recoveredLift`, which needs
  `leadingCoeff f = 1`) apply directly. The standalone fast tier
  (`factorFastFactorsWithBound`) still selects `choosePrimeData?` and is a
  verification-guarded, decline-only heuristic for `lc ≢ 1 (mod p)`.
- **The fast-core acceptance floor is `bhksRecoveryFloor`** (CLD column adequacy
  `cldCoeffFloor` joined with both Mignotte bounds), so a
  `bhksRecoveryCoreWithBound` success carries `bhksRecoveryFloor core ≤ k'` — enough
  for the partition machinery AND `hsep`/`hthr` at the witness precision. The
  old "L'=W is cap-only" analysis (#7985-era) no longer applies to the
  `W ⊆ L'` direction: `normalizedFactors_card_le_bhksEquivalenceClassIndicators_size`
  (`LatticeTier.lean`) proves it at any floor-cleared precision.
- The cap (`latticePrecisionCap`) dominates every floor component by
  construction (`bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap`).

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
  **But `grind` only knows the ring *axioms*, not the *characteristic*:** it
  proves `x + 0 = x` and `0 * x = 0`, yet **fails** on char-`p` facts like
  `(1 : ZMod64 2) + 1 = 0`. For those, route through the canonical residue:
  `(1 : ZMod64 2) = ZMod64.ofNat 2 1` and `(0 : ZMod64 2) = ZMod64.ofNat 2 0`
  hold by `rfl`, so `apply ZMod64.ext_toNat; simp only [toNat_mul, toNat_add,
  toNat_ofNat]; decide` discharges any concrete `ZMod64 p` arithmetic
  (`toNat_mul`/`toNat_add`/`toNat_ofNat` are `@[simp, grind =]`, reducing the
  goal to a `Nat`-mod identity `decide`/`omega` closes). This is how the
  GF(2)-indicator facts `if b then 1 else 0` ↦ `*`=AND / `+`=XOR get proved
  (`HexGF2Mathlib.toFpPoly_mul`).
- **Promoting `@[simp]` → `@[simp, grind =]` (Phase 6 sweep): being a
  literal `lhs = rhs` is necessary but not sufficient.** `grind =` also
  needs the LHS *head* to be a valid pattern. A lemma whose LHS head
  unfolds to a `dite` is rejected with `invalid pattern, (non-forbidden)
  application expected` followed by a whnf PANIC — a hard build crash, not
  a soft failure. The canonical offender is `Array.getD` (e.g.
  `p.toArray.getD n 0 = …` in `HexPoly/Dense.lean`): `getD` reduces to a
  `dite` over `Array.getInternal`. Leave such lemmas as plain `@[simp]`.
  Plain *def*-headed LHSs (`coeff`, `size`, `support`) and `Option.getD`
  LHSs are fine. A second, softer rejection: a lemma whose **conclusion is
  wrapped in a `let`** (e.g. `montgomeryReduce_m_spec` in `HexArith/Montgomery/Redc.lean`:
  `let m := Tlo * ctx.p'; m.toNat = …`) is not a bare `Eq`, so `grind =`
  refuses it with `invalid E-matching equality theorem, conclusion must be an
  equality` even though it "looks like a literal equation." Leave such lemmas
  `@[simp]`-only; it is a permanent property of the statement shape, not a
  fixable regression, so no follow-up issue is warranted. A third rejection,
  independent of the head/conclusion shape: a literal `lhs = rhs` whose
  **parameters appear only under a binder in the LHS** is rejected with
  `invalid pattern(s) for <lemma> … the following theorem parameters cannot
  be instantiated`. `grind =` keys on the LHS head term, so a param that
  surfaces only inside a `fun`/`ofFn` lambda (e.g. `dotProduct_basis_basis`'s
  `i j` inside `ofFn (fun b => if i = b then …)`, or
  `columnTupleMatrix_compose_perm_entry`'s `s sigma` inside
  `fun i => s[sigma[i]]`, both `HexMatrix`) cannot be solved for. Same hard
  build error, same disposition: leave `@[simp]`-only, note why in the
  docstring/PR body. Indices that appear as a projection of a direct param
  (`i.val` inside a `Fin.mk` index) DO instantiate fine — only fully
  binder-bound params fail. A second flavour of the same rejection:
  params that survive only inside a **reducible type wrapper** that
  `grind` unfolds away. A junk-value lemma like
  `(0 : GFq p n h)⁻¹ = 0` (`HexGFq/Basic.lean`, #8144) looks clean —
  `lhs = rhs`, params `n`/`h` present in the `GFq p n h` type — but
  `GFq p n h` reduces to `GFqField.FiniteField (modulus h) …`, so the
  LHS pattern collapses to the parameter-free literal
  `@OfNat.ofNat (GFqField.FiniteField …) 0` (`modulus h` is opaque to
  pattern solving), and `n`/`h` cannot be instantiated. Same hard build
  error, same disposition. Note this does **not** transfer from a
  sibling library where the wrapper does *not* reduce: GF2n's
  `inv_zero` (`HexGF2/Field.lean`, #8124) keeps the `GF2n n …` type in
  its pattern and promotes fine. Premise-check each wrapper-type
  junk-value lemma against the real build before trusting a cross-library
  precedent.
- **A clean `Eq` conclusion is still rejected if the LHS pattern cannot
  instantiate a *data* parameter the conclusion drops.** `grind =`
  E-matches on the LHS, so every theorem parameter must be recoverable
  from it. A *proof*-typed dropped parameter is tolerated (grind leaves it
  as a metavariable); a *data*-typed one is a hard build error: `invalid
  pattern(s) for `foo` … the following theorem parameters cannot be
  instantiated: ctx : …`. Canonical offender: `p_odd_nat (ctx : MontCtx p)
  : p.toNat % 2 = 1` in `HexArith/Montgomery/Context.lean` — the pattern
  `p.toNat % 2` mentions only `p`, never the data parameter `ctx`, so it is
  rejected and left `@[simp]`-only. Contrast `mk_p_odd_nat (p) (hp : p % 2
  = 1) : p.toNat % 2 = 1` in the same file: same conclusion, but its
  dropped `hp` is a *proof*, so `grind =` accepts it. Rule of thumb for
  sweeps: a projection/specialization lemma whose conclusion forgets a
  *data* argument is ineligible; one that forgets only a *proof* argument
  (including proof-equality `mk_*` projections like `(mk p hp).p_odd = hp`)
  is fine.
- **`grind =` ACCEPTS `↔` (Iff) — it is NOT an ineligible shape.** `grind =`
  registers `a ↔ b` as a rewrite rule exactly like `a = b`, so a public
  characterising `↔` lemma (`p.isZero = true ↔ p = 0`,
  `memLattice (s.swapStep k).b v ↔ memLattice s.b v`) is a valid, sound,
  *terminating* `grind =` annotation when the LHS strictly reduces — and
  `↔ + grind =` is an established, deliberate pattern in this codebase
  (the LLL `*_memLattice_iff` capstone rewrites #6594, the HexArith
  carry/borrow wrappers, etc.). The Phase 6 sweep PRs scope themselves to
  `Eq` conclusions and their planning bodies call `↔` "left as `@[simp]`-only",
  but that is a conservative *scope choice for the mechanical sweep*, NOT a
  prohibition: do not "revert" a sound `↔ + grind =` lemma in an audit, and
  do not mis-read the `let`-binder rejection above as covering `↔`. The
  genuinely-rejected conclusion shapes (hard build error) are `<`, `≤`,
  `Ne`, `∧`, `Associated`, and `let`-wrapped — so a green build is itself a
  proof that none of those carry `grind =`.
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
- **`FpPoly` *products* need `FpPoly.*` rw lemmas, NOT `DensePoly.*_poly`.**
  Same instance-path divergence: a product `a * z` you write for `FpPoly` terms
  carries the canonical `Mul (ZMod64 p)`, but the general `DensePoly`
  product lemmas (`mul_comm_poly`, `mul_assoc_poly`, `mul_add_right_poly`,
  `mul_add_left_poly`, `neg_mul_right_poly`, `mul_sub_zero_comm`,
  `sub_eq_add_neg_poly` *inside a product*) carry the `Lean.Grind.CommRing`-
  derived `Mul`, so `rw [DensePoly.mul_comm_poly …]` reports "did not find
  pattern" on a goal that visibly contains `a * z`. Use `FpPoly.mul_comm`,
  `FpPoly.mul_assoc`, `FpPoly.left_distrib`, `FpPoly.right_distrib`,
  `FpPoly.sub_eq_add_neg`, `FpPoly.add_assoc`, `FpPoly.add_left_neg`,
  `FpPoly.add_right_neg`, `FpPoly.add_zero`, `FpPoly.mul_zero` for `rw`. There
  is no `FpPoly.mul_sub`/`sub_mul`/`neg_mul`; derive them once from
  `right_distrib`/`left_distrib` + additive cancellation (`a - b + b = a` via
  `sub_eq_add_neg`+`add_assoc`+`add_left_neg`+`add_zero`). A `DensePoly` product
  lemma still applies to an `FpPoly` goal via **`exact`/`:=`/`.trans`** (defeq-
  tolerant) or by binding a `have` whose stated type uses the `FpPoly` ops
  (then `rw [thatHave]`). `+`/`-`/coeff/`∣`/`Congr` lemmas (`DensePoly.coeff_add`
  — needs an explicit `(0+0=0)` arg —, `coeff_sub_ring`, `dvd_add_poly`,
  `dvd_mul_left_poly`, `congr_mod`, `mod_eq_mod_of_congr`) DO match `FpPoly`
  under their `DensePoly` names. `grind` does *not* prove `FpPoly` product/ring
  identities (only the `ZMod64` coefficient ring), so do not reach for it there.
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
- **Executable gcd/Bezout/modular-division lemmas silently need
  `[Hex.ZMod64.PrimeModulus p]`** (via `GcdLaws`/`DivModLaws`/field), but
  Mathlib-layer transport theorems usually carry only `[Fact (Nat.Prime p)]`.
  The mismatch surfaces as a confusing "failed to synthesize `PrimeModulus p`"
  deep inside a transport proof (e.g. when calling
  `DensePoly.xgcd_bezout` or `dvd_xPowSubX_iff_frobeniusDiffMod_isZero`).
  Bridge it with `haveI : Hex.ZMod64.PrimeModulus p :=
  HexBerlekampMathlib.primeModulus_of_fact p` (landed by #7774;
  builds the witness from `Nat.Prime.two_le` + `eq_one_or_self_of_dvd`).
  (`HexBerlekampZassenhausMathlib/Basic.lean` exposes `toMathlibPolynomial_dvd`
  and `self_dvd_monicModPImage` for exactly this.)
- **Through `fpPolyEquiv : FpPoly p ≃+* Polynomial (ZMod p)`, `map_mul` and
  `map_add` work but `map_one`/`map_zero`/`map_sub` do NOT.** `toMathlibPolynomial
  f` is defeq `fpPolyEquiv f`, and `map_mul`/`map_add` need only `MulHomClass`/
  `AddHomClass` (i.e. `[Mul]`/`[Add]`, which `FpPoly` has), so
  `map_mul fpPolyEquiv a b` / `map_add fpPolyEquiv a b` close
  `toMathlibPolynomial (a * b) = …` / `(a + b) = …` directly. But `map_one`/
  `map_zero`/`map_sub` resolve `OneHomClass`/`ZeroHomClass`/`AddGroup`-class
  instances that need Mathlib `MulOneClass`/`AddGroup` on `FpPoly` — which it
  lacks — so they fail with "failed to synthesize `OneHomClass (FpPoly p ≃+* …)`".
  Prove `toMathlibPolynomial (1 : FpPoly p) = 1` inline by `Polynomial.ext` +
  `coeff_toMathlibPolynomial` + `(1 : FpPoly p) = DensePoly.C 1` (rfl) +
  `coeff_C`/`Polynomial.coeff_one` (mirror `toZMod_zero` for the `Zero.zero`
  else-branch via `exact`, not `simp`); for subtraction use
  `toMathlibPolynomial_sub` (the named coeffwise lemma), not `map_sub`.
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

- **Don't `set`/`let` `bhksLatticeBasis …` when a hypothesis depends on it
  through a dependent type.** In BHKS proofs `S : LiftedFactorSupport
  (bhksLatticeBasis f p a liftedFactors)` (and `Fin L.factorCount`,
  `AggregateResidueData`, etc.) mention the basis in their *type*. `set L :=
  bhksLatticeBasis …` abstracts inside that type and produces an `S✝` /
  `i ∈ S✝` mismatch against the goal's `S`, which then cascades into
  `(deterministic) timeout at whnf` on later lemma applications. A `let L`
  is defeq but its fvar won't match the goal's spelled-out basis under the
  syntactic `rw` you need for the final `AggregateResidueData`/sum
  assembly. Simplest fix in the Mathlib layer: **spell
  `Hex.bhksLatticeBasis f p a liftedFactors` out in full** everywhere it must
  match the goal; only `set` the plain `ZPoly` pieces (`G := supportProduct …`),
  whose types carry no `S` dependency, and compute `supportProduct_cldSum_*`
  *before* that `set` so it folds the product into `G`.

## Proving *inside* the Mathlib-free files

Lemmas that live in the executable files themselves (`HexPoly/*`,
`HexPolyZ/*`, `HexBerlekamp/*` including `RabinSoundness.lean`,
`HexBerlekampZassenhaus/Basic.lean`) cannot use Mathlib tactics
or `Monoid`/`CommRing` lemmas — those modules don't import Mathlib.

- **`by_contra`, `ring`, `omega`-via-Mathlib, `set`, `conv_lhs`/`conv_rhs`,
  `push_neg` are out.** They report "unknown tactic". Replacements: `by_contra`
  → `rcases Nat.eq_zero_or_pos n` / `rcases Nat.lt_trichotomy a b` /
  `by_cases` + `Classical.byContradiction`; `set x := e` → `let x := e` (but a
  `let` of a *huge* term blows the `whnf` heartbeat budget — `generalize e = x`
  to an opaque var instead, after extracting the facts you need about `e`);
  `push_neg` → `Classical.not_forall.mp` / `Classical.not_exists.mp`; `conv_lhs
  => rw [h]` → `rw [h] at <aux-have>` then `exact`. `omega`/`simp`/`rcases` are
  core and available.
- **The general order lemmas and transitivity dot-notation are out too.**
  `le_trans`/`lt_of_le_of_lt`/`lt_of_lt_of_le` report "unknown identifier", and
  `(h : a ≤ b).trans_eq`/`.trans` fail with "environment does not contain
  `Nat.le.trans_eq`". Use the type-prefixed core lemmas — `Nat.le_trans`,
  `Nat.lt_of_le_of_lt`, `Nat.le_of_lt`, `Nat.le_of_eq`, `Nat.le_antisymm` (and
  `Int.*` analogues) — or just `omega` for any concrete `Nat`/`Int` inequality
  chain. Transitivity is common in size/degree bookkeeping, so this bites most
  arithmetic proofs in the executable layer.
- **`@[nolint ...]` is unavailable** — the attribute lives in Mathlib's
  linter framework, so writing `@[nolint unusedArguments]` (or any
  `nolint`) in a Mathlib-free file is a build error (`unsupportedSyntax`),
  even though `lake exe runLinter` itself resolves from the mathlib dep.
  This bites Phase 6 linter audits: a Mathlib-free lib **cannot suppress**
  a `unusedArguments` lint on a deliberate phantom argument (e.g. a proof
  carried only to pin a precondition, or a witness carried only for
  dot-notation). Restructure the signature or punch-list the lint as an
  accepted exception — do not reach for `@[nolint]`.
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

### Phase 6 `@[simp]`/`@[grind]` annotation pitfalls

Adding automation annotations to a characterising lemma is not free; two
traps cost a build cycle each:

- **Bare `@[grind]` on a conditional/equational lemma errors with "Try
  these".** When grind cannot uniquely pick an E-matching pattern (typical
  for `dot … = 0` / `entry … = 0` lemmas with `i ≠ j` / `i < j` side
  conditions) it refuses and prints `[apply] [grind =] for pattern: …`. Use
  the explicit marker it suggests — `@[grind =]` selects the conclusion
  pattern and elaborates silently. Plain `@[grind]` is only safe on lemmas
  with an obvious head.
- **Match the marker to the lemma shape; ground Prop facts need `@[grind .]`,
  not bare `@[grind]`.** Even a hypothesis-free fact with an obvious head
  (`DensePoly.Monic c`, `FpPoly.Irreducible c`, `0 < FpPoly.degree c` for a
  *concrete* `c`) makes plain `@[grind]` print `info: Try this … [grind .]`
  on every build — noise the Phase 6 "no new warnings" criterion rejects.
  Use the explicit `@[grind .]` it suggests (the fact/apply form, keyed on
  the constant; no loop, builds silently). Reserve the file's
  `@[grind =>]` + `grind_pattern` convention for *parametric* Prop wrappers
  that carry a free variable (e.g. `conwayPoly_irreducible (h : SupportedEntry p n)`).
  For a projection that fires from a hypothesis — `(h : lookup p n = some f) :
  P f` — use `@[grind →]` (forward). Quick rule: equation → `=`, ground Prop
  → `.`, hypothesis-driven Prop → `→`, parametric Prop → `=>` + `grind_pattern`.
- **`@[simp]` on a "push through" transport equality can break a downstream
  proof in the same file.** A lemma like `basis (rowAdd b …) = basis b`
  looks like a clean normal form, but as `@[simp]` it fires inside dependent
  terms (e.g. a `coeffMatrix` proof obligation) and triggers `rewrite …
  motive is not type correct`. Transport/invariance equalities are exactly
  the class the Phase 6 issues warn against blanket-annotating — leave them
  un-annotated unless you confirm the whole library still builds. Stick to
  genuine value normal forms (`coeffs_diag = 1`, `basis_zero`) for `@[simp]`.

## Signature gotcha

A hypothesis whose type mentions `toMathlibPolynomial`/`monicModPImage`/`modP`
at `primeData.p` is elaborated **before** any `letI := primeData.bounds`, so an
implicit `[Bounds primeData.p]` cannot be synthesized and the type silently
becomes `sorry`. Write the instance explicitly in such signatures:
`@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds (…)`.

## Reducing `DensePoly.degree?.getD 0` (the `dite` idiom)

`DensePoly.degree? p = if _h : p.size = 0 then none else some (p.size - 1)` is a
**`dite`**, so `simp [DensePoly.degree?, h]` with a bare `h : p.size ≠ 0` often
fails to discharge the discriminant and leaves `(if … then none else …).getD 0`
unreduced. Two reliable reductions:

- nonzero size → degree: `obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne;
  simp [DensePoly.degree?, hm]` (substituting `size = m+1` makes the
  discriminant syntactically nonzero, which `simp` kills via `Nat.succ_ne_zero`).
  Then `p.degree?.getD 0 = p.size - 1`.
- zero size → degree: `simp [DensePoly.degree?, h0]` with `h0 : p.size = 0`
  reduces fine (the `0 = 0` branch is decidable).

Also: `0 < p.size` is `Nat.le`, so `hsize_pos.ne'` does **not** typecheck
(`Nat.le.ne'` doesn't exist). Use `Nat.pos_iff_ne_zero.mp hsize_pos` for
`p.size ≠ 0`, and `Hex.ZPoly.size_pos_of_ne_zero p hp` to get `0 < p.size` from
`p ≠ 0`.

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

### Raw-irreducibility contracts on the fast path must be guarded by `shouldRecordPolynomialFactor`

The unguarded shape `factorFastFactorsWithBound f B = some rawFactors →
∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw` is **false**, not just
underivable: the constant early-return (`squareFreeCore.degree?.getD 0 = 0`)
emits `reassemblePolynomialFactors normalized #[squareFreeCore]` with
`squareFreeCore = 1` (for `f = 1`), and `Irreducible 1` is impossible (`1` is a
unit). #8067 was skipped on exactly this; #8079 fixed it. The satisfiable
contract guards each raw obligation with the recorded-factor filter:
`Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true →
Hex.ZPoly.Irreducible raw`. The guard excludes the unit/constant raw outputs
that never become recorded `(Hex.factor f).factors` entries; it is discharged
for free at the consumer from `Hex.factorWithBound_entry_shouldRecord` (every
recorded entry passes the filter), so the guarded form composes exactly where
the unguarded one was needed. The fast producers of the guarded contract:
`Hex.factorFastFactorsWithBound_raw_irreducible_of_constant` (degree-0
early-return; reassembly is a power of `X`, the unit core fails the guard via
`shouldRecordPolynomialFactor_one`) and
`factorFastFactorsWithBound_raw_guardedIrreducible_of_recoveredLift` (BHKS
core-success, routing through the #8058 capstone). Slow producers
(`slowModularRaw_irreducible_of_fast_none`,
`factorTrialFactorsWithBound_factor_irreducible_of_fast_none`) keep their
*unguarded* statements — `fast = none` forces `degree ≠ 0`, so there is no unit
core — and imply the guarded form by `fun raw hmem _ => producer raw hmem`. Note
this guarded contract is the fast-path counterpart to the `normalizeFactorSign`
sign-guard trap below: both are sound *narrowings* of an over-quantified raw
obligation, not core-facts assembly. Both fast guarded sub-branch producers
have now landed in `IntReductionMod.lean`: the small-mod-singleton
(`factorsModP.size ≤ 1`) producer
`factorFastFactorsWithBound_raw_guardedIrreducible_of_smallModSingleton` (#8097)
and the quadratic short-circuit producer
`factorFastFactorsWithBound_raw_irreducible_of_quadratic` (#8101). They were
written two different ways, and both routes are worth knowing: the private
`Hex.reassemblePolynomialFactors` (private to `HexBerlekampZassenhaus/Basic.lean`)
cannot be named from the Mathlib layer to state the dispatcher's value equation
`factorFastFactorsWithBound f B = some (reassemblePolynomialFactors …)`, and
there are two ways around that obstacle.

**Route A — name the reassembly value through the public branch theorem (the
singleton route).** Do **not** reach for `unfold Hex.factorFastFactorsWithBound`
in the Mathlib-layer proof — unfolding that def forces a `whnf` of the schedule
loop and times out the per-declaration heartbeat (the error pins to the
declaration's first line, masking the real goals). Instead `rcases` the public
`Hex.factorFastFactorsWithBound_branch_of_choosePrimeData?_some f B primeData
hchoose` (9-way disjunction (a)–(i)): its singleton disjuncts (c) `B=1` and (g)
`1<B` already carry `factorFastFactorsWithBound f B = some
(reassemblePolynomialFactors (normalizeForFactor f) #[squareFreeCore])` as their
first conjunct, so the private term enters your context through that theorem's
type without being written. Eliminate the other seven disjuncts from the branch
markers (`hdeg`, `hB_pos`, `hsmall`, and the `B = 1 ∨ quad = none` dispatch
guard — the fast-core ones carry `¬ size ≤ 1` contradicting `hsmall`; (f)'s
`quad = some` contradicts the guard at `1<B`). Then combine the disjunct's `hv`
with `hfast` via `Option.some.inj (hfast.symm.trans hv)`, `rw` the resulting
`rawFactors = reassemble…` into the membership, and feed it to the public
`Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`.
For the singleton arm the irreducibility substrate is
`squareFreeCore_irreducible_of_smallModSingletonBranch` →
`reassemblyExpansionComplete_singleton_of_irreducible_of_pos_lc` (both
`IntReductionMod.lean`); since `hdeg` forces positive core degree the core is
genuinely irreducible, so the recorded-factor guard is discharged for free and
is not consumed.

**Route B — name it through a public equation lemma in Basic.lean (the quadratic
route).** `unfold Hex.factorFastFactorsWithBound` in the Mathlib layer fails with
`Unknown identifier Hex.reassemblePolynomialFactors`. The constant producer
(`_raw_irreducible_of_constant`) gets away with `unfold` only because it lives
*in* Basic.lean where the private def is in scope. The entry umbrellas dodge it
via `factorWithBound_entry_mem_*_branch_raw` (membership lemmas whose *types*
carry the private term, which flows through without you naming it). For a new
raw producer along this route, add a one-line public equation lemma in Basic.lean
(`factorFastFactorsWithBound_eq_some_of_<branch>`, proved by `unfold` +
`if_neg`/`rw [hquad]`) and consume it from the Mathlib side; the private term
then arrives inside the equation's type, and the
`_factor_irreducible_of_complete_and_core_irreducible` lift accepts the resulting
`hmem` directly. The quadratic producer uses this route via
`factorFastFactorsWithBound_eq_some_of_quadratic`.

The slow-path raw irreducibility (`slowModularRaw_irreducible_of_fast_none`,
#7665) is *unconditional* because the slow path runs a single fixed-precision
`exhaustiveCoreFactorsWithBound` at `exhaustiveLiftBound` — one deterministic
array, so `hraw : … = some rawFactors` pins it directly and the irreducibility
producer applies at that one precision. **Do not assume the fast path is the same
shape.** `bhksRecoveryCoreWithBound` is a *schedule loop* (`Basic.lean:6935`): it
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
  `bhksRecoveryCoreWithBound_some_factor_count_eq_of_cut`, whose loop-result params
  (`k`,`fuel`) and cut-precision param (`L`) are already independent.
- Those decoupled wrappers still take `h : bhksRecoveryCoreWithBound core B
  primeData start fuel = some hinputs.expectedFactors` as a hypothesis. Producing
  that `h` for the real `start = initialHenselPrecision a` is the **scheduled-loop
  determinism obligation** (loop's first success returns the cap recovery). It is
  *not* derivable from the cap package: `bhksRecoveryCoreWithBound_isSome_of_
  recovery_on_schedule` (`Basic.lean:7105`) proves existence, not factor
  identity, and `bhksRecoverClassified_success_*` (`Basic.lean:11238-11322`) give
  product/dvd/sign for any success but neither irreducibility nor equality to the
  cap recovery. Closing it needs "recovery fails below the Mignotte precision" (a
  BHKS precision-soundness theorem) or a universal "recovery success ⟹ irreducible
  at arbitrary precision" — neither is in the tree. Before claiming a fast-BHKS
  "expose the loop array" / unconditional `h_raw` issue, confirm a determinism
  producer exists, else land the decoupled bridges + diagnose (#7664).

### The fast-path lift exponent `liftData.k` is double-log small — hsep/hthr are *false*, not just underivable (#7928)

`precisionForCoeffBound` is applied **twice** on the public fast path, so the
CLD lattice runs at a precision far below the BHKS column-adequacy threshold.
The public caller computes `a := precisionForCoeffBound B primeData.p`
(`Basic.lean:7699/7714`, `B = latticePrecisionCap core`) and passes `a` as
`bhksRecoveryCoreWithBound`'s coefficient-bound parameter; the loop then feeds the
schedule variable `k` into `toMonicLiftData core k primeData`, which applies
`precisionForCoeffBound` **again** (`:7001`, `(henselLiftData _ B _).k = B`).
Net: the lattice's actual exponent is
`liftData.k = precisionForCoeffBound k p = ceilLogP p (2k+1)`, collapsing
double-logarithmically. Concretely for `cldGuardF = x²−5x+6`, `p=5`: every
scheduled `k ∈ [4,8,12]` (cap included) gives `liftData.k = 2` (modulus 25), but
the CLD floor `precisionForCoeffBound (bhksCoeffBound (toMonic core).monic 0 =
16) 5 = 3` is not met. So **hsep** (`2·bhksCoeffBound (lift S).f j <
(lift S).p ^ (lift S).a`, with `(lift S).a = d.k = liftData.k = 2`) is literally
`32 < 25` — **false**, not merely "not derivable from success." The final
product check (`Array.polyProduct candidates == f`) rescues *correctness*
empirically (true factor coefficients are tiny) but certifies nothing about
column-adequacy. **Consequence:** no acceptance gate against the current
`liftData.k` (the #7928 plan) can supply hsep/hthr — it would only flip fixtures
`some → none`. Verify with a pure-integer `#eval` scratch (`bhksCoeffBound`,
`precisionForCoeffBound`, `henselPrecisionSchedule`, `latticePrecisionCap` all
run under `lake env lean`, no extern). The real fix is a precision-*schedule*
correction (drop the double `precisionForCoeffBound`), which is soundness-
sensitive and touches the CI-gated determinism cluster — not a cheap gate.
Before claiming any "discharge hsep/hthr" / "CLD precision floor" fast-path
issue, `#eval` `liftData.k` at the scheduled precisions and confirm it actually
clears the CLD floor; as of #7928 it did not.

### Resolved by #7938 (schedule) + #7951 (gate); the gate cascade is large

#7938 dropped the double `precisionForCoeffBound` so the schedule now iterates
*coefficient bounds* `k` up to the cap `latticePrecisionCap f` (single
conversion inside `toMonicLiftData`). #7951 then added the acceptance gate:
`bhksRecoveryCoreWithBound`'s `.success` branch accepts only when
`k ≥ cldCoeffFloor core = 2·max_j bhksCoeffBound (toMonic core).monic j`, else
continues the schedule. Post-#7951, `success → k ≥ cldCoeffFloor core` (hence
`hsep` via `precisionForCoeffBound_spec`) *is* derivable — that is the premise
#7945's hsep/hthr proofs consume. Verify the floor numerically with a
pure-integer `#eval` (`cldCoeffFloor`, `latticePrecisionCap`, the schedule)
under `lake env lean` — for `cldGuardF` floor`=32`, cap`=50803201`, first gated
success at `k=32`/`liftData.k=3` (`2·bhksCoeffBound=32 < 5^3=125`).

Two traps when touching the gate:

- **Adding an acceptance condition to `bhksRecoveryCoreWithBound` cascades through
  the entire CI-gated capstone chain, not just the obvious determinism lemmas.**
  Every wrapper whose conclusion asserts `factorFast … ≠ none` / `= some …`
  needs the new side condition threaded as an *open hypothesis* (like `hno`):
  the `*_of_recovery_on_schedule` / `*_of_forwardInputs_*` lemmas in
  `Basic.lean` + `PartitionRefinement.lean`, **and** the whole festooned
  `Recovery.lean` chain — the `_internalCapPositive*` variants and all ~18
  `factorFast_terminates*` capstones (which route through `factorFast_terminates`
  → `…_internalCapPositiveAndPrimeLowerBound`). Size it up front by grepping the
  `hB_pos`/`one_le_latticePrecisionCap f`/`hchoose` arg chain (~30 lemmas);
  do **not** regex-replace on `f primeData` (it appears pervasively in
  hypothesis *types* like `CanonicalRecoveryTailInputs f primeData …`, so a blind
  sed corrupts signatures — target exact call lines). The success→*property*
  lemmas (`_product`, `_dvd`, `_some_all_of_recovery`, `_some_classifiedSuccess`)
  stay signature-stable; they only need a `by_cases hfloor` in the `.success`
  case. Discharging the floor side condition needs
  `cldCoeffFloor core ≤ latticePrecisionCap f` (a `toMonic` coefficient-norm
  vs `bhksBound`-slack analysis with no existing infra) — thread it, don't try
  to prove it inline.
- **Reducing the gate `ite` on a `k ≥ cldCoeffFloor core` condition in a
  *goal*.** `rw [if_pos hge]` fails ("did not find pattern" — the `GE.ge`
  Decidable instance the `rw` infers differs from the goal's) and `split` may
  silently not fire. Use `simp only [ge_iff_le, hfloor, if_true]` (or
  `simp [hclass, hfloor] at hfast` when reducing it inside a *hypothesis*, which
  is robust to the instance gap).

### The floor gate discharges `cut` (hsep/hthr) but NOT the bad-vector exclusion — `L'=W` is still cap-only (#7985)

A "success ⟹ recovery package / `EquivalenceClassRecoveryHypotheses` /
`ForwardRecoveryInputs` producer" directive (the #7917 prerequisite) looks like
a thin assembly after #7980 landed hsep/hthr, but is **not** constructible.
`bhksRecoveryCoreWithBound_some_indicatorCandidates` (`Basic.lean:11785`) already
gives `k'`, `hrows`, `hcandidates`, non-degeneracy, and product=core from loop
success with no extra hypotheses — so `hcandidates`/`hsize` are free. The whole
deliverable collapses to the single field `hindicators`
(`equivalenceClassIndicatorsOfLiftData … = expectedIndicatorArrayOfSupports
trueSupports`), whose only route
(`equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports`,
`Recovery.lean:572`) demands `lattice_eq_indicators` = the BHKS Lemma 3.3
equality `L'=W`. That needs `SeparationHypotheses.no_projected_not_indicator`
(bad-vector exclusion), whose **only** producer
(`no_projected_not_indicator_of_latticePrecisionCap_le`,
`TerminationBound.lean:508`) requires precision `≥ latticePrecisionCap` **and**
the still-open `BadVectorBridgeData` (BHKS Lemma 3.2 resultant divisibility).
Crucially: the #7951 gate forces only `k' ≥ cldCoeffFloor core`, which feeds
**only** the CLD column adequacy (`cut`/hsep/hthr, in `CLDColumnBound.lean`) —
`cldCoeffFloor` appears in **zero** lines of `BadVector.lean`/`Lattice.lean`/
`TerminationBound.lean`, all of which key the exclusion on
`latticePrecisionCap … ≤ a`. And floor ≪ cap by orders of magnitude
(`cldGuardF`: floor=32, cap=50803201, both pure-integer `#eval`-checkable), so
the cap producer cannot fire at the first-success precision. The `on_schedule`
`hno` route is *worse than hard — it is false*: the gated loop returns at the
first success `k'=floor ≪ cap`, so a non-cap scheduled precision recovers,
contradicting `hno` (which fixes target=cap). There is also no function
producing a genuine `trueSupports` from `core`/success; inverting the indicator
array gives junk that the downstream #7917 `hpartition`/`hfac`/`lift` (all over
the *same* `trueSupports`) cannot consume. So **diagnose and skip** any such
producer issue: the genuine prerequisite is either a floor-keyed bad-vector
exclusion (push the `TerminationBound.lean` cap argument down to the CLD floor)
or a `BadVectorBridgeData` producer from core facts — soundness substrate, not a
thin producer. (#7985 skipped on exactly this.)

**#7938 fixed only the *cap*, not the success precision — the trap persists
(#7945).** #7938 removed the *caller-side* double `precisionForCoeffBound` (the
public path now passes the raw cap `B = latticePrecisionCap core`), so the
*cap* schedule entry is now adequate (cldGuardF: `liftData.k = 12` at `k = cap =
50803201`). But the per-iteration lift still applies `precisionForCoeffBound` to
the **schedule variable** `k` (`toMonicLiftData core k primeData` ⟹ `liftData.k
= precisionForCoeffBound k p`, `Basic.lean:7001-7017`), and the loop returns at
the **first** `k` that recovers — not the cap. For cldGuardF the first schedule
entry `k = 4` already recovers (the `polyProduct == f` product check passes on
the tiny true coefficients), so `liftData.k = precisionForCoeffBound 4 5 = 2`,
and hsep is `2·bhksCoeffBound … = 2·16 = 32 < 5² = 25` → **false** (floor needs
`precisionForCoeffBound 16 5 = 3`). So "the schedule fix makes hsep/hthr
provable" is still a false premise: success is certified by the empirical
product check, not by column-adequacy, so `success ⟹ hsep at liftData.k` remains
refutable. The genuine residual is an **executable** acceptance gate (reject a
success whose `liftData.k < bhksCoeffCutThreshold`, forcing cldGuardF from
`k=4 → liftData.k=2` to `k=16 → liftData.k=3`) plus its Mathlib determinism
remodel — not a proofs-only deliverable. (#7945 skipped on exactly this.)

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

## `HexGF2Mathlib` defines a project-local `RingEquiv`/`TypeEquiv` shadowing Mathlib's

`HexGF2Mathlib/Basic.lean` declares its own minimal `structure RingEquiv`
(fields `toFun`/`invFun`/`left_inv`/`right_inv`/`map_mul'`/`map_add'`, a CoeFun
to `toFun`, and `symm`) **with the same `≃+*` notation** (`infixl:25 " ≃+* "`)
and a `TypeEquiv` shadowing `Equiv`. So `HexGF2Mathlib.GF2n.equiv :
GF2n … ≃+* GenericFiniteField` is **`HexGF2Mathlib.RingEquiv`, not Mathlib's**.

Symptom when you forget: composing it with a Mathlib `RingEquiv` (e.g. a `cast`-
based equiv on the generic Conway field) fails with `RingEquiv.trans`/`.trans`
resolving to `HexGF2Mathlib.RingEquiv.trans` (which doesn't exist), or an
"Application type mismatch" / "type mismatch" between two `≃+*` types that
**print identically** (one is the custom struct, one is Mathlib's). `e.symm`,
`e.map_mul'`, `e.symm_apply_apply` dot-notation resolves into the custom
namespace too. Confirm early with `set_option pp.all true in #check e` — Mathlib's
prints `@RingEquiv.{…}`, the custom one prints `@HexGF2Mathlib.RingEquiv.{…}`.

Recipe to compose a custom `e : A ≃+*[Hex] B` with a Mathlib `g : B ≃+* C` into
a Mathlib `A ≃+* C`: build the Mathlib structure literal directly,
`{ toFun := fun x => g (e x), invFun := fun x => e.invFun (g.symm x), … }`, and
discharge its fields from **`e`'s struct projections** (`e.left_inv`,
`e.right_inv`, `e.map_mul'`, `e.map_add'` — `e` is a bare structure, no
`MulHomClass`) and **`g`'s Mathlib lemmas** (`RingEquiv.symm_apply_apply`,
`apply_symm_apply`, `map_mul`, `map_add`). Do **not** `RingEquiv.trans` across
the boundary — the two `RingEquiv`s are different types. Inline `e`/`g`
(no `let`): a `let`-bound equiv whose type mentions the heavy
`GFqField.FiniteField`/`GenericFiniteField` carrier blows the `whnf` heartbeat
budget (same trap as the `set d := toMonicLiftData` warning above); name a thin
`private def` for the repackaged `e` if you must, but reference it inline.

### `GF2Poly` multiplication is carryless with no exported coeff-convolution

Bridging `GF2Poly`'s product to `FpPoly 2` / Mathlib multiplication
(`toFpPoly_mul`-shaped goals: `toFpPoly (p * q) = toFpPoly p * toFpPoly q`) is
**not** a token swap, even though the issue body may say "coeff infrastructure
is in-file". `GF2Poly` multiplies via carryless `clmul`, and the only public
product-coefficient lemma is `Hex.GF2Poly.coeff_mul : (p * q).coeff n =
coeffWords (mulWords p.words q.words) n` — the *word-level* carryless product,
**not** a coefficient convolution. There is **no** exported lemma of the shape
`(p * q).coeff n = ⊕_{i+j=n} (p.coeff i && q.coeff j)`; the convolution
internals (`clmulCoeffAt`, `clmulSourcePairCoeff`, `coeffWords_mulWords_contrib`)
are all `private` to `HexGF2/Multiply.lean`, so they are unreachable from the
Mathlib bridge. Closing such a goal needs *new infrastructure*: (1) a public
carryless-convolution coeff lemma in `HexGF2/Multiply.lean`, proved from the
private internals by reindexing the (word, bit) double decomposition
`64*I + A` / `64*J + B` into flat indices `s + t = n`; plus (2) a `ZMod64 2`
parity-sum bridge (the diagonal `mulCoeffSum` over `ZMod64 2` of indicator
coefficients = XOR parity). The `*_one`/`*_add`/inverse directions of the same
bridge *are* in-file (coeff-level: `coeff_toFpPoly` + `coeff_ofFpPoly` via the
`packWord` bit-extraction helpers); only `mul` carries this gap. (#7900 landed
4/5; the `mul` bridge is #7901.)

### Bridging `GF2n`/`GF2nPoly` `≃+*` obligations to the `GFqField` quotient

The four `≃+*` obligations for `GF2n.equiv` / `GF2nPoly.equiv` in
`HexGF2Mathlib/Field.lean` (`ofGeneric_toGeneric`, `toGeneric_ofGeneric`,
`toGeneric_add`, `toGeneric_mul`) compose the `GF2Poly ≃+* FpPoly 2` bridge with
the `GFqField` quotient layer. The whole proof factors through **one** crux
helper plus mechanical glue (#7936 landed the `GF2n` single-word side; `GF2nPoly`
is #7937):

- **The crux is `toFpPoly (p % q) = GFqRing.reduceMod (toFpPoly q) (toFpPoly p)`**
  — `toFpPoly` commutes with the polynomial remainder. Prove it from
  `Hex.GF2Poly.div_mul_add_mod p q` (`(p/q)*q + p%q = p`), push `toFpPoly`
  through (`toFpPoly_add`/`toFpPoly_mul`), then `GFqRing.reduceMod_add_mul_self_right`
  (kills the `(p/q)*q` term) and `GFqRing.reduceMod_eq_self_of_degree_lt` (the
  remainder is already reduced). Degree transports via a one-liner
  `FpPoly.degree (toFpPoly p) = p.degree` from `degree?_toFpPoly` (both `degree`s
  are `degree?.getD 0`).
- **`Hex.GFqRing.reduceMod` and its algebraic lemmas need a
  `ZMod64.PrimeModulus 2` instance** (the FpPoly division law). Add
  `instance : Hex.ZMod64.PrimeModulus 2 := Hex.ZMod64.primeModulusOfPrime prime_two`
  in the namespace once; without it you get a bare "failed to synthesize
  `ZMod64.PrimeModulus 2`" deep inside a `reduceMod`-lemma application.
- **Reach the executable `reduce`/`reduceWide` value without naming private
  defs.** `(Hex.GF2n.reduce w).val` is **defeq** to the fully-public term
  `Hex.GF2Poly.canonicalWordLT n hn64 (Hex.GF2Poly.packedReduceWord n irr
  (Hex.GF2Poly.ofUInt64 w))` (it unfolds through the `private` `canonicalWord`,
  `reducePoly`, `toPolyWord`), so a helper stated over that public term applies
  by `exact`/defeq — no need to de-privatize `HexGF2/Field.lean` or
  `HexGF2/Euclid.lean`. The masking is idempotent: `canonicalWordLT n hn64 v = v`
  for `v.toNat < 2^n` (re-prove the private `canonicalWordLT_eq_self_of_lt`
  inline via `UInt64.toNat_inj` + `Nat.mod_eq_of_lt`, fed
  `packedReduceWord_toNat_lt`), then `ofUInt64_packedReduceWord_eq_of_degree_lt`
  (public) + `mod_degree_lt` close it. The low-word round-trip
  `ofUInt64 (p.toWords.getD 0 0) = p` for reduced `p` (#7936 replicated the
  private `ofUInt64_lowWord_eq_of_degree_lt_64`; its proof uses only public
  `coeff_ofWords`/`ext_coeff`/`coeff_eq_false_of_degree?_lt`). All of this lives
  in the Mathlib layer — **no executable-layer edits**, matching the issue's
  "add helpers privately / to Basic.lean" guidance.
- **`rw [helper]` leaves trivial side goals (`0 < n`, `n < 64`) when the helper
  carries `include`d section hypotheses not fixed by the rewrite pattern** (e.g.
  a helper whose statement mentions `n`/`irr` but uses `hn`/`hn64` only in its
  proof). The fix is named args in the `rw`: `rw [helper (hn := hn) (hn64 :=
  hn64)]`. Also note `rw`'s closing `rfl` runs at *reducible* transparency, so a
  residual goal that is true only by unfolding a plain `def` (e.g.
  `modulusFpPoly = toFpPoly (ofUInt64Monic irr n)`) is **not** auto-closed —
  append an explicit `rfl` (default transparency) or pre-unfold the def.

With those, `toGeneric_add`/`_mul` are
`apply GFqField.ext; apply GFqRing.ext; simp only [toGeneric, toQuotient_*,
repr_*_ofPoly]; rw [ofUInt64_{add,mul}_val, toFpPoly_mod_modulus, toFpPoly_{add,mul},
reduceMod_idem]`, and the round-trips chain the same helpers with
`ofFpPoly_toFpPoly`/`toFpPoly_ofFpPoly` + the low-word round-trip.

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
`coordination skip` rather than attempting the integration. **But before
concluding a transport/producer is genuinely missing, grep producer proof
*bodies*, not just signatures: a needed construction is frequently performed
*inline inside a larger producer's proof* and can be lifted to a top-level
lemma, even when no theorem states it.** #8068 was nearly skipped a 5th time on
"no original→monic `RepresentsIntegerFactorAtLift` inversion exists"
(`representsIntegerFactorAtLift_of_monicCorrespondent` only goes monic→original);
that conclusion was *wrong* — the partition producer
`initialLiftedFactorSubsetPartitionEvidence_of_toMonicChoosePrimeData` already
reconstructs the monic correspondent from the *factor itself* (a local `descent`
`have`, `IntReductionMod.lean`), via `exists_monicCorrespondent_of_dvd` +
`representsModP_correspondent` + `toMonicLiftData_represents_lifted_monicCorrespondent`,
never the represents predicate's hidden witness. Extracting that `have` as
`monicCorrespondentDescent_of_representsAtLift` unblocked the whole separation-free
route. A fan-out `Explore` agent that only checks the named-lemma path will
report a confident, wrong "NO" here — read the construction sites yourself.
Substrate producers
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

## The Mathlib layer IS CI-gated — keep it green; establish a baseline first

`ci.yml` has a `Build HO-1 Mathlib bridge` step (`lake build
HexBerlekampZassenhausMathlib`, currently `ci.yml:67`) that builds the whole
`HexBerlekampZassenhausMathlib` library — and transitively `HexBerlekampMathlib`,
which it imports. So **both** Mathlib layers are merge-gating: an
`unknown identifier` / elaboration error there turns CI red and blocks merge,
and a green CI rollup **does** mean those layers compile (the shipped `sorry`s
are warnings, not errors). Do not assume the layer can be "hard-red on main" —
it cannot, CI gates it. (Earlier versions of this skill claimed CI did not build
this layer; that was true before the bridge step was added and is now wrong.)

**But the GF(2)/GF(q) Mathlib layers are NOT in that build graph.**
`HexBerlekampZassenhausMathlib` does not import `HexGF2Mathlib` /
`HexGFqMathlib`, and `ci.yml` builds no other Mathlib library, so those two CAN
be hard-red on `main` indefinitely — a break merges unnoticed (e.g. #7907's
`toFpPoly_mul` stopped matching `coeff_mul_diagonal`'s private `xorBoolList`
wrapper and left the whole layer red). So when you touch `HexGF2Mathlib` /
`HexGFqMathlib`, do **not** assume a red baseline is your fault: build the
unmodified target first (`lake build HexGF2Mathlib`), and expect to repair
pre-existing breakage in the file you are editing and in downstream consumers
your fix unmasks (`HexGFqMathlib/GF2q.lean` consumes
`GF2n.GenericFiniteField`). A stale-olean rebuild (`touch` the dep source +
`lake build <DepModule>`) confirms genuine vs cache breakage.

Practical consequence for a boundary change: building only
`HexBerlekampMathlib.<Module>` is **not** enough to know your PR is green — run
`lake build HexBerlekampZassenhausMathlib` and confirm it finishes
(`Build completed successfully`, zero `error:`) before opening the PR, because
that whole library is what CI runs. If your change to an upstream lemma (e.g.
removing or renaming a `HexBerlekampMathlib` declaration) breaks a downstream
consumer, CI will catch it — find the consumers with `grep -rn <name>
HexBerlekampZassenhausMathlib/` first. A fresh worktree has no built Mathlib, so
run `lake exe cache get` first (prebuilt oleans in minutes; a from-scratch
Mathlib compile is hours). Only the project's own files then rebuild.

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

**Reviewing a *transitive* proof term (the "no hidden sorry/axiom/native_decide"
review deliverable) is different — grepping added lines is not enough.** Use
`#print axioms <decl>` in a throwaway `lake env lean Scratch.lean` (after a
`lake build <Module>` so the olean is fresh). A clean cone reports exactly
`[propext, Classical.choice, Quot.sound]`; a `sorryAx` entry means a shipped
`sorry` (e.g. `Hex.ZPoly.isIrreducible_iff` in `Basic.lean`) is in the cone, and
a `Lean.ofReduceBool` entry means `native_decide`. This cleanly distinguishes
in-cone from the project's out-of-cone shipped sorries, which line-grep cannot.

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
  `set_option … in` → `/-- doc -/` → `structure …`. The same applies to any
  `… in` declaration modifier — e.g. `omit [Inst] in` to silence the
  unused-section-variable linter on a pure-`Nat` helper in an instance-carrying
  `variable` block — must come *before* the docstring (`omit … in` → `/-- doc -/`
  → `theorem …`), else the same `unexpected token 'omit'` parse error. Once the budget is large
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

### `BHKS.phi f g` is `0` for non-monic `g` — bound the real column `h·g'`, not `phi`

`phi f g := (f * g').divByMonic g`, and `Polynomial.divByMonic _ q = 0`
whenever `q` is **not** monic (`if Monic q then … else 0`). So any directive
that asks to "drop the monic hypothesis from a `phi`-stated bound" while keeping
the conclusion over `phi (toPolynomial f) (toPolynomial g)` is **vacuous for
exactly the non-monic case** it claims to cover: the LHS is identically `0`.
This bites the core-coordinate cut, whose true integer factors are primitive
(non-monic). The genuine BHKS column is `Φ(g) = f·g'/g = h·g'` for `f = g·h`,
which `phi` computes only when `g` is monic. The monic-free bound is
`BHKS.abs_factorDeriv_coeff_le` / `BHKS.abs_factorDeriv_coeff_le_bhksCoeffBound`
(`CLDColumnBound.lean`), stated over `h * g.derivative` with a cofactor witness
`hfac : f = g * h` — not over `phi`. The analytic core
(`derivative_eq_sum_rootDeletionDerivativeSummand`,
`mahlerMeasure_rootDeletionDerivativeSummand_le`) is already monic-free; only
`phi_eq_factor_mul_derivative` (the `divByMonic` identity) and
`Monic.natDegree_mul'` used monic, replaced by starting from `h·g'` and the
domain `Polynomial.natDegree_mul`. Note the CLD residue bridge
`residue_eq_phi_coeff_of_congr` is still monic-only and needs the analogous
non-monic restatement before a non-monic consumer can use it.

### "Package the recovery witnesses into `TrueFactorLift`" is the centered/raw trap

A directive asking you to derive a `TrueFactorLift` family (the hypothesis of
`bhksRecoveryCoreWithBound_some_factor_zpolyIrreducible_of_lift`,
`PartitionRefinement.lean`) from `RepresentsIntegerFactorAtLift` recovery
witnesses is **not** a packaging step — it asks for a witness recovery cannot
provide. `TrueFactorLift.support_product_eq` needs the **raw** integer product
`supportProduct L S = factor` (`Lattice.lean`, `supportProduct` is
`Array.polyProduct` with no mod reduction) plus `factor * cofactor = f` over ℤ.
`RepresentsIntegerFactorAtLift` / `RecoveredAtLift` give only a mod-`p^k`
congruence + the **centered** equality `centeredLiftPoly (liftedFactorProduct d
S) (p^k) = monicFactor` (already discharged by
`RecoveredAtLift.candidate_eq_of_monic_dvd`, `Basic.lean`) — i.e. the
`RecoveredLift.recovered_eq` shape, **not** `TrueFactorLift`. For a support of
size ≥ 2 over mod-`p^k` Hensel lifts the raw product overflows `p^k/2`, so the
raw equality (and `factor_mul`) is false; the `RecoveredLift` docstring
(`Lattice.lean`, "deliberately does not assert the raw integer equality") says
this outright. So: recovery → `RecoveredLift` is landable; recovery →
`TrueFactorLift` is the #7479-class exact-product / unscaled-support migration,
a separate structural remodel. Diagnose and skip the latter rather than
attempting it as a thin composition. (#7854 was skipped on exactly this, with
the added wrinkle that its executable extractor lived in an unmerged PR — for
any "residual after PR #N" issue, `grep` the named substrate symbols on `main`
first; if absent, the residual depends on the unmerged PR and cannot build
yet.)

**`RecoveredLift` cannot feed this column — the period trap (#7866, #7867).**
The lattice column `(trueFactorCLDVector L S)[natAdd factorCount j]` is
`∑_{i∈S} psiCut(zᵢ)` (sum of **per-factor** cuts; `cldRows = map (cldCoeffs …)`),
and `two_mul_natAbs_sum_psiCut_le` needs the **strong** input
`∑ᵢ centeredResiduePow p a (zᵢ) = y`, `|y| ≤ B` — the *integer* sum of per-factor
centered residues is small, forcing the wraparound `k = 0`. Only per-factor
`gᵢ ∣ f over ℤ` (raw `support_product_eq`, via
`residue_cldQuotientMod_eq_phi_coeff`) gives that. `RecoveredLift` carries only
`factor ∣ f` (`factor_mul`), so the best it yields is the **weak** aggregate
residue `centeredResiduePow p a (∑ zᵢ) = c` — which controls `aggregateCldTail`
(`Basic.lean:4665`, `psiCut` applied *once after summing*), **not**
`∑ psiCut(zᵢ)`. They differ by an unbounded period `p^{a-b}·k`. Concrete:
`p=2,a=4,b=1,z₁=z₂=8` gives `centeredResiduePow 2 4 16 = 0` (weak holds) yet
`∑ psiCut = 8`, `2·8 = 16 ≫ |T| = 2`. The **monic coordinate** only fixes the
`dilate (lc f)` transport in `recovered_eq` (`dilate` collapses at `lc=1`); it is
orthogonal to this period, so it does not rescue a per-factor-column producer.
Any "bound the **zero-period** tight column (`trueFactorCLDVector`) from
`RecoveredLift`" directive is unsound for this reason — do not reach for the
per-factor `tightColumnBound_of_lift` route from a `RecoveredLift`.

**The sound fix landed (#7876) and is NOT a basis redesign.** The executable
`bhksLatticeBasis` already carries the diagonal *period rows* `diag(p^(a−ℓⱼ))`, so
the *period-adjusted* tail `∑ psiCut(zᵢ) − tⱼ·p^(a−ℓⱼ)` is a genuine lattice
vector (`periodAdjustedVector`, `CLDColumnBound.lean`) — packaged as a
`SupportShortVectorData` (the period-adjusted certificate carrying its own
`vector`), **not** the zero-period `trueFactorCLDVector`.
`supportShortVectorData_of_recoveredLift` bounds each period-adjusted column by
`factorCount/2` from the aggregate residue (`recoveredLift_aggregate_residue`,
#7872) plus `two_mul_natAbs_sum_psiCut_period_le` (#7869), and
`cutProjectionHypotheses_of_shortVectors` (the existing `SupportShortVectorData`
consumer) carries it to the fast-disjunct endpoint
(`bhksRecoveryCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`). Two
load-bearing facts the earlier "skip" advice missed: (a) the period lemma's
*proof* gives `2|d| < T.card+1`, i.e. `≤ T.card` over ℤ — the tight column bound,
fitting the exact radius `4r+n·r²` (its stated `≤ T.card+1` was weaker than
proved; #7876 strengthened it in place); (b) the period reduction lives in the
lattice's *period rows*, applied to the ordinary per-factor cut sum — no
executable basis change (and no `aggregateCldTail` emission) is needed.

### M1 (`monicTarget`/`scale`) per-subset recovery: the strong scaled congruence is FALSE for proper factors (#8319)

The non-monic M1 recovery directive (the `RecoveredAtLiftM1` family producer
feeding the fast-core `hcut`) is repeatedly rescoped to "produce, per true
support `S`, `reduceModPow (scaledLiftedFactorProduct core d S) = reduceModPow
factor` with `factor` a primitive divisor of `core`." That congruence — the
`hscaled` field of the landed `recoveredAtLiftM1_of_recovery` (`Basic.lean`) and
of `cutProjectionHypotheses_of_recoveryData` (`CLDColumnBound.lean`) — is **not
merely unproduced; it is false** for any proper factor whose cofactor has
non-unit leading coefficient. `scaledLiftedFactorProduct core d S = scale
(leadingCoeff core) (∏S)` scales by the **full** `lc core = lc(g)·lc(h)`
regardless of `S`, while `∏S ≡ g/lc(g)` (the monic factor of `monicTarget`), so
`scale (lc core)(∏S) ≡ lc(h)·g (mod p^k)` — carrying the spurious constant
`lc(cofactor)`. Executable counterexample (`lake env lean`, pure-integer ZPoly
ops, no extern): `core=(2x+1)(x+3)`, `g=x+3`, `lc core=2`; `scale 2 (x+3)=2x+6`,
`reduceModPow (2x+6) 5 3 = [6,2] ≠ [3,1] = reduceModPow (x+3) 5 3`, yet
`primitivePart (2x+6) = x+3`. The strong form holds only at `lc(cofactor)=1` —
i.e. the **whole-product** support (`factor=core`), which is exactly what the
only producer
`scaledLiftedFactorProduct_congr_core_of_product_congr_monicTarget` covers.

So `recoveredAtLiftM1_of_recovery`'s premise is unsatisfiable for proper
supports — a dead end for the capstone despite compiling green. The structure's
*own* `RecoveredAtLiftM1.recovered_eq` is sound (it has the `primitivePart` that
strips `lc(h)`); only the `_of_recovery` constructor's strong hypothesis is
wrong. The sound path is (a) a primitivePart-aware constructor taking the honest
`scale (lc core)(∏S) ≡ c·factor (mod p^k)`, `c = lc(cofactor) > 0`, plus (b) a
producer of *that* honest per-subset congruence — the subset→integer-divisor
modular-factorization correspondence in the **scale** coordinate. (b) is the
#7479/#7866-class remodel: the correspondence exists only in the **dilate**
coordinate (`RepresentsIntegerFactorAtLift`/`RecoveredAtLift`, on which
`liftedTrueSupports` is defined; `dilate c q` coeff `cⁿ·qₙ` ≠ `scale c q` coeff
`c·qₙ`, no bridge), and `coreLiftData_liftedFactor_hensel_semantics`
(`LiftBridge.lean`) gives only the per-**factor** `hfac` `core ≡ gᵢ·h`, not
per-**subset** primitive-divisor recovery. Before claiming any rescoped #8319,
do not attempt the strong congruence — it is unsound; the real work is (b).

### Producers of data-carrying certificate structures must be `def`, not `theorem`

This layer has many certificate *structures* that carry data, not Props:
`SupportShortVectorData` (a `vector` field), `TrueFactorCLDVectorData`,
`CutProjectionHypotheses`, `RecoveredLift`. A producer concluding
`: <SuchStruct>` is a `def`, not a `theorem` — `theorem foo :
SupportShortVectorData L S` errors with "type of theorem `foo` is not a
proposition". Match the existing producers (`cutProjectionHypotheses_of_shortVectors`
is a `def`).

Inside such a `def` you **cannot `obtain`/`rcases` an `Exists`** to extract a
witness — the tactic fails with "recursor `Exists.casesOn` can only eliminate
into `Prop`" because the goal is data-valued (`Type`). This bites two common
shapes: the custom `∣` (`a ∣ b := ∃ r, b = a * r`, so `obtain ⟨cof, hcof⟩ :=
hdvd` fails) and any `…_getD_candidate`-style `∃ quotient, …` success witness.
Extract with `.choose` / `.choose_spec` instead (e.g. `have hcof :
M = cl * hdvd.choose := hdvd.choose_spec`; pass `hdvd.choose` as the cofactor
field). These layers run under `noncomputable section`, so `Classical.choice`
is free. If you must rewrite the *type* a `.choose` was taken over (e.g.
`rw [hindicators] at hSpec` where `hSpec := hex.choose_spec`), the motive breaks
("motive is not type correct"); `rw` the equation into the `Exists` *before*
taking `.choose_spec`.

Reusing `Recovery.lean` helpers (`liftedFactorSubsetsOfSupports`,
`selectedFactorArraysOfSupports_polyProduct`,
`bhksIndicatorSelectedFactors_expectedIndicatorArrayOfSupports`,
`supportPartitionByMinColumn_class_*`) from another file: they live in
`BHKS.ForwardRecoveryInputs`, *not* `BHKS` — reference them from inside a
`namespace ForwardRecoveryInputs` block (else autoImplicit silently turns the
unresolved name into a `Sort u_1` binder and you get a misleading "Function
expected"). Several recovery helpers are `private` (`selectedFactorsOfMembers_toList`,
the Mathlib-`Basic` `polyProduct_monic_of_all_monic`, the executable
`bhksIndicatorCandidate?_normalizeFactorSign`/`_leadingCoeff_nonneg`): prefer the
public `liftedFactorProduct_monic` for product monicity, and derive a
sign-normalization (`normalizeFactorSign c = c`) from positive leading
coefficient (`leadingCoeff_primitivePart_dilate_pos`) rather than de-privatizing
the executable layer (which forces a ~15-min `CrossCheck` rebuild).

### Projection equalities from a `*Lift` package: destructure, don't `rw [D.basis_eq]`

To prove `L.p = D.p` / `L.precision = D.a` for `D : RecoveredLift L S` (or
`TrueFactorLift`), do **not** `rw [D.basis_eq]` in the goal: `D`'s own type
mentions `L`, so abstracting `L` gives "motive is not type correct". Add a helper
lemma proved by the destructure pattern the namespace already uses
(`rcases D with ⟨…, basis_eq, …⟩; cases basis_eq; rfl`) — e.g.
`RecoveredLift.p_eq`/`precision_eq`/`cutThresholds_eq` — then consume it with
`:=` or `simp only [hLp]` (simp rewrites the *projection term* fine; only the
`rw [D.basis_eq]` whole-`L` abstraction fails).

### Kernel-facing recursive specs: structural recursion only

Definitions that cross-check `decide`s must kernel-reduce (design principle
11). Two traps, verified on v4.32.0-rc1:

- A multi-clause recursion whose clauses decrease *different* arguments (the
  padded-zip shape) gets an **auto-derived lexicographic measure**
  (`invImage`/`Prod.instWellFoundedRelation`), which does **not**
  kernel-reduce — even `decide +kernel` sticks. Restructure so one argument
  decreases in every clause (fold the asymmetric clause into a `List.map`,
  as in `DensePoly.zipPad`).
- Well-founded recursion with an explicit Nat measure
  (`termination_by xs.length + ys.length`) *does* kernel-reduce, but the
  definition is `@[irreducible]` by default, so plain `decide` still fails
  at every use site until you add `unseal foo in` or switch to
  `decide +kernel` (`@[semireducible]` is warned ineffective for WF
  definitions). For a spec with many downstream `decide` sites, structural
  recursion avoids all per-site annotations.

### Diagnosing "decide sticks": elaborator whnf vs kernel reduction

A stuck plain `decide` on a deep executable pipeline (e.g.
`decide (Hex.ZPoly.isIrreducible f)`, which runs the whole factorizer) does
**not** show that the kernel cannot reduce it — plain `decide` evaluates the
`Decidable` instance in the *elaborator*, whose whnf respects
`@[irreducible]` and never sees `unseal`-gated WF fixpoint bodies, so it
sticks on definitions the kernel unfolds without complaint. Before
concluding a kernel-decide route is infeasible (the wrong call was made once
on the `irreducibility!`/`factor_poly!` fallbacks, #8863), probe with
`decide +kernel`, and remember two refinements verified there:

- Under the module system the *kernel's* remaining obstacle is the exposure
  closure, and `import all` is **per-file, not recursive**: an umbrella
  `import all HexBerlekampZassenhaus` does not pull in dependency bodies.
  The stuck constant may be several libraries down (that case needed
  `HexHensel`, the matrix libs, and core's non-exposed `Fin.foldl` from
  `Init.Data.Fin.Fold`). Find it by descending with `Lean.Kernel.whnf`
  probes, not by guessing.
- With the closure complete, `WellFounded.Nat.fix` measures (fuel loops,
  divide-and-conquer recursions) all kernel-reduce at tolerable cost — the
  BZ factorizer replays a Swinnerton-Dyer quartic in seconds and degree 12
  in tens of seconds. The genuine hard boundary is an `@[extern]`-backed
  `opaque` in the path (e.g. `lllNative` in the lattice tier), which no
  amount of exposure fixes — scope kernel-decide features to inputs whose
  replay stays in the kernel-reducible tiers.
- For raw-`Expr` emission the `decide +kernel` equivalent is: build
  `of_decide_eq_true (Eq.refl true)` with the instance given explicitly and
  assign it *without* an elaborator `isDefEq` on the refl slot — the kernel
  verifies at declaration check. Runtime-precheck the Bool with the compiled
  evaluator first so failures surface as elaboration errors, and precheck
  kernel reducibility with `Lean.Kernel.whnf` so a missing `import all`
  closure produces a named error instead of a kernel type mismatch.
