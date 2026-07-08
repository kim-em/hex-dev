/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.Recombination
public meta import HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination

public section
set_option backward.proofsInPublic true

/-!
This module collects `factorClassical`/`Trial`/`Lattice`/`factorize` and the `factorize_scalar` theorems.
-/
namespace Hex

private theorem bhksRecoveryCoreWithBound_ne_none_of_recovery_on_schedule
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hfloor : bhksRecoveryFloor core ≤ target)
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hrecover :
      bhksRecover? core (ZPoly.toMonicLiftData core target primeData) = some factors) :
    bhksRecoveryCoreWithBound core B primeData start fuel ≠ none := by
  intro hnone
  have hsome :=
    bhksRecoveryCoreWithBound_isSome_of_recovery_on_schedule
      core B primeData hfloor hmem hrecover
  rw [hnone] at hsome
  simp at hsome

private def bhksRecoveryGuardPrimeData : PrimeChoiceData :=
  letI := bounds_five
  let c : SmallPrimeCandidate :=
    { p := 5, bounds := bounds_five, prime := prime_five }
  { p := 5
    fModP := ZPoly.modP 5 cldGuardF
    factorsModP := berlekampFactorsModP cldGuardF c }

#guard bhksRecoveryCoreWithBound cldGuardF 1 bhksRecoveryGuardPrimeData
    (initialHenselPrecision 1) (ZPoly.quadraticDoublingSteps 1 + 2) =
  none

-- With the CLD-adequacy acceptance gate, a coefficient bound below
-- `cldCoeffFloor cldGuardF = 32` cannot be accepted: the schedule reaches the
-- cap `B` while every success is still below the floor, so the loop reports
-- `none`.
#guard bhksRecoveryCoreWithBound cldGuardF 4 bhksRecoveryGuardPrimeData
    (initialHenselPrecision 4) (ZPoly.quadraticDoublingSteps 4 + 2) =
  none

-- At a bound that reaches the floor the first gated success is accepted: for
-- `cldGuardF` this is schedule index `k = 32` (lift precision `liftData.k = 3`,
-- modulus `5 ^ 3 = 125`), recovering the same factors.
#guard bhksRecoveryCoreWithBound cldGuardF 32 bhksRecoveryGuardPrimeData
    (initialHenselPrecision 32) (ZPoly.quadraticDoublingSteps 32 + 2) =
  some bhksGuardFactors

namespace ZPoly

/--
Optional prime-choice data for the monic polynomial sent to Hensel lifting.

This is the prime selector for every tier that lifts through
`toMonicLiftData` (fast, classical, lattice, slow modular): the selected
modular factor data is the Berlekamp-form mod-`p` factorisation of
`(toMonic core).monic`, the polynomial that `toMonicLiftData` passes to
`henselLiftData`, so the Hensel seeds match the lift target (#8519, #8533).
-/
@[expose]
def toMonicPrimeData? (core : ZPoly) : Option PrimeChoiceData :=
  choosePrimeData? (toMonic core).monic

/-- Internal Hensel precision bound for the slow exhaustive branch.

It preserves the public caller's coefficient bound while also covering the
monic transform used by `toMonicLiftData`. -/
def exhaustiveLiftBound (core : ZPoly) (B : Nat) : Nat :=
  max B (defaultFactorCoeffBound (toMonic core).monic)

theorem le_exhaustiveLiftBound (core : ZPoly) (B : Nat) :
    B ≤ exhaustiveLiftBound core B := by
  exact Nat.le_max_left B (defaultFactorCoeffBound (toMonic core).monic)

theorem monicBound_le_exhaustiveLiftBound (core : ZPoly) (B : Nat) :
    defaultFactorCoeffBound (toMonic core).monic ≤ exhaustiveLiftBound core B := by
  exact Nat.le_max_right B (defaultFactorCoeffBound (toMonic core).monic)

theorem toMonicPrimeData?_prime
    (core : ZPoly) (data : PrimeChoiceData)
    (hdata : toMonicPrimeData? core = some data) :
    Nat.Prime data.p := by
  exact choosePrimeData?_prime (toMonic core).monic data hdata

theorem toMonicPrimeData?_isGoodPrime
    (core : ZPoly) (data : PrimeChoiceData)
    (hdata : toMonicPrimeData? core = some data) :
    @isGoodPrime (toMonic core).monic data.p data.bounds = true := by
  exact choosePrimeData?_isGoodPrime (toMonic core).monic data hdata

theorem toMonicPrimeData?_factorsModP_berlekamp_form
    (core : ZPoly) (data : PrimeChoiceData)
    (hdata : toMonicPrimeData? core = some data) :
    factorsModPBerlekampForm (toMonic core).monic data := by
  obtain ⟨hzero, heq⟩ :=
    choosePrimeData?_factorsModP_berlekamp_form
      (toMonic core).monic data hdata
  exact ⟨toMonicPrimeData?_prime core data hdata, hzero, heq⟩

end ZPoly

private def exhaustiveNonMonicQuadraticGuard : ZPoly :=
  DensePoly.ofCoeffs #[1, 0, 2]

#guard (ZPoly.toMonic exhaustiveNonMonicQuadraticGuard).monic =
  DensePoly.ofCoeffs #[2, 0, 1]

#guard quadraticIntegerRootFactors? exhaustiveNonMonicQuadraticGuard = none

set_option maxHeartbeats 800000

/-- Classical-tier core factorisation (the small-`r` tier): size-ordered
subset recombination via `scaledRecombinationSmart`. Returns `none` when the subset budget is exhausted
before the search completes — an *untrustworthy* "no split" that the cost-based
dispatcher routes to the lattice tier rather than reporting as irreducible. A
genuine irreducible core (search completed within budget) returns `some #[core]`. -/
@[expose]
def classicalCoreFactorsWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Option (Array ZPoly) :=
  if B = 0 then
    some #[core]
  else
    let liftData := ZPoly.toMonicLiftData core (ZPoly.exhaustiveLiftBound core B) primeData
    let (res, stats) :=
      scaledRecombinationSmart (DensePoly.leadingCoeff core) core
        (liftModulus liftData) liftData.liftedFactors.toList
    if stats.budgetExhausted then
      none
    else
      match res with
      | some factors => some (if factors.isEmpty then #[core] else factors.toArray)
      | none => some #[core]

/-! ### Recursive per-remainder re-lift (#8625, deliverable 2)

The classical tier's irreducibility certificate for an unsplit remainder is
gated at the monic-core Mignotte floor of the WHOLE core (#8620): the
transported partition cannot certify below it. The only sound sub-floor
route is a fresh lift/partition/coverage stack per remainder, at the
remainder's OWN monic floor, reusing the parent's prime and per-remainder
tracked mod-p factors (re-running the prime walk or Berlekamp per remainder
was measured and rejected; see `reports/bz-recursive-relift-findings.md`
and the #8625 thread).

Structure: an escalation ladder lifts each node's tracked factors to
`k = 1, 2, 4, ...` strictly below the node's floor exponent, scanning
subsets of size at most `reliftSubFloorCap` for an early split (peels are
self-certifying via `exactQuotient?`, so the sub-floor scan carries no
coverage obligation); peeled pieces recurse with tracked data derived by
monic-dilation transport plus a mod-p divisibility filter. A node that
reaches its floor unsplit runs today's full budgeted scan
(`classicalCoreFactorsWithBound`) at its own floor, whose coverage
certifies irreducibility. Each rung re-lifts from the mod-p seeds
(incremental rung-to-rung lifting is a later optimization). -/

namespace FpPoly

/-- Monic dilation over `F_p`: scale coefficient `i` of `u` by
`c ^ (deg u - i)`, i.e. `(monicDilate c u)(x) = c ^ (deg u) * u (x / c)` for a
unit `c`. Monic polynomials map to monic polynomials, `monicDilate 1 = id`,
and `monicDilate c⁻¹` inverts `monicDilate c`. Transport for the recursive
re-lift: a peel `t = g * h` satisfies, coefficientwise over `ℤ`,
`(toMonic t).monic = D_{lc h} ((ZPoly.toMonic g).monic) * D_{lc g} ((toMonic h).monic)`
where `D` is this dilation, so the mod-p factors of a piece's monic transform
are the undilated tracked factors of the parent's. -/
@[expose]
def monicDilate {p : Nat} [ZMod64.Bounds p] (c : ZMod64 p) (u : FpPoly p) :
    FpPoly p :=
  FpPoly.ofCoeffs ((Array.range u.size).map fun i => u.coeff i * c ^ (u.size - 1 - i))

end FpPoly

/-- Tracked per-piece prime data for the recursive re-lift: the mod-p factors
of `(ZPoly.toMonic piece).monic` are the piece's tracked seed factors (the
mod-p side of the lifted pairs its peel consumed) undilated by the cofactor's
leading coefficient. `none` when the undilation is degenerate (the cofactor's
leading coefficient vanishes mod `p`) — impossible for pieces of degree at
least 2 at a good prime (the parent image would not be squarefree mod `p`),
and treated as a decline by the caller. -/
def piecePrimeData? {q : Nat} [ZMod64.Bounds q]
    (piece : ZPoly) (cofactorLc : Int) (seeds : List (FpPoly q)) :
    Option PrimeChoiceData :=
  let c := ZMod64.ofNat q (ZPoly.intModNat cofactorLc q)
  if c = 0 then
    none
  else
    some { p := q
           fModP := ZPoly.modP q (ZPoly.toMonic piece).monic
           factorsModP := (seeds.map (FpPoly.monicDilate c⁻¹)).toArray }

/-- Division-loop core of `boundedExactQuotient?`: synthetic division from the
top, aborting as soon as a quotient coefficient would exceed `qbound` in
magnitude or the candidate's leading coefficient does not divide the running
top coefficient (with a fast path skipping the exact-divisibility divisions
for monic candidates). Produces an UNVERIFIED quotient: only the wrapper's
re-multiplication guard confers soundness, so this loop carries no proof
obligations. -/
def boundedExactQuotientDiv (target cand : ZPoly) (qbound : Nat) :
    Option ZPoly := Id.run do
  let n := target.size
  let m := cand.size
  if m < 2 || m > n then return none
  let lc := cand.coeff (m - 1)
  if lc == 0 then return none
  let mut rem := target.toArray
  let dq := n - m
  let mut q : Array Int := Array.replicate (dq + 1) 0
  let monic := lc == 1
  for step in [0:dq + 1] do
    let i := dq - step
    let c := rem[i + m - 1]!
    let cq ← if monic then pure c
      else
        if c % lc != 0 then return none
        else pure (c / lc)
    if cq.natAbs > qbound then return none
    if cq != 0 then
      q := q.set! i cq
      for j in [0:m] do
        rem := rem.set! (i + j) (rem[i + j]! - cq * cand.coeff j)
  for j in [0:m - 1] do
    if rem[j]! != 0 then return none
  return some (DensePoly.ofCoeffs q)

/-- Exact division over `ℤ` with early abort, for the sub-floor peel: the
division loop (`boundedExactQuotientDiv`) rejects failing candidates cheaply,
and a success is verified by one re-multiplication, so soundness
(`boundedExactQuotient?_product`) reads off the guard exactly as for
`exactQuotient?` while failed candidates — the hot path of a sub-floor rung —
never pay a full generic `divMod` plus re-multiplication. Rejects constant
candidates; a `none` misses a peel at this rung only, so no completeness
obligation attaches. -/
@[expose]
def boundedExactQuotient? (target cand : ZPoly) (qbound : Nat) : Option ZPoly :=
  if 2 ≤ cand.size then
    (boundedExactQuotientDiv target cand qbound).bind fun quotient =>
      if quotient * cand == target then some quotient else none
  else
    none

/-- Successful bounded exact division extracts a multiplication witness. -/
theorem boundedExactQuotient?_product
    {target cand quotient : ZPoly} {qbound : Nat}
    (h : boundedExactQuotient? target cand qbound = some quotient) :
    quotient * cand = target := by
  unfold boundedExactQuotient? at h
  split at h
  · cases hdiv : boundedExactQuotientDiv target cand qbound with
    | none => rw [hdiv] at h; simp at h
    | some q' =>
        rw [hdiv] at h
        simp only [Option.bind_some] at h
        split at h
        · rename_i hcheck
          cases h
          exact beq_iff_eq.mp hcheck
        · simp at h
  · simp at h

/-- Successful bounded exact division certifies a nonconstant candidate. -/
theorem boundedExactQuotient?_cand_size
    {target cand quotient : ZPoly} {qbound : Nat}
    (h : boundedExactQuotient? target cand qbound = some quotient) :
    2 ≤ cand.size := by
  unfold boundedExactQuotient? at h
  split at h
  · assumption
  · simp at h

/-- Coefficientwise reduction mod `m` (plain residues; the candidate pipeline
centers afterwards via `centeredLiftPoly`). -/
def reduceModInt (g : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs (g.toArray.map (fun c => Int.emod c (Int.ofNat m)))

/-- Product of a subset of lifted factors, reduced mod `m` after each
multiply, so no intermediate coefficient grows beyond `m`. -/
def productModInt (s : List ZPoly) (m : Nat) : ZPoly :=
  s.foldl (fun acc g => reduceModInt (acc * g) m) (1 : ZPoly)

/-- First verified peel among the scaled candidates of one subset-size level
of `(lifted factor, mod-p seed)` pairs: returns the peeled factor, the seeds
its subset consumed, its quotient, and the unused complement. Peels are
self-certifying (`boundedExactQuotient?` re-verifies the product over `ℤ`),
so a miss certifies nothing — which keeps this loop free to be lean: a
plain trailing-coefficient divisibility test instead of the full floor-scan
prefilter, a modular subset product, and the monic fast path that skips the
dilate/primitive-part/sign normalisation (a product of monic lifted factors
under a monic transform is already primitive with positive leading
coefficient). -/
def subFloorPeelSize {q : Nat} [ZMod64.Bounds q]
    (coreLc : Int) (target : ZPoly) (modulus qbound : Nat) :
    List (List (ZPoly × FpPoly q) × List (ZPoly × FpPoly q)) →
      Option (ZPoly × List (FpPoly q) × ZPoly × List (ZPoly × FpPoly q))
  | [] => none
  | sc :: rest =>
      let raw := centeredLiftPoly (productModInt (sc.1.map (·.1)) modulus) modulus
      let c0 := raw.coeff 0
      if c0 != 0 && Int.emod (coreLc ^ (raw.size - 1) * target.coeff 0) c0 != 0 then
        subFloorPeelSize coreLc target modulus qbound rest
      else
        let candidate :=
          if coreLc == 1 && DensePoly.leadingCoeff raw == 1 then raw
          else
            normalizeFactorSign <| ZPoly.primitivePart <| ZPoly.dilate coreLc raw
        if shouldRecordPolynomialFactor candidate then
          match boundedExactQuotient? target candidate qbound with
          | some quotient => some (candidate, sc.1.map (·.2), quotient, sc.2)
          | none => subFloorPeelSize coreLc target modulus qbound rest
        else subFloorPeelSize coreLc target modulus qbound rest

/-- First verified peel across the subset-size levels in `sizes`, in order. -/
def subFloorPeel? {q : Nat} [ZMod64.Bounds q]
    (coreLc : Int) (target : ZPoly) (modulus qbound : Nat)
    (pairs : List (ZPoly × FpPoly q)) :
    (sizes : List Nat) →
      Option (ZPoly × List (FpPoly q) × ZPoly × List (ZPoly × FpPoly q))
  | [] => none
  | d :: ds =>
      match subFloorPeelSize coreLc target modulus qbound
          (subsetsOfSizeWithComplement pairs d) with
      | some res => some res
      | none => subFloorPeel? coreLc target modulus qbound pairs ds

/-- Greedy per-rung peel: repeatedly peel verified factors off `target`,
threading the complement of the lifted pairs (one lift serves the whole
rung), until no subset of size at most `min cap (r / 2)` divides; the final
remainder is then pushed unsplit with the leftover seeds. Any 2-way split
has a side covering at most half the local factors, so the `r / 2` clamp
loses no splits, and it also keeps the peel loop from consuming the whole
factor list (the remainder always retains at least one local factor).
`coreLc` stays the ORIGINAL node's leading coefficient down the peel chain,
matching the scaled-candidate construction of `scaledRecombinationSmartAux`
(the lifted factors belong to the node's monic transform). -/
def subFloorScan {q : Nat} [ZMod64.Bounds q]
    (coreLc : Int) (modulus cap qbound : Nat) :
    Nat → ZPoly → List (ZPoly × FpPoly q) →
      Array (ZPoly × List (FpPoly q)) → Array (ZPoly × List (FpPoly q))
  | 0, target, pairs, acc => acc.push (target, pairs.map (·.2))
  | fuel + 1, target, pairs, acc =>
      let hi := min cap (pairs.length / 2)
      match subFloorPeel? coreLc target modulus qbound pairs
          ((List.range hi).map (· + 1)) with
      | some (candidate, seeds, quotient, rest) =>
          subFloorScan coreLc modulus cap qbound fuel quotient rest
            (acc.push (candidate, seeds))
      | none => acc.push (target, pairs.map (·.2))

/-- Sub-floor escalation ladder for one node: lift the node's tracked mod-p
factors to `k = 1, 2, 4, ...` strictly below the node's floor exponent and
run the greedy capped peel at each rung. `some pieces` (at least two, each
paired with its tracked seeds) is the first rung's split; `none` means no
sub-floor split was found and the caller runs the full floor scan. -/
def reliftLadder (pd : PrimeChoiceData) (cap : Nat) (g : ZPoly)
    (floorK qbound : Nat) :
    (k fuel : Nat) →
      Option (Array (ZPoly × List (@FpPoly pd.p pd.bounds)))
  | _, 0 => none
  | k, fuel + 1 =>
      letI := pd.bounds
      if k < floorK then
        let lifted := ZPoly.multifactorLiftQuadratic pd.p k (ZPoly.toMonic g).monic
          (pd.factorsModP.map FpPoly.liftToZ)
        let pairs := lifted.toList.zip pd.factorsModP.toList
        let pieces := subFloorScan (DensePoly.leadingCoeff g) (pd.p ^ k) cap qbound
          (pairs.length + 1) g pairs #[]
        if pieces.size ≥ 2 then some pieces
        else reliftLadder pd cap g floorK qbound (2 * k) fuel
      else none

/-! ### Product soundness for the sub-floor peel

Every piece array the sub-floor machinery emits multiplies back to the node
target. Peels are gated by `boundedExactQuotient?`'s re-multiplication guard,
so these lemmas are structural inductions with no division reasoning. -/

private theorem polyProduct_push_factor (factors : Array ZPoly) (factor : ZPoly) :
    Array.polyProduct (factors.push factor) =
      Array.polyProduct factors * factor := by
  cases factors with
  | mk xs =>
      induction xs generalizing factor with
      | nil => simp [Array.polyProduct, ZPoly.one_mul_zpoly]
      | cons x xs ih => simp [Array.polyProduct, List.foldl_cons] at ih ⊢

/-- A successful single-level peel multiplies back to the target. -/
theorem subFloorPeelSize_product {p : Nat} [ZMod64.Bounds p]
    (coreLc : Int) (target : ZPoly) (modulus qbound : Nat)
    (l : List (List (ZPoly × FpPoly p) × List (ZPoly × FpPoly p)))
    {cand : ZPoly} {seeds : List (FpPoly p)} {quot : ZPoly}
    {rest : List (ZPoly × FpPoly p)}
    (h : subFloorPeelSize coreLc target modulus qbound l =
      some (cand, seeds, quot, rest)) :
    quot * cand = target := by
  induction l with
  | nil => simp [subFloorPeelSize] at h
  | cons sc tail ih =>
      simp only [subFloorPeelSize] at h
      split at h
      · exact ih h
      · -- candidate fast path / scaled path, then shouldRecord, then the match
        split at h
        · split at h
          · split at h
            · rename_i quotient hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hcand, -, hquot, -⟩ := h
              subst hcand
              subst hquot
              exact boundedExactQuotient?_product hq
            · exact ih h
          · exact ih h
        · split at h
          · split at h
            · rename_i quotient hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hcand, -, hquot, -⟩ := h
              subst hcand
              subst hquot
              exact boundedExactQuotient?_product hq
            · exact ih h
          · exact ih h

/-- A successful multi-level peel multiplies back to the target. -/
theorem subFloorPeel?_product {p : Nat} [ZMod64.Bounds p]
    (coreLc : Int) (target : ZPoly) (modulus qbound : Nat)
    (pairs : List (ZPoly × FpPoly p)) (sizes : List Nat)
    {cand : ZPoly} {seeds : List (FpPoly p)} {quot : ZPoly}
    {rest : List (ZPoly × FpPoly p)}
    (h : subFloorPeel? coreLc target modulus qbound pairs sizes =
      some (cand, seeds, quot, rest)) :
    quot * cand = target := by
  induction sizes with
  | nil => simp [subFloorPeel?] at h
  | cons d ds ih =>
      simp only [subFloorPeel?] at h
      generalize hlev : subFloorPeelSize coreLc target modulus qbound
        (subsetsOfSizeWithComplement pairs d) = res at h
      cases res with
      | none => exact ih h
      | some r =>
          cases h
          exact subFloorPeelSize_product coreLc target modulus qbound _ hlev

/-- The greedy per-rung peel's pieces multiply back to `acc`'s product times
the target. -/
theorem subFloorScan_polyProduct {p : Nat} [ZMod64.Bounds p]
    (coreLc : Int) (modulus cap qbound : Nat) :
    ∀ (fuel : Nat) (target : ZPoly) (pairs : List (ZPoly × FpPoly p))
      (acc : Array (ZPoly × List (FpPoly p))),
      Array.polyProduct
          ((subFloorScan coreLc modulus cap qbound fuel target pairs acc).map (·.1)) =
        Array.polyProduct (acc.map (·.1)) * target
  | 0, target, pairs, acc => by
      simp only [subFloorScan, Array.map_push, polyProduct_push_factor]
  | fuel + 1, target, pairs, acc => by
      simp only [subFloorScan]
      generalize hpeel : subFloorPeel? coreLc target modulus qbound pairs
        ((List.range (min cap (pairs.length / 2))).map (· + 1)) = res
      cases res with
      | none =>
          simp only [Array.map_push, polyProduct_push_factor]
      | some r =>
          obtain ⟨cand, seeds, quot, rest⟩ := r
          rw [subFloorScan_polyProduct coreLc modulus cap qbound fuel quot rest
            (acc.push (cand, seeds)),
            Array.map_push, polyProduct_push_factor, DensePoly.mul_assoc_poly]
          have hpq : quot * cand = target :=
            subFloorPeel?_product coreLc target modulus qbound pairs _ hpeel
          rw [show (cand, seeds).fst * quot = target from by
            rw [DensePoly.mul_comm_poly (S := Int)]; exact hpq]

/-- The ladder's split pieces multiply back to the node target. -/
theorem reliftLadder_polyProduct
    (pd : PrimeChoiceData) (cap : Nat) (g : ZPoly) (floorK qbound : Nat) :
    ∀ (k fuel : Nat) {pieces},
      reliftLadder pd cap g floorK qbound k fuel = some pieces →
      Array.polyProduct (pieces.map (·.1)) = g
  | k, 0, pieces, h => by simp [reliftLadder] at h
  | k, fuel + 1, pieces, h => by
      letI := pd.bounds
      simp only [reliftLadder] at h
      split at h
      · split at h
        · cases h
          rename_i hval
          have := subFloorScan_polyProduct (p := pd.p)
            (DensePoly.leadingCoeff g) (pd.p ^ k) cap qbound
            (((ZPoly.multifactorLiftQuadratic pd.p k (ZPoly.toMonic g).monic
                (pd.factorsModP.map FpPoly.liftToZ)).toList.zip
              pd.factorsModP.toList).length + 1) g
            ((ZPoly.multifactorLiftQuadratic pd.p k (ZPoly.toMonic g).monic
                (pd.factorsModP.map FpPoly.liftToZ)).toList.zip
              pd.factorsModP.toList) #[]
          simpa [Array.polyProduct, ZPoly.one_mul_zpoly] using this
        · exact reliftLadder_polyProduct pd cap g floorK qbound (2 * k) fuel h
      · simp at h

/-- Sub-floor scan-size cap for the recursive re-lift, per the #8625
measurement: cap 1 misses the pair splits of the Mignotte-swell family, and
larger caps grow the failed sub-floor scan tails combinatorially. -/
def reliftSubFloorCap : Nat := 2

/-- Recursive per-remainder classical certification (#8625): sub-floor ladder
plus recursion on peels, falling back to today's full floor scan
(`classicalCoreFactorsWithBound`) for nodes that never split early. Pieces
are certified at their OWN monic-core Mignotte floor — below the parent's
whenever the piece is a proper factor, which is the sub-floor win. `none`
declines to the lattice tier exactly as today (budget exhaustion in a floor
scan, or a tracked-data derivation failure the certification proof shows
unreachable). `fuel` dominates the split depth (every peel has positive
degree, so depth is at most the degree). -/
def classicalCoreFactorsRecursiveAux (cap : Nat) :
    Nat → ZPoly → Option Nat → PrimeChoiceData → Option (Array ZPoly)
  | 0, _, _, _ => none
  | fuel + 1, g, B?, pd =>
      if g.degree?.getD 0 ≤ 1 then
        some #[g]
      else if pd.factorsModP.size == 1 then
        some #[g]
      else
        let monicBound := ZPoly.defaultFactorCoeffBound (ZPoly.toMonic g).monic
        let floorK := precisionForCoeffBound
          (match B? with | some B => max B monicBound | none => monicBound) pd.p
        match reliftLadder pd cap g floorK monicBound 1 (floorK + 1) with
        | some pieces =>
            letI := pd.bounds
            let lcg := DensePoly.leadingCoeff g
            pieces.foldl (init := some #[]) fun acc? piece =>
              acc?.bind fun acc =>
                (piecePrimeData? piece.1 (lcg / DensePoly.leadingCoeff piece.1)
                    piece.2).bind fun pdPiece =>
                  (classicalCoreFactorsRecursiveAux cap fuel piece.1
                    none pdPiece).map (acc ++ ·)
        | none =>
            classicalCoreFactorsWithBound g
              (B?.getD (ZPoly.defaultFactorCoeffBound g)) pd

/-- Entry point for the recursive classical tier: same signature and decline
semantics as `classicalCoreFactorsWithBound`, with sub-floor per-remainder
certification. Not yet wired into `factorClassicalFactorsWithBound`; the
switch lands with the certification re-key. -/
@[expose]
def classicalCoreFactorsRecursive
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Option (Array ZPoly) :=
  if B = 0 then
    some #[core]
  else
    classicalCoreFactorsRecursiveAux reliftSubFloorCap
      (core.degree?.getD 0 + 1) core (some B) primeData

/-- Raw factor array for the classical small-`r` tier. Declines (`none`) on no
admissible prime or subset-budget exhaustion. -/
@[expose]
def factorClassicalFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
    | none =>
        (ZPoly.toMonicPrimeData? normalized.squareFreeCore).bind fun primeData =>
          (classicalCoreFactorsWithBound normalized.squareFreeCore B primeData).map fun coreFactors =>
            reassemblePolynomialFactors normalized coreFactors

def factorClassicalWithBound (f : ZPoly) (B : Nat) : Option Factorization :=
  (factorClassicalFactorsWithBound f B).map (factorizationOfFactors f)

/-- Factor via the size-ordered classical recombination tier at the default
Mignotte bound. The small-`r` tier of the cost-based hybrid; returns `none` when
no admissible prime is available or the subset budget is exceeded. -/
def factorClassical (f : ZPoly) : Option Factorization :=
  factorClassicalWithBound f (ZPoly.defaultFactorCoeffBound f)

/-- Per-`factorize` diagnostic trace, consumed by the merge-blocking performance gate.
`tier` records which path produced the answer (`constant` / `quadratic` /
`classical` / `noPrime`); `declined = true` marks an untrustworthy result (no
admissible prime, or subset-budget exhaustion) that the dispatcher routes onward.
As the lattice tier and dispatcher land, `tier`/`latticeDim` gain those cases. -/
structure FactorTrace where
  tier : String
  prime : Nat
  liftedFactorCount : Nat
  subsetCandidates : Nat
  declined : Bool
deriving Repr, DecidableEq

/-- Classical-tier factorisation with its diagnostic trace. The `Option` result
agrees with `factorClassicalWithBound f B`; the trace exposes the prime, the
lifted-factor count `r`, the recombination candidate count, and whether the tier
declined (budget exhausted / no admissible prime). -/
@[expose]
def factorClassicalTracedWithBound (f : ZPoly) (B : Nat) : Option Factorization × FactorTrace :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    (some (factorizationOfFactors f
        (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])),
      { tier := "constant", prime := 0, liftedFactorCount := 0, subsetCandidates := 0, declined := false })
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors =>
        (some (factorizationOfFactors f (reassemblePolynomialFactors normalized coreFactors)),
          { tier := "quadratic", prime := 0, liftedFactorCount := 0, subsetCandidates := 0, declined := false })
    | none =>
        match ZPoly.toMonicPrimeData? normalized.squareFreeCore with
        | none =>
            (none, { tier := "noPrime", prime := 0, liftedFactorCount := 0, subsetCandidates := 0, declined := true })
        | some primeData =>
            if B = 0 then
              (some (factorizationOfFactors f (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])),
                { tier := "classical", prime := primeData.p, liftedFactorCount := 0, subsetCandidates := 0, declined := false })
            else
              let core := normalized.squareFreeCore
              let liftData := ZPoly.toMonicLiftData core (ZPoly.exhaustiveLiftBound core B) primeData
              let (res, stats) :=
                scaledRecombinationSmart (DensePoly.leadingCoeff core) core
                  (liftModulus liftData) liftData.liftedFactors.toList
              let r := liftData.liftedFactors.size
              let trace : FactorTrace :=
                { tier := "classical", prime := primeData.p, liftedFactorCount := r,
                  subsetCandidates := stats.candidatesTried, declined := stats.budgetExhausted }
              if stats.budgetExhausted then
                (none, trace)
              else
                let coreFactors := match res with
                  | some factors => if factors.isEmpty then #[core] else factors.toArray
                  | none => #[core]
                (some (factorizationOfFactors f (reassemblePolynomialFactors normalized coreFactors)), trace)

/-- Classical-tier factorisation with trace, at the default Mignotte bound. -/
@[expose]
def factorClassicalTraced (f : ZPoly) : Option Factorization × FactorTrace :=
  factorClassicalTracedWithBound f (ZPoly.defaultFactorCoeffBound f)

/-- Subset-enumeration budget that runs the classical recombination search to
completion for `r` lifted factors: `2 ^ r` exceeds the total subset count, so the
search enumerates every subset and either splits or certifies irreducibility,
with no early stop. -/
def completionSubsetBudget (r : Nat) : Nat := 2 ^ r

/-- `scaledRecombinationSmart` with the #8530 level-aware tightening removed: the
supplied `budget` is used directly instead of `levelAwareSubsetBudget r budget`,
so the search runs to the full budget rather than stopping at the last completable
subset-size level. Reuses the same proven size/candidate loops; used only by the
benchmark `factorClassicalNoDecline` entry to expose the classical exponential
wall. Production `factorize` (via `scaledRecombinationSmart`) is untouched. -/
def scaledRecombinationFull
    (coreLc : Int) (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget : Nat) : Option (List ZPoly) × RecombStats :=
  let r := localFactors.length
  let (res, remaining) :=
    scaledRecombinationSmartAux coreLc f modulus localFactors budget
      (budget + (r + 1) * (2 * r + 3))
  (res,
    { candidatesTried := budget - remaining,
      budgetExhausted := res.isNone && remaining == 0 })

/-- Classical core factors run to completion: no level-aware tightening and no
early decline. On full enumeration with no split, returns the irreducible core
rather than declining; the only `none` comes from an upstream missing prime. Its
answers therefore always agree with the production tier where both terminate. -/
def classicalCoreFactorsToCompletion
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Option (Array ZPoly) :=
  if B = 0 then
    some #[core]
  else
    let liftData := ZPoly.toMonicLiftData core (ZPoly.exhaustiveLiftBound core B) primeData
    let r := liftData.liftedFactors.size
    let (res, _stats) :=
      scaledRecombinationFull (DensePoly.leadingCoeff core) core
        (liftModulus liftData) liftData.liftedFactors.toList (completionSubsetBudget r)
    match res with
    | some factors => some (if factors.isEmpty then #[core] else factors.toArray)
    | none => some #[core]

/-- Raw factor array for the no-decline classical tier; mirror of
`factorClassicalFactorsWithBound` using `classicalCoreFactorsToCompletion`. -/
def factorClassicalNoDeclineFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
    | none =>
        (ZPoly.toMonicPrimeData? normalized.squareFreeCore).bind fun primeData =>
          (classicalCoreFactorsToCompletion normalized.squareFreeCore B primeData).map fun coreFactors =>
            reassemblePolynomialFactors normalized coreFactors

def factorClassicalNoDeclineWithBound (f : ZPoly) (B : Nat) : Option Factorization :=
  (factorClassicalNoDeclineFactorsWithBound f B).map (factorizationOfFactors f)

/-- Classical recombination run to completion or cutoff, with the #8530 level-
aware early decline disabled. The `hexbz_factor_service --entry
factorClassicalNoDecline` line uses this to make the classical exponential wall
visible on the cross-system cactus charts: it runs the full subset enumeration
(so its answers are correct where it terminates) instead of declining high-`r`
cores to the lattice tier. Production `factorize`/`factorClassical` are untouched. -/
def factorClassicalNoDecline (f : ZPoly) : Option Factorization :=
  factorClassicalNoDeclineWithBound f (ZPoly.defaultFactorCoeffBound f)

-- (X-1)(X-2)(X-3): a reducible cubic (past the quadratic short-circuit) that the
-- size-ordered recombination must split into three linear factors.
private def classicalGuardCubic : ZPoly := DensePoly.ofCoeffs #[-6, 11, -6, 1]

#guard ((factorClassical classicalGuardCubic).map Factorization.product) = some classicalGuardCubic
#guard ((factorClassical classicalGuardCubic).map (·.factors.size)) = some 3
-- The no-decline entry agrees with the production classical tier where both terminate.
#guard ((factorClassicalNoDecline classicalGuardCubic).map Factorization.product) = some classicalGuardCubic
#guard ((factorClassicalNoDecline classicalGuardCubic).map (·.factors.size)) = some 3
-- A higher-`r` reducible (six linear factors): the no-decline enumeration must
-- recover all six, never collapse to a wrong irreducible core.
private def classicalGuardSextic : ZPoly := DensePoly.ofCoeffs #[720, -1764, 1624, -735, 175, -21, 1]
#guard ((factorClassicalNoDecline classicalGuardSextic).map Factorization.product) = some classicalGuardSextic
#guard ((factorClassicalNoDecline classicalGuardSextic).map (·.factors.size)) = some 6
#guard ((factorClassical classicalGuardSextic).map (·.factors.size)) = some 6
#guard ((factorClassical exhaustiveNonMonicQuadraticGuard).map Factorization.product)
  = some exhaustiveNonMonicQuadraticGuard

-- the traced variant's result agrees with `factorClassical`, and reports the
-- classical tier, no decline, and a small (size-ordered) candidate count.
#guard (factorClassicalTraced classicalGuardCubic).1 = factorClassical classicalGuardCubic
#guard (factorClassicalTraced classicalGuardCubic).2.tier = "classical"
#guard (factorClassicalTraced classicalGuardCubic).2.declined = false
#guard (factorClassicalTraced classicalGuardCubic).2.subsetCandidates ≤ 64

/-- Raw factor array produced by the integer trial-division slow path.

Handles the deg-0 core and integer-root cases up front via the same
constant/quadratic-root short-circuits as the classical tier; the residual
exhaustive branch dispatches to the standalone integer trial-division core
(`exhaustiveIntegerTrialCoreFactorsWithBound`). This is the trial-division
tier of the three-tier `factorize` combinator (SPEC PR #6580). -/
@[expose]
def factorTrialFactorsWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    reassemblePolynomialFactors normalized #[normalized.squareFreeCore]
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => reassemblePolynomialFactors normalized coreFactors
    | none =>
        let coreFactors :=
          exhaustiveIntegerTrialCoreFactorsWithBound normalized.squareFreeCore B
        reassemblePolynomialFactors normalized coreFactors

#guard factorTrialFactorsWithBound exhaustiveNonMonicQuadraticGuard 4 =
  #[exhaustiveNonMonicQuadraticGuard]

@[expose]
def factorTrialWithBound (f : ZPoly) (B : Nat) : Factorization :=
  factorizationOfFactors f (factorTrialFactorsWithBound f B)

/-- Characterise the bounded integer trial-division slow wrapper as the raw
factor array packed into the public `Factorization` representation. -/
theorem factorTrialWithBound_eq_factorizationOfFactors
    (f : ZPoly) (B : Nat) :
    factorTrialWithBound f B =
      factorizationOfFactors f (factorTrialFactorsWithBound f B) := rfl

/--
Factor using the integer trial-division path at the default Mignotte
coefficient bound. This is the trial-division tier of the three-tier
`factorize` combinator (SPEC PR #6580).
-/
def factorTrial (f : ZPoly) : Factorization :=
  factorTrialWithBound f (ZPoly.defaultFactorCoeffBound f)

#guard factorTrial exhaustiveNonMonicQuadraticGuard =
  factorizationOfFactors exhaustiveNonMonicQuadraticGuard #[exhaustiveNonMonicQuadraticGuard]

/--
Precision cap used by the public fast path.

The cap is the larger of the BHKS separation threshold bound of the
square-free core and the Mignotte coefficient bound of the input, so later
termination proofs can use the same precision for both lattice separation
and exact integer reconstruction.

The BHKS component is computed from `(normalizeForFactor f).squareFreeCore`
— the polynomial the CLD pipeline actually lifts and separates — not from
`f` itself: a square-free core can have a larger coefficient norm than `f`
(for `f = (x¹⁸ - 1)(x¹⁹ - 1)` the core `f / (x - 1)` has `coeffNormSq 36`
against `f`'s `4`, and `bhksBound core > bhksBound f`), so a cap keyed on
`f` can sit below the core's separation threshold (#8521).
-/
def latticePrecisionCap (f : ZPoly) : Nat :=
  let core := (normalizeForFactor f).squareFreeCore
  max (max (bhksBound core) (cldCoeffFloor core))
    (max (ZPoly.defaultFactorCoeffBound f)
      (max (ZPoly.defaultFactorCoeffBound core)
        (ZPoly.defaultFactorCoeffBound (ZPoly.toMonic core).monic)))

theorem bhksBound_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    bhksBound (normalizeForFactor f).squareFreeCore ≤ latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- The cap clears the CLD column-adequacy floor of the square-free core, so the
lattice tier's cap-precision run is column-adequate by construction (#8519). -/
theorem cldCoeffFloor_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    cldCoeffFloor (normalizeForFactor f).squareFreeCore ≤ latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem defaultFactorCoeffBound_le_latticePrecisionCap (f : ZPoly) :
    ZPoly.defaultFactorCoeffBound f ≤ latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The public precision cap clears the whole fast-core acceptance floor, so
the gated loop always has admissible precisions on its schedule (#8519). -/
theorem bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    bhksRecoveryFloor (normalizeForFactor f).squareFreeCore ≤ latticePrecisionCap f := by
  unfold bhksRecoveryFloor
  refine Nat.max_le.mpr ⟨cldCoeffFloor_squareFreeCore_le_latticePrecisionCap f,
    Nat.max_le.mpr ⟨?_, ?_⟩⟩
  · unfold latticePrecisionCap
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)
  · unfold latticePrecisionCap
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)

/-- The cap dominates the Mignotte bound of the square-free core itself, needed
by the true-support nonemptiness argument at cap precision (#8519). -/
theorem defaultFactorCoeffBound_squareFreeCore_le_latticePrecisionCap (f : ZPoly) :
    ZPoly.defaultFactorCoeffBound (normalizeForFactor f).squareFreeCore ≤
      latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)

/-- The cap dominates the Mignotte bound of the monic transform of the
square-free core, the `hbound` input of the toMonic partition producers
(#8519). -/
theorem defaultFactorCoeffBound_toMonic_squareFreeCore_le_latticePrecisionCap
    (f : ZPoly) :
    ZPoly.defaultFactorCoeffBound
        (ZPoly.toMonic (normalizeForFactor f).squareFreeCore).monic ≤
      latticePrecisionCap f := by
  unfold latticePrecisionCap
  exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)

/--
At the public precision cap, the monic lift for the square-free core clears
the BHKS separation threshold: `2 · bhksBound core < p ^ k`.  This is the
`hprec` obligation of the lattice tier's cap-precision irreducibility
certification (#8417 / #8521); it is what forces the cap's BHKS component to
be computed from the core rather than from `f`.
-/
theorem two_mul_bhksBound_squareFreeCore_lt_pow_cap
    (f : ZPoly) (primeData : PrimeChoiceData) (hp : 2 ≤ primeData.p) :
    2 * bhksBound (normalizeForFactor f).squareFreeCore <
      primeData.p ^
        (ZPoly.toMonicLiftData (normalizeForFactor f).squareFreeCore
          (latticePrecisionCap f) primeData).k := by
  have hk :
      (ZPoly.toMonicLiftData (normalizeForFactor f).squareFreeCore
          (latticePrecisionCap f) primeData).k =
        precisionForCoeffBound (latticePrecisionCap f) primeData.p := by
    unfold ZPoly.toMonicLiftData
    exact henselLiftData_k _ _ _
  rw [hk]
  have hle := bhksBound_squareFreeCore_le_latticePrecisionCap f
  have hspec := precisionForCoeffBound_spec hp (latticePrecisionCap f)
  omega

/-- Variant of `two_mul_bhksBound_squareFreeCore_lt_pow_cap` keyed on the
lattice tier's prime-selection witness, matching the shape of the `hprec`
side goal at the `factorLatticeFactorsWithBound` call site. -/
theorem two_mul_bhksBound_squareFreeCore_lt_pow_cap_of_choosePrimeData
    (f : ZPoly) (primeData : PrimeChoiceData)
    (hchoose :
      choosePrimeData? (normalizeForFactor f).squareFreeCore = some primeData) :
    2 * bhksBound (normalizeForFactor f).squareFreeCore <
      primeData.p ^
        (ZPoly.toMonicLiftData (normalizeForFactor f).squareFreeCore
          (latticePrecisionCap f) primeData).k :=
  two_mul_bhksBound_squareFreeCore_lt_pow_cap f primeData
    (choosePrimeData?_prime _ primeData hchoose).two_le

/-- Variant of `two_mul_bhksBound_squareFreeCore_lt_pow_cap` keyed on the
lattice tier's monic-transform prime-selection witness (#8519). -/
theorem two_mul_bhksBound_squareFreeCore_lt_pow_cap_of_toMonicPrimeData
    (f : ZPoly) (primeData : PrimeChoiceData)
    (hselected :
      ZPoly.toMonicPrimeData? (normalizeForFactor f).squareFreeCore = some primeData) :
    2 * bhksBound (normalizeForFactor f).squareFreeCore <
      primeData.p ^
        (ZPoly.toMonicLiftData (normalizeForFactor f).squareFreeCore
          (latticePrecisionCap f) primeData).k :=
  two_mul_bhksBound_squareFreeCore_lt_pow_cap f primeData
    (ZPoly.toMonicPrimeData?_prime _ primeData hselected).two_le

-- #8521 regression witness: for `f = (x¹⁸ - 1)(x¹⁹ - 1) = x³⁷ - x¹⁹ - x¹⁸ + 1`
-- the square-free core `f / (x - 1)` has `bhksBound` exceeding the pre-fix cap
-- `max (bhksBound f) (defaultFactorCoeffBound f)`, so keying the cap's BHKS
-- component on `f` undershoots the core's separation threshold.
#guard
  let f : ZPoly := DensePoly.ofCoeffs
    #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  bhksBound (normalizeForFactor f).squareFreeCore >
    max (bhksBound f) (ZPoly.defaultFactorCoeffBound f)

/-- The CLD recovery's equivalence-class partition at this precision is the single
all-ones class — the signature of an *irreducible* input (all lifted mod-`p`
factors form the one integer factor). At column-adequate precision
(`bhksRecoveryFloor core ≤ k`) this certifies irreducibility — the proven count
lower bound forces a reducible core to exhibit ≥ 2 classes there
(`latticeArm3_bhksSingleAllOnes_irreducible` in the Mathlib layer) — while
below the floor it may instead mean the lattice has not separated the factors
yet, so callers must only trust it at `k ≥ bhksRecoveryFloor core`. (A cap-free
CLD path would treat this partition as `degenerate` and decline, which is why
such a path "misses" on Swinnerton-Dyer inputs; the lattice tier uses this predicate, both
in `latticeCoreLoop`'s early stop and in the trailing cap check, to turn the
declined-but-certified case into a positive irreducibility verdict.) -/
@[expose]
def bhksSingleAllOnesPartition (f : ZPoly) (d : LiftData) : Bool :=
  -- Monic (`M2`) coordinate, matching `bhksRecoverClassified` (#8519).
  let L := bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let projected := bhksProjectedRows L hrows
    let indicators := bhksEquivalenceClassIndicators projected
    !indicators.isEmpty && !projected.projectedRows.isEmpty &&
      indicators.size == 1 && bhksIndicatorAllOnes projected.factorCount (indicators.getD 0 #[])
  else
    false

/-- The fused recovery step's all-ones flag equals `bhksSingleAllOnesPartition`:
both read the single-all-ones signature off the same CLD lattice / RREF indicator
partition, so the lattice tier reads it off the one lattice build the classifier
already ran (#8543). -/
private theorem bhksRecoverClassifiedWithAllOnes_snd (f : ZPoly) (d : LiftData) :
    (bhksRecoverClassifiedWithAllOnes f d).2 = bhksSingleAllOnesPartition f d := by
  rw [bhksRecoverClassifiedWithAllOnes, bhksSingleAllOnesPartition]
  by_cases hrows :
      1 ≤ (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).factorCount +
        (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).coeffWidth
  · simp only [dif_pos hrows]
  · simp only [dif_neg hrows]

/-- Lattice-tier recombination loop: `bhksRecoveryLoop` plus certificate-backed
early termination (#8395).  The split path is byte-identical to the fast loop —
below `floor` every step is skipped, and at/above `floor` a classified recovery
success is accepted immediately.  The single change is the `.degenerate` arm: at
`k ≥ floor` the loop re-examines the partition, and the single all-ones class is
accepted as a **sound** irreducibility certificate (`some #[core]`) instead of
advancing the schedule.  Soundness is not heuristic: at column-adequate precision
(`bhksRecoveryFloor core ≤ k`) the proven count lower bound forces a reducible core
to exhibit ≥ 2 equivalence classes, so all-ones can only be reported for a
genuinely irreducible core (`latticeArm3_bhksSingleAllOnes_irreducible` in the
Mathlib layer consumes exactly the `⟨k, floor ≤ k, all-ones⟩` witness this loop
produces).  Without the early stop the loop grinds the doubling schedule to the
conservative BHKS cap on every irreducible input.

Private: only `latticeCoreWithBound` (which passes `bhksRecoveryFloorGate core`) is
the semantically supported entry point; the bare `floor` parameter must not be
set independently. -/
private def latticeCoreLoop
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) :
    Nat → Nat → Option (Array ZPoly)
  | _k, 0 => none
  | k, fuel + 1 =>
      if k < floor then
        if k ≥ B then
          none
        else
          latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
      else
        -- Build the CLD lattice once per step and read both the classification
        -- and the single-all-ones certificate off it (#8543): the `.degenerate`
        -- arm below no longer re-runs `bhksSingleAllOnesPartition`, which would
        -- rebuild the whole Hensel-lift/CLD/LLL/indicator pipeline.
        let step := bhksRecoverClassifiedWithAllOnes core (ZPoly.toMonicLiftData core k primeData)
        match step.1 with
        | .success factors =>
          some factors
        | .candidateFailure =>
          if k ≥ B then
            none
          else
            latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .productMismatch _ =>
          if k ≥ B then
            none
          else
            latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .degenerate =>
          if step.2 then
            some #[core]
          else if k ≥ B then
            none
          else
            latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel

/-- Lattice-tier core loop entry: `bhksRecoveryCoreWithBound` with certificate-backed
early termination on the single all-ones partition (#8395).  Computes the CLD
column-adequacy floor once (through the irreducible `bhksRecoveryFloorGate`) and runs
`latticeCoreLoop`. -/
def latticeCoreWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    Option (Array ZPoly) :=
  latticeCoreLoop core B (bhksRecoveryFloorGate core) primeData k fuel

/-- Behavioural unfolding for the lattice-tier loop: the fused-step body is
propositionally equal to the two-call form (`bhksRecoverClassified` for the
classification, `bhksSingleAllOnesPartition` for the certificate).  The fused step
only shares the one lattice build across the classification and the all-ones flag
(#8543); `bhksRecoverClassifiedWithAllOnes_fst`/`_snd` pin the two projections to
those surfaces, so the loop's spec reasons about it exactly as before. -/
private theorem latticeCoreLoop_unfold
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    latticeCoreLoop core B floor primeData k (fuel + 1) =
      (if k < floor then
        if k ≥ B then
          none
        else
          latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
      else
        match bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
        | .success factors => some factors
        | .candidateFailure =>
          if k ≥ B then none
          else latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .productMismatch _ =>
          if k ≥ B then none
          else latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .degenerate =>
          if bhksSingleAllOnesPartition core (ZPoly.toMonicLiftData core k primeData) then
            some #[core]
          else if k ≥ B then none
          else latticeCoreLoop core B floor primeData (nextHenselPrecision k B) fuel) := by
  rw [latticeCoreLoop]
  by_cases hfl : k < floor
  · rw [if_pos hfl, if_pos hfl]
  · rw [if_neg hfl, if_neg hfl]
    simp only [bhksRecoverClassifiedWithAllOnes_fst, bhksRecoverClassifiedWithAllOnes_snd]

/-- Structural spec for the lattice-tier loop: every success is either a fast-loop
success (the split path is untouched) or the certificate-backed early stop — the
singleton `#[core]` together with a concrete witness precision `k'` at/above the
column-adequacy floor whose partition is the single all-ones class. -/
private theorem latticeCoreLoop_some_spec
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) :
    ∀ fuel k cf,
      latticeCoreLoop core B floor primeData k fuel = some cf →
        bhksRecoveryLoop core B floor primeData k fuel = some cf ∨
          (cf = #[core] ∧ ∃ k', floor ≤ k' ∧
            bhksSingleAllOnesPartition core (ZPoly.toMonicLiftData core k' primeData)
              = true) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k cf h
      simp [latticeCoreLoop] at h
  | succ fuel ih =>
      intro k cf h
      rw [latticeCoreLoop_unfold] at h
      rw [bhksRecoveryLoop]
      by_cases hfl : k < floor
      · rw [if_pos hfl] at h ⊢
        by_cases hk : k ≥ B
        · simp [hk] at h
        · rw [if_neg hk] at h ⊢
          exact ih _ cf h
      · rw [if_neg hfl] at h ⊢
        cases hclass : bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
        | success factors =>
            rw [hclass] at h
            exact Or.inl h
        | candidateFailure =>
            rw [hclass] at h
            by_cases hk : k ≥ B
            · simp [hk] at h
            · rw [if_neg hk] at h ⊢
              exact ih _ cf h
        | productMismatch cands =>
            rw [hclass] at h
            by_cases hk : k ≥ B
            · simp [hk] at h
            · rw [if_neg hk] at h ⊢
              exact ih _ cf h
        | degenerate =>
            rw [hclass] at h
            by_cases hones :
                bhksSingleAllOnesPartition core (ZPoly.toMonicLiftData core k primeData) = true
            · rw [if_pos hones] at h
              exact Or.inr ⟨(Option.some.inj h).symm,
                k, Nat.le_of_not_lt hfl, hones⟩
            · rw [if_neg hones] at h
              by_cases hk : k ≥ B
              · simp [hk] at h
              · rw [if_neg hk] at h ⊢
                exact ih _ cf h

/-- Public structural spec for `latticeCoreWithBound`: a success is either a
`bhksRecoveryCoreWithBound` success or the early irreducibility certificate — the
singleton `#[core]` with a witness precision `k'` clearing `bhksRecoveryFloor core`
whose partition is the single all-ones class.  The witness pair is exactly the
`hB_floor`/`hbhks` input of the Mathlib layer's
`latticeArm3_bhksSingleAllOnes_irreducible`. -/
theorem latticeCoreWithBound_some_spec
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData} {k fuel : Nat}
    {cf : Array ZPoly}
    (h : latticeCoreWithBound core B primeData k fuel = some cf) :
    bhksRecoveryCoreWithBound core B primeData k fuel = some cf ∨
      (cf = #[core] ∧ ∃ k', bhksRecoveryFloor core ≤ k' ∧
        bhksSingleAllOnesPartition core (ZPoly.toMonicLiftData core k' primeData)
          = true) := by
  rw [latticeCoreWithBound, bhksRecoveryFloorGate_eq] at h
  rcases latticeCoreLoop_some_spec core B (bhksRecoveryFloor core) primeData fuel k cf h with
    hfast | hcert
  · rw [bhksRecoveryCoreWithBound, bhksRecoveryFloorGate_eq]
    exact Or.inl hfast
  · exact Or.inr hcert

/-- Large-`r` lattice-tier core factorisation: the van Hoeij CLD recovery, plus
**irreducibility certification**. When the recovery splits `core`, use its
factors; when the loop's certificate-backed early stop fires (single all-ones
partition at column-adequate precision, #8395), `core` is irreducible
(`#[core]`); when the loop declines all the way to the cap, check the
cap-precision partition once more: the single all-ones class means `core` is
irreducible (`#[core]`), anything else is a genuine failure (`none`).

Both certification arms are gated on the column-adequacy floor: the loop's
early stop only examines the partition at `k ≥ bhksRecoveryFloorGate core`, and the
trailing cap check requires `bhksRecoveryFloorGate core ≤ B` — below the floor the
all-ones partition may merely mean the lattice has not separated the factors
yet, so certifying there would be unsound.  The public `factorLattice` supplies
`latticePrecisionCap`, which clears the floor by construction. -/
@[expose]
def latticeCoreFactorsWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Option (Array ZPoly) :=
  if primeData.factorsModP.size ≤ 1 then
    some #[core]
  else
    match latticeCoreWithBound core B primeData
        (initialHenselPrecision B) (ZPoly.quadraticDoublingSteps B + 2) with
    | some coreFactors => some coreFactors
    | none =>
        if bhksRecoveryFloorGate core ≤ B then
          if bhksSingleAllOnesPartition core (ZPoly.toMonicLiftData core B primeData) then
            some #[core]
          else
            none
        else
          none

/-- Raw factor array for the large-`r` lattice tier: the CLD lattice recovery,
certifying irreducibility at the cap so that Swinnerton-Dyer / high-`r`
irreducibles return `some #[f]` instead of `none`. -/
@[expose]
def factorLatticeFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  else if B = 0 then
    none
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
    | none =>
        -- Select the prime on the monic transform (`toMonicPrimeData?`, as the
        -- classical tier does): `latticeCoreFactorsWithBound` Hensel-lifts the
        -- selected modular factors against `(ZPoly.toMonic core).monic`, so the
        -- seeds must be that transform's mod-`p` factorisation.  Selecting on
        -- `core` itself breaks the lift invariant whenever
        -- `leadingCoeff core ≢ 1 (mod p)` (#8519).
        match ZPoly.toMonicPrimeData? normalized.squareFreeCore with
        | none => none
        | some primeData =>
            (latticeCoreFactorsWithBound normalized.squareFreeCore B primeData).map
              fun coreFactors => reassemblePolynomialFactors normalized coreFactors

@[expose]
def factorLatticeWithBound (f : ZPoly) (B : Nat) : Option Factorization :=
  (factorLatticeFactorsWithBound f B).map (factorizationOfFactors f)

/-- Van Hoeij CLD lattice tier (large-`r`) at the full BHKS precision cap.
Certifies irreducibility (unlike a cap-free CLD path), so it returns `some` on
Swinnerton-Dyer and cyclotomic high-`r` irreducibles. -/
@[expose]
def factorLattice (f : ZPoly) : Option Factorization :=
  factorLatticeWithBound f (latticePrecisionCap f)

-- Swinnerton-Dyer SD2 and Φ₁₅: irreducible over ℤ but split mod p; a cap-free
-- CLD path misses, `factorLattice` certifies them as single irreducible factors.
#guard ((factorLattice (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).map (·.factors.size)) = some 1
#guard ((factorLattice (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).map Factorization.product)
  = some (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])
#guard ((factorLattice (DensePoly.ofCoeffs #[1, -1, 0, 1, -1, 1, 0, -1, 1])).map (·.factors.size)) = some 1
-- a reducible input the CLD splits directly still works
#guard ((factorLattice (DensePoly.ofCoeffs #[6, 0, -5, 0, 1])).map Factorization.product)
  = some (DensePoly.ofCoeffs #[6, 0, -5, 0, 1])

/-- Cost-based hybrid dispatch (the public combinator, once swapped in).

**Policy: classical-first.** The size-ordered classical tier handles every input
within its subset budget — fast for reducibles (it peels factors) and bounded for
irreducibles (it exhausts subsets up to the budget, ~0.26s worst case, then
declines). The lattice tier is *correct but slow* (it grinds to the precision cap),
so we never run it speculatively: we run classical first and fall back to the
lattice only when classical declines (budget exhausted, i.e. `r` too large), then
to trial division when no admissible prime exists. This dominates an up-front
`r`-estimate that could mis-route a reducible high-`r` input to the slow lattice.

Returns the chosen `Factorization` and a `FactorTrace` whose `tier` records which
tier answered; `declined = true` marks that the classical tier did not answer and
a fallback was taken (the merge gate asserts this never happens unexpectedly).

**Self-certifying.** Each non-backstop tier's `Factorization` is accepted only
when it reconstructs the input (`Factorization.product φ = f`, decidable on
`ZPoly`); on the (corpus-never) miss it falls through to the proven
`factorTrial` backstop. This makes `Factorization.product (ZPoly.factorize f) = f`
provable unconditionally without yet proving the classical recombination loop
reconstructs (that, with per-factor irreducibility, is the separate re-proof
step). The classical tier is correct on the whole conformance corpus, so the
guard always passes there and the emitted factor/trace values are unchanged. -/
@[expose]
def factorTraced (f : ZPoly) : Factorization × FactorTrace :=
  match factorClassicalTraced f with
  | (some φ, trace) =>
      if Factorization.product φ = f then (φ, trace)   -- classical answered, certified
      else (factorTrial f, { trace with tier := "trial", declined := true })
  | (none, trace) =>
      match factorLattice f with
      | some φ =>
          if Factorization.product φ = f then (φ, { trace with tier := "lattice" })
          else (factorTrial f, { trace with tier := "trial", declined := true })
      | none => (factorTrial f, { trace with tier := "trial" })  -- totality backstop

/--
The public factorisation (SPEC *Hybrid dispatch*). There is no up-front tier
selection: the classical tier runs first under a level-aware subset budget and
its answer is accepted only when the packed product reconstructs `f`; on decline
(budget exhaustion or no admissible prime) the CLD lattice tier runs at the
lattice precision cap under the same self-certifying acceptance check; and any
residual falls through to the `factorTrial` totality backstop, which is
`choosePrimeData?`-independent and so makes `factorize` unconditionally correct
on every `ZPoly`. Total.

Lives in the `ZPoly` namespace so the public surface is dot-notation on a
polynomial: `f.factorize`.
-/
@[expose]
def ZPoly.factorize (f : ZPoly) : Factorization :=
  (factorTraced f).1

/-- The irreducible factors of `f` with their multiplicities: the `factors`
field of the full factorisation `f.factorize`. -/
@[expose]
def ZPoly.factors (f : ZPoly) : Array (ZPoly × Nat) :=
  (ZPoly.factorize f).factors

-- classical answers the corpus, including small/medium-r Swinnerton-Dyer / cyclotomic
-- irreducibles, so no fallback is taken (the lattice/trial arms cover only the
-- budget-exceeding tail and the no-prime case).
#guard Factorization.product (ZPoly.factorize (DensePoly.ofCoeffs #[6, 0, -5, 0, 1]))
  = DensePoly.ofCoeffs #[6, 0, -5, 0, 1]                                      -- reducible
#guard (factorTraced (DensePoly.ofCoeffs #[6, 0, -5, 0, 1])).2.tier = "classical"
#guard Factorization.product (ZPoly.factorize (DensePoly.ofCoeffs #[1, 0, -10, 0, 1]))
  = DensePoly.ofCoeffs #[1, 0, -10, 0, 1]                                     -- SD2, irreducible
#guard ((ZPoly.factorize (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).factors.size) = 1
#guard (factorTraced (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).2.tier = "classical"
#guard (factorTraced (DensePoly.ofCoeffs #[1, 0, -10, 0, 1])).2.declined = false

/-- The classical traced tier's `Factorization` agrees with the raw classical
factor array packed through `factorizationOfFactors f`. The traced variant only
adds the diagnostic `FactorTrace` in the `.2` component; its `.1` is the same
self-certifying-free classical answer as `factorClassicalFactorsWithBound`. -/
theorem factorClassicalTracedWithBound_fst (f : ZPoly) (B : Nat) :
    (factorClassicalTracedWithBound f B).1 =
      (factorClassicalFactorsWithBound f B).map (factorizationOfFactors f) := by
  unfold factorClassicalTracedWithBound factorClassicalFactorsWithBound
    classicalCoreFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp only [hdeg, if_true, Option.map_some]
  · simp only [hdeg, if_false]
    cases quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some cf => simp only [Option.map_some]
    | none =>
        cases ZPoly.toMonicPrimeData? (normalizeForFactor f).squareFreeCore with
        | none => simp only [Option.map_none, Option.bind_none]
        | some primeData =>
            simp only [Option.bind_some]
            by_cases hB : B = 0
            · simp only [hB, if_true, Option.map_some]
            · simp only [hB, if_false]
              generalize
                scaledRecombinationSmart
                  (DensePoly.leadingCoeff (normalizeForFactor f).squareFreeCore)
                  (normalizeForFactor f).squareFreeCore
                  (liftModulus
                    (ZPoly.toMonicLiftData (normalizeForFactor f).squareFreeCore
                      (ZPoly.exhaustiveLiftBound (normalizeForFactor f).squareFreeCore B)
                      primeData))
                  (ZPoly.toMonicLiftData (normalizeForFactor f).squareFreeCore
                      (ZPoly.exhaustiveLiftBound (normalizeForFactor f).squareFreeCore B)
                      primeData).liftedFactors.toList = rs
              obtain ⟨res, stats⟩ := rs
              by_cases hbudget : stats.budgetExhausted = true
              · rw [if_pos hbudget, if_pos hbudget]; rfl
              · rw [if_neg hbudget, if_neg hbudget]
                cases res with
                | some factors => simp only [Option.map_some]
                | none => simp only [Option.map_some]

/-- The CLD lattice tier's `Factorization` is the raw lattice factor array packed
through `factorizationOfFactors f`. -/
theorem factorLattice_eq_map (f : ZPoly) :
    factorLattice f =
      (factorLatticeFactorsWithBound f (latticePrecisionCap f)).map
        (factorizationOfFactors f) := rfl

/-- Raw factor array assembled by the cost-based hybrid, the bridge counterpart
of `factorFactors`-consuming structural lemmas.

Each non-backstop tier (`factorClassicalFactorsWithBound` / lattice) is accepted
only when its `factorizationOfFactors`-packed answer reconstructs `f` (the
self-certifying guard mirrored here), and every fallback is the proven
`factorTrial` backstop's raw array. The headline contract
`ZPoly.factorize f = factorizationOfFactors f (factorFactors f)` is
`factorize_eq_factorizationOfFactors`. -/
def factorFactors (f : ZPoly) : Array ZPoly :=
  match factorClassicalFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) with
  | some cf =>
      if Factorization.product (factorizationOfFactors f cf) = f then cf
      else factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
  | none =>
      match factorLatticeFactorsWithBound f (latticePrecisionCap f) with
      | some cf =>
          if Factorization.product (factorizationOfFactors f cf) = f then cf
          else factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
      | none => factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)

/-- The cost-based hybrid factorisation is the `factorizationOfFactors`-packed
form of its raw factor array `factorFactors`. Every tier (classical /
lattice / trial) assembles via `factorizationOfFactors f`, so this bridge lets
the structural `factorizationOfFactors_entry_*` lemmas re-point every
`factorize`-level entry contract onto the hybrid. -/
theorem factorize_eq_factorizationOfFactors (f : ZPoly) :
    ZPoly.factorize f = factorizationOfFactors f (factorFactors f) := by
  have htrial : factorTrial f =
      factorizationOfFactors f
        (factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)) := by
    rw [factorTrial, factorTrialWithBound_eq_factorizationOfFactors]
  unfold ZPoly.factorize factorTraced factorFactors
  have hclassical :
      (factorClassicalTraced f).1 =
        (factorClassicalFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)).map
          (factorizationOfFactors f) := by
    rw [factorClassicalTraced, factorClassicalTracedWithBound_fst]
  rcases hcl : factorClassicalTraced f with ⟨cres, trace⟩
  rw [hcl] at hclassical
  cases hcf : factorClassicalFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) with
  | some cf =>
      rw [hcf] at hclassical
      simp only [Option.map_some] at hclassical
      subst hclassical
      by_cases hp : Factorization.product (factorizationOfFactors f cf) = f
      · simp only [hp, if_true]
      · simp only [hp, if_false]; exact htrial
  | none =>
      rw [hcf] at hclassical
      simp only [Option.map_none] at hclassical
      subst hclassical
      simp only
      rw [factorLattice_eq_map]
      cases hl : factorLatticeFactorsWithBound f (latticePrecisionCap f) with
      | some cf =>
          simp only [Option.map_some]
          by_cases hp : Factorization.product (factorizationOfFactors f cf) = f
          · simp only [hp, if_true]
          · simp only [hp, if_false]; exact htrial
      | none =>
          simp only [Option.map_none]; exact htrial

/-- Every raw factor of the cost-based hybrid comes from one of its three
dispatch branches: the classical tier's certified output, the CLD lattice
tier's certified output, or the `factorTrial` totality backstop. It
exposes the branch source (mirroring `factorize_entry_mem_raw_source` for the
raw hybrid array) without leaking the private `factorizationOfFactors` guard, so
the Mathlib-side irreducibility assembly can case-split over the branches. -/
theorem factorFactors_mem_source (f : ZPoly) {raw : ZPoly}
    (hmem : raw ∈ (factorFactors f).toList) :
    (∃ cf, factorClassicalFactorsWithBound f (ZPoly.defaultFactorCoeffBound f) =
        some cf ∧ raw ∈ cf.toList) ∨
      (∃ cf, factorLatticeFactorsWithBound f (latticePrecisionCap f) =
        some cf ∧ raw ∈ cf.toList) ∨
      raw ∈ (factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)).toList := by
  unfold factorFactors at hmem
  rcases Option.eq_none_or_eq_some
      (factorClassicalFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)) with hcf | ⟨cf, hcf⟩
  · simp only [hcf] at hmem
    rcases Option.eq_none_or_eq_some
        (factorLatticeFactorsWithBound f (latticePrecisionCap f)) with hl | ⟨cf, hl⟩
    · simp only [hl] at hmem
      exact Or.inr (Or.inr hmem)
    · simp only [hl] at hmem
      rcases Classical.em (Factorization.product (factorizationOfFactors f cf) = f) with hp | hp
      · rw [if_pos hp] at hmem; exact Or.inr (Or.inl ⟨cf, hl, hmem⟩)
      · rw [if_neg hp] at hmem; exact Or.inr (Or.inr hmem)
  · simp only [hcf] at hmem
    rcases Classical.em (Factorization.product (factorizationOfFactors f cf) = f) with hp | hp
    · rw [if_pos hp] at hmem; exact Or.inl ⟨cf, hcf, hmem⟩
    · rw [if_neg hp] at hmem; exact Or.inr (Or.inr hmem)

/-- Smoke-test driver for the core-coordinate fast recovery: select the good
prime exactly as the fast path does, then run `coreRecover?` against the
`coreLiftData` (`monicTarget`) lift at the public precision cap.  Used by the
`#guard`s below to exercise `coreRecover?` end-to-end on real non-monic
multi-factor inputs; nothing in the production path routes through it (the
production `latticeCoreLoop` still consumes `bhksRecover?`). -/
private def coreRecoverSmoke? (c : ZPoly) : Option (Array ZPoly) :=
  match choosePrimeData? c with
  | some pd => coreRecover? c (ZPoly.coreLiftData c (latticePrecisionCap c) pd)
  | none => none

-- `(2x+1)(x⁴+1)`: recovers the two integer factors in `core`'s own coordinate.
#guard coreRecoverSmoke? (DensePoly.ofCoeffs #[1, 2, 0, 0, 1, 2]) =
  some #[DensePoly.ofCoeffs #[1, 0, 0, 0, 1], DensePoly.ofCoeffs #[1, 2]]
-- `(3x+2)(x²+2)`
#guard coreRecoverSmoke? (DensePoly.ofCoeffs #[4, 6, 2, 3]) =
  some #[DensePoly.ofCoeffs #[2, 3], DensePoly.ofCoeffs #[2, 0, 1]]
-- `(6x²-1)(x+5)`
#guard coreRecoverSmoke? (DensePoly.ofCoeffs #[-5, -1, 30, 6]) =
  some #[DensePoly.ofCoeffs #[5, 1], DensePoly.ofCoeffs #[-1, 0, 6]]
-- `2x²-3x+1 = (2x-1)(x-1)`
#guard coreRecoverSmoke? (DensePoly.ofCoeffs #[1, -3, 2]) =
  some #[DensePoly.ofCoeffs #[-1, 1], DensePoly.ofCoeffs #[-1, 2]]

-- Each recovered factorization multiplies back to the core input.
#guard (coreRecoverSmoke? (DensePoly.ofCoeffs #[1, 2, 0, 0, 1, 2])).map Array.polyProduct =
  some (DensePoly.ofCoeffs #[1, 2, 0, 0, 1, 2])
#guard (coreRecoverSmoke? (DensePoly.ofCoeffs #[4, 6, 2, 3])).map Array.polyProduct =
  some (DensePoly.ofCoeffs #[4, 6, 2, 3])
#guard (coreRecoverSmoke? (DensePoly.ofCoeffs #[-5, -1, 30, 6])).map Array.polyProduct =
  some (DensePoly.ofCoeffs #[-5, -1, 30, 6])
#guard (coreRecoverSmoke? (DensePoly.ofCoeffs #[1, -3, 2])).map Array.polyProduct =
  some (DensePoly.ofCoeffs #[1, -3, 2])

/--
Product of every odd prime searched by the historical bounded
`choosePrimeData?`: the fixed `smallPrimeCandidates` plus every prime formerly
materialized by the `73`/`128` extended list, namely
`3, 5, 7, 11, 13, 17, 19, 23, 31, 71, 73, 79, 83, 89, 97, 101, 103, 107,
109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
277, 281, 283, 293, 307, 311, 313, 317`.
-/
private def finitePrimeSearchProduct : Int :=
  8519695066439135286155430686880858459745606608870837864424372151015956571725147275621002356920661035228663328981905

/--
Regression fixture for the old bounded prime search. It is `P * X^2 + X + 1`,
where `P` is the product of every odd prime in the former closed candidate set.
The expanded SPEC prefix now includes primes that were not in that former set;
this fixture confirms one of them is enough to keep prime selection from
falling through to the no-prime branch on this input.
-/
private def finitePrimeSearchNoneQuadratic : ZPoly :=
  DensePoly.ofCoeffs #[1, 1, finitePrimeSearchProduct]

#guard
  match choosePrimeData? finitePrimeSearchNoneQuadratic with
  | none => false
  | some data => data.p == 29

set_option maxHeartbeats 800000

private theorem content_ne_zero_of_zpoly_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    ZPoly.content f ≠ 0 := by
  intro hcontent
  apply hf
  have hreconstruct := ZPoly.content_mul_primitivePart f
  rw [hcontent] at hreconstruct
  have hzero : DensePoly.scale (0 : Int) (ZPoly.primitivePart f) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale (R := Int) (0 : Int) (ZPoly.primitivePart f) n
      (Int.zero_mul 0)]
    rw [DensePoly.coeff_zero]
    exact Int.zero_mul _
  rw [hzero] at hreconstruct
  exact hreconstruct.symm

private theorem signedContentScalarContract_eq_zero_iff (f : ZPoly) :
    (if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f) = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_cases hf : f = 0
    · exact hf
    have hcontent_ne := content_ne_zero_of_zpoly_ne_zero f hf
    rw [if_neg hf] at h
    by_cases hneg : DensePoly.leadingCoeff f < 0
    · rw [if_pos hneg] at h
      exact absurd (Int.neg_eq_zero.mp h) hcontent_ne
    · rw [if_neg hneg] at h
      exact absurd h hcontent_ne
  · intro hf
    simp [hf]

/-- Scalar contract for a factorization assembled from a raw factor array.
The public statement exposes the signed-content convention without exposing
the private helper used to compute it. -/
theorem factorizationOfFactors_scalar (f : ZPoly) (rawFactors : Array ZPoly) :
    (factorizationOfFactors f rawFactors).scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  rfl

@[simp, grind =] theorem factorizationOfFactors_scalar_zero (rawFactors : Array ZPoly) :
    (factorizationOfFactors 0 rawFactors).scalar = 0 := by
  simp [factorizationOfFactors_scalar]

theorem factorizationOfFactors_scalar_of_leadingCoeff_neg
    {f : ZPoly} (rawFactors : Array ZPoly)
    (hf : f ≠ 0) (hneg : DensePoly.leadingCoeff f < 0) :
    (factorizationOfFactors f rawFactors).scalar = -ZPoly.content f := by
  simp [factorizationOfFactors_scalar, hf, hneg]

theorem factorizationOfFactors_scalar_of_leadingCoeff_pos
    {f : ZPoly} (rawFactors : Array ZPoly)
    (hf : f ≠ 0) (hpos : 0 < DensePoly.leadingCoeff f) :
    (factorizationOfFactors f rawFactors).scalar = ZPoly.content f := by
  have hnot_neg : ¬ DensePoly.leadingCoeff f < 0 := by omega
  simp [factorizationOfFactors_scalar, hf, hnot_neg]

theorem factorizationOfFactors_scalar_eq_zero_iff
    (f : ZPoly) (rawFactors : Array ZPoly) :
    (factorizationOfFactors f rawFactors).scalar = 0 ↔ f = 0 := by
  rw [factorizationOfFactors_scalar]
  exact signedContentScalarContract_eq_zero_iff f

/-- Scalar contract for the default public factorization entry point. -/
theorem factorize_scalar (f : ZPoly) :
    (ZPoly.factorize f).scalar =
      if f = 0 then
        0
      else if DensePoly.leadingCoeff f < 0 then
        -ZPoly.content f
      else
        ZPoly.content f := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar f (factorFactors f)

@[simp, grind =] theorem factorize_scalar_zero :
    (ZPoly.factorize 0).scalar = 0 := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_zero (factorFactors 0)

/-- The default factorization of `0` records no polynomial factors: the
square-free core of `0` is the unit `1`, so every reassembled raw factor is
dropped by the `shouldRecordPolynomialFactor` filter.  This lets the capstone
`factorize_irreducible_of_nonUnit` discharge the degenerate `f = 0` case
vacuously, without a nonzero hypothesis. -/
theorem factorize_zero_factors : (ZPoly.factorize (0 : ZPoly)).factors = #[] := by
  decide

theorem factorize_scalar_of_leadingCoeff_neg
    {f : ZPoly} (hf : f ≠ 0) (hneg : DensePoly.leadingCoeff f < 0) :
    (ZPoly.factorize f).scalar = -ZPoly.content f := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_of_leadingCoeff_neg (factorFactors f) hf hneg

theorem factorize_scalar_of_leadingCoeff_pos
    {f : ZPoly} (hf : f ≠ 0) (hpos : 0 < DensePoly.leadingCoeff f) :
    (ZPoly.factorize f).scalar = ZPoly.content f := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_of_leadingCoeff_pos (factorFactors f) hf hpos

theorem factorize_scalar_eq_zero_iff (f : ZPoly) :
    (ZPoly.factorize f).scalar = 0 ↔ f = 0 := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_scalar_eq_zero_iff f (factorFactors f)

/-- Every recorded entry of the default public factorization has positive
multiplicity. -/
theorem factorize_entry_multiplicity_pos
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList) :
    0 < entry.2 := by
  rw [factorize_eq_factorizationOfFactors] at hmem
  exact factorizationOfFactors_entry_multiplicity_pos f (factorFactors f) entry hmem

/-- Every recorded entry of the default public factorization is fixed by
`normalizeFactorSign`. -/
theorem factorize_entry_normalizeFactorSign_id
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList) :
    normalizeFactorSign entry.1 = entry.1 := by
  rw [factorize_eq_factorizationOfFactors] at hmem
  exact factorizationOfFactors_entry_normalizeFactorSign_id f (factorFactors f) entry hmem
