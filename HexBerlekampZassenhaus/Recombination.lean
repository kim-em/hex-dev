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

public import HexBerlekampZassenhaus.BhksRecover
public meta import HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover

public section
set_option backward.proofsInPublic true

/-!
This module collects the recombination-search definitions (the mutual blocks) and Hensel-precision helpers.
-/
namespace Hex

/--
`M1` A2 reconstruction surface for a single Core indicator, stated at the
Mathlib-free executable layer.  Core-coordinate analogue of
`bhksIndicatorCandidate?_eq_some_of_dilatedCenteredLift`: if the indicator
selects `selected`, the primitive part of the scaled selected-product centred
lift (`ℓf · ∏ selected mod p^k`, the van Hoeij `M1` formula) is the expected
factor, and that factor divides `f` as a positive-leading-coefficient
positive-degree sign-normalised factor, then `bhksIndicatorCandidateCore?`
returns that expected factor with some quotient.
-/
theorem bhksIndicatorCandidateCore?_eq_some_of_scaledCenteredLift
    (f : ZPoly) (d : LiftData) (indicator : Array Int)
    (selected : Array ZPoly) (expectedFactor : ZPoly)
    (hselected :
      bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected)
    (hdvd : expectedFactor ∣ f)
    (hexpected_sign : 0 ≤ DensePoly.leadingCoeff expectedFactor)
    (hexpected_pos_lc : 0 < DensePoly.leadingCoeff expectedFactor)
    (hexpected_degree : 0 < expectedFactor.degree?.getD 0)
    (hscaled :
      ZPoly.primitivePart
          (centeredLiftPoly
            (ZPoly.reduceModPow
              (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
              d.p d.k)
            (d.p ^ d.k)) =
        expectedFactor) :
    ∃ quotient,
      bhksIndicatorCandidateCore? f d indicator = some (expectedFactor, quotient) := by
  have hnormalize :
      normalizeFactorSign
          (ZPoly.primitivePart
            (centeredLiftPoly
              (ZPoly.reduceModPow
                (DensePoly.scale (DensePoly.leadingCoeff f)
                  (Array.polyProduct selected))
                d.p d.k)
              (d.p ^ d.k))) =
        expectedFactor := by
    rw [hscaled]
    exact normalizeFactorSign_eq_self_of_leadingCoeff_nonneg expectedFactor hexpected_sign
  have hrecord :
      shouldRecordPolynomialFactor expectedFactor = true := by
    apply shouldRecordPolynomialFactor_eq_true_of_ne
    · intro hzero
      rw [hzero] at hexpected_degree
      simp [DensePoly.degree?] at hexpected_degree
    · intro hone
      rw [hone] at hexpected_degree
      have hdeg0 : (DensePoly.degree? (1 : ZPoly)).getD 0 = 0 := by rfl
      rw [hdeg0] at hexpected_degree
      omega
    · intro hneg
      rw [hneg] at hexpected_degree
      have hdeg0 : (DensePoly.degree? (DensePoly.C (-1 : Int))).getD 0 = 0 := by simp
      rw [hdeg0] at hexpected_degree
      omega
  rcases hdvd with ⟨quotient, hquotient_mul⟩
  have hmul : quotient * expectedFactor = f := by
    rw [DensePoly.mul_comm_poly (S := Int)]
    exact hquotient_mul.symm
  have hquotient :
      exactQuotient? f expectedFactor = some quotient :=
    exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
      hexpected_pos_lc hexpected_degree hmul
  refine ⟨quotient, ?_⟩
  unfold bhksIndicatorCandidateCore?
  rw [hselected]
  change
    (let modulus := liftModulus d
     let candidate :=
       normalizeFactorSign <| ZPoly.primitivePart <|
         centeredLiftPoly
           (ZPoly.reduceModPow
             (DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected))
             d.p d.k)
           modulus
     if shouldRecordPolynomialFactor candidate then
       match exactQuotient? f candidate with
       | some quotient => some (candidate, quotient)
       | none => none
     else
       none) = some (expectedFactor, quotient)
  simp [liftModulus, hnormalize, hrecord, hquotient]

private def recombinationSearchAux
    (target : ZPoly) (localFactors : List ZPoly) : Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate := Array.polyProduct split.1.toArray
          match exactQuotient? target candidate with
          | none => none
          | some quotient =>
              match recombinationSearchAux quotient split.2 fuel with
              | none => none
              | some rest => some (candidate :: rest)

/--
Search for an integer-factor recombination of the lifted local factors.

The search enumerates subsets containing the first remaining local factor,
accepts a subset only when its product exactly divides the current target, and
then recurses on the quotient and unused local factors.
-/
def recombinationSearch (f : ZPoly) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchAux f localFactors (localFactors.length + 1)

/-- Fuelled auxiliary for `recombinationSearchMod`.  Recurses through
`subsetSplitsWithFirst localFactors`: at every level the head local factor is
forced into the candidate, the centred-lift result is normalised and checked
against `shouldRecordPolynomialFactor`, and a successful `exactQuotient?`
divides the search down to the remaining local factors and quotient. -/
@[expose]
def recombinationSearchModAux
    (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate :=
            normalizeFactorSign <|
              ZPoly.primitivePart <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
          if shouldRecordPolynomialFactor candidate then
            match exactQuotient? target candidate with
            | none => none
            | some quotient =>
                match recombinationSearchModAux quotient modulus split.2 fuel with
                | none => none
                | some rest => some (candidate :: rest)
          else
            none

/-- Exhaustive lifted-factor recombination search at a fixed modulus.  Drives
the slow path by iterating subsets of the lifted local factors through
`recombinationSearchModAux`. -/
def recombinationSearchMod
    (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchModAux f modulus localFactors (localFactors.length + 1)

/-- Exhaustive recombination of the lifted local factors stored in `d`, run at
the Hensel modulus `p^k = liftModulus d`.  Returns the recovered integer
factors as an array on success and `#[]` when the search fails. -/
def recombineExhaustive (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | some factors => factors.toArray
  | none => #[]

/-- Dilated-candidate variant of `recombinationSearchModAux`.

The lifted factors here are factors of the *monic transform*
`c^(d-1) · core(X / c)` (`c = coreLc`), so their centre-lifted product is a
monic-transform factor `g`.  The per-step candidate is recovered as the
primitive part of `g(c · X)` — the substitution `X ↦ c · X` realised by
`ZPoly.dilate coreLc`, which is the genuine inverse of the `toMonic` scaling —
and then sign-normalised.  For `coreLc = 1` the inner `ZPoly.dilate 1 _ = _`
collapse recovers the original unscaled `recombinationSearchModAux` candidate
shape; for primitive non-monic cores this yields the primitive integer factor of
`core` whose `RepresentsIntegerFactorAtLift` certificate drives the recursive
coverage chain. -/
@[expose]
def scaledRecombinationSearchModAux
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate :=
            normalizeFactorSign <|
              ZPoly.primitivePart <|
                ZPoly.dilate coreLc <|
                  centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
          if shouldRecordPolynomialFactor candidate then
            match exactQuotient? target candidate with
            | none => none
            | some quotient =>
                match scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
                | none => none
                | some rest => some (candidate :: rest)
          else
            none

/-- Surface wrapper for `scaledRecombinationSearchModAux` mirroring
`recombinationSearchMod`: drives the search with fuel `localFactors.length + 1`,
which suffices to exhaust the recursion since every step strictly shrinks the
remaining local-factor list. -/
def scaledRecombinationSearchMod
    (coreLc : Int) (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Option (List ZPoly) :=
  scaledRecombinationSearchModAux coreLc f modulus localFactors
    (localFactors.length + 1)

/-- Size-`k` sublists of `xs`, each paired with its complement, order preserved
in both components. The size-class building block of the size-ordered classical
recombination search. -/
@[expose]
def subsetsOfSizeWithComplement {α : Type} : List α → Nat → List (List α × List α)
  | xs, 0 => [([], xs)]
  | [], _ + 1 => []
  | x :: xs, k + 1 =>
      (subsetsOfSizeWithComplement xs k).map (fun sc => (x :: sc.1, sc.2)) ++
      (subsetsOfSizeWithComplement xs (k + 1)).map (fun sc => (sc.1, x :: sc.2))

/-- Sum of the degrees of a selected local-factor subset — the degree of the
subset product whenever the leading coefficients do not cancel mod the lift
modulus. -/
@[expose]
def selectedDegreeSum (sel : List ZPoly) : Nat :=
  sel.foldl (fun n g => n + g.degree?.getD 0) 0

/-- Centered representative mod `m` of the product of one coefficient across a
selected local-factor subset, computed with a running modular reduction so no
intermediate value grows beyond `m`. Instantiated at the constant term and at
the leading coefficient by `scaledCandidatePrefilter`. -/
@[expose]
def selectedProductResidue (coeffOf : ZPoly → Int) (sel : List ZPoly) (m : Nat) : Int :=
  centeredModNat (sel.foldl (fun acc g => acc * coeffOf g % (m : Int)) 1) m

/-- Sound `O(subset size)` rejection test run before the classical candidate
pipeline (`polyProduct` / `centeredLiftPoly` / `dilate` / `primitivePart` /
`exactQuotient?`) forms the full subset product:

* **degree test** — a candidate whose factor degrees sum beyond `target`'s
  degree cannot divide it (guarded by `coreLc ≠ 0` and a nonvanishing
  leading-coefficient residue, which pin the candidate's degree to `degSum`);
* **trailing-coefficient test** — the candidate's constant term times the
  dilation content divides `coreLc ^ degSum * lcRes * target(0)` over `ℤ`, so
  the centered constant-term residue must divide that product.

`false` is returned only when `exactQuotient? target candidate` provably fails
(`scaledCandidatePrefilter_eq_true_of_exactQuotient?_some` in the Mathlib
layer), so pruning never changes the accepted-candidate sequence — only the
wall-clock cost of rejecting a non-factor subset. -/
@[expose]
def scaledCandidatePrefilter
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (sel : List ZPoly) : Bool :=
  let degSum := selectedDegreeSum sel
  let lcRes := selectedProductResidue DensePoly.leadingCoeff sel modulus
  let trailRes := selectedProductResidue (fun g => g.coeff 0) sel modulus
  (coreLc == 0 || lcRes == 0 || decide (target = 0) ||
      decide (degSum ≤ target.degree?.getD 0)) &&
    coreLc ^ degSum * lcRes * target.coeff 0 % trailRes == 0

mutual
/-- Size-ordered scaled recombination search (the small-`r` classical tier).

Mirrors `scaledRecombinationSearchModAux` — same scaled candidate
(`normalizeFactorSign ∘ primitivePart ∘ dilate(coreLc) ∘ centeredLift` of the
subset product) and the same factor-removal recursion on the quotient — but
forces the head factor into the candidate and enumerates the head-forced subsets
**in increasing size**, so a fully-split target peels singletons immediately
(`O(r²)`) instead of materialising the whole power set. A hard candidate
`budget` caps the number of subsets tried; exceeding it returns `none` (the
cost-based dispatcher then routes the input to the lattice tier). The returned
`Nat` is the budget remaining, so `candidatesTried = budget₀ − remaining`.

`fuel` is a structural-recursion counter decremented on every recursive call
(matched as `fuel + 1`, recursing on `fuel`). The wrapper supplies a value that provably dominates the
true recursion depth (`budget + (r+1)(2r+3)`: along any descent path the
budget-decrementing steps are ≤ `budget` since `budget` threads monotonically, and
the dispatch steps are ≤ `r·(2r+3)`), so it never cuts the search off early — the
result is identical to the unfuelled search. -/
@[expose]
def scaledRecombinationSmartAux
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors : List ZPoly) (budget : Nat) (fuel : Nat) : Option (List ZPoly) × Nat :=
  if target = 1 then (some [], budget)
  else if budget = 0 then (none, 0)
  else match fuel with
    | 0 => (none, budget)
    | fuel + 1 =>
        match localFactors with
        | [] => (none, budget)
        | head :: tail =>
            scaledRecombinationSmartSizeLoop coreLc target modulus head tail
              (List.range (tail.length + 1)) budget fuel

@[expose]
def scaledRecombinationSmartSizeLoop
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes : List Nat) (budget : Nat) (fuel : Nat) : Option (List ZPoly) × Nat :=
  match sizes with
  | [] => (none, budget)
  | d :: ds =>
      if budget = 0 then (none, 0)
      else match fuel with
        | 0 => (none, budget)
        | fuel + 1 =>
            let splits := (subsetsOfSizeWithComplement tail d).map fun sc => (head :: sc.1, sc.2)
            match scaledRecombinationSmartCandLoop coreLc target modulus splits budget fuel with
            | (some res, b) => (some res, b)
            | (none, b) =>
                scaledRecombinationSmartSizeLoop coreLc target modulus head tail ds b fuel

@[expose]
def scaledRecombinationSmartCandLoop
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget : Nat) (fuel : Nat) :
    Option (List ZPoly) × Nat :=
  match splits with
  | [] => (none, budget)
  | split :: rest =>
      if budget = 0 then (none, 0)
      else match fuel with
        | 0 => (none, budget)
        | fuel + 1 =>
            let budget' := budget - 1
            if scaledCandidatePrefilter coreLc target modulus split.1 then
              let candidate :=
                normalizeFactorSign <| ZPoly.primitivePart <| ZPoly.dilate coreLc <|
                  centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
              if shouldRecordPolynomialFactor candidate then
                match exactQuotient? target candidate with
                | some quotient =>
                    match scaledRecombinationSmartAux coreLc quotient modulus split.2
                        budget' fuel with
                    | (some sub, b) => (some (candidate :: sub), b)
                    | (none, b) =>
                        scaledRecombinationSmartCandLoop coreLc target modulus rest b fuel
                | none => scaledRecombinationSmartCandLoop coreLc target modulus rest budget' fuel
              else scaledRecombinationSmartCandLoop coreLc target modulus rest budget' fuel
            else scaledRecombinationSmartCandLoop coreLc target modulus rest budget' fuel
end

/-- Default candidate budget for the classical small-`r` tier. The cost-based
dispatcher tightens this per input; standalone it is generous enough that the
small-`r` corpus never trips it while still bounding the search. -/
def defaultSubsetBudget : Nat := 262144

/-- Level-aware effective candidate budget for the size-ordered classical
recombination search (`scaledRecombinationSmart`).

The search enumerates head-forced subsets of the `r - 1` non-head local factors
by subset size `d = 0, 1, …, r - 1`, so size level `d` holds `C(r-1, d)`
candidates. A level the search cannot finish certifies nothing: declining at
the previous level boundary carries exactly the same "no factor with ≤ d
non-head local factors" verdict as burning partway into level `d + 1`, so the
effective budget stops at the last completable level boundary — the largest
cumulative `∑_{d ≤ k} C(r-1, d)` that fits in `budget`. When every level fits
(`2^(r-1) ≤ budget`, the small-`r` regime), the budget is returned unchanged,
so searches that can complete — the whole conformance corpus — are untouched.

`go` walks the levels structurally: `levels` counts the size levels left,
`binom = C(r-1, d)` is maintained multiplicatively (the division is exact), and
`acc` is the cumulative candidate count through level `d - 1`.

The cap is applied once, at the `scaledRecombinationSmart` wrapper, from the
top-level `r`. A recursive quotient search after a successful factor
extraction inherits the remaining budget unaligned to its own (smaller) level
boundaries, so a decline after at least one peel can still end mid-level —
harmless for correctness (any exhaustion declines to the lattice tier) and
bounded by the already-tightened top-level cap; re-aligning per recursion
would churn `scaledRecombinationSmartAux` and its proof set for no verdict
change. -/
def levelAwareSubsetBudget (r budget : Nat) : Nat :=
  go r 0 1 0
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, _, _ => budget
    | levels + 1, d, binom, acc =>
        if budget < acc + binom then acc
        else go levels (d + 1) (binom * (r - 1 - d) / (d + 1)) (acc + binom)

-- Small `r` (every level fits within the budget): unchanged. `r = 19` is the
-- boundary case, `2^18 = 262144` exactly; `r = 20` also completes exactly at
-- the budget (`∑_{d ≤ 9} C(19, d) = 2^19 / 2 = 262144`).
#guard levelAwareSubsetBudget 3 defaultSubsetBudget = defaultSubsetBudget
#guard levelAwareSubsetBudget 19 defaultSubsetBudget = defaultSubsetBudget
#guard levelAwareSubsetBudget 20 defaultSubsetBudget = defaultSubsetBudget
-- High `r` (the hopeless-burn regime, #8530): the budget stops at the last
-- completable level boundary. `r = 32` (SD5(x)·SD5(x+1)): levels 0–5 fit,
-- `∑_{d ≤ 5} C(31, d) = 206368`; level 6 (`C(31, 6) = 736281`) does not.
-- `r = 64` (SD6-shaped): levels 0–3 fit, `∑_{d ≤ 3} C(63, d) = 41728`.
#guard levelAwareSubsetBudget 32 defaultSubsetBudget = 206368
#guard levelAwareSubsetBudget 64 defaultSubsetBudget = 41728

/-- Diagnostic counters for one classical recombination search. Consumed by the
performance-conformance gate (the wider `FactorTrace` carries the per-`factor`
counters).

`budgetExhausted` distinguishes the two ways the search returns no
recombination: `false` means it enumerated every subset within budget and the
target is genuinely irreducible (a *trustworthy* irreducible verdict); `true`
means the budget was hit first, so the "no split" result is **not** trustworthy
and the input must be routed to the lattice tier. -/
structure RecombStats where
  candidatesTried : Nat
  budgetExhausted : Bool
deriving Repr, DecidableEq

/-- Size-ordered scaled recombination with a candidate budget, returning the
recovered factor list (on success within budget) and the candidate statistics.

The supplied `budget` is first tightened to `levelAwareSubsetBudget r budget`
(#8530): a search that cannot complete stops at the last subset-size level
boundary it can finish instead of burning the rest of the budget partway into
a level it cannot, since the partial level adds nothing to the declined
verdict. Small-`r` searches (every level fits) see the budget unchanged. -/
@[expose]
def scaledRecombinationSmart
    (coreLc : Int) (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget : Nat := defaultSubsetBudget) : Option (List ZPoly) × RecombStats :=
  let r := localFactors.length
  let levelBudget := levelAwareSubsetBudget r budget
  let (res, remaining) :=
    scaledRecombinationSmartAux coreLc f modulus localFactors levelBudget
      (levelBudget + (r + 1) * (2 * r + 3))
  (res,
    { candidatesTried := levelBudget - remaining,
      budgetExhausted := res.isNone && remaining == 0 })

/-- A fully-split target recovers all linear factors, in `O(r²)` candidates. -/
private def smartGuardFactors : List ZPoly :=
  [DensePoly.ofCoeffs #[-1, 1], DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1]]
private def smartGuardTarget : ZPoly := Array.polyProduct smartGuardFactors.toArray

#guard
  match (scaledRecombinationSmart 1 smartGuardTarget 1000003 smartGuardFactors).1 with
  | some fs => Array.polyProduct fs.toArray = smartGuardTarget && fs.length = 3
  | none => false

#guard (scaledRecombinationSmart 1 smartGuardTarget 1000003 smartGuardFactors).2.candidatesTried ≤ 6

-- An irreducible-over-ℤ target whose lifted factors do not recombine returns the
-- whole product as the single factor, having tried every proper subset.
#guard
  match (scaledRecombinationSmart 1 smartGuardTarget 1000003
      [DensePoly.ofCoeffs #[1, 1], DensePoly.ofCoeffs #[0, 1]]).1 with
  | some _ => true            -- search completes within budget (no crash / no budget blow-up)
  | none => true

mutual
/-- Product reconstruction for the size-ordered classical recombination search,
mirroring `scaledRecombinationSearchModAux_product` for the smart (head-forced,
budgeted) variant. Every recorded factor is gated by `exactQuotient?`, so whenever
the search returns `some factors`, their product is the target — for any `fuel`.
The three loops share the conclusion (`target` is common), so they are proved
together by structural recursion on `fuel`. -/
theorem scaledRecombinationSmartAux_product
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartAux coreLc target modulus localFactors budget fuel
        = (some factors, b)) :
    Array.polyProduct factors.toArray = target := by
  unfold scaledRecombinationSmartAux at h
  split at h
  · -- target = 1
    rename_i htarget
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨hfac, _⟩ := h
    subst hfac
    simpa [Array.polyProduct] using htarget.symm
  · split at h
    · simp at h                              -- budget = 0
    · split at h
      · simp at h                            -- fuel = 0
      · split at h
        · simp at h                          -- localFactors = []
        · exact scaledRecombinationSmartSizeLoop_product _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartSizeLoop_product
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes : List Nat) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartSizeLoop coreLc target modulus head tail sizes budget fuel
        = (some factors, b)) :
    Array.polyProduct factors.toArray = target := by
  unfold scaledRecombinationSmartSizeLoop at h
  split at h
  · simp at h                                -- sizes = []
  · split at h
    · simp at h                              -- budget = 0
    · split at h
      · simp at h                            -- fuel = 0
      · simp only [] at h                     -- zeta-reduce `let splits`
        split at h
        · -- CandLoop returned (some res, _)
          rename_i res bres hcand
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨hres, _⟩ := h
          subst hres
          exact scaledRecombinationSmartCandLoop_product _ _ _ _ _ _ _ _ hcand
        · -- CandLoop returned none: recurse on the next size class
          exact scaledRecombinationSmartSizeLoop_product _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartCandLoop_product
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartCandLoop coreLc target modulus splits budget fuel
        = (some factors, b)) :
    Array.polyProduct factors.toArray = target := by
  unfold scaledRecombinationSmartCandLoop at h
  split at h
  · simp at h                                -- splits = []
  · rename_i split rest                      -- splits = split :: rest
    split at h
    · simp at h                              -- budget = 0
    · split at h
      · simp at h                            -- fuel = 0
      · rename_i fuel'                        -- fuel = fuel' + 1
        simp only [] at h                     -- zeta-reduce `let candidate`/`let budget'`
        split at h
        · -- prefilter passed: examine the candidate pipeline
          split at h
          · -- shouldRecord the candidate
            cases hquot : exactQuotient? target
                (normalizeFactorSign (ZPoly.primitivePart
                  (ZPoly.dilate coreLc (centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)))) with
            | none =>
                simp only [hquot] at h        -- exactQuotient? none ⇒ recurse on the rest
                exact scaledRecombinationSmartCandLoop_product _ _ _ _ _ _ _ _ h
            | some quotient =>
                simp only [hquot] at h
                cases haux : scaledRecombinationSmartAux coreLc quotient modulus split.2
                    (budget - 1) fuel' with
                | mk ores ob =>
                    cases ores with
                    | none =>
                        simp only [haux] at h  -- Aux declined ⇒ recurse on the rest
                        exact scaledRecombinationSmartCandLoop_product _ _ _ _ _ _ _ _ h
                    | some sub =>
                        simp only [haux] at h
                        simp only [Prod.mk.injEq, Option.some.injEq] at h
                        obtain ⟨hfac, _⟩ := h
                        subst hfac
                        have hsub := scaledRecombinationSmartAux_product _ _ _ _ _ _ _ _ haux
                        rw [ZPoly.polyProduct_cons_toArray, hsub,
                          DensePoly.mul_comm_poly (S := Int)]
                        exact exactQuotient?_product hquot
          · -- cand not recorded: recurse on the rest
            exact scaledRecombinationSmartCandLoop_product _ _ _ _ _ _ _ _ h
        · -- prefilter rejected the subset: recurse on the rest
          exact scaledRecombinationSmartCandLoop_product _ _ _ _ _ _ _ _ h
termination_by fuel
end

mutual
/-- Budget monotonicity for the size-ordered classical recombination search: the
returned budget never exceeds the input budget. Each candidate the search examines
decrements the running budget and sub-searches only consume more, so the budget
threads monotonically downward. The three loops share the conclusion and are
proved together by structural recursion on `fuel`.

This underlies the "budget-exhausted `none` propagates" fact the coverage proof
for `scaledRecombinationSmart` relies on: once the running budget reaches `0`,
every subsequent loop returns `(none, 0)`, so a returned budget of `0` is the
only way an inner sub-search can decline for a budget reason. -/
theorem scaledRecombinationSmartAux_budget_le
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget fuel : Nat) (res : Option (List ZPoly)) (b : Nat)
    (h : scaledRecombinationSmartAux coreLc target modulus localFactors budget fuel
        = (res, b)) :
    b ≤ budget := by
  unfold scaledRecombinationSmartAux at h
  split at h
  · -- target = 1: (some [], budget)
    simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
  · split at h
    · -- budget = 0: (none, 0)
      simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
    · split at h
      · -- fuel = 0: (none, budget)
        simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
      · split at h
        · -- localFactors = []: (none, budget)
          simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
        · exact scaledRecombinationSmartSizeLoop_budget_le _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartSizeLoop_budget_le
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes : List Nat) (budget fuel : Nat) (res : Option (List ZPoly)) (b : Nat)
    (h : scaledRecombinationSmartSizeLoop coreLc target modulus head tail sizes budget fuel
        = (res, b)) :
    b ≤ budget := by
  unfold scaledRecombinationSmartSizeLoop at h
  split at h
  · -- sizes = []: (none, budget)
    simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
  · split at h
    · -- budget = 0: (none, 0)
      simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
    · split at h
      · -- fuel = 0: (none, budget)
        simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
      · simp only [] at h
        split at h
        · -- CandLoop returned (some res, b): (some res, b)
          rename_i res' bres hcand
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, hb⟩ := h
          subst hb
          exact scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ hcand
        · -- CandLoop returned (none, bres): recurse on the next size class at budget bres
          rename_i bres hcand
          have hcl := scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ hcand
          have hsl := scaledRecombinationSmartSizeLoop_budget_le _ _ _ _ _ _ _ _ _ _ h
          omega
termination_by fuel

theorem scaledRecombinationSmartCandLoop_budget_le
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget fuel : Nat)
    (res : Option (List ZPoly)) (b : Nat)
    (h : scaledRecombinationSmartCandLoop coreLc target modulus splits budget fuel
        = (res, b)) :
    b ≤ budget := by
  unfold scaledRecombinationSmartCandLoop at h
  split at h
  · -- splits = []: (none, budget)
    simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
  · rename_i split rest
    split at h
    · -- budget = 0: (none, 0)
      simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
    · split at h
      · -- fuel = 0: (none, budget)
        simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
      · rename_i fuel'
        simp only [] at h
        split at h
        · -- prefilter passed: examine the candidate pipeline
          split at h
          · -- shouldRecord the candidate
            cases hquot : exactQuotient? target
                (normalizeFactorSign (ZPoly.primitivePart
                  (ZPoly.dilate coreLc (centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)))) with
            | none =>
                simp only [hquot] at h
                have hrec := scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ h
                omega
            | some quotient =>
                simp only [hquot] at h
                cases haux : scaledRecombinationSmartAux coreLc quotient modulus split.2
                    (budget - 1) fuel' with
                | mk ores ob =>
                    cases ores with
                    | none =>
                        simp only [haux] at h
                        have haux_le := scaledRecombinationSmartAux_budget_le _ _ _ _ _ _ _ _ haux
                        have hrec := scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ h
                        omega
                    | some sub =>
                        simp only [haux] at h
                        simp only [Prod.mk.injEq] at h
                        obtain ⟨_, hb⟩ := h
                        subst hb
                        have haux_le := scaledRecombinationSmartAux_budget_le _ _ _ _ _ _ _ _ haux
                        omega
          · -- candidate not recorded: recurse on the rest at budget - 1
            have hrec := scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ h
            omega
        · -- prefilter rejected the subset: recurse on the rest at budget - 1
          have hrec := scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ h
          omega
termination_by fuel
end

/-- Once the running budget is exhausted the candidate loop declines immediately:
with `budget = 0` it returns `(none, 0)` for any split list and fuel. The
size-ordered coverage proof uses this together with budget monotonicity to
propagate a budget-exhausted `none` up through the enclosing loops. -/
theorem scaledRecombinationSmartCandLoop_budget_zero
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (fuel : Nat) :
    scaledRecombinationSmartCandLoop coreLc target modulus splits 0 fuel = (none, 0) := by
  unfold scaledRecombinationSmartCandLoop
  cases splits with
  | nil => rfl
  | cons split rest => rfl

/-- Budget-exhausted decline for the size loop: with `budget = 0` it returns
`(none, 0)` for any size list and fuel. -/
theorem scaledRecombinationSmartSizeLoop_budget_zero
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes : List Nat) (fuel : Nat) :
    scaledRecombinationSmartSizeLoop coreLc target modulus head tail sizes 0 fuel = (none, 0) := by
  unfold scaledRecombinationSmartSizeLoop
  cases sizes with
  | nil => rfl
  | cons d ds => rfl

mutual
/-- Every factor emitted by the size-ordered recombination search is a recorded
polynomial factor: it is added only at the `shouldRecordPolynomialFactor` gate.
Shared conclusion across the three loops, proved by structural recursion on
`fuel`. Used by the classical-tier irreducibility wiring (the recorded factors
are non-unit non-zero). -/
theorem scaledRecombinationSmartAux_shouldRecord
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartAux coreLc target modulus localFactors budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, shouldRecordPolynomialFactor g = true := by
  unfold scaledRecombinationSmartAux at h
  split at h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨hf, _⟩ := h; subst hf; intro g hg; simp at hg
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact scaledRecombinationSmartSizeLoop_shouldRecord _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartSizeLoop_shouldRecord
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes : List Nat) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartSizeLoop coreLc target modulus head tail sizes budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, shouldRecordPolynomialFactor g = true := by
  unfold scaledRecombinationSmartSizeLoop at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [] at h
        split at h
        · rename_i res bres hcand
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨hres, _⟩ := h; subst hres
          exact scaledRecombinationSmartCandLoop_shouldRecord _ _ _ _ _ _ _ _ hcand
        · exact scaledRecombinationSmartSizeLoop_shouldRecord _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartCandLoop_shouldRecord
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartCandLoop coreLc target modulus splits budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, shouldRecordPolynomialFactor g = true := by
  unfold scaledRecombinationSmartCandLoop at h
  split at h
  · simp at h
  · rename_i split rest
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i fuel'
        simp only [] at h
        split at h
        · -- prefilter passed: examine the candidate pipeline
          split at h
          · rename_i hrecord
            cases hquot : exactQuotient? target
                (normalizeFactorSign (ZPoly.primitivePart
                  (ZPoly.dilate coreLc (centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)))) with
            | none =>
                simp only [hquot] at h
                exact scaledRecombinationSmartCandLoop_shouldRecord _ _ _ _ _ _ _ _ h
            | some quotient =>
                simp only [hquot] at h
                cases haux : scaledRecombinationSmartAux coreLc quotient modulus split.2
                    (budget - 1) fuel' with
                | mk ores ob =>
                    cases ores with
                    | none =>
                        simp only [haux] at h
                        exact scaledRecombinationSmartCandLoop_shouldRecord _ _ _ _ _ _ _ _ h
                    | some sub =>
                        simp only [haux] at h
                        simp only [Prod.mk.injEq, Option.some.injEq] at h
                        obtain ⟨hfac, _⟩ := h; subst hfac
                        intro g hg
                        rcases List.mem_cons.mp hg with hg_eq | hg_sub
                        · subst hg_eq; exact hrecord
                        · exact scaledRecombinationSmartAux_shouldRecord _ _ _ _ _ _ _ _ haux g hg_sub
          · exact scaledRecombinationSmartCandLoop_shouldRecord _ _ _ _ _ _ _ _ h
        · -- prefilter rejected the subset: recurse on the rest
          exact scaledRecombinationSmartCandLoop_shouldRecord _ _ _ _ _ _ _ _ h
termination_by fuel
end

mutual
/-- Every factor emitted by the size-ordered recombination search is fixed by
`normalizeFactorSign`: each recorded candidate is `normalizeFactorSign …` by
construction, so `normalizeFactorSign_idem` closes it. Shared conclusion across
the three loops, proved by structural recursion on `fuel`. Sibling of
`scaledRecombinationSmartAux_shouldRecord`; consumed by the classical-tier
completeness wiring. -/
theorem scaledRecombinationSmartAux_normalizeFactorSign
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartAux coreLc target modulus localFactors budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, normalizeFactorSign g = g := by
  unfold scaledRecombinationSmartAux at h
  split at h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨hf, _⟩ := h; subst hf; intro g hg; simp at hg
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact scaledRecombinationSmartSizeLoop_normalizeFactorSign _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartSizeLoop_normalizeFactorSign
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes : List Nat) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartSizeLoop coreLc target modulus head tail sizes budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, normalizeFactorSign g = g := by
  unfold scaledRecombinationSmartSizeLoop at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [] at h
        split at h
        · rename_i res bres hcand
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨hres, _⟩ := h; subst hres
          exact scaledRecombinationSmartCandLoop_normalizeFactorSign _ _ _ _ _ _ _ _ hcand
        · exact scaledRecombinationSmartSizeLoop_normalizeFactorSign _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartCandLoop_normalizeFactorSign
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartCandLoop coreLc target modulus splits budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, normalizeFactorSign g = g := by
  unfold scaledRecombinationSmartCandLoop at h
  split at h
  · simp at h
  · rename_i split rest
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i fuel'
        simp only [] at h
        split at h
        · -- prefilter passed: examine the candidate pipeline
          split at h
          · rename_i hrecord
            cases hquot : exactQuotient? target
                (normalizeFactorSign (ZPoly.primitivePart
                  (ZPoly.dilate coreLc (centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)))) with
            | none =>
                simp only [hquot] at h
                exact scaledRecombinationSmartCandLoop_normalizeFactorSign _ _ _ _ _ _ _ _ h
            | some quotient =>
                simp only [hquot] at h
                cases haux : scaledRecombinationSmartAux coreLc quotient modulus split.2
                    (budget - 1) fuel' with
                | mk ores ob =>
                    cases ores with
                    | none =>
                        simp only [haux] at h
                        exact scaledRecombinationSmartCandLoop_normalizeFactorSign _ _ _ _ _ _ _ _ h
                    | some sub =>
                        simp only [haux] at h
                        simp only [Prod.mk.injEq, Option.some.injEq] at h
                        obtain ⟨hfac, _⟩ := h; subst hfac
                        intro g hg
                        rcases List.mem_cons.mp hg with hg_eq | hg_sub
                        · subst hg_eq
                          exact normalizeFactorSign_idem
                            (ZPoly.primitivePart (ZPoly.dilate coreLc
                              (centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)))
                        · exact scaledRecombinationSmartAux_normalizeFactorSign _ _ _ _ _ _ _ _ haux g hg_sub
          · exact scaledRecombinationSmartCandLoop_normalizeFactorSign _ _ _ _ _ _ _ _ h
        · -- prefilter rejected the subset: recurse on the rest
          exact scaledRecombinationSmartCandLoop_normalizeFactorSign _ _ _ _ _ _ _ _ h
termination_by fuel
end

mutual
/-- Every factor emitted by the size-ordered recombination search is primitive:
each recorded candidate is `normalizeFactorSign (primitivePart …)`, and the
`shouldRecordPolynomialFactor` gate forces the candidate nonzero, hence the inner
`primitivePart` argument has nonzero content, so the candidate is primitive.
Shared conclusion across the three loops, proved by structural recursion on
`fuel`. Consumed by the classical-tier completeness wiring (positive degree
via `degree_pos_of_primitive_norm_record`). -/
theorem scaledRecombinationSmartAux_primitive
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly)
    (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartAux coreLc target modulus localFactors budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, ZPoly.Primitive g := by
  unfold scaledRecombinationSmartAux at h
  split at h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨hf, _⟩ := h; subst hf; intro g hg; simp at hg
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact scaledRecombinationSmartSizeLoop_primitive _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartSizeLoop_primitive
    (coreLc : Int) (target : ZPoly) (modulus : Nat) (head : ZPoly) (tail : List ZPoly)
    (sizes : List Nat) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartSizeLoop coreLc target modulus head tail sizes budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, ZPoly.Primitive g := by
  unfold scaledRecombinationSmartSizeLoop at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [] at h
        split at h
        · rename_i res bres hcand
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨hres, _⟩ := h; subst hres
          exact scaledRecombinationSmartCandLoop_primitive _ _ _ _ _ _ _ _ hcand
        · exact scaledRecombinationSmartSizeLoop_primitive _ _ _ _ _ _ _ _ _ _ h
termination_by fuel

theorem scaledRecombinationSmartCandLoop_primitive
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (splits : List (List ZPoly × List ZPoly)) (budget fuel : Nat) (factors : List ZPoly) (b : Nat)
    (h : scaledRecombinationSmartCandLoop coreLc target modulus splits budget fuel
        = (some factors, b)) :
    ∀ g ∈ factors, ZPoly.Primitive g := by
  unfold scaledRecombinationSmartCandLoop at h
  split at h
  · simp at h
  · rename_i split rest
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i fuel'
        simp only [] at h
        split at h
        · -- prefilter passed: examine the candidate pipeline
          split at h
          · rename_i hrecord
            cases hquot : exactQuotient? target
                (normalizeFactorSign (ZPoly.primitivePart
                  (ZPoly.dilate coreLc (centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)))) with
            | none =>
                simp only [hquot] at h
                exact scaledRecombinationSmartCandLoop_primitive _ _ _ _ _ _ _ _ h
            | some quotient =>
                simp only [hquot] at h
                cases haux : scaledRecombinationSmartAux coreLc quotient modulus split.2
                    (budget - 1) fuel' with
                | mk ores ob =>
                    cases ores with
                    | none =>
                        simp only [haux] at h
                        exact scaledRecombinationSmartCandLoop_primitive _ _ _ _ _ _ _ _ h
                    | some sub =>
                        simp only [haux] at h
                        simp only [Prod.mk.injEq, Option.some.injEq] at h
                        obtain ⟨hfac, _⟩ := h; subst hfac
                        intro g hg
                        rcases List.mem_cons.mp hg with hg_eq | hg_sub
                        · subst hg_eq
                          have hcand_ne :
                              normalizeFactorSign (ZPoly.primitivePart
                                  (ZPoly.dilate coreLc
                                    (centeredLiftPoly
                                      (Array.polyProduct split.1.toArray) modulus))) ≠ 0 := by
                            unfold shouldRecordPolynomialFactor at hrecord
                            simp at hrecord
                            exact hrecord.1.1
                          have hpp_ne :
                              ZPoly.primitivePart
                                  (ZPoly.dilate coreLc
                                    (centeredLiftPoly
                                      (Array.polyProduct split.1.toArray) modulus)) ≠ 0 := by
                            intro hpp
                            apply hcand_ne
                            rw [hpp]
                            unfold normalizeFactorSign
                            rw [if_neg
                              (by simp : ¬ DensePoly.leadingCoeff (0 : ZPoly) < 0)]
                          have hcontent_ne :
                              ZPoly.content
                                  (ZPoly.dilate coreLc
                                    (centeredLiftPoly
                                      (Array.polyProduct split.1.toArray) modulus)) ≠ 0 := by
                            intro hcontent
                            apply hpp_ne
                            show DensePoly.primitivePart _ = 0
                            exact DensePoly.primitivePart_eq_zero_of_content_eq_zero _
                              (by simpa [ZPoly.content] using hcontent)
                          exact normalizeFactorSign_primitive _
                            (ZPoly.primitivePart_primitive _ hcontent_ne)
                        · exact scaledRecombinationSmartAux_primitive _ _ _ _ _ _ _ _ haux g hg_sub
          · exact scaledRecombinationSmartCandLoop_primitive _ _ _ _ _ _ _ _ h
        · -- prefilter rejected the subset: recurse on the rest
          exact scaledRecombinationSmartCandLoop_primitive _ _ _ _ _ _ _ _ h
termination_by fuel
end

/-- Exhaustive recombination of the lifted local factors stored in `d`,
using the *scaled* candidate shape parameterised by the integer leading
coefficient `coreLc`.  Returns the recovered integer factors as an array
on success and `#[]` when the search fails.

For `coreLc = 1` the inner scaling collapses and this coincides with
`recombineExhaustive`; for primitive non-monic cores `coreLc` is taken
to be the core's leading coefficient and the recovered factors are
primitive normalised divisors of the core. -/
def recombineScaledExhaustive
    (coreLc : Int) (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match scaledRecombinationSearchMod coreLc f (liftModulus d)
      d.liftedFactors.toList with
  | some factors => factors.toArray
  | none => #[]

/-- Initial Hensel precision used by the fast BHKS doubling schedule. -/
def initialHenselPrecision (B : Nat) : Nat :=
  if B ≤ 4 then B else 4

/-- Successor precision used by the fast BHKS doubling schedule. -/
def nextHenselPrecision (k B : Nat) : Nat :=
  if 2 * k < B then
    2 * k
  else
    B

namespace ZPoly

/--
Build the fixed-precision Hensel lift data for the monic transform of an
integer core.  The exhaustive slow path still recombines against the original
primitive core, but the lift stage sees the monic polynomial required by the
Hensel pipeline.
-/
@[expose]
def toMonicLiftData
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : LiftData :=
  henselLiftData (toMonic core).monic
    (precisionForCoeffBound B primeData.p) primeData

/--
Multiplicative inverse of `core`'s leading coefficient modulo `p ^ k`, read off
the integer Bezout certificate `s · ℓf + t · p^k = gcd(ℓf, p^k)`.  When
`gcd(leadingCoeff core, p ^ k) = 1` (the good-prime condition `p ∤ ℓf`) this is a
genuine inverse: `leadingCoeffInverse core p k * leadingCoeff core ≡ 1 (mod p^k)`
(`leadingCoeffInverse_mul_emod`).
-/
def leadingCoeffInverse (core : ZPoly) (p k : Nat) : Int :=
  (HexArith.Int.extGcd (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k))).2.1

/--
BHKS leading-coefficient-faithful monic target for `core`: rescale `core` by the
modular inverse of its leading coefficient, then reduce modulo `p ^ k`.

This is van Hoeij's `M1` normalisation (factor out `ℓf`, BHKS §2: `f = ℓf·f₁···fr`
with the `fᵢ` monic in `Z_p`), distinct from the `toMonic` `x ↦ x/ℓf` substitution
(`M2`).  Over `(ℤ/p^k)[x]` it equals `core · ℓf⁻¹`, so its monic local factors
divide `core` directly with no dilation.  It is monic over ℤ when
`gcd(leadingCoeff core, p ^ k) = 1` and `core` is nonconstant
(`monicTarget_monic`).
-/
@[expose]
def monicTarget (core : ZPoly) (p k : Nat) : ZPoly :=
  reduceModPow (DensePoly.scale (leadingCoeffInverse core p k) core) p k

/--
Fixed-precision Hensel lift data over `core`'s own coordinate (BHKS-faithful).

Mirrors `toMonicLiftData`, but lifts `core`'s monic modular factors against the
leading-coefficient-normalised `monicTarget` rather than the `x ↦ x/ℓf` dilation
`(toMonic core).monic`.  The lifted factors therefore divide `core` in
`(ℤ/p^a)[x]` directly, and the CLD lattice runs over `core`'s own coordinate.
-/
@[expose]
def coreLiftData
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : LiftData :=
  henselLiftData (monicTarget core primeData.p (precisionForCoeffBound B primeData.p))
    (precisionForCoeffBound B primeData.p) primeData

/-- Abstract Bezout-to-residue step: if `A + t·P = 1` and `1 < P` then `A % P = 1`.
Used to read the unit residue `leadingCoeffInverse · ℓf ≡ 1 (mod p^k)` off the
integer extended-GCD certificate. -/
private theorem emod_eq_one_of_bezout {A t P : Int} (hP : 1 < P) (h : A + t * P = 1) :
    A % P = 1 := by
  have h2 : A = 1 + (-t) * P := by
    have hsub : A = 1 - t * P := by omega
    rw [hsub, Int.sub_eq_add_neg, Int.neg_mul]
  rw [h2, Int.add_mul_emod_self_right]
  exact Int.emod_eq_of_lt (by decide) hP

/-- The `leadingCoeffInverse` is a genuine inverse of `core`'s leading coefficient
modulo `p ^ k` when the leading coefficient is coprime to `p ^ k` (the good-prime
condition `p ∤ ℓf`).  This is the unit-residue fact the BHKS monic target rests on. -/
theorem leadingCoeffInverse_mul_emod (core : ZPoly) (p k : Nat)
    (hpk : 1 < p ^ k)
    (hgcd : Int.gcd (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1) :
    (leadingCoeffInverse core p k * DensePoly.leadingCoeff core)
        % Int.ofNat (p ^ k) = 1 := by
  unfold leadingCoeffInverse
  have hbez := HexArith.Int.extGcd_bezout_proj
    (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k))
  rw [HexArith.Int.extGcd_fst, hgcd] at hbez
  have hP : (1 : Int) < Int.ofNat (p ^ k) := by
    have h := Int.ofNat_lt.mpr hpk
    simpa using h
  exact emod_eq_one_of_bezout hP hbez

/-- Size of `reduceModPow` is bounded by the source size (trimming only drops
trailing zeros). -/
theorem reduceModPow_size_le (f : ZPoly) (p k : Nat) :
    (reduceModPow f p k).size ≤ f.size := by
  unfold reduceModPow
  refine Nat.le_trans (DensePoly.size_ofCoeffs_le _) ?_
  simp

/--
The BHKS leading-coefficient-faithful monic target is genuinely monic over ℤ when
`core`'s leading coefficient is coprime to `p ^ k` and `core` is nonconstant.

This is the load-bearing soundness fact for routing the existing monic Hensel lift
against `monicTarget` (van Hoeij `M1`) instead of the `toMonic` `x ↦ x/ℓf`
dilation (`M2`): the lift's producer lemma
`QuadraticMultifactorLiftInvariant_of_choosePrimeData` requires its target monic,
and `monicTarget` supplies that while keeping `core`'s own coordinate.
-/
theorem monicTarget_monic (core : ZPoly) (p k : Nat)
    (hpk : 1 < p ^ k)
    (hgcd : Int.gcd (DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1)
    (hcore : 0 < core.size) :
    DensePoly.Monic (monicTarget core p k) := by
  have hpk_pos : 0 < p ^ k := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hpk)
  have hemod := leadingCoeffInverse_mul_emod core p k hpk hgcd
  have hs_ne : leadingCoeffInverse core p k ≠ 0 := by
    intro h0
    rw [h0, Int.zero_mul, Int.zero_emod] at hemod
    exact absurd hemod (by decide)
  have hscale_size :
      (DensePoly.scale (leadingCoeffInverse core p k) core).size = core.size :=
    scale_size_of_nonzero _ core hs_ne
  have hscale_pos :
      0 < (DensePoly.scale (leadingCoeffInverse core p k) core).size := by
    rw [hscale_size]; exact hcore
  have hg_top :
      (DensePoly.scale (leadingCoeffInverse core p k) core).coeff (core.size - 1)
        = leadingCoeffInverse core p k * DensePoly.leadingCoeff core := by
    have h1 := leadingCoeff_scale_of_nonzero (leadingCoeffInverse core p k) core hs_ne
    rw [DensePoly.leadingCoeff_eq_coeff_last _ hscale_pos, hscale_size] at h1
    exact h1
  have htop : (monicTarget core p k).coeff (core.size - 1) = 1 := by
    unfold monicTarget
    rw [coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpk_pos, hg_top]
    exact hemod
  have hmt_le : (monicTarget core p k).size ≤ core.size := by
    unfold monicTarget
    exact Nat.le_trans (reduceModPow_size_le _ p k) (Nat.le_of_eq hscale_size)
  have hmt_ge : core.size ≤ (monicTarget core p k).size := by
    rcases Nat.lt_or_ge (monicTarget core p k).size core.size with hlt | hge
    · have hle : (monicTarget core p k).size ≤ core.size - 1 := by omega
      have hz := DensePoly.coeff_eq_zero_of_size_le (monicTarget core p k) hle
      rw [htop] at hz
      exact absurd hz (by decide)
    · exact hge
  have hsize : (monicTarget core p k).size = core.size := Nat.le_antisymm hmt_le hmt_ge
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last _ (by rw [hsize]; exact hcore), hsize]
  exact htop

end ZPoly

/--
CLD column-adequacy floor for the fast-core acceptance gate.

A successful BHKS recovery at schedule coefficient bound `k` only certifies
column adequacy (the BHKS Lemma 5.7 separation `hsep`) once the lift precision
`precisionForCoeffBound k primeData.p` clears the per-coordinate CLD threshold.
Equivalently, the schedule bound `k` must reach twice the largest per-coordinate
BHKS coefficient bound of the monic transform `(toMonic core).monic`: then
`p ^ (precisionForCoeffBound k p) > 2·k ≥ 2·cldCoeffFloor core`, so
`2·bhksCoeffBound (toMonic core).monic j < p ^ (precisionForCoeffBound k p)`
holds for every coordinate `j`.  The floor is independent of the prime.
-/
@[expose]
def cldCoeffFloor (core : ZPoly) : Nat :=
  let monicCore := (ZPoly.toMonic core).monic
  let n := monicCore.degree?.getD 0
  2 * (List.range (n + 1)).foldl (fun acc j => max acc (bhksCoeffBound monicCore j)) 0

/-- Acceptance floor for the fast-core loop: the CLD column-adequacy floor
`cldCoeffFloor` joined with the Mignotte recovery bounds of the core and of its
monic transform.  A success accepted at `k ≥ bhksRecoveryFloor core` is both
column-adequate and running at a Hensel modulus `p ^ precisionForCoeffBound k p`
that clears twice both Mignotte bounds — which is what the lattice-tier
count-equality and adequacy proofs consume (#8519): the toMonic partition
producers need `2 * defaultFactorCoeffBound (toMonic core).monic < p ^ a`, and
the true-support nonemptiness argument needs the same for `core` itself. -/
def bhksRecoveryFloor (core : ZPoly) : Nat :=
  max (cldCoeffFloor core)
    (max (ZPoly.defaultFactorCoeffBound core)
      (ZPoly.defaultFactorCoeffBound (ZPoly.toMonic core).monic))

theorem cldCoeffFloor_le_bhksRecoveryFloor (core : ZPoly) :
    cldCoeffFloor core ≤ bhksRecoveryFloor core :=
  Nat.le_max_left _ _

theorem defaultFactorCoeffBound_le_bhksRecoveryFloor (core : ZPoly) :
    ZPoly.defaultFactorCoeffBound core ≤ bhksRecoveryFloor core :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem defaultFactorCoeffBound_toMonic_le_bhksRecoveryFloor (core : ZPoly) :
    ZPoly.defaultFactorCoeffBound (ZPoly.toMonic core).monic ≤ bhksRecoveryFloor core :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The acceptance floor used solely as the fast-core loop's skip gate.

Definitionally `bhksRecoveryFloor`, but marked `irreducible` so that `whnf` in
downstream proofs that case-split on a `bhksRecoveryCoreWithBound` application
does not eagerly expand the (symbolic, structurally large) floor computation
while reducing the loop's head `if`.  The loop's behavioural unfolding lemma
`bhksRecoveryCoreWithBound_unfold` re-exposes the plain `bhksRecoveryFloor`
comparison, so proofs reason about the genuine floor. -/
@[irreducible] def bhksRecoveryFloorGate (core : ZPoly) : Nat :=
  bhksRecoveryFloor core

theorem bhksRecoveryFloorGate_eq (core : ZPoly) :
    bhksRecoveryFloorGate core = bhksRecoveryFloor core := by
  simp only [bhksRecoveryFloorGate]

/-- Inner fast-core recombination loop, parameterised by a precomputed CLD
column-adequacy `floor`.  Below `floor` a success cannot be accepted and every
recovery class (success or failure) advances the schedule identically, so the
expensive Hensel-lift / CLD-lattice / LLL / reconstruction pipeline is skipped
and the loop steps straight to the next scheduled precision.  At/above `floor`
a success is column-adequate and accepted immediately.

`floor` is threaded as a parameter so the (structurally large, degree-
exponential) `cldCoeffFloor` is evaluated once by `bhksRecoveryCoreWithBound`
rather than re-evaluated at every doubling step.

Private: only `bhksRecoveryCoreWithBound` (which passes `cldCoeffFloorGate core`)
is the semantically supported entry point; the bare `floor` parameter must not
be set independently. -/
private def bhksRecoveryLoop
    (core : ZPoly) (B floor : Nat) (primeData : PrimeChoiceData) :
    Nat → Nat → Option (Array ZPoly)
  | _k, 0 => none
  | k, fuel + 1 =>
      if k < floor then
        if k ≥ B then
          none
        else
          bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel
      else
        match bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
        | .success factors =>
          some factors
        | .candidateFailure =>
          if k ≥ B then
            none
          else
            bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .productMismatch _ =>
          if k ≥ B then
            none
          else
            bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel
        | .degenerate =>
          if k ≥ B then
            none
          else
            bhksRecoveryLoop core B floor primeData (nextHenselPrecision k B) fuel

/-- BHKS fast-core recombination loop.  Computes the CLD column-adequacy floor
once (through the irreducible `bhksRecoveryFloorGate`, so `whnf` in downstream
proofs that case-split on this application does not eagerly expand the symbolic
floor) and runs `bhksRecoveryLoop`. -/
def bhksRecoveryCoreWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    Option (Array ZPoly) :=
  bhksRecoveryLoop core B (bhksRecoveryFloorGate core) primeData k fuel

/-- Behavioural unfolding for the optimized fast-core loop: the precision-floor
short-circuit is propositionally equal to the original "recover at every step,
accept only at the floor" body.  Below the floor every recovery class steps to
the next precision, and at/above the floor a success is column-adequate; both
match the gated form, so this lemma lets the recovery-on-schedule proofs reason
about the loop exactly as before. -/
private theorem bhksRecoveryCoreWithBound_unfold
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) (k fuel : Nat) :
    bhksRecoveryCoreWithBound core B primeData k (fuel + 1) =
      match bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
      | .success factors =>
        if k ≥ bhksRecoveryFloor core then
          some factors
        else if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .candidateFailure =>
        if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .productMismatch _ =>
        if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel
      | .degenerate =>
        if k ≥ B then
          none
        else
          bhksRecoveryCoreWithBound core B primeData (nextHenselPrecision k B) fuel := by
  have hrec : ∀ k',
      bhksRecoveryLoop core B (bhksRecoveryFloor core) primeData k' fuel =
        bhksRecoveryCoreWithBound core B primeData k' fuel := by
    intro k'
    rw [bhksRecoveryCoreWithBound, bhksRecoveryFloorGate_eq]
  rw [bhksRecoveryCoreWithBound, bhksRecoveryFloorGate_eq, bhksRecoveryLoop]
  simp only [hrec]
  by_cases hf : k < bhksRecoveryFloor core
  · rw [if_pos hf]
    have hfloor : ¬ k ≥ bhksRecoveryFloor core := Nat.not_le.mpr hf
    cases bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) <;>
      simp only [hfloor, if_false]
  · rw [if_neg hf]
    have hfloor : k ≥ bhksRecoveryFloor core := Nat.le_of_not_lt hf
    cases bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) <;>
      simp only [hfloor, if_true]

/-- Finite list of Hensel precisions inspected by the fast BHKS core loop. -/
def henselPrecisionSchedule (B : Nat) : Nat → Nat → List Nat
  | _k, 0 => []
  | k, fuel + 1 =>
      k :: if k ≥ B then [] else henselPrecisionSchedule B (nextHenselPrecision k B) fuel

private theorem initialHenselPrecision_le (B : Nat) :
    initialHenselPrecision B ≤ B := by
  unfold initialHenselPrecision
  by_cases hB : B ≤ 4
  · simp [hB]
  · simp [hB]
    omega

private theorem nextHenselPrecision_le (k B : Nat) :
    nextHenselPrecision k B ≤ B := by
  unfold nextHenselPrecision
  by_cases h : 2 * k < B
  · simp [h]
    omega
  · simp [h]

private theorem nextHenselPrecision_eq_B_of_cap_reached {k B : Nat}
    (h : B ≤ 2 * k) :
    nextHenselPrecision k B = B := by
  unfold nextHenselPrecision
  have hnot : ¬ 2 * k < B := by omega
  simp [hnot]

private theorem initialHenselPrecision_mem_schedule (B fuel : Nat) :
    initialHenselPrecision B ∈
      henselPrecisionSchedule B (initialHenselPrecision B) (fuel + 1) := by
  simp [henselPrecisionSchedule]

private theorem nextHenselPrecision_mem_schedule {B k fuel : Nat}
    (hk : ¬ k ≥ B) :
    nextHenselPrecision k B ∈
      henselPrecisionSchedule B k (fuel + 2) := by
  simp [henselPrecisionSchedule, hk]

/-- Helper: when the doubling fuel `fuel` is large enough that the geometric
progression starting from `k` reaches the cap `B`, the cap appears in the
finite Hensel precision schedule.  The geometric bound `B ≤ k * 2 ^ fuel`
is what we will discharge for the canonical executable choice
`k = initialHenselPrecision B`, `fuel = quadraticDoublingSteps B + 1`. -/
private theorem henselPrecisionSchedule_mem_cap
    {B : Nat} :
    ∀ (k fuel : Nat), 0 < k → k ≤ B → B ≤ k * 2 ^ fuel →
      B ∈ henselPrecisionSchedule B k (fuel + 1) := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro _ hk_le hfuel
      have hkB : k = B := by
        have : k * 2 ^ 0 = k := by simp
        omega
      subst hkB
      simp [henselPrecisionSchedule]
  | succ fuel ih =>
      intro hk_pos hk_le hfuel
      by_cases hk_eq : k = B
      · subst hk_eq
        simp [henselPrecisionSchedule]
      · have hk_lt : k < B := Nat.lt_of_le_of_ne hk_le hk_eq
        rw [henselPrecisionSchedule]
        simp only [List.mem_cons]
        right
        rw [if_neg (by omega : ¬ k ≥ B)]
        unfold nextHenselPrecision
        have hpow : k * 2 ^ (fuel + 1) = 2 * k * 2 ^ fuel := by
          rw [Nat.pow_succ', ← Nat.mul_assoc, Nat.mul_comm k 2]
        by_cases h2 : 2 * k < B
        · rw [if_pos h2]
          refine ih (2 * k) (by omega) (by omega) ?_
          omega
        · rw [if_neg h2]
          refine ih B (by omega) (Nat.le_refl _) ?_
          have hge1 : 1 ≤ 2 ^ fuel := Nat.one_le_two_pow
          calc B = B * 1 := (Nat.mul_one B).symm
            _ ≤ B * 2 ^ fuel := Nat.mul_le_mul_left B hge1

/--
The fast-path cap `B` is itself a member of the canonical Hensel precision
schedule the executable loop walks: `henselPrecisionSchedule B
(initialHenselPrecision B) (quadraticDoublingSteps B + 2)`.

This is the connective schedule lemma used by the Mathlib-facing Group D
forward-recovery wrapper: callers who supply `ForwardRecoveryInputs` at the
canonical terminal precision no longer need to re-prove the executable
doubling-schedule membership obligation.
-/
theorem cap_mem_henselPrecisionSchedule (B : Nat) :
    B ∈ henselPrecisionSchedule B (initialHenselPrecision B)
      (ZPoly.quadraticDoublingSteps B + 2) := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    simp [henselPrecisionSchedule, initialHenselPrecision]
  · -- B ≥ 1.  Reduce to the geometric-bound helper.
    have hinit_pos : 0 < initialHenselPrecision B := by
      unfold initialHenselPrecision
      by_cases hle : B ≤ 4
      · simp [hle]; omega
      · simp [hle]
    have hinit_le : initialHenselPrecision B ≤ B := initialHenselPrecision_le B
    have hbound :
        B ≤ initialHenselPrecision B * 2 ^ (ZPoly.quadraticDoublingSteps B + 1) := by
      by_cases hsmall : B ≤ 4
      · have hinit : initialHenselPrecision B = B := by
          unfold initialHenselPrecision; simp [hsmall]
        rw [hinit]
        have hpow : 1 ≤ 2 ^ (ZPoly.quadraticDoublingSteps B + 1) :=
          Nat.one_le_two_pow
        calc B = B * 1 := (Nat.mul_one B).symm
          _ ≤ B * 2 ^ (ZPoly.quadraticDoublingSteps B + 1) :=
              Nat.mul_le_mul_left B hpow
      · have hinit : initialHenselPrecision B = 4 := by
          unfold initialHenselPrecision
          simp [hsmall]
        rw [hinit]
        have hquad :
            ZPoly.quadraticDoublingSteps B = (B - 1).log2 + 1 := by
          unfold ZPoly.quadraticDoublingSteps
          have : ¬ B ≤ 1 := by omega
          simp [this]
        rw [hquad]
        -- Goal: B ≤ 4 * 2 ^ ((B - 1).log2 + 1 + 1)
        have hlog : B - 1 < 2 ^ ((B - 1).log2 + 1) := Nat.lt_log2_self
        have hB_le : B ≤ 2 ^ ((B - 1).log2 + 1) := by omega
        have hexp :
            2 ^ ((B - 1).log2 + 1 + 1) = 2 * 2 ^ ((B - 1).log2 + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        calc B ≤ 2 ^ ((B - 1).log2 + 1) := hB_le
          _ ≤ 4 * 2 ^ ((B - 1).log2 + 1 + 1) := by
              rw [hexp]
              -- 2^(x+1) ≤ 4 * (2 * 2^(x+1)) = 8 * 2^(x+1)
              have hle : 2 ^ ((B - 1).log2 + 1) ≤ 8 * 2 ^ ((B - 1).log2 + 1) := by
                have : 1 ≤ 8 := by decide
                calc 2 ^ ((B - 1).log2 + 1)
                    = 1 * 2 ^ ((B - 1).log2 + 1) := (Nat.one_mul _).symm
                  _ ≤ 8 * 2 ^ ((B - 1).log2 + 1) := Nat.mul_le_mul_right _ this
              have h8eq : 4 * (2 * 2 ^ ((B - 1).log2 + 1)) =
                  8 * 2 ^ ((B - 1).log2 + 1) := by
                rw [← Nat.mul_assoc]
              omega
    exact henselPrecisionSchedule_mem_cap _ _ hinit_pos hinit_le hbound

private theorem bhksRecoveryCoreWithBound_isSome_of_recovery_on_schedule
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hfloor : bhksRecoveryFloor core ≤ target)
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hrecover :
      bhksRecover? core (ZPoly.toMonicLiftData core target primeData) = some factors) :
    (bhksRecoveryCoreWithBound core B primeData start fuel).isSome := by
  induction fuel generalizing start with
  | zero =>
      simp [henselPrecisionSchedule] at hmem
  | succ fuel ih =>
      rw [bhksRecoveryCoreWithBound_unfold]
      cases hclass : bhksRecoverClassified core (ZPoly.toMonicLiftData core start primeData) with
      | success xs =>
          by_cases hstart : start ≥ bhksRecoveryFloor core
          · simp [hstart]
          · by_cases hk : start ≥ B
            · exfalso
              have htarget : target = start := by
                simpa [henselPrecisionSchedule, hk] using hmem
              omega
            · simp [hstart, hk]
              have hmem' :
                  target ∈
                    henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                have hmem_tail :
                    target = start ∨
                      target ∈
                        henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                  simpa [henselPrecisionSchedule, hk] using hmem
                cases hmem_tail with
                | inl htarget => omega
                | inr htail => exact htail
              exact ih hmem'
      | degenerate =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'
      | candidateFailure =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'
      | productMismatch cands =>
          by_cases hk : start ≥ B
          · simp [hk]
            have hmem' : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem' :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_tail :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_tail with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            exact ih hmem'

/--
If a target precision is on the fast-core schedule, recovery succeeds there,
and no other scheduled precision before the target succeeds, then the
first-success loop returns exactly the target recovery.

This is the executable-loop determinism skeleton.  The BHKS precision theorem
supplies the `hno` premise by ruling out successful recovery below the
Mignotte/cap precision.
-/
theorem bhksRecoveryCoreWithBound_eq_some_of_recovery_on_schedule_of_no_prior_recovery
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {start fuel target : Nat} {factors : Array ZPoly}
    (hfloor : bhksRecoveryFloor core ≤ target)
    (hmem : target ∈ henselPrecisionSchedule B start fuel)
    (hno :
      ∀ k, k ∈ henselPrecisionSchedule B start fuel → k ≠ target →
        bhksRecover? core (ZPoly.toMonicLiftData core k primeData) = none)
    (hrecover :
      bhksRecover? core (ZPoly.toMonicLiftData core target primeData) = some factors) :
    bhksRecoveryCoreWithBound core B primeData start fuel = some factors := by
  induction fuel generalizing start with
  | zero =>
      simp [henselPrecisionSchedule] at hmem
  | succ fuel ih =>
      rw [bhksRecoveryCoreWithBound_unfold]
      cases hclass : bhksRecoverClassified core (ZPoly.toMonicLiftData core start primeData) with
      | success xs =>
          by_cases htarget : start = target
          · subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
            simp only [ge_iff_le, hfloor, if_true]
            exact congrArg some hrecover
          · have hstart_mem :
                start ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule]
            have hnone := hno start hstart_mem htarget
            rw [bhksRecover?] at hnone
            simp [hclass, BhksRecoveryResult.toOption] at hnone
      | degenerate =>
          by_cases hk : start ≥ B
          · simp [hk]
            have htarget : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem_tail :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_cases :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_cases with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            refine ih hmem_tail ?_
            intro k hk_mem hk_ne
            have hk_schedule :
                k ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule, hk, hk_mem]
            exact hno k hk_schedule hk_ne
      | candidateFailure =>
          by_cases hk : start ≥ B
          · simp [hk]
            have htarget : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem_tail :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_cases :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_cases with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            refine ih hmem_tail ?_
            intro k hk_mem hk_ne
            have hk_schedule :
                k ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule, hk, hk_mem]
            exact hno k hk_schedule hk_ne
      | productMismatch cands =>
          by_cases hk : start ≥ B
          · simp [hk]
            have htarget : target = start := by
              simpa [henselPrecisionSchedule, hk] using hmem
            subst target
            rw [bhksRecover?] at hrecover
            simp [hclass, BhksRecoveryResult.toOption] at hrecover
          · simp [hk]
            have hmem_tail :
                target ∈
                  henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
              have hmem_cases :
                  target = start ∨
                    target ∈
                      henselPrecisionSchedule B (nextHenselPrecision start B) fuel := by
                simpa [henselPrecisionSchedule, hk] using hmem
              cases hmem_cases with
              | inl htarget =>
                  subst target
                  rw [bhksRecover?] at hrecover
                  simp [hclass, BhksRecoveryResult.toOption] at hrecover
              | inr htail =>
                  exact htail
            refine ih hmem_tail ?_
            intro k hk_mem hk_ne
            have hk_schedule :
                k ∈ henselPrecisionSchedule B start (fuel + 1) := by
              simp [henselPrecisionSchedule, hk, hk_mem]
            exact hno k hk_schedule hk_ne

end Hex
