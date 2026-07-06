/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyFp.Degree
public meta import HexModArith.Ring
public import HexModArith.Prime
public import HexPolyFp.Degree
public import HexPolyFp.SquareFree.YunCorrect
import all HexPolyFp.SquareFree.Algebra
import all HexPolyFp.SquareFree.YunContribution
import all HexPolyFp.SquareFree.YunReduce
import all HexPolyFp.SquareFree.YunMeasure
import all HexPolyFp.SquareFree.YunCorrect

public section
set_option backward.proofsInPublic true

/-!
Executable Yun-style square-free decomposition for `F_p[x]`. The algebra
foundations and the Yun correctness engine live in the
`HexPolyFp.SquareFree.*` submodules; this module exposes
`squareFreeDecomposition` and the public square-free / pairwise-coprime /
weighted-product theorems.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]
/--
Compute a square-free decomposition by normalizing away the leading scalar and
running Yun's algorithm on the resulting monic polynomial.
-/
@[expose]
def squareFreeDecomposition (hp : Hex.Nat.Prime p) (f : FpPoly p) : SquareFreeDecomposition p :=
  let _ := hp
  let normalized := normalizeMonic f
  let unit := normalized.1
  let monicPart := normalized.2
  let factors := squareFreeAux monicPart 1 (monicPart.size + 1)
  { unit, factors }

private theorem squareFreeAux_weightedProduct_nonzero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (hresidual : squareFreeAuxRevResidualSatisfied f 1 (f.size + 1))
    (hrawState : YunDerivativeActiveRawStateProvider hp) :
    weightedProduct (squareFreeAux f 1 (f.size + 1)) = f := by
  unfold squareFreeAux
  have hinvariant := squareFreeAuxRev_reconstruction_invariant f 1 (f.size + 1) []
  rw [hinvariant]
  simp [weightedProduct_nil]
  exact squareFreeAuxRevContribution_correct
    hp f hzero hreachable hresidual hrawState

private theorem normalizeMonic_zero_squareFree_weightedProduct
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : (normalizeMonic f).2.isZero = true) :
    DensePoly.C (normalizeMonic f).1 *
      weightedProduct
        (squareFreeAux (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)) =
        f := by
  rw [squareFreeAux_zero_weightedProduct (normalizeMonic f).2 hzero]
  have hmonic_zero : (normalizeMonic f).2 = 0 :=
    eq_zero_of_isZero_true (normalizeMonic f).2 hzero
  have hreconstruct := normalizeMonic_reconstruct hp f
  rw [hmonic_zero] at hreconstruct
  simp at hreconstruct
  rw [← hreconstruct]
  rfl

private theorem yunFactorsWithLevel_multiplicity_pos_raw
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p))
    (hbase : 0 < base) (hlevel : 0 < level)
    (hacc : ∀ sf ∈ accRev, 0 < sf.multiplicity) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel accRev).1,
      0 < sf.multiplicity := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simpa [yunFactorsWithLevel] using hacc
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simpa [hc] using hacc
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using
            ih y (w / y) (level + 1) accRev (Nat.succ_pos level) hacc
        · have hacc' :
              ∀ sf ∈ ({ factor := z, multiplicity := base * level } :: accRev),
                0 < sf.multiplicity := by
            intro sf hsf
            rcases List.mem_cons.mp hsf with hsf | hsf
            · subst sf
              exact Nat.mul_pos hbase hlevel
            · exact hacc sf hsf
          simpa [y, z, hz] using
            ih y (w / y) (level + 1)
              ({ factor := z, multiplicity := base * level } :: accRev)
              (Nat.succ_pos level) hacc'

private theorem squareFreeAuxRev_multiplicity_pos_raw
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hmultiplicity : 0 < multiplicity)
    (hacc : ∀ sf ∈ accRev, 0 < sf.multiplicity) :
    ∀ sf ∈ squareFreeAuxRev f multiplicity fuel accRev,
      0 < sf.multiplicity := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simpa [squareFreeAuxRev] using hacc
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simpa [hzero] using hacc
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · have hp_pos : 0 < p := by
            have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
            omega
          simpa [hdf] using
            ih (pthRoot f) (multiplicity * p) accRev
              (Nat.mul_pos hmultiplicity hp_pos) hacc
        · simp [hdf]
          let g := monicGcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          have hloop :
              ∀ sf ∈ loop.1, 0 < sf.multiplicity := by
            simpa [loop, c, g] using
              yunFactorsWithLevel_multiplicity_pos_raw
                c g multiplicity 1 fuel accRev hmultiplicity (by omega) hacc
          by_cases hrepeated : isOne loop.2
          · simpa [loop, c, g, hrepeated] using hloop
          · have hp_pos : 0 < p := by
              have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
              omega
            simpa [loop, c, g, hrepeated] using
              ih (pthRoot loop.2) (multiplicity * p) loop.1
                (Nat.mul_pos hmultiplicity hp_pos) hloop

/-- The factors emitted by `squareFreeDecomposition` are pairwise coprime,
witnessed by the normalized gcd of any two distinct factors reducing to `1`.
This is the underlying coprimality result that the public
`squareFreeDecomposition_pairwise_coprime` wrapper delegates to; callers reason
about distinct square-free parts in isolation, relying on this to know no common
factor links them. -/
theorem squareFree_pairwise_coprime (hp : Hex.Nat.Prime p)
    (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    d.factors.Pairwise
      (fun a b => (normalizeMonic (DensePoly.gcd a.factor b.factor)).2 = 1) := by
  unfold squareFreeDecomposition squareFreeAux
  exact squareFreeAuxRev_pairwise_coprime_nil hp
    (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)
    (Nat.lt_succ_self _)
    (normalizeMonic_squareFreeContributionReachable hp f)

/-- The decomposition reconstructs its input: multiplying the emitted unit by the
weighted product of the factors (each raised to its recorded multiplicity)
recovers `f`. This is the underlying reconstruction identity that the public
`squareFreeDecomposition_weightedProduct` wrapper delegates to; it certifies the
decomposition loses no information, so a caller can substitute the factored form
for `f` anywhere. -/
theorem squareFree_weightedProduct (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    DensePoly.C d.unit * weightedProduct d.factors = f := by
  dsimp [squareFreeDecomposition]
  by_cases hzero : (normalizeMonic f).2.isZero
  · exact normalizeMonic_zero_squareFree_weightedProduct hp f hzero
  · have hnonzero : (normalizeMonic f).2.isZero = false := by
      cases h : (normalizeMonic f).2.isZero <;> simp [h] at hzero ⊢
    have hresidual :
        squareFreeAuxRevResidualSatisfied
          (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1) :=
      squareFreeAuxRevResidualSatisfied_of_size_lt hp
        (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1) (by omega)
    rw [squareFreeAux_weightedProduct_nonzero hp (normalizeMonic f).2 hnonzero
      (normalizeMonic_squareFreeContributionReachable hp f)
      hresidual (yunDerivativeActiveRawStateProvider_holds hp)]
    exact normalizeMonic_reconstruct hp f

/-- Each factor emitted by `squareFreeDecomposition` is itself square-free,
witnessed by the normalized gcd of the factor with its derivative reducing to
`1`. This is the underlying square-freeness result that the public
`squareFreeDecomposition_factors_squareFree` wrapper delegates to; it is the
defining guarantee of the decomposition, letting a caller treat every emitted
factor as having no repeated irreducible part. -/
theorem squareFree_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors,
      (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 = 1 := by
  unfold squareFreeDecomposition squareFreeAux
  apply squareFreeAuxRev_factors_squareFree hp
  intro sf hsf
  simp at hsf

/-- Public square-freeness wrapper: every factor emitted by
`squareFreeDecomposition` is square-free, witnessed by the normalized gcd with
its derivative reducing to `1`. The provider instantiation is closed internally,
so no provider arguments appear in the statement. -/
theorem squareFreeDecomposition_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors,
      (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 = 1 :=
  squareFree_factors_squareFree hp f

/-- Every factor emitted by `squareFreeDecomposition` carries a strictly positive
multiplicity, so no factor is recorded at multiplicity `0`. A caller iterating
the factor list can therefore treat each recorded exponent as a genuine power and
need not special-case a zero exponent. -/
theorem squareFreeDecomposition_multiplicity_pos (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors, 0 < sf.multiplicity := by
  dsimp [squareFreeDecomposition, squareFreeAux]
  intro sf hsf
  have hraw :
      ∀ sf ∈ squareFreeAuxRev (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1) [],
        0 < sf.multiplicity := by
    apply squareFreeAuxRev_multiplicity_pos_raw hp
    · omega
    · intro sf hsf
      simp at hsf
  exact hraw sf (by simpa using hsf)

/-- Public reconstruction wrapper: the emitted unit and weighted factor product
recover the input. The provider instantiation is closed internally, so no
provider arguments appear in the statement. -/
theorem squareFreeDecomposition_weightedProduct (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    DensePoly.C d.unit * weightedProduct d.factors = f :=
  squareFree_weightedProduct hp f

/-- Public coprimality wrapper: the emitted factors are pairwise coprime, witnessed
by the normalized gcd reducing to `1`. The provider instantiation is closed
internally, so no provider arguments appear in the statement. -/
theorem squareFreeDecomposition_pairwise_coprime (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    d.factors.Pairwise
      (fun a b => (normalizeMonic (DensePoly.gcd a.factor b.factor)).2 = 1) :=
  squareFree_pairwise_coprime hp f

private instance squareFreeGuardBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem prime_five_squareFree_guard : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private def polyFiveSquareFreeGuard (coeffs : Array Nat) : FpPoly 5 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNatsSquareFreeGuard (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

#guard
  let f := polyFiveSquareFreeGuard #[1, 1, 1]
  let d := squareFreeDecomposition prime_five_squareFree_guard f
  d.factors.all (fun sf =>
    coeffNatsSquareFreeGuard
      (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 == [1])

-- Scalar-leak regression (issue #7005): over `F_5` (p > 2) the raw gcd in the
-- Yun loop can free a non-trivial unit constant that was never folded back into
-- the reconstruction unit. For `f = (x+1)^5 (x+2)^5 (x+3)` (monic, degree 11)
-- the pre-fix reconstruction evaluated to `3·f`; routing every gcd through the
-- monic `monicGcd` restores `weightedProduct d.factors = f` exactly.
#guard
  let f := polyFiveSquareFreeGuard #[1, 2, 0, 0, 0, 4, 3, 0, 0, 0, 3, 1]
  let d := squareFreeDecomposition prime_five_squareFree_guard f
  coeffNatsSquareFreeGuard (weightedProduct d.factors) ==
    coeffNatsSquareFreeGuard f

private instance squareFreeGuardBoundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem prime_two_squareFree_guard : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

private def polyTwoSquareFreeGuard (coeffs : Array Nat) : FpPoly 2 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 2 n))

private def coeffNatsSquareFreeGuardTwo (f : FpPoly 2) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

#guard
  let f := polyTwoSquareFreeGuard #[1, 0, 1, 0, 1, 0, 1]
  let d := squareFreeDecomposition prime_two_squareFree_guard f
  coeffNatsSquareFreeGuardTwo (weightedProduct d.factors) ==
    coeffNatsSquareFreeGuardTwo f

private theorem linearPow_eq_powLinear (f : FpPoly p) (n : Nat) :
    FpPoly.linearPow f n = powLinear f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : FpPoly.linearPow f (n + 1) = FpPoly.linearPow f n * f := rfl
      have h2 : powLinear f (n + 1) = powLinear f n * f := rfl
      rw [h1, h2, ih]

/-- Freshman's dream for `FpPoly.linearPow`: in characteristic `p`, raising to
the prime power is additive. -/
theorem linearPow_add_prime
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) :
    FpPoly.linearPow (f + g) p =
      FpPoly.linearPow f p + FpPoly.linearPow g p := by
  rw [linearPow_eq_powLinear, linearPow_eq_powLinear, linearPow_eq_powLinear]
  exact powLinear_add_prime hp f g

/-- `FpPoly.linearPow` of a product factors over the base. -/
theorem linearPow_mul_base (f g : FpPoly p) (n : Nat) :
    FpPoly.linearPow (f * g) n =
      FpPoly.linearPow f n * FpPoly.linearPow g n := by
  rw [linearPow_eq_powLinear, linearPow_eq_powLinear, linearPow_eq_powLinear]
  exact powLinear_mul_base f g n


end FpPoly
end Hex
