/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.Formula

public section

/-! Truth of a shared real formula from signs at one checked open-cell sample. -/

namespace Hex.RCF.RealCoefficients

open HexPolyMathlib.Interpret HexRealRootsMathlib

/-- Casting the exact three-valued sign through the integers preserves it. -/
theorem sign_cast_sign (y : ℝ) :
    SignType.sign (((SignType.sign y : Int) : ℝ)) = SignType.sign y := by
  cases h : SignType.sign y <;> simp

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

omit [One E] [Sub E] [NatCast E] [DecidableEq Ctx] in
/-- Exact signs at the dyadic sample decide the formula on its whole open cell,
provided the carrier contains every atom root and the atom polynomials have
their stated real interpretations. The root coverage and sample membership
come from checked isolation replay. -/
theorem open_formula (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
    (ha : ∀ a b, f (a + b) = f a + f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (point : Dyadic → E)
    (hpoint : ∀ d, f (point d) = HexRealRootsMathlib.Dyadic.toReal d)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (root : Fin cert.isolations.intervals.size → ℝ) (hmono : StrictMono root)
    (hcomplete : ∀ z, (interpret f hz head).IsRoot z ↔ ∃ i, root i = z)
    (cut : Fin (cert.isolations.intervals.size + 1))
    (hsample : Cell.Region root (.open cut)
      (HexRealRootsMathlib.Dyadic.toReal (cert.isolations.openPoint cut)))
    (formula : Hex.RealFormula.QF n) (ρ : Fin n → ℝ)
    (x : ℝ) (hx : Cell.Region root (.open cut) x)
    (polynomial : Hex.RealFormula.Poly n → DensePoly E)
    (hpolynomial : ∀ p ∈ formula.polys,
      (interpret f hz (polynomial p)).eval x = p.eval ρ)
    (hroots : ∀ p ∈ formula.polys,
      interpret f hz (polynomial p) = 0 ∨
        ∀ z, (interpret f hz (polynomial p)).IsRoot z →
          (interpret f hz head).IsRoot z) :
    formula.evalSigns (fun p =>
      some (Sign.ofInt (sign ((polynomial p).eval
        (point (cert.isolations.openPoint cut)))))) = some true ↔
      formula.toProp ρ := by
  apply Hex.RealFormula.QF.evalSigns_eq_true_iff
  intro p hp
  let observed := sign ((polynomial p).eval
    (point (cert.isolations.openPoint cut)))
  refine ⟨Sign.ofInt observed, rfl, ?_⟩
  rw [Sign.ofInt_spec]
  have hs := cert.open_sign f hz ha hm sign hsign point hpoint
    head (polynomial p) root hmono hcomplete cut hsample
    (hroots p hp) x hx
  change observed = (SignType.sign ((interpret f hz (polynomial p)).eval x) : Int) at hs
  rw [hs, ← hpolynomial p hp]
  exact sign_cast_sign _

end Hex.RCF.RealCoefficients
