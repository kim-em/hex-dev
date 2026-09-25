/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexNumberFieldMathlib.AdjoinRoot
public import HexRCF.RealCoefficients.Coefficients
public import HexRCF.RealCoefficients.LiteralSign
public import HexBerlekampZassenhausMathlib.FactorSoundness
public import HexRootsMathlib.Conjugate

public section

namespace Hex.RCF.RealCoefficients.Field

/-- A short checked irreducibility witness supplies the instance needed for
zero reflection in a literal fixed field. The expensive default factorizer is
used by the soundness theorem, not replayed on this witness. -/
theorem checkedIrreducible (p : ZPoly) (w : ZPoly.IrredWitness)
    (h : ZPoly.checkIrredWitness p w = true) (hd : 0 < p.natDegree) :
    ZPoly.CheckedIrreducible p :=
  ⟨(ZPoly.isIrreducible_iff p).mpr
    (ZPoly.irreducible_of_checkIrredWitness p w h), hd⟩

/-- Rebuild a selected root directly from printable square data. -/
def literalRep (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec) :
    RefinedIsolation p :=
  ⟨⟨s, .ofWitness hw⟩, hp⟩

/-- The literal representative names the same root used by the coordinate field. -/
theorem literalRep_mk (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec) :
    SimpleRoot.mk (literalRep p s hw hp) = SimpleRoot.ofSquare p s hw hp := by
  exact (HexRootsMathlib.SimpleRoot.ofSquare_mk (literalRep p s hw hp) hw hp).symm

/-- A real-axis square selects a real embedding of its fixed field. -/
theorem literalRep_real (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) :
    (literalRep p s hw hp).root.im = 0 :=
  (HexRootsMathlib.RefinedIsolation.meetsRealAxis_iff _).mp hreal

/-- The selected real root zeros the rational defining polynomial used by
the sign table. -/
theorem literalRep_root (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true) :
    (LiteralSign.realPoly (ZPoly.toRatPoly p)).IsRoot
      (literalRep p s hw hp).root.re := by
  let rep := literalRep p s hw hp
  have hr : (rep.root.re : ℂ) = rep.root :=
    Complex.ext rfl (literalRep_real p s hw hp hreal).symm
  have hpoly : (LiteralSign.realPoly (ZPoly.toRatPoly p)).map Complex.ofRealHom =
      HexRootsMathlib.toPolyℂ p := by
    ext i
    simp [LiteralSign.realPoly, HexRootsMathlib.toPolyℂ]
  have hz := HexRootsMathlib.RefinedIsolation.isRoot rep
  apply Complex.ofReal_injective
  change Complex.ofRealHom
    ((LiteralSign.realPoly (ZPoly.toRatPoly p)).eval rep.root.re) = 0
  have heval := Polynomial.eval_map_apply (f := Complex.ofRealHom)
    (p := LiteralSign.realPoly (ZPoly.toRatPoly p)) rep.root.re
  rw [← heval, hpoly]
  change (HexRootsMathlib.toPolyℂ p).eval (rep.root.re : ℂ) = 0
  rw [hr]
  exact hz

/-- The square's rational circumscribed radius gives strict open endpoints
for a rational Tarski query at its selected root. -/
theorem literalRep_bounds (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec) :
    (((s.re - s.radiusHi).toRat : Rat) : ℝ) <
        (literalRep p s hw hp).root.re ∧
      (literalRep p s hw hp).root.re <
        (((s.re + s.radiusHi).toRat : Rat) : ℝ) := by
  let rep := literalRep p s hw hp
  have hmem : rep.root ∈ HexRootsMathlib.DyadicSquare.closedDisc s :=
    HexRootsMathlib.RefinedIsolation.root_mem_closedDisc rep
  have hdist : dist rep.root (HexRootsMathlib.DyadicSquare.center s) ≤
      HexRootsMathlib.DyadicSquare.radius s := by
    simpa only [HexRootsMathlib.DyadicSquare.closedDisc,
      Metric.mem_closedBall] using hmem
  have hcenter : (HexRootsMathlib.DyadicSquare.center s).re =
      HexRootsMathlib.Dyadic.toReal s.re := by
    simp [HexRootsMathlib.DyadicSquare.center_eq, Hex.DyadicSquare.center]
  have hreal : |rep.root.re - HexRootsMathlib.Dyadic.toReal s.re| ≤
      HexRootsMathlib.DyadicSquare.radius s := by
    have h := Complex.abs_re_le_norm
      (rep.root - HexRootsMathlib.DyadicSquare.center s)
    rw [Complex.sub_re, hcenter] at h
    rw [dist_eq_norm] at hdist
    exact h.trans hdist
  have hstrict := hreal.trans_lt (HexRootsMathlib.DyadicSquare.radius_lt_radiusHi s)
  have hpair := abs_lt.mp hstrict
  have hleft : (((s.re - s.radiusHi).toRat : Rat) : ℝ) =
      HexRootsMathlib.Dyadic.toReal s.re -
        HexRootsMathlib.Dyadic.toReal s.radiusHi := by
    rw [← HexRootsMathlib.Dyadic.toReal_sub]
    rfl
  have hright : (((s.re + s.radiusHi).toRat : Rat) : ℝ) =
      HexRootsMathlib.Dyadic.toReal s.re +
        HexRootsMathlib.Dyadic.toReal s.radiusHi := by
    rw [← HexRootsMathlib.Dyadic.toReal_add]
    rfl
  rw [hleft, hright]
  constructor <;> linarith [hpair.1, hpair.2]

variable {p : ZPoly} {x : SimpleRoot p}

/-- Interpret the existing reduced rational coordinates at a specified real
root. The root and its isolating representative remain explicit parameters. -/
noncomputable def value (rep : RefinedIsolation p) (a : PolyQuot p x) : ℝ :=
  (HexPolyMathlib.toPolynomial a.coeffs).eval₂ (Rat.castHom ℝ) rep.root.re

/-- The coordinate polynomial used by literal Tarski queries denotes exactly
the selected real field value. -/
theorem value_realPoly (rep : RefinedIsolation p) (a : PolyQuot p x) :
    value rep a = (LiteralSign.realPoly a.coeffs).eval rep.root.re := by
  have hmap : LiteralSign.realPoly a.coeffs =
      (HexPolyMathlib.toPolynomial a.coeffs).map (Rat.castHom ℝ) := by
    ext i
    simp [LiteralSign.realPoly]
  rw [hmap, Polynomial.eval_map]
  rfl

/-- Bind every rational sign certificate to the defining polynomial and the
specific literal square whose root names this field. -/
@[expose] def checkSignTable (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp))) : Bool :=
  decide (table.head = ZPoly.toRatPoly p) &&
    decide (table.lower = (s.re - s.radiusHi).toRat) &&
    decide (table.upper = (s.re + s.radiusHi).toRat) &&
    s.meetsRealAxis &&
    table.check PolyQuot.coeffs

/-- Accepted literal signs agree with the selected real embedding of the
field. Missing table entries use the semantic fallback in `Table.sign`. -/
theorem checkSignTable_spec (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (checked : checkSignTable p s hw hp table = true)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    table.sign (value (literalRep p s hw hp)) a =
      (SignType.sign (value (literalRep p s hw hp) a) : Int) := by
  simp only [checkSignTable, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨hhead, hlower⟩, hupper⟩, hreal⟩, htable⟩ := checked
  have hx : (LiteralSign.realPoly table.head).IsRoot
      (literalRep p s hw hp).root.re := by
    rw [hhead]
    exact literalRep_root p s hw hp hreal
  have hl : (table.lower : ℝ) < (literalRep p s hw hp).root.re := by
    rw [hlower]
    exact (literalRep_bounds p s hw hp).1
  have hu : (literalRep p s hw hp).root.re < (table.upper : ℝ) := by
    rw [hupper]
    exact (literalRep_bounds p s hw hp).2
  exact table.sign_spec PolyQuot.coeffs (value (literalRep p s hw hp))
    (literalRep p s hw hp).root.re
    hx hl hu
    (fun a => value_realPoly (literalRep p s hw hp) a) htable a

/-- A recorded hit can be used directly by executable consumers without
relying on the semantic fallback for absent table entries. -/
theorem checkSignTable_lookup (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (checked : checkSignTable p s hw hp table = true)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) (observed : Int)
    (hit : table.lookup? a = some observed) :
    observed = (SignType.sign (value (literalRep p s hw hp) a) : Int) := by
  have hs := checkSignTable_spec p s hw hp table checked a
  unfold LiteralSign.Table.sign at hs
  rw [hit] at hs
  exact hs

/-- Real interpretation retains the selected complex embedding when its root
is real. No projection of a nonreal field is admitted by this correspondence. -/
theorem value_complex (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = x)
    (hr : rep.root.im = 0) (a : PolyQuot p x) :
    (value rep a : ℂ) = PolyQuot.toComplex a rep hrep := by
  change Complex.ofRealHom
    ((HexPolyMathlib.toPolynomial a.coeffs).eval₂ (Rat.castHom ℝ) rep.root.re) = _
  rw [Polynomial.hom_eval₂]
  change (HexPolyMathlib.toPolynomial a.coeffs).eval₂
    (Complex.ofRealHom.comp (Rat.castHom ℝ)) (rep.root.re : ℂ) = _
  have he : (rep.root.re : ℂ) = rep.root := Complex.ext rfl hr.symm
  rw [he]
  rfl

/-- A recorded sign is the sign at the selected complex embedding, which is
real for this checked square. The finite table must contain the queried key. -/
theorem checkSignTable_lookup_complex (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (table : LiteralSign.Table
      (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (checked : checkSignTable p s hw hp table = true)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) (observed : Int)
    (hit : table.lookup? a = some observed) :
    observed = (SignType.sign
      (PolyQuot.toComplex a (literalRep p s hw hp)
        (literalRep_mk p s hw hp)).re : Int) := by
  have hv := congrArg Complex.re
    (value_complex (literalRep p s hw hp) (literalRep_mk p s hw hp)
      (literalRep_real p s hw hp hreal) a)
  simp only [Complex.ofReal_re] at hv
  rw [← hv]
  exact checkSignTable_lookup p s hw hp table checked a observed hit

variable (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = x)
variable (hr : rep.root.im = 0)
include hrep hr

@[simp] theorem value_zero : value rep (0 : PolyQuot p x) = 0 := by
  apply Complex.ofReal_injective
  rw [value_complex rep hrep hr, PolyQuot.map_zero, Complex.ofReal_zero]

@[simp] theorem value_one : value rep (1 : PolyQuot p x) = 1 := by
  apply Complex.ofReal_injective
  rw [value_complex rep hrep hr, PolyQuot.map_one, Complex.ofReal_one]

theorem value_add (a b : PolyQuot p x) :
    value rep (a + b) = value rep a + value rep b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, value_complex rep hrep hr,
    value_complex rep hrep hr, value_complex rep hrep hr, PolyQuot.map_add]

theorem value_sub (a b : PolyQuot p x) :
    value rep (a - b) = value rep a - value rep b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sub, value_complex rep hrep hr,
    value_complex rep hrep hr, value_complex rep hrep hr, PolyQuot.map_sub]

theorem value_mul (a b : PolyQuot p x) :
    value rep (a * b) = value rep a * value rep b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, value_complex rep hrep hr,
    value_complex rep hrep hr, value_complex rep hrep hr, PolyQuot.map_mul]

theorem value_natCast (n : Nat) : value rep (n : PolyQuot p x) = (n : ℝ) := by
  apply Complex.ofReal_injective
  rw [value_complex rep hrep hr]
  change PolyQuot.toComplex ((n : Rat) • (1 : PolyQuot p x)) rep hrep = _
  rw [PolyQuot.map_smul, PolyQuot.map_one, mul_one]
  norm_cast

variable [ZPoly.CheckedIrreducible p]

/-- Zero reflection comes from the existing injective field embedding and the
reduced-coordinate invariant, not equality of canonical algebraic numbers. -/
theorem value_eq_zero (a : PolyQuot p x) : value rep a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply PolyQuot.toComplex_injective rep hrep
    dsimp only
    rw [PolyQuot.map_zero, ← value_complex rep hrep hr, h, Complex.ofReal_zero]
  · rintro rfl
    exact value_zero rep hrep hr

theorem value_inv (a : PolyQuot p x) : value rep a⁻¹ = (value rep a)⁻¹ := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_inv, value_complex rep hrep hr,
    value_complex rep hrep hr, PolyQuot.map_inv]

theorem value_div (a b : PolyQuot p x) :
    value rep (a / b) = value rep a / value rep b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, value_complex rep hrep hr,
    value_complex rep hrep hr, value_complex rep hrep hr, PolyQuot.map_div]

omit hrep hr [ZPoly.CheckedIrreducible p] in
/-- The fixed-coordinate interpretation agrees with the existing conversion
from a user's `QAdjoin` value, at that generator's chosen real embedding. -/
theorem value_ofField (generator : RealAlgebraicNumber)
    (a : QAdjoin generator.toAlgebraic) :
    value generator.toAlgebraic.rep a = (Coefficients.ofField generator a).toReal := by
  rw [Coefficients.ofField_toReal]
  rfl

end Hex.RCF.RealCoefficients.Field
