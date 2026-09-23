/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.SignMatrix
public import HexRCF.RealFormula

public section

/-! Evaluate shared real formulas from signs supplied by checked cells. -/

namespace Hex.RCF.RealCoefficients

open Hex.RealFormula

namespace QF

private theorem polys_go_append (p : Hex.RealFormula.QF n)
    (tail : List (Hex.RealFormula.Poly n)) :
    Hex.RealFormula.QF.polys.go p tail =
      Hex.RealFormula.QF.polys.go p [] ++ tail := by
  induction p generalizing tail with
  | atom a => rfl
  | tt | ff => rfl
  | not p ih =>
      change Hex.RealFormula.QF.polys.go p tail =
        Hex.RealFormula.QF.polys.go p [] ++ tail
      exact ih tail
  | and p q ihp ihq | or p q ihp ihq =>
      change Hex.RealFormula.QF.polys.go p
          (Hex.RealFormula.QF.polys.go q tail) =
        Hex.RealFormula.QF.polys.go p
          (Hex.RealFormula.QF.polys.go q []) ++ tail
      calc
        Hex.RealFormula.QF.polys.go p (Hex.RealFormula.QF.polys.go q tail)
            = Hex.RealFormula.QF.polys.go p [] ++
                Hex.RealFormula.QF.polys.go q tail := ihp _
        _ = Hex.RealFormula.QF.polys.go p [] ++
              (Hex.RealFormula.QF.polys.go q [] ++ tail) := by rw [ihq]
        _ = (Hex.RealFormula.QF.polys.go p [] ++
              Hex.RealFormula.QF.polys.go q []) ++ tail :=
                (List.append_assoc _ _ _).symm
        _ = Hex.RealFormula.QF.polys.go p
              (Hex.RealFormula.QF.polys.go q []) ++ tail :=
              (congrArg (fun ys => ys ++ tail)
                (ihp (Hex.RealFormula.QF.polys.go q []))).symm

@[simp] private theorem polys_atom (a : Hex.RealFormula.Atom n) :
    (Hex.RealFormula.QF.atom a).polys = [a.p] := rfl
@[simp] private theorem polys_not (p : Hex.RealFormula.QF n) :
    p.not.polys = p.polys := rfl
@[simp] private theorem polys_and (p q : Hex.RealFormula.QF n) :
    (p.and q).polys = p.polys ++ q.polys :=
  polys_go_append p (Hex.RealFormula.QF.polys.go q [])
@[simp] private theorem polys_or (p q : Hex.RealFormula.QF n) :
    (p.or q).polys = p.polys ++ q.polys :=
  polys_go_append p (Hex.RealFormula.QF.polys.go q [])

/-- Every Boolean branch is evaluated, including one whose other branch has
already decided the truth value. Thus a missing sign always fails closed. -/
@[expose] def evalSigns (signOf : Hex.RealFormula.Poly n → Option Sign) : Hex.RealFormula.QF n → Option Bool
  | .atom a => do
      let sign ← signOf a.p
      pure ((RealFormula.toCmp a.cmp).evalSign sign)
  | .tt => some true
  | .ff => some false
  | .not p => do
      let value ← evalSigns signOf p
      pure (!value)
  | .and p q => do
      let left ← evalSigns signOf p
      let right ← evalSigns signOf q
      pure (left && right)
  | .or p q => do
      let left ← evalSigns signOf p
      let right ← evalSigns signOf q
      pure (left || right)

/-- The executable Boolean result agrees with the original formula whenever
each referenced polynomial has an exact sign at the given real valuation. -/
theorem evalSigns_spec {formula : Hex.RealFormula.QF n}
    {signOf : Hex.RealFormula.Poly n → Option Sign} {ρ : Fin n → ℝ}
    (hlookup : ∀ p ∈ formula.polys, ∃ sign,
      signOf p = some sign ∧
      SignType.sign (((sign.toInt : Int) : ℝ)) = SignType.sign (p.eval ρ)) :
    ∃ value, evalSigns signOf formula = some value ∧
      (value = true ↔ formula.toProp ρ) := by
  induction formula with
  | atom a =>
      obtain ⟨sign, hs, hsign⟩ := hlookup a.p (by simp)
      refine ⟨(RealFormula.toCmp a.cmp).evalSign sign, by simp [evalSigns, hs], ?_⟩
      rw [Hex.RealFormula.QF.toProp, Hex.RealFormula.Atom.toProp]
      exact (Hex.RCF.Cmp.evalSign_iff hsign).trans
        (RealFormula.toCmp_correct a.cmp (a.p.eval ρ))
  | tt => exact ⟨true, rfl, by simp [Hex.RealFormula.QF.toProp]⟩
  | ff => exact ⟨false, rfl, by simp [Hex.RealFormula.QF.toProp]⟩
  | not p ih =>
      obtain ⟨v, hv, hp⟩ := ih (by
        intro q hq
        exact hlookup q (by simpa using hq))
      refine ⟨!v, by simp [evalSigns, hv], ?_⟩
      cases v <;> simp_all [Hex.RealFormula.QF.toProp]
  | and p q ihp ihq =>
      obtain ⟨v, hv, hp⟩ := ihp (by
        intro r hr
        exact hlookup r (by simp [hr]))
      obtain ⟨w, hw, hq⟩ := ihq (by
        intro r hr
        exact hlookup r (by simp [hr]))
      refine ⟨v && w, by simp [evalSigns, hv, hw], ?_⟩
      cases v <;> cases w <;> simp_all [Hex.RealFormula.QF.toProp]
  | or p q ihp ihq =>
      obtain ⟨v, hv, hp⟩ := ihp (by
        intro r hr
        exact hlookup r (by simp [hr]))
      obtain ⟨w, hw, hq⟩ := ihq (by
        intro r hr
        exact hlookup r (by simp [hr]))
      refine ⟨v || w, by simp [evalSigns, hv, hw], ?_⟩
      cases v <;> cases w <;> simp_all [Hex.RealFormula.QF.toProp]

end QF
end Hex.RCF.RealCoefficients
