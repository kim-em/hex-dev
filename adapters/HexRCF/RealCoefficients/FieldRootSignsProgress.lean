/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.IsolationAssembly
public import HexRCF.RealCoefficients.FieldRootSigns
public section
namespace Hex.RCF.RealCoefficients.FieldRootSigns.Table
variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
  [Neg E] [Inv E] [NatCast E]
variable (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
  (h1 : f 1 = 1) (ha : ∀ a b, f (a+b) = f a + f b)
  (hs : ∀ a b, f (a-b) = f a - f b) (hm : ∀ a b, f (a*b) = f a * f b)
  (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
  (hnat : ∀ n : Nat, f (n : E) = (n : ℝ))
  (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
  (point : Dyadic → E)
include hz h1 ha hs hm hn hi hnat hsign

/-- The actual root-sign table producer succeeds on every formula after
isolation construction succeeds. Missing rows, malformed domains and copied
root queries cannot be assumed away: their checks are proved here. -/
theorem build_success {Ctx : Type v} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly E) (isolations : IsolationCert)
    (cert : IsolationReplay E Ctx)
    (produced : IsolationReplay.build sign point context head isolations = some cert)
    (query : RealFormula.Poly n → DensePoly E) (formula : RealFormula.QF n) :
    ∃ table, build sign point context head cert query formula = some table := by
  classical
  have checked := (IsolationReplay.build_checked sign point context head isolations cert produced).2
  have chain := IsolationReplay.build_squarefree sign point context head isolations cert produced
  let row (atom : RealFormula.Poly n) : Entry E Ctx n cert.isolations.intervals.size :=
    ⟨atom, Vector.ofFn fun i => cert.queryAt sign point context head (query atom) i⟩
  let table : Table E Ctx n cert.isolations.intervals.size := ⟨formula.polys.map row⟩
  have accepted : table.check sign point context head cert.isolations.intervals.toVector query formula = true := by
    apply List.all_eq_true.mpr
    intro atom present
    have available : ∃ entry ∈ table.entries, sameAtom atom entry = true :=
      ⟨row atom, List.mem_map.mpr ⟨atom, present, rfl⟩, by simp [sameAtom, row]⟩
    cases found : table.entries.find? (sameAtom atom) with
    | none =>
      obtain ⟨entry, mem, matchAtom⟩ := available
      have absent := List.find?_eq_none.mp found entry mem
      simp [matchAtom] at absent
    | some entry =>
      have member := List.mem_of_find?_eq_some found
      have matchAtom := List.find?_some (p := sameAtom atom) found
      obtain ⟨original, _, rowEq⟩ := List.mem_map.mp member
      have originalEq : original = atom := by
        simpa [← rowEq, sameAtom, row] using matchAtom
      subst original
      subst entry
      apply List.all_eq_true.mpr
      intro i _
      have queryChecked := IsolationReplay.queryAt_checked f hz h1 ha hs hm hn hi hnat
        sign hsign point context head (query atom) cert checked chain i
      change Sturm.check sign context head (query atom)
        (.finite (point cert.isolations.intervals[i.val].lower))
        (.finite (point cert.isolations.intervals[i.val].upper))
        (Vector.ofFn fun j => cert.queryAt sign point context head (query atom) j)[i.val].value
        (Vector.ofFn fun j => cert.queryAt sign point context head (query atom) j)[i.val] = true
      simpa only [Vector.getElem_ofFn, Fin.getElem_fin] using queryChecked
  refine ⟨table, ?_⟩
  unfold build
  change (if table.check sign point context head cert.isolations.intervals.toVector query formula
    then some table else none) = some table
  simp only [accepted, ite_eq_left]

end Hex.RCF.RealCoefficients.FieldRootSigns.Table
