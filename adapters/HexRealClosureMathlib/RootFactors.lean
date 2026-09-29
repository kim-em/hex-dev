/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFactors
public import HexRealClosureMathlib.RootOrder
public import HexRealClosureMathlib.YunInvariant
public import HexRealClosureMathlib.ZeroFactor

public section

namespace Hex.RealClosure.Roots
open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
variable [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (ha : ∀ a b, φ (a + b) = φ a + φ b)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (hnat : ∀ n : Nat, φ (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))
variable (hn : ∀ a, φ (-a) = -φ a) (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)

omit [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
  [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem interpret_polynomial (p : DensePoly E) :
    interpret φ hz p = HexPolyMathlib.toPolynomial (DensePoly.Interpret.map φ hz p) := by
  ext i
  simp only [coeff_interpret, HexPolyMathlib.coeff_toPolynomial, DensePoly.Interpret.map_coeff]

/-- Interpret a completed root while retaining its emitted multiplicity. -/
@[expose] noncomputable def Entry.value {context : Ctx} (entry : Entry sign context) : K :=
  entry.root.value φ hz h1 ha hs hm hnat hsign

include hz h1 ha hs hm hnat hsign hn hi in
/-- Successful factor completion emits exactly the roots of the actual input
factors, each with the label supplied by that factor. -/
theorem factorEntries_spec {context : Ctx} (factors : List (DensePoly E × Nat))
    {out : List (Entry sign context)}
    (accepted : factorEntries sign context factors = .ok out) (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧
      entry.multiplicity = label) ↔
    ∃ factor ∈ factors, (interpret φ hz factor.1).IsRoot x ∧ factor.2 = label := by
  induction factors generalizing out with
  | nil =>
    have empty : out = [] := by simpa [factorEntries] using accepted.symm
    simp [empty]
  | cons factor factors ih =>
    obtain ⟨positive, completion, entries, _, remaining, output⟩ := factorEntries_cons accepted
    have coverage := completion.coverage φ hz h1 ha hs hm hnat hsign hn hi x
    rw [← completion.roots.entries_values φ hz h1 ha hs hm hnat hsign] at coverage
    rw [output]
    simp only [List.mem_append, List.mem_map, Entry.value]
    constructor
    · rintro ⟨entry, member | member, value, multiplicity⟩
      · obtain ⟨root, present, rfl⟩ := member
        refine ⟨factor, List.mem_cons_self, ?_, multiplicity⟩
        exact coverage.mp (List.mem_map.mpr ⟨root, present, value⟩)
      · obtain ⟨other, present, root, same⟩ := (ih remaining).mp ⟨entry, member, value, multiplicity⟩
        exact ⟨other, List.mem_cons_of_mem _ present, root, same⟩
    · rintro ⟨other, member, root, same⟩
      rcases List.mem_cons.mp member with rfl | present
      · obtain ⟨root, present, value⟩ := List.mem_map.mp (coverage.mpr root)
        exact ⟨⟨root, other.2, positive⟩, Or.inl ⟨root, present, rfl⟩, value, same⟩
      · obtain ⟨entry, member, value, multiplicity⟩ := (ih remaining).mpr ⟨other, present, root, same⟩
        exact ⟨entry, Or.inr member, value, multiplicity⟩


include hz h1 ha hs hm hnat hsign hn hi in
/-- Labels attached to roots of actual Yun factors equal the input's root
multiplicity. The raw coefficient type needs no field instance. -/
theorem factorEntries_multiplicity
    (hd : ∀ a b, φ (a / b) = φ a / φ b)
    {context : Ctx} (p : DensePoly E)
    {unit : E} {factors : Array (DensePoly E × Nat)}
    (decomposed : Yun.decomposeRaw p = .factors unit factors)
    {out : List (Entry sign context)}
    (accepted : factorEntries sign context factors.toList = .ok out)
    {entry : Entry sign context} (member : entry ∈ out) :
    (interpret φ hz p).rootMultiplicity (entry.value φ hz h1 ha hs hm hnat hsign) =
      entry.multiplicity := by
  have degree : 0 < p.natDegree := by
    by_contra h
    have zeroDegree : p.natDegree = 0 := Nat.eq_zero_of_not_pos h
    have nonzero := (Yun.decompose_unit p unit factors decomposed).2
    have empty : factors = #[] := by
      have same := decomposed
      simp only [Yun.decomposeRaw, nonzero, Bool.false_eq_true, zeroDegree,
        ↓reduceIte, Yun.Decomposition.factors.injEq] at same
      exact same.2.symm
    have output : out = [] := by simpa [empty, factorEntries] using accepted.symm
    simp [output] at member
  have mapped := Yun.map_decomposeRaw φ hz hs hm hd hi hnat p
  rw [decomposed] at mapped
  have produced : Yun.decomposeRaw (DensePoly.Interpret.map φ hz p) =
      .factors (φ unit) (factors.map fun factor =>
        (DensePoly.Interpret.map φ hz factor.1, factor.2)) := mapped.symm
  have components := Yun.decompose_factor (DensePoly.Interpret.map φ hz p)
    (by simpa only [DensePoly.Interpret.map_degree] using degree) _ _ produced
  obtain ⟨factor, present, root, label⟩ :=
    (factorEntries_spec φ hz h1 ha hs hm hnat hsign hn hi factors.toList accepted
      (entry.value φ hz h1 ha hs hm hnat hsign) entry.multiplicity).mp
        ⟨entry, member, rfl, rfl⟩
  have component := components (DensePoly.Interpret.map φ hz factor.1, factor.2)
    (Array.mem_map.mpr ⟨factor, Array.mem_toList_iff.mp present, rfl⟩)
  rw [interpret_polynomial] at root ⊢
  exact ((component.roots _).mp root).trans label

include hz h1 ha hs hm hnat hsign hn hi in
/-- Every input root occurs among the completed actual Yun factors with its
original multiplicity. This statement is tied to both producer results. -/
theorem factorEntries_complete
    (hd : ∀ a b, φ (a / b) = φ a / φ b)
    {context : Ctx} (p : DensePoly E) (nonzero : interpret φ hz p ≠ 0)
    {unit : E} {factors : Array (DensePoly E × Nat)}
    (decomposed : Yun.decomposeRaw p = .factors unit factors)
    {out : List (Entry sign context)}
    (accepted : factorEntries sign context factors.toList = .ok out)
    (x : K) (root : (interpret φ hz p).IsRoot x) :
    ∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧
      entry.multiplicity = (interpret φ hz p).rootMultiplicity x := by
  have mapped := Yun.map_decomposeRaw φ hz hs hm hd hi hnat p
  rw [decomposed] at mapped
  have produced : Yun.decomposeRaw (DensePoly.Interpret.map φ hz p) =
      .factors (φ unit) (factors.map fun factor =>
        (DensePoly.Interpret.map φ hz factor.1, factor.2)) := mapped.symm
  have rawNonzero : DensePoly.Interpret.map φ hz p ≠ 0 := by
    intro zero
    apply nonzero
    rw [interpret_polynomial, zero, HexPolyMathlib.toPolynomial_zero]
  rw [interpret_polynomial] at root
  obtain ⟨scalar, components, computed, component, member, label, root⟩ :=
    Yun.decompose_root (DensePoly.Interpret.map φ hz p) x rawNonzero root
  rw [produced] at computed
  cases (Yun.Decomposition.factors.inj computed).2
  obtain ⟨factor, present, rfl⟩ := Array.mem_map.mp member
  rw [← interpret_polynomial] at root label
  exact (factorEntries_spec φ hz h1 ha hs hm hnat hsign hn hi factors.toList accepted
    x ((interpret φ hz p).rootMultiplicity x)).mpr
      ⟨factor, Array.mem_toList_iff.mpr present, root, label⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- Actual Yun completion has exact coverage and multiplicities over the
common ambient field, including the empty output for a nonzero constant. -/
theorem factorEntries_roots (hd : ∀ a b, φ (a / b) = φ a / φ b)
    {context : Ctx} (p : DensePoly E) (nonzero : interpret φ hz p ≠ 0)
    {unit : E} {factors : Array (DensePoly E × Nat)}
    (decomposed : Yun.decomposeRaw p = .factors unit factors)
    {out : List (Entry sign context)}
    (accepted : factorEntries sign context factors.toList = .ok out)
    (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧
      entry.multiplicity = label) ↔
    (interpret φ hz p).IsRoot x ∧ label = (interpret φ hz p).rootMultiplicity x := by
  constructor
  · rintro ⟨entry, member, value, multiplicity⟩
    have exactLabel := factorEntries_multiplicity φ hz h1 ha hs hm hnat hsign hn hi
      hd p decomposed accepted member
    rw [value] at exactLabel
    refine ⟨(Polynomial.rootMultiplicity_pos nonzero).mp ?_, multiplicity.symm.trans exactLabel.symm⟩
    rw [exactLabel]
    exact entry.positive
  · rintro ⟨root, rfl⟩
    exact factorEntries_complete φ hz h1 ha hs hm hnat hsign hn hi hd p nonzero
      decomposed accepted x root

private theorem assemble_result {context : Ctx} (p : DensePoly E)
    {out : List (Entry sign context)}
    (accepted : assemble sign context p = .ok (.finite out)) :
    p.isZero = false ∧ ∃ unit factors entries,
      Yun.decomposeRaw (ZeroFactor.remove p).1 = .factors unit factors ∧
      factorEntries sign context factors.toList = .ok entries ∧
      out = if positive : 0 < (ZeroFactor.remove p).2 then
        ⟨.point 0, (ZeroFactor.remove p).2, positive⟩ :: entries else entries := by
  by_cases zero : p.isZero = true
  · simp [assemble, zero] at accepted
  · have nonzero : p.isZero = false := Bool.eq_false_of_ne_true zero
    cases decomposed : Yun.decomposeRaw (ZeroFactor.remove p).1 with
    | zero => simp [assemble, nonzero, decomposed] at accepted
    | factors unit factors =>
      cases completed : factorEntries sign context factors.toList with
      | error error => simp [assemble, nonzero, decomposed, completed] at accepted
      | ok entries =>
        refine ⟨nonzero, unit, factors, entries, rfl, completed, ?_⟩
        split
        · rename_i positive
          simpa [assemble, nonzero, decomposed, completed, positive] using accepted.symm
        · rename_i positive
          simpa [assemble, nonzero, decomposed, completed, positive] using accepted.symm

include hz h1 ha hs hm hnat hsign hn hi in
/-- Successful finite assembly covers exactly the original roots and their
positive original multiplicities, including the single restored zero root. -/
theorem assemble_spec (hd : ∀ a b, φ (a / b) = φ a / φ b)
    {context : Ctx} (p : DensePoly E) {out : List (Entry sign context)}
    (accepted : assemble sign context p = .ok (.finite out)) (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧
      entry.multiplicity = label) ↔
    (interpret φ hz p).IsRoot x ∧ label = (interpret φ hz p).rootMultiplicity x := by
  obtain ⟨notZero, unit, factors, entries, decomposed, completed, output⟩ := assemble_result p accepted
  have nonzero : interpret φ hz p ≠ 0 := by
    intro zero
    have rawZero := (interpret_eq_zero φ hz p).mp zero
    subst p
    have isZero : (0 : DensePoly E).isZero = true :=
      (DensePoly.isZero_eq_true_iff _).mpr DensePoly.size_zero
    simp [isZero] at notZero
  have removed := ZeroFactor.remove_spec φ hz p nonzero
  have coverage := factorEntries_roots φ hz h1 ha hs hm hnat hsign hn hi hd
    (ZeroFactor.remove p).1 removed.1 decomposed completed x label
  rw [output]
  by_cases atZero : x = 0
  · subst x
    have noRoot : ¬ (interpret φ hz (ZeroFactor.remove p).1).IsRoot 0 := removed.2.1
    have multiplicity := ZeroFactor.remove_multiplicity φ hz p nonzero
    have root : (interpret φ hz p).IsRoot 0 ↔ 0 < (ZeroFactor.remove p).2 := by
      rw [← Polynomial.rootMultiplicity_pos nonzero, multiplicity]
    by_cases positive : 0 < (ZeroFactor.remove p).2
    · simp only [positive, ↓reduceDIte, List.mem_cons]
      rw [root, multiplicity]
      simp only [positive, true_and]
      constructor
      · rintro ⟨entry, same | member, value, label⟩
        · subst entry
          exact label.symm
        · exact False.elim (noRoot ((coverage.mp ⟨entry, member, value, label⟩).1))
      · intro label
        exact ⟨⟨.point 0, (ZeroFactor.remove p).2, positive⟩, Or.inl rfl,
          (hz 0).mpr rfl, label.symm⟩
    · simp only [positive, ↓reduceDIte, coverage, noRoot, root, false_and]
  · have originalRoots := ZeroFactor.remove_roots φ hz p nonzero x atZero
    have multiplicity := ZeroFactor.remove_rootMultiplicity φ hz p nonzero x atZero
    rw [originalRoots, multiplicity]
    by_cases positive : 0 < (ZeroFactor.remove p).2
    · simp only [positive, ↓reduceDIte, List.mem_cons]
      constructor
      · rintro ⟨entry, same | member, value, label⟩
        · subst entry
          have zeroValue : (⟨.point 0, (ZeroFactor.remove p).2, positive⟩ :
              Entry sign context).value φ hz h1 ha hs hm hnat hsign = 0 := (hz 0).mpr rfl
          exact False.elim (atZero (value.symm.trans zeroValue))
        · exact coverage.mp ⟨entry, member, value, label⟩
      · intro root
        obtain ⟨entry, member, value, label⟩ := coverage.mpr root
        exact ⟨entry, Or.inr member, value, label⟩
    · simpa only [positive, ↓reduceDIte] using coverage

omit [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The separate all-roots result is returned exactly for semantic zero. -/
theorem assemble_all {sign : E → Int} (context : Ctx) (p : DensePoly E) :
    assemble sign context p = .ok .all ↔ interpret φ hz p = 0 := by
  have raw : assemble sign context p = .ok .all ↔ p.isZero = true := by
    by_cases zero : p.isZero = true
    · simp [assemble, zero]
    · cases decomposed : Yun.decomposeRaw (ZeroFactor.remove p).1 with
      | zero => simp [assemble, zero, decomposed]
      | factors unit factors =>
        cases completed : factorEntries sign context factors.toList with
        | error error => simp [assemble, zero, decomposed, completed]
        | ok entries =>
          by_cases positive : 0 < (ZeroFactor.remove p).2 <;>
            simp [assemble, zero, decomposed, completed, positive]
  rw [raw, DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff,
    interpret_eq_zero φ hz]

end Hex.RealClosure.Roots

/-- info: 'Hex.RealClosure.Roots.factorEntries_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.factorEntries_spec

/-- info: 'Hex.RealClosure.Roots.factorEntries_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.factorEntries_multiplicity
/-- info: 'Hex.RealClosure.Roots.factorEntries_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.factorEntries_complete

/-- info: 'Hex.RealClosure.Roots.factorEntries_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.factorEntries_roots
/-- info: 'Hex.RealClosure.Roots.assemble_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.assemble_spec

/-- info: 'Hex.RealClosure.Roots.assemble_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.assemble_all
