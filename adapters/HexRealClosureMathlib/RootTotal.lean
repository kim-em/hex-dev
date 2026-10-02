/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.RootFactors
public import HexRealClosureMathlib.IsolationTotal
public import HexRealClosure.CompleteRoots

public section

namespace Hex.RealClosure.Roots
open HexPolyMathlib.Interpret

attribute [local instance 2000] Field.toGrindField

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
variable (hd : ∀ a b, φ (a / b) = φ a / φ b)

include hz h1 ha hs hm hnat hsign hn hi in
/-- A finite list of nonzero squarefree factors with positive labels has a
successful actual root completion. -/
theorem factorEntries_success (context : Ctx) (factors : List (DensePoly E × Nat))
    (valid : ∀ factor ∈ factors, 0 < factor.2 ∧ interpret φ hz factor.1 ≠ 0 ∧
      Squarefree (interpret φ hz factor.1)) :
    ∃ entries, factorEntries sign context factors = .ok entries := by
  induction factors with
  | nil => exact ⟨[], rfl⟩
  | cons factor factors ih =>
    obtain ⟨positive, nonzero, squarefree⟩ := valid factor List.mem_cons_self
    obtain ⟨completion, completed⟩ := Isolation.complete?_success φ hz h1 ha hs hm hnat
      hsign hn hi context factor.1 nonzero squarefree
    obtain ⟨entries, remaining⟩ := ih (fun other member =>
      valid other (List.mem_cons_of_mem _ member))
    exact ⟨completion.roots.entries.map (fun root => ⟨root, factor.2, positive⟩) ++ entries,
      by simp [factorEntries, positive, completed, remaining]⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The actual raw Yun result satisfies the premises needed to complete all
of its factors, including a constant input's empty factor list. -/
theorem factorEntries_yun (context : Ctx) (p : DensePoly E)
    {unit : E} {factors : Array (DensePoly E × Nat)}
    (decomposed : Yun.decomposeRaw p = .factors unit factors) :
    ∃ entries, factorEntries sign context factors.toList = .ok entries := by
  let mapped := DensePoly.Interpret.map φ hz p
  let mappedFactors := factors.map fun factor =>
    (DensePoly.Interpret.map φ hz factor.1, factor.2)
  have produced : Yun.decomposeRaw mapped = .factors (φ unit) mappedFactors := by
    have transported := Yun.map_decomposeRaw φ hz hs hm hd hi hnat p
    rw [decomposed] at transported
    exact transported.symm
  have checked : Yun.check mapped (.factors (φ unit) mappedFactors) = true := by
    have sound := Yun.decompose_sound mapped
    change Yun.check mapped (Yun.decomposeRaw mapped) = true at sound
    rwa [produced] at sound
  apply factorEntries_success φ hz h1 ha hs hm hnat hsign hn hi context factors.toList
  intro factor member
  have present : (DensePoly.Interpret.map φ hz factor.1, factor.2) ∈ mappedFactors :=
    Array.mem_map.mpr ⟨factor, Array.mem_toList_iff.mp member, rfl⟩
  obtain ⟨positive, degree, _, _⟩ := Yun.check_factor mapped (φ unit) mappedFactors
    _ present checked
  have nonzero : DensePoly.Interpret.map φ hz factor.1 ≠ 0 := by
    intro zero
    rw [zero] at degree
    simp at degree
  refine ⟨positive, ?_, ?_⟩
  · rw [interpret_map]
    exact fun zero => nonzero (HexPolyMathlib.equiv.injective
      (zero.trans HexPolyMathlib.toPolynomial_zero.symm))
  · rw [interpret_map]
    exact Yun.check_factor_squarefree mapped (φ unit) mappedFactors _ present checked

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Root assembly succeeds for every input. Semantic zero retains `all`;
every other input completes its actual zero extraction and Yun factors. -/
theorem assemble_success (context : Ctx) (p : DensePoly E) :
    ∃ output, assemble sign context p = .ok output := by
  by_cases zero : p.isZero = true
  · exact ⟨.all, by simp [assemble, zero]⟩
  have nonzero : interpret φ hz p ≠ 0 := by
    intro interpreted
    exact zero (by rw [(interpret_eq_zero φ hz p).mp interpreted]; rfl)
  have removed := ZeroFactor.remove_spec φ hz p nonzero
  have rawNonzero : (ZeroFactor.remove p).1 ≠ 0 := by
    intro rawZero
    apply removed.1
    rw [rawZero, interpret_zero φ hz]
  have notZero : (ZeroFactor.remove p).1.isZero = false := by
    apply Bool.eq_false_of_ne_true
    intro isZero
    exact rawNonzero ((DensePoly.size_eq_zero_iff _).mp
      ((DensePoly.isZero_eq_true_iff _).mp isZero))
  cases decomposed : Yun.decomposeRaw (ZeroFactor.remove p).1 with
  | zero =>
    simp only [Yun.decomposeRaw, notZero, Bool.false_eq_true, ↓reduceIte] at decomposed
    split at decomposed <;> cases decomposed
  | factors unit factors =>
    obtain ⟨entries, completed⟩ := factorEntries_yun φ hz h1 ha hs hm hnat hsign hn hi hd
      context (ZeroFactor.remove p).1 decomposed
    by_cases positive : 0 < (ZeroFactor.remove p).2
    · exact ⟨.finite (⟨.point 0, (ZeroFactor.remove p).2, positive⟩ :: entries),
        by simp [assemble, zero, decomposed, completed, positive]⟩
    · exact ⟨.finite entries, by simp [assemble, zero, decomposed, completed, positive]⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The full checked root producer succeeds for every input. The sorter
retains the exact entries and their original positive multiplicities. -/
theorem roots?_success (context : Ctx) (p : DensePoly E) :
    ∃ output, roots? sign context p = .ok output := by
  obtain ⟨output, assembled⟩ := assemble_success φ hz h1 ha hs hm hnat hsign hn hi hd context p
  cases output with
  | all => exact ⟨.all, by simp [roots?, assembled]⟩
  | finite entries =>
    have distinct := assemble_nodup φ hz h1 ha hs hm hnat hsign hn hi hd p assembled
    obtain ⟨out, sorted, _⟩ := Isolation.Root.sortBy_success φ hz h1 ha hs hm hnat hsign
      hn hi hd Entry.root entries distinct
    exact ⟨.finite out, by simp [roots?, assembled, sorted]⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The ordinary root API returns its actual successful construction. -/
theorem roots_success (context : Ctx) (p : DensePoly E) :
    ∃ output, roots? sign context p = .ok output ∧ roots sign context p = output := by
  obtain ⟨output, built⟩ := roots?_success φ hz h1 ha hs hm hnat hsign hn hi hd context p
  exact ⟨output, built, roots_of_success built⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Checked complete roots cover exactly the input's mathematical roots
with their exact multiplicities after the actual global sort. -/
theorem roots?_spec {context : Ctx} (p : DensePoly E) {out : List (Entry sign context)}
    (built : roots? sign context p = .ok (.finite out)) (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧
      entry.multiplicity = label) ↔
      (interpret φ hz p).IsRoot x ∧ label = (interpret φ hz p).rootMultiplicity x := by
  obtain ⟨entries, assembled, sorted⟩ := roots?_finite built
  have preserved := Isolation.Root.sortBy_perm Entry.root sorted
  rw [← assemble_spec φ hz h1 ha hs hm hnat hsign hn hi hd p assembled x label]
  constructor
  · rintro ⟨entry, member, value, multiplicity⟩
    exact ⟨entry, preserved.mem_iff.mp member, value, multiplicity⟩
  · rintro ⟨entry, member, value, multiplicity⟩
    exact ⟨entry, preserved.mem_iff.mpr member, value, multiplicity⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Checked complete root entries are strictly increasing by their actual
mathematical values across all Yun factors and restored coefficient roots. -/
theorem roots?_sorted {context : Ctx} (p : DensePoly E) {out : List (Entry sign context)}
    (built : roots? sign context p = .ok (.finite out)) :
    (out.map (Entry.value φ hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) := by
  obtain ⟨_, _, sorted⟩ := roots?_finite built
  exact Isolation.Root.sortBy_sorted φ hz h1 ha hs hm hnat hsign hn hi hd Entry.root sorted

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The total complete root API retains `all` exactly for semantic zero. -/
theorem roots_all (context : Ctx) (p : DensePoly E) :
    roots sign context p = .all ↔ interpret φ hz p = 0 := by
  obtain ⟨output, built, returned⟩ := roots_success φ hz h1 ha hs hm hnat hsign hn hi hd context p
  constructor
  · intro all
    have outputAll : output = .all := returned.symm.trans all
    rw [outputAll] at built
    exact (assemble_all φ hz context p).mp ((roots?_all p).mp built)
  · intro zero
    exact roots_of_success ((roots?_all p).mpr ((assemble_all φ hz context p).mpr zero))

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The ordinary complete root result has exact root coverage and multiplicities. -/
theorem roots_spec {context : Ctx} (p : DensePoly E) {out : List (Entry sign context)}
    (returned : roots sign context p = .finite out) (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧
      entry.multiplicity = label) ↔
      (interpret φ hz p).IsRoot x ∧ label = (interpret φ hz p).rootMultiplicity x := by
  obtain ⟨output, built, computed⟩ := roots_success φ hz h1 ha hs hm hnat hsign hn hi hd context p
  rw [computed.symm.trans returned] at built
  exact roots?_spec φ hz h1 ha hs hm hnat hsign hn hi hd p built x label

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The ordinary complete root result is strictly increasing. -/
theorem roots_sorted {context : Ctx} (p : DensePoly E) {out : List (Entry sign context)}
    (returned : roots sign context p = .finite out) :
    (out.map (Entry.value φ hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) := by
  obtain ⟨output, built, computed⟩ := roots_success φ hz h1 ha hs hm hnat hsign hn hi hd context p
  rw [computed.symm.trans returned] at built
  exact roots?_sorted φ hz h1 ha hs hm hnat hsign hn hi hd p built

end Hex.RealClosure.Roots

/-- info: 'Hex.RealClosure.Roots.assemble_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.assemble_success

/-- info: 'Hex.RealClosure.Roots.roots_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.roots_success

/-- info: 'Hex.RealClosure.Roots.roots_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.roots_all

/-- info: 'Hex.RealClosure.Roots.roots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.roots_spec

/-- info: 'Hex.RealClosure.Roots.roots_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.roots_sorted
