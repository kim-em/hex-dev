/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.List.Sort
public import HexRealClosureMathlib.RootTotal
public import HexRealClosureMathlib.IsolationPolicy
public import HexRealClosure.RootPolicy
public import HexRealClosureMathlib.IsolationTotal
public import HexRealClosure.CompleteRoots

public section

namespace Hex.RealClosure.Roots.Policy
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


variable (policy : Isolation.Policy)
include hz h1 ha hs hm hnat hsign hn hi in
/-- A finite list of nonzero squarefree factors with positive labels has a
successful actual root completion. -/
theorem factorEntries_success (context : Ctx) (factors : List (DensePoly E × Nat))
    (valid : ∀ factor ∈ factors, 0 < factor.2 ∧ interpret φ hz factor.1 ≠ 0 ∧
      Squarefree (interpret φ hz factor.1)) :
    ∃ entries, factorEntries policy sign context factors = .ok entries := by
  induction factors with
  | nil => exact ⟨[], rfl⟩
  | cons factor factors ih =>
    obtain ⟨positive, nonzero, squarefree⟩ := valid factor List.mem_cons_self
    obtain ⟨completion, completed⟩ := Isolation.Policy.complete?_success φ hz h1 ha hs hm sign hsign hn hi hnat policy
      context factor.1 nonzero squarefree
    obtain ⟨entries, remaining⟩ := ih (fun other member =>
      valid other (List.mem_cons_of_mem _ member))
    exact ⟨completion.entries.map (fun root => ⟨root, factor.2, positive⟩) ++ entries,
      by simp [factorEntries, positive, completed, remaining]⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The actual raw Yun result satisfies the premises needed to complete all
of its factors, including a constant input's empty factor list. -/
theorem factorEntries_yun (context : Ctx) (p : DensePoly E)
    {unit : E} {factors : Array (DensePoly E × Nat)}
    (decomposed : Yun.decomposeRaw p = .factors unit factors) :
    ∃ entries, factorEntries policy sign context factors.toList = .ok entries := by
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
  apply factorEntries_success φ hz h1 ha hs hm hnat hsign hn hi policy context factors.toList
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


include hz h1 ha hs hm hnat hsign hn hi in
/-- The policy changes the descriptors retained for a factor, while preserving
its mathematical values and original positive multiplicity exactly. -/
theorem factorEntries_perm (context : Ctx) (factors : List (DensePoly E × Nat))
    (out original : List (Entry sign context))
    (built : factorEntries policy sign context factors = .ok out)
    (standard : Roots.factorEntries sign context factors = .ok original) :
    (out.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)).Perm
      (original.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)) := by
  induction factors generalizing out original with
  | nil =>
    have first : out = [] := by simpa [factorEntries] using built.symm
    have second : original = [] := by simpa [Roots.factorEntries] using standard.symm
    simp [first, second]
  | cons factor factors ih =>
    obtain ⟨positive, completion, entries, completed, remaining, output⟩ := factorEntries_cons built
    obtain ⟨oldPositive, old, oldEntries, oldCompleted, oldRemaining, oldOutput⟩ :=
      Roots.factorEntries_cons standard
    have first := Isolation.Policy.complete?_nodup φ hz h1 ha hs hm sign hsign hn hi hnat
      policy context factor.1 completion completed
    have second := old.nodup φ hz h1 ha hs hm hnat hsign hn hi
    have coverage : ∀ x : K, x ∈ completion.values φ hz h1 ha hs hm hnat hsign ↔
        x ∈ old.roots.values φ hz h1 ha hs hm hnat hsign := fun x =>
      (Isolation.Policy.complete?_coverage φ hz h1 ha hs hm sign hsign hn hi hnat
        policy context factor.1 completion completed x).trans
          (old.coverage φ hz h1 ha hs hm hnat hsign hn hi x).symm
    have same := (List.subperm_of_subset first (fun x h => (coverage x).mp h)).antisymm
      (List.subperm_of_subset second (fun x h => (coverage x).mpr h))
    rw [← completion.entries_values φ hz h1 ha hs hm hnat hsign,
      ← old.roots.entries_values φ hz h1 ha hs hm hnat hsign] at same
    have labeled := same.map (fun x => (x, factor.2))
    rw [output, oldOutput, List.map_append, List.map_append]
    apply List.Perm.append _ (ih entries oldEntries remaining oldRemaining)
    simpa only [List.map_map, Function.comp_def, Entry.value] using labeled

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Root assembly succeeds for every input. Semantic zero retains `all`;
every other input completes its actual zero extraction and Yun factors. -/
theorem assemble_success (context : Ctx) (p : DensePoly E) :
    ∃ output, assemble policy sign context p = .ok output := by
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
      policy context (ZeroFactor.remove p).1 decomposed
    by_cases positive : 0 < (ZeroFactor.remove p).2
    · exact ⟨.finite (⟨.point 0, (ZeroFactor.remove p).2, positive⟩ :: entries),
        by simp [assemble, zero, decomposed, completed, positive]⟩
    · exact ⟨.finite entries, by simp [assemble, zero, decomposed, completed, positive]⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- Policy changes preserve all original root values and multiplicities,
including the separately extracted zero root. -/
theorem assemble_perm (context : Ctx) (p : DensePoly E)
    (out original : List (Entry sign context))
    (built : assemble policy sign context p = .ok (.finite out))
    (standard : Roots.assemble sign context p = .ok (.finite original)) :
    (out.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)).Perm
      (original.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)) := by
  by_cases zero : p.isZero = true
  · simp [assemble, zero] at built
  cases decomposed : Yun.decomposeRaw (ZeroFactor.remove p).1 with
  | zero => simp [assemble, zero, decomposed] at built
  | factors unit factors =>
    cases completed : factorEntries policy sign context factors.toList with
    | error error => simp [assemble, zero, decomposed, completed] at built
    | ok entries =>
      cases oldCompleted : Roots.factorEntries sign context factors.toList with
      | error error => simp [Roots.assemble, zero, decomposed, oldCompleted] at standard
      | ok oldEntries =>
        have preserved := factorEntries_perm φ hz h1 ha hs hm hnat hsign hn hi
          policy context factors.toList entries oldEntries completed oldCompleted
        by_cases positive : 0 < (ZeroFactor.remove p).2
        · have same : out = ⟨.point 0, (ZeroFactor.remove p).2, positive⟩ :: entries := by
            simpa [assemble, zero, decomposed, completed, positive] using built.symm
          have oldSame : original = ⟨.point 0, (ZeroFactor.remove p).2, positive⟩ :: oldEntries := by
            simpa [Roots.assemble, zero, decomposed, oldCompleted, positive] using standard.symm
          rw [same, oldSame, List.map_cons, List.map_cons]
          exact preserved.cons _
        · have same : out = entries := by
            simpa [assemble, zero, decomposed, completed, positive] using built.symm
          have oldSame : original = oldEntries := by
            simpa [Roots.assemble, zero, decomposed, oldCompleted, positive] using standard.symm
          rw [same, oldSame]
          exact preserved

omit [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The separate all-roots case remains exactly semantic zero for every policy. -/
theorem assemble_all {sign : E → Int} (context : Ctx) (p : DensePoly E) :
    assemble policy sign context p = .ok .all ↔ interpret φ hz p = 0 := by
  have raw : assemble policy sign context p = .ok .all ↔ p.isZero = true := by
    by_cases zero : p.isZero = true
    · simp [assemble, zero]
    · cases decomposed : Yun.decomposeRaw (ZeroFactor.remove p).1 with
      | zero => simp [assemble, zero, decomposed]
      | factors unit factors =>
        cases completed : factorEntries policy sign context factors.toList with
        | error error => simp [assemble, zero, decomposed, completed]
        | ok entries =>
          by_cases positive : 0 < (ZeroFactor.remove p).2 <;>
            simp [assemble, zero, decomposed, completed, positive]
  rw [raw, DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff,
    interpret_eq_zero φ hz]

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Every policy emits each original root once before global sorting. -/
theorem assemble_nodup (context : Ctx) (p : DensePoly E)
    (out : List (Entry sign context)) (built : assemble policy sign context p = .ok (.finite out)) :
    (out.map (Entry.value φ hz h1 ha hs hm hnat hsign)).Nodup := by
  obtain ⟨original, standard⟩ := Roots.assemble_success φ hz h1 ha hs hm hnat hsign hn hi hd context p
  cases original with
  | all =>
    have zero := (Roots.assemble_all φ hz context p).mp standard
    have all := (assemble_all φ hz policy (sign := sign) context p).mpr zero
    rw [built] at all
    cases all
  | finite entries =>
    have preserved := (assemble_perm φ hz h1 ha hs hm hnat hsign hn hi
      policy context p out entries built standard).map Prod.fst
    simp only [List.map_map, Function.comp_def] at preserved
    exact preserved.nodup_iff.mpr (Roots.assemble_nodup φ hz h1 ha hs hm hnat hsign hn hi hd p standard)

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Complete roots with the chosen policy succeed on every polynomial. -/
theorem roots?_success (context : Ctx) (p : DensePoly E) :
    ∃ output, roots? policy sign context p = .ok output := by
  obtain ⟨output, assembled⟩ := assemble_success φ hz h1 ha hs hm hnat hsign hn hi hd policy context p
  cases output with
  | all => exact ⟨.all, by simp [roots?, assembled]⟩
  | finite entries =>
    have distinct := assemble_nodup φ hz h1 ha hs hm hnat hsign hn hi hd policy context p entries assembled
    obtain ⟨out, sorted, _⟩ := Isolation.Root.sortBy_success φ hz h1 ha hs hm hnat hsign
      hn hi hd Entry.root entries distinct
    exact ⟨.finite out, by simp [roots?, assembled, sorted]⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Every policy retains the exact original multiplicity for every root. -/
theorem assemble_spec (context : Ctx) (p : DensePoly E) (out : List (Entry sign context))
    (built : assemble policy sign context p = .ok (.finite out)) (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧ entry.multiplicity = label) ↔
      (interpret φ hz p).IsRoot x ∧ label = (interpret φ hz p).rootMultiplicity x := by
  obtain ⟨original, standard⟩ := Roots.assemble_success φ hz h1 ha hs hm hnat hsign hn hi hd context p
  cases original with
  | all =>
    have zero := (Roots.assemble_all φ hz context p).mp standard
    have all := (assemble_all φ hz policy (sign := sign) context p).mpr zero
    rw [built] at all
    cases all
  | finite entries =>
    have preserved := assemble_perm φ hz h1 ha hs hm hnat hsign hn hi policy context p out entries built standard
    have membership := preserved.mem_iff (a := (x, label))
    simp only [List.mem_map, Prod.mk.injEq] at membership
    exact membership.trans (Roots.assemble_spec φ hz h1 ha hs hm hnat hsign hn hi hd p standard x label)

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Global sorting preserves every root and its original multiplicity under
all permitted finite isolation choices. -/
theorem roots?_spec (context : Ctx) (p : DensePoly E) (out : List (Entry sign context))
    (built : roots? policy sign context p = .ok (.finite out)) (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧ entry.multiplicity = label) ↔
      (interpret φ hz p).IsRoot x ∧ label = (interpret φ hz p).rootMultiplicity x := by
  obtain ⟨entries, assembled, sorted⟩ := roots?_finite built
  have preserved := Isolation.Root.sortBy_perm Entry.root sorted
  rw [← assemble_spec φ hz h1 ha hs hm hnat hsign hn hi hd policy context p entries assembled x label]
  constructor
  · rintro ⟨entry, member, value, multiplicity⟩
    exact ⟨entry, preserved.mem_iff.mp member, value, multiplicity⟩
  · rintro ⟨entry, member, value, multiplicity⟩
    exact ⟨entry, preserved.mem_iff.mpr member, value, multiplicity⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Output values are strictly increasing, retaining their attached labels. -/
theorem roots?_sorted (context : Ctx) (p : DensePoly E) (out : List (Entry sign context))
    (built : roots? policy sign context p = .ok (.finite out)) :
    out.Pairwise (fun a b => a.value φ hz h1 ha hs hm hnat hsign < b.value φ hz h1 ha hs hm hnat hsign) := by
  obtain ⟨_, _, sorted⟩ := roots?_finite built
  simpa only [List.pairwise_map, Entry.value] using
    Isolation.Root.sortBy_sorted φ hz h1 ha hs hm hnat hsign hn hi hd Entry.root sorted

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The ordinary operation returns its actual successful complete producer. -/
theorem roots_success (context : Ctx) (p : DensePoly E) :
    ∃ output, roots? policy sign context p = .ok output ∧ roots policy sign context p = output := by
  obtain ⟨output, built⟩ := roots?_success φ hz h1 ha hs hm hnat hsign hn hi hd policy context p
  exact ⟨output, built, roots_of_success built⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- All policies return the same mathematical RootSet, including labels. -/
theorem roots?_agreement (other : Isolation.Policy) (context : Ctx) (p : DensePoly E)
    (first second : List (Entry sign context))
    (built : roots? policy sign context p = .ok (.finite first))
    (again : roots? other sign context p = .ok (.finite second)) (x : K) (label : Nat) :
    (∃ entry ∈ first, entry.value φ hz h1 ha hs hm hnat hsign = x ∧ entry.multiplicity = label) ↔
      (∃ entry ∈ second, entry.value φ hz h1 ha hs hm hnat hsign = x ∧ entry.multiplicity = label) :=
  (roots?_spec φ hz h1 ha hs hm hnat hsign hn hi hd policy context p first built x label).trans
    (roots?_spec φ hz h1 ha hs hm hnat hsign hn hi hd other context p second again x label).symm

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The ordinary API retains semantic zero's separate universal result. -/
theorem roots_all (context : Ctx) (p : DensePoly E) :
    roots policy sign context p = .all ↔ interpret φ hz p = 0 := by
  obtain ⟨output, built, returned⟩ := roots_success φ hz h1 ha hs hm hnat hsign hn hi hd policy context p
  constructor
  · intro all
    rw [all] at returned
    cases returned
    exact (assemble_all φ hz policy context p).mp ((roots?_all policy p).mp built)
  · intro zero
    exact roots_of_success ((roots?_all policy p).mpr ((assemble_all φ hz policy context p).mpr zero))

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Ordinary finite roots have the exact original multiplicities. -/
theorem roots_spec (context : Ctx) (p : DensePoly E) (out : List (Entry sign context))
    (returned : roots policy sign context p = .finite out) (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.value φ hz h1 ha hs hm hnat hsign = x ∧ entry.multiplicity = label) ↔
      (interpret φ hz p).IsRoot x ∧ label = (interpret φ hz p).rootMultiplicity x := by
  obtain ⟨output, built, computed⟩ := roots_success φ hz h1 ha hs hm hnat hsign hn hi hd policy context p
  rw [returned] at computed
  cases computed
  exact roots?_spec φ hz h1 ha hs hm hnat hsign hn hi hd policy context p out built x label

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Ordinary finite root values are strictly increasing. -/
theorem roots_sorted (context : Ctx) (p : DensePoly E) (out : List (Entry sign context))
    (returned : roots policy sign context p = .finite out) :
    out.Pairwise (fun a b => a.value φ hz h1 ha hs hm hnat hsign < b.value φ hz h1 ha hs hm hnat hsign) := by
  obtain ⟨output, built, computed⟩ := roots_success φ hz h1 ha hs hm hnat hsign hn hi hd policy context p
  rw [returned] at computed
  cases computed
  exact roots?_sorted φ hz h1 ha hs hm hnat hsign hn hi hd policy context p out built

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Strict ordering turns policy agreement into equality of the complete
interpreted lists of values with their original multiplicities. -/
theorem roots?_equal (other : Isolation.Policy) (context : Ctx) (p : DensePoly E)
    (first second : List (Entry sign context))
    (built : roots? policy sign context p = .ok (.finite first))
    (again : roots? other sign context p = .ok (.finite second)) :
    (first.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)) =
      (second.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)) := by
  let observation := fun e : Entry sign context =>
    (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)
  have orderedFirst : (first.map observation).Pairwise (fun a b => a.1 < b.1) := by
    simpa only [List.pairwise_map] using
      roots?_sorted φ hz h1 ha hs hm hnat hsign hn hi hd policy context p first built
  have orderedSecond : (second.map observation).Pairwise (fun a b => a.1 < b.1) := by
    simpa only [List.pairwise_map] using
      roots?_sorted φ hz h1 ha hs hm hnat hsign hn hi hd other context p second again
  have firstNodup := (orderedFirst.imp (S := fun a b => a ≠ b) (fun less same => by
    cases same
    exact lt_irrefl _ less)).nodup
  have secondNodup := (orderedSecond.imp (S := fun a b => a ≠ b) (fun less same => by
    cases same
    exact lt_irrefl _ less)).nodup
  have members (a : K × Nat) : a ∈ first.map observation ↔ a ∈ second.map observation := by
    rcases a with ⟨value, label⟩
    simpa only [List.mem_map, observation, Prod.mk.injEq] using
      roots?_agreement φ hz h1 ha hs hm hnat hsign hn hi hd policy other context p
        first second built again value label
  have same := (List.subperm_of_subset firstNodup (fun a h => (members a).mp h)).antisymm
    (List.subperm_of_subset secondNodup (fun a h => (members a).mpr h))
  exact List.Perm.eq_of_pairwise (fun a b _ _ less greater =>
    False.elim ((not_lt_of_ge (le_of_lt greater)) less)) orderedFirst orderedSecond same

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Ordinary roots preserve the complete ordered value and multiplicity list
across isolation choices. -/
theorem roots_equal (other : Isolation.Policy) (context : Ctx) (p : DensePoly E)
    (first second : List (Entry sign context))
    (built : roots policy sign context p = .finite first)
    (again : roots other sign context p = .finite second) :
    (first.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)) =
      (second.map fun e => (e.value φ hz h1 ha hs hm hnat hsign, e.multiplicity)) := by
  obtain ⟨output, checked, computed⟩ :=
    roots_success φ hz h1 ha hs hm hnat hsign hn hi hd policy context p
  rw [built] at computed
  cases computed
  obtain ⟨output, checkedOther, computed⟩ :=
    roots_success φ hz h1 ha hs hm hnat hsign hn hi hd other context p
  rw [again] at computed
  cases computed
  exact roots?_equal φ hz h1 ha hs hm hnat hsign hn hi hd policy other context p
    first second checked checkedOther

/-- info: 'Hex.RealClosure.Roots.Policy.roots?_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.roots?_equal

/-- info: 'Hex.RealClosure.Roots.Policy.roots?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.roots?_spec

/-- info: 'Hex.RealClosure.Roots.Policy.roots?_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.roots?_sorted

/-- info: 'Hex.RealClosure.Roots.Policy.roots?_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.roots?_agreement

/-- info: 'Hex.RealClosure.Roots.Policy.roots?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.roots?_success

/-- info: 'Hex.RealClosure.Roots.Policy.assemble_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.assemble_perm

/-- info: 'Hex.RealClosure.Roots.Policy.factorEntries_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.factorEntries_perm

/-- info: 'Hex.RealClosure.Roots.Policy.factorEntries_yun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Roots.Policy.factorEntries_yun

end Hex.RealClosure.Roots.Policy
