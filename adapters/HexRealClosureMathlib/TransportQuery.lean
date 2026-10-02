/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportArithmetic
public import HexRealRoots.Tarski

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [CommRing K] [DecidableEq K]

/-- Interpret exactly the supplied quotient and scales; no division runs. -/
@[expose] def step (read : E → K) (s : Hex.RemainderStep E) : Hex.RemainderStep K :=
  ⟨read s.leftScale, polynomial read s.quotient, read s.rightScale⟩

/-- Interpret the stored chain, retaining its degrees and terminal evidence. -/
@[expose] def chain (read : E → K) (cert : Hex.SignedRemainderChain E) :
    Hex.SignedRemainderChain K :=
  { chain := cert.chain.map (polynomial read)
    degrees := cert.degrees
    initial := step read cert.initial
    steps := cert.steps.map (step read)
    terminal := cert.terminal.map (fun pair => (read pair.1, polynomial read pair.2)) }

/-- Default-indexed chain reads commute with coefficient interpretation. -/
theorem chain_entry (read : E → K) (zero : read 0 = 0)
    (cert : Hex.SignedRemainderChain E) (i : Nat) :
    (chain read cert).chain.getD i 0 = polynomial read (cert.chain.getD i 0) := by
  change (cert.chain.map (polynomial read)).getD i 0 = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getD_eq_getD_getElem?]
  cases h : cert.chain[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact ((polynomial_zero read zero 0 (by simp)).mpr rfl).symm
  | some p => simp only [Option.map_some, Option.getD_some]

variable [Add E] [Sub E] [Mul E]

/-- One accepted signed recurrence transports from finite scalar work and the
signs of its two literal scales. No field laws on source expressions are used. -/
theorem step_check (read : E → K) (zero : read 0 = 0)
    (sourceSign : E → Int) (targetSign : K → Int)
    (a b c : Hex.DensePoly E) (s : Hex.RemainderStep E)
    (data : Recurrence read a b c s.leftScale s.quotient s.rightScale)
    (left : targetSign (read s.leftScale) = sourceSign s.leftScale)
    (right : targetSign (read s.rightScale) = sourceSign s.rightScale)
    (accepted : Hex.SignedRemainderChain.checkStep sourceSign a b c s = true) :
    Hex.SignedRemainderChain.checkStep targetSign
      (polynomial read a) (polynomial read b) (polynomial read c) (step read s) = true := by
  simp only [Hex.SignedRemainderChain.checkStep, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at accepted ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [step, left] using accepted.1
  · simpa only [step, right] using accepted.2.1
  · exact data.zero read zero a b c s.leftScale s.quotient s.rightScale accepted.2.2

omit [Add E] [Sub E] [Mul E] in
/-- Default-indexed step reads retain the exact supplied data. -/
theorem chain_step (read : E → K) (zero : read 0 = 0)
    (cert : Hex.SignedRemainderChain E) (i : Nat) :
    (chain read cert).steps.getD i ⟨0, 0, 0⟩ = step read (cert.steps.getD i ⟨0, 0, 0⟩) := by
  change (cert.steps.map (step read)).getD i ⟨0, 0, 0⟩ = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getD_eq_getD_getElem?]
  cases h : cert.steps[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, step, zero,
      (polynomial_zero read zero 0 (by simp)).mpr rfl]
  | some s => simp only [Option.map_some, Option.getD_some]

variable [NatCast E]

/-- Finite arithmetic, leading guards and scale signs for precisely the stored
initial identity, recurrence entries and terminal pair of one chain. -/
structure ChainData (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (p f : Hex.DensePoly E) (cert : Hex.SignedRemainderChain E) : Prop where
  head : Leading read p
  entries : ∀ r ∈ cert.chain, Leading read r
  initial : Initial read p f (cert.chain.getD 1 0)
    cert.initial.leftScale cert.initial.quotient cert.initial.rightScale
  initialLeft : targetSign (read cert.initial.leftScale) = sourceSign cert.initial.leftScale
  initialRight : targetSign (read cert.initial.rightScale) = sourceSign cert.initial.rightScale
  recurrences : ∀ i < cert.steps.size,
    Recurrence read (cert.chain.getD i 0) (cert.chain.getD (i + 1) 0)
      (cert.chain.getD (i + 2) 0) (cert.steps.getD i ⟨0, 0, 0⟩).leftScale
        (cert.steps.getD i ⟨0, 0, 0⟩).quotient (cert.steps.getD i ⟨0, 0, 0⟩).rightScale
  stepLeft : ∀ i < cert.steps.size,
    targetSign (read (cert.steps.getD i ⟨0, 0, 0⟩).leftScale) =
      sourceSign (cert.steps.getD i ⟨0, 0, 0⟩).leftScale
  stepRight : ∀ i < cert.steps.size,
    targetSign (read (cert.steps.getD i ⟨0, 0, 0⟩).rightScale) =
      sourceSign (cert.steps.getD i ⟨0, 0, 0⟩).rightScale
  terminal : ∀ scale q, cert.terminal = some (scale, q) →
    Terminal read (cert.chain.getD (cert.chain.size - 2) 0)
      (cert.chain.getD (cert.chain.size - 1) 0) scale q
  terminalSign : ∀ scale q, cert.terminal = some (scale, q) →
    targetSign (read scale) = sourceSign scale

/-- The complete accepted native signed-chain check transports from finite
scalar work, with its literal head, degree data, descent and terminal retained. -/
theorem chain_check (read : E → K) (zero : read 0 = 0)
    (sourceSign : E → Int) (targetSign : K → Int)
    (p f : Hex.DensePoly E) (cert : Hex.SignedRemainderChain E)
    (data : ChainData read sourceSign targetSign p f cert)
    (accepted : Hex.SignedRemainderChain.check sourceSign p f cert = true) :
    Hex.SignedRemainderChain.check targetSign
      (polynomial read p) (polynomial read f) (chain read cert) = true := by
  have entry_leading i : Leading read (cert.chain.getD i 0) := by
    rw [Array.getD_eq_getD_getElem?]
    cases h : cert.chain[i]? with
    | none => simp only [Option.getD_none]; intro h; simp at h
    | some r =>
      simp only [Option.getD_some]
      exact data.entries r (Array.mem_of_getElem? h)
  have source := accepted
  simp only [Hex.SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at source
  obtain ⟨hp, hn, hb, hh, hd, hnonzero, hdesc, hl, hr, hi, ht⟩ := source
  have psize := polynomial_size read zero p data.head
  have rowsize i := polynomial_size read zero (cert.chain.getD i 0) (entry_leading i)
  have chain_size : (chain read cert).chain.size = cert.chain.size := by simp [chain]
  have degree_map : (cert.chain.map (polynomial read)).map Hex.DensePoly.natDegree =
      cert.chain.map Hex.DensePoly.natDegree := by
    rw [Array.map_map]
    apply Array.ext (by simp)
    intro i hi hj
    simp only [Array.getElem_map]
    have bound : i < cert.chain.size := by simpa using hi
    exact polynomial_degree read zero cert.chain[i] (data.entries _ (by simp))
  simp only [Hex.SignedRemainderChain.check, chain_size, psize,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨?_, hn, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [polynomial_isZero read zero p data.head] using hp
  · simp only [chain, Array.getElem?_map, hh, Option.map_some]
  · simpa only [chain, Hex.Array.map'_eq_map, degree_map] using hd
  · rw [← chain_size]
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro r hr
    simp only [chain, Array.mem_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    simpa only [polynomial_isZero read zero q (data.entries q hq)] using
      Array.all_eq_true_iff_forall_mem.mp hnonzero q hq
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    simpa only [chain_entry read zero, rowsize, chain_size] using
      Array.all_eq_true_iff_forall_mem.mp hdesc i hi
  · simpa only [chain, step, data.initialLeft] using hl
  · simpa only [chain, step, data.initialRight] using hr
  · rw [chain_entry read zero]
    exact data.initial.zero read zero p f _ _ _ _ hi
  · by_cases single : cert.chain.size = 1
    · simp only [single, ↓reduceIte, Bool.and_eq_true] at ht ⊢
      constructor
      · simpa only [chain, Array.isEmpty, Array.size_map] using ht.1
      · simpa only [chain, Option.isNone_map] using ht.2
    · simp only [single, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at ht ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [chain, Array.size_map] using ht.1
      · apply Array.all_eq_true_iff_forall_mem.mpr
        intro i hi
        have idx : i < cert.steps.size := by
          simpa only [chain, Array.size_map] using Array.mem_range.mp hi
        rw [chain_entry read zero, chain_entry read zero, chain_entry read zero,
          chain_step read zero]
        exact step_check read zero sourceSign targetSign _ _ _ _
          (data.recurrences i idx) (data.stepLeft i idx) (data.stepRight i idx)
          (Array.all_eq_true_iff_forall_mem.mp ht.2.1 i (Array.mem_range.mpr idx))
      · cases terminal : cert.terminal with
        | none => simp only [terminal, Bool.false_eq_true] at ht; exact ht.2.2.elim
        | some pair =>
          obtain ⟨scale, q⟩ := pair
          rw [show (chain read cert).terminal = some (read scale, polynomial read q) by
            simp only [chain, terminal, Option.map_some]]
          change (decide (targetSign (read scale) = 1) &&
            Hex.SignedRemainderChain.subIsZero
              (Hex.DensePoly.scale (read scale)
                ((chain read cert).chain.getD (cert.chain.size - 2) 0))
              (polynomial read q * (chain read cert).chain.getD (cert.chain.size - 1) 0)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          simp only [terminal, Bool.and_eq_true, decide_eq_true_eq] at ht
          refine ⟨?_, ?_⟩
          · rw [data.terminalSign scale q terminal]
            exact ht.2.2.1
          · rw [chain_entry read zero, chain_entry read zero]
            exact (data.terminal scale q terminal).zero read zero _ _ scale q ht.2.2.2

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.chain_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.chain_entry

/-- info: 'Hex.RealClosure.Transport.step_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.step_check

/-- info: 'Hex.RealClosure.Transport.chain_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.chain_step

/-- info: 'Hex.RealClosure.Transport.chain_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.chain_check
