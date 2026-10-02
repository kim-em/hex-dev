/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski

public section

namespace Hex.SignedRemainderChain

private theorem getD_push_lt {A : Type u} (xs : Array A) (a d : A) (i : Nat) (hi : i < xs.size) :
    (xs.push a).getD i d = xs.getD i d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hi, Nat.ne_of_lt hi]

private theorem getD_push_last {A : Type u} (xs : Array A) (a d : A) :
    (xs.push a).getD xs.size d = a := by
  simp [Array.getD_eq_getD_getElem?]

variable {D : Type u} [Zero D] [DecidableEq D] [Add D] [Sub D] [Mul D] [NatCast D]

/-- The part of a literal replay already established before its terminal
zero identity. The array stores every actual quotient and positive scale. -/
structure Prefix (sign : D → Int) (p f : DensePoly D) (initial : RemainderStep D)
    (chain : Array (DensePoly D)) (steps : Array (RemainderStep D)) : Prop where
  two_le : 2 ≤ chain.size
  head : chain[0]? = some p
  nonzero : ∀ r ∈ chain, r ≠ 0
  descent : ∀ i, i + 1 < chain.size → (chain.getD (i + 1) 0).size < (chain.getD i 0).size
  left_pos : sign initial.leftScale = 1
  right_pos : sign initial.rightScale = 1
  initial_eq : subIsZero (DensePoly.scale initial.leftScale (f * p.derivative))
    (initial.quotient * p + DensePoly.scale initial.rightScale (chain.getD 1 0)) = true
  size_steps : steps.size + 2 = chain.size
  recurrences : ∀ i, i < steps.size → checkStep sign (chain.getD i 0) (chain.getD (i + 1) 0)
    (chain.getD (i + 2) 0) (steps.getD i ⟨0, 0, 0⟩) = true

/-- A correctly reduced initial pair starts a replay prefix. -/
theorem Prefix.pair (sign : D → Int) (p f second : DensePoly D) (initial : RemainderStep D)
    (hp : p ≠ 0) (hs : second ≠ 0) (hd : second.size < p.size)
    (hl : sign initial.leftScale = 1) (hr : sign initial.rightScale = 1)
    (hi : subIsZero (DensePoly.scale initial.leftScale (f * p.derivative))
      (initial.quotient * p + DensePoly.scale initial.rightScale second) = true) :
    Prefix sign p f initial #[p, second] #[] := by
  constructor
  · exact Nat.le_refl 2
  · rfl
  · intro r hmem
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact hp
    · exact hs
  · intro i hi
    have hi' : i = 0 := by change i + 1 < 2 at hi; omega
    subst i
    exact hd
  · exact hl
  · exact hr
  · exact hi
  · rfl
  · intro i hi
    exact False.elim (Nat.not_lt_zero i hi)

/-- Appending an actual signed-remainder step preserves all prior literal
identities and adds precisely the new final recurrence. -/
theorem Prefix.push {sign : D → Int} {p f : DensePoly D} {initial : RemainderStep D}
    {chain : Array (DensePoly D)} {steps : Array (RemainderStep D)}
    (h : Prefix sign p f initial chain steps) (next : DensePoly D) (step : RemainderStep D)
    (hn : next ≠ 0) (hd : next.size < (chain.getD (chain.size - 1) 0).size)
    (hs : checkStep sign (chain.getD (chain.size - 2) 0) (chain.getD (chain.size - 1) 0)
      next step = true) : Prefix sign p f initial (chain.push next) (steps.push step) := by
  have htwo := h.two_le
  constructor
  · simp only [Array.size_push]; omega
  · simpa only [Array.getElem?_push, show ¬ 0 = chain.size by omega, ↓reduceIte] using h.head
  · intro r hr
    rcases Array.mem_push.mp hr with hr | hr
    · exact h.nonzero r hr
    · subst r; exact hn
  · intro i hi
    simp only [Array.size_push] at hi
    by_cases hi' : i + 1 < chain.size
    · rw [getD_push_lt _ _ _ _ hi', getD_push_lt _ _ _ _ (by omega)]
      exact h.descent i hi'
    · have heq : i + 1 = chain.size := by omega
      have heq' : i = chain.size - 1 := by omega
      rw [heq, getD_push_last, getD_push_lt _ _ _ _ (by omega), heq']
      exact hd
  · exact h.left_pos
  · exact h.right_pos
  · rw [getD_push_lt _ _ _ _ (by omega)]
    exact h.initial_eq
  · simp only [Array.size_push]; have hh := h.size_steps; omega
  · intro i hi
    simp only [Array.size_push] at hi
    have hsize := h.size_steps
    by_cases hi' : i < steps.size
    · rw [getD_push_lt _ _ _ _ hi', getD_push_lt _ _ _ _ (by omega),
        getD_push_lt _ _ _ _ (by omega), getD_push_lt _ _ _ _ (by omega)]
      exact h.recurrences i hi'
    · have heq : i = steps.size := by omega
      have heq2 : i + 2 = chain.size := by omega
      rw [heq2, getD_push_last, getD_push_lt _ _ _ _ (by omega),
        getD_push_lt _ _ _ _ (by omega), heq, getD_push_last]
      have hprev : steps.size = chain.size - 2 := by omega
      have hcur : steps.size + 1 = chain.size - 1 := by omega
      rw [hcur, hprev]
      exact hs

/-- Finishing an established prefix with a positive terminal zero identity
passes the actual finite checker, with the computed degree evidence. -/
theorem Prefix.finish {sign : D → Int} {p f : DensePoly D} {initial : RemainderStep D}
    {chain : Array (DensePoly D)} {steps : Array (RemainderStep D)}
    (h : Prefix sign p f initial chain steps) (hp : p ≠ 0) (bound : chain.size ≤ p.size)
    (u : D) (q : DensePoly D) (hu : sign u = 1)
    (ht : subIsZero (DensePoly.scale u (chain.getD (chain.size - 2) 0))
      (q * chain.getD (chain.size - 1) 0) = true) :
    check sign p f ⟨chain, Hex.Array.map' DensePoly.natDegree chain,
      initial, steps, some (u, q)⟩ = true := by
  have hn := h.two_le
  have hp' : 0 < p.size := Nat.pos_of_ne_zero (fun hh => hp ((DensePoly.size_eq_zero_iff p).mp hh))
  simp only [check, show chain.size ≠ 1 by omega, ↓reduceIte, Bool.and_eq_true,
    Bool.not_eq_true', DensePoly.isZero_eq_false_iff, decide_eq_true_eq, and_assoc]
  refine ⟨hp', by omega, bound, h.head, True.intro, ?_, ?_, h.left_pos, h.right_pos,
    h.initial_eq, h.size_steps, ?_, hu, ht⟩
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro r hr
    change (!r.isZero) = true
    rw [Bool.not_eq_true', DensePoly.isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero (fun hh => h.nonzero r hr ((DensePoly.size_eq_zero_iff r).mp hh))
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    have hi' := Array.mem_range.mp hi
    exact decide_eq_true (h.descent i (by omega))
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    exact h.recurrences i (Array.mem_range.mp hi)

/-- A zero initial remainder has a singleton replay, with no fictitious
second entry or terminal pair. -/
theorem singleton_checks (sign : D → Int) (p f : DensePoly D) (initial : RemainderStep D)
    (hp : p ≠ 0) (hl : sign initial.leftScale = 1) (hr : sign initial.rightScale = 1)
    (hi : subIsZero (DensePoly.scale initial.leftScale (f * p.derivative))
      (initial.quotient * p + DensePoly.scale initial.rightScale 0) = true) :
    check sign p f ⟨#[p], #[p.natDegree], initial, #[], none⟩ = true := by
  have hp' : 0 < p.size := Nat.pos_of_ne_zero (fun hh => hp ((DensePoly.size_eq_zero_iff p).mp hh))
  simp only [check, ← Array.all_toList, Array.toList_range]
  change ((!p.isZero && decide (0 < 1) && decide (1 ≤ p.size) && decide (some p = some p) &&
    decide (#[p.natDegree] = #[p.natDegree]) && (!p.isZero && true) && true &&
    decide (sign initial.leftScale = 1) && decide (sign initial.rightScale = 1) &&
    subIsZero (DensePoly.scale initial.leftScale (f * p.derivative))
      (initial.quotient * p + DensePoly.scale initial.rightScale 0)) && true) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true', DensePoly.isZero_eq_false_iff,
    decide_eq_true_eq, hp', hl, hr, hi, true_and, and_true]
  omega

/-- The actual array loop preserves its established prefix and finishes with
accepted terminal evidence. The hypotheses are mathematical laws of the
backend, not arguments to the executable producer or arithmetic operations. -/
theorem buildAux_checks [One D] [Neg D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D)
    (hnext : ∀ r : DensePoly D, r ≠ 0 →
      -(normalize r).2 ≠ 0 ∧ (-(normalize r).2).size ≤ r.size)
    (hstep : ∀ a b : DensePoly D, b ≠ 0 →
      (DensePoly.positivePseudoDiv sign a b).remainder.isZero = false →
      checkStep sign a b (-(normalize (DensePoly.positivePseudoDiv sign a b).remainder).2)
        ⟨(DensePoly.positivePseudoDiv sign a b).multiplier,
          (DensePoly.positivePseudoDiv sign a b).quotient,
          (normalize (DensePoly.positivePseudoDiv sign a b).remainder).1⟩ = true)
    (hterminal : ∀ a b : DensePoly D, b ≠ 0 →
      (DensePoly.positivePseudoDiv sign a b).remainder.isZero = true →
      sign (DensePoly.positivePseudoDiv sign a b).multiplier = 1 ∧
      subIsZero (DensePoly.scale (DensePoly.positivePseudoDiv sign a b).multiplier a)
        ((DensePoly.positivePseudoDiv sign a b).quotient * b) = true)
    (p f : DensePoly D) (initial : RemainderStep D) (hp : p ≠ 0)
    (fuel : Nat) (prev cur : DensePoly D) (chain : Array (DensePoly D)) (steps : Array (RemainderStep D))
    (h : Prefix sign p f initial chain steps)
    (hprev : chain.getD (chain.size - 2) 0 = prev)
    (hcur : chain.getD (chain.size - 1) 0 = cur)
    (hc : cur ≠ 0) (hfuel : cur.size ≤ fuel)
    (hcapacity : chain.size + cur.size - 1 ≤ p.size) :
    let result := buildAux sign normalize fuel prev cur chain steps
    check sign p f ⟨result.1, Hex.Array.map' DensePoly.natDegree result.1,
      initial, result.2.1, result.2.2⟩ = true := by
  induction fuel generalizing prev cur chain steps with
  | zero => exact False.elim (hc ((DensePoly.size_eq_zero_iff cur).mp (by omega)))
  | succ fuel ih =>
    simp only [buildAux]
    split
    · rename_i hr
      have ht := hterminal prev cur hc hr
      refine h.finish hp ?_ _ _ ht.1 ?_
      · have hcpos := Nat.pos_of_ne_zero (fun hh => hc ((DensePoly.size_eq_zero_iff cur).mp hh))
        omega
      · simpa only [hprev, hcur] using ht.2
    · rename_i hr
      have hrfalse : (DensePoly.positivePseudoDiv sign prev cur).remainder.isZero = false :=
        Bool.of_not_eq_true hr
      have hrne : (DensePoly.positivePseudoDiv sign prev cur).remainder ≠ 0 := by
        intro hz
        rw [hz] at hr
        exact hr rfl
      have hn := hnext _ hrne
      have hd := DensePoly.positivePseudoDiv_remainder_lt sign prev cur hc
      have htwo := h.two_le
      have hpref := h.push (-(normalize (DensePoly.positivePseudoDiv sign prev cur).remainder).2)
        ⟨(DensePoly.positivePseudoDiv sign prev cur).multiplier,
          (DensePoly.positivePseudoDiv sign prev cur).quotient,
          (normalize (DensePoly.positivePseudoDiv sign prev cur).remainder).1⟩ hn.1
        (by rw [hcur]; omega) (by simpa only [hprev, hcur] using hstep prev cur hc hrfalse)
      refine ih cur _ _ _ hpref ?_ ?_ hn.1 ?_ ?_
      · simp only [Array.size_push]
        rw [getD_push_lt _ _ _ _ (by omega)]
        have hi : chain.size + 1 - 2 = chain.size - 1 := by omega
        simpa only [hi] using hcur
      · simp only [Array.size_push, Nat.add_sub_cancel, getD_push_last]
      · omega
      · simp only [Array.size_push]
        omega

end Hex.SignedRemainderChain

namespace Hex.Endpoint

/-- Finite endpoint evaluation signs and coefficient signs in `[-1,1]` also give bounded
infinity signs, including the negative-infinity degree-parity correction. -/
theorem signAt_bounds {D : Type u} {E : Type v} [Zero D] [DecidableEq D]
    (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (hsign : ∀ c, -1 ≤ sign c ∧ sign c ≤ 1)
    (heval : ∀ p x, -1 ≤ endpointSigns.evalSign p x ∧ endpointSigns.evalSign p x ≤ 1)
    (p : DensePoly D) (endpoint : Endpoint E) :
    -1 ≤ endpoint.signAt sign endpointSigns p ∧ endpoint.signAt sign endpointSigns p ≤ 1 := by
  cases endpoint with
  | finite x => exact heval p x
  | posInf => exact hsign p.leadingCoeff
  | negInf =>
    have h := hsign p.leadingCoeff
    simp only [signAt]
    split
    · simp only [Int.mul_neg_one]
      omega
    · simpa only [Int.mul_one] using h

end Hex.Endpoint

namespace Hex.TarskiCertificate

variable {D : Type u} {E : Type v} {Ctx : Type w}
variable [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]

omit [One D] [Add D] [Sub D] [Mul D] [NatCast D] in
/-- Endpoint operations with three-valued signs produce bounded sign arrays. -/
theorem signs_bounded (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (hvalues : ∀ p : DensePoly D, ∀ e : Endpoint E,
      -1 ≤ e.signAt sign endpointSigns p ∧ e.signAt sign endpointSigns p ≤ 1)
    (chain : Array (DensePoly D)) (endpoint : Endpoint E) :
    (signs sign endpointSigns chain endpoint).all (fun s => -1 ≤ s && s ≤ 1) = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro s hs
  simp only [signs, Hex.Array.map'_eq_map, Array.mem_map] at hs
  obtain ⟨p, _, rfl⟩ := hs
  change (decide (-1 ≤ endpoint.signAt sign endpointSigns p) &&
    decide (endpoint.signAt sign endpointSigns p ≤ 1)) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact hvalues p endpoint

/-- The shared producer's complete certificate passes replay whenever its
chain backend and endpoint sign operations satisfy their established laws. Literal
inputs, context, endpoints, signs and variations are checked without alteration. -/
theorem certify_checks [Neg D] [DecidableEq E] [DecidableEq Ctx]
    (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (normalize : DensePoly D → D × DensePoly D)
    (hchains : ∀ p g : DensePoly D, p ≠ 0 →
      SignedRemainderChain.check sign p g (SignedRemainderChain.build sign normalize p g) = true)
    (hvalues : ∀ p : DensePoly D, ∀ e : Endpoint E,
      -1 ≤ e.signAt sign endpointSigns p ∧ e.signAt sign endpointSigns p ≤ 1)
    (context : Ctx) (p g : DensePoly D) (a b : Endpoint E) (cert : TarskiCertificate D E Ctx)
    (hcert : certify sign endpointSigns normalize context p g a b = some cert) :
    check sign endpointSigns context p g a b cert.value cert = true := by
  simp only [certify] at hcert
  split at hcert
  · contradiction
  · rename_i hguard
    split at hcert
    · contradiction
    · rename_i hsquarefree
      have hg : checkEndpoints endpointSigns p a b = true := by
        apply Bool.of_not_eq_false
        intro hh
        apply hguard
        rw [hh]
        rfl
      have hsf : SignedRemainderChain.lastIsConstant (SignedRemainderChain.build sign normalize p 1) = true := by
        apply Bool.of_not_eq_false
        intro hh
        apply hsquarefree
        rw [hh]
        rfl
      have hp : p ≠ 0 := by
        have hg' := hg
        simp only [checkEndpoints, Bool.and_eq_true] at hg'
        have hpn := hg'.1.1.1
        rw [Bool.not_eq_true', DensePoly.isZero_eq_false_iff] at hpn
        intro hz
        have hs := (DensePoly.size_eq_zero_iff p).mpr hz
        omega
      cases Option.some.inj hcert
      simp only [check_eq, fromChains]
      simp only [decide_true, hg, hsf, hchains p _ hp,
        signs_bounded sign endpointSigns hvalues, Bool.and_true]

end Hex.TarskiCertificate
