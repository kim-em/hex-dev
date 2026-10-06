/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Infinity
public import TauCeti.Algebra.Polynomial.Squarefree
public import HexRealRootsTheory.TarskiGcd
public import HexRealRootsTheory.TarskiSigns
public import HexRealRootsTheory.TarskiSum
public import HexRealRoots.Map
public import HexRealRootsTheory.SignVariations
import all HexRealRootsTheory.TarskiSum

@[expose] public section

namespace HexRealRootsTheory.Tarski

open Hex HexPolyTheory.Interpret Polynomial

variable {D : Type u} {K : Type v} [Zero D] [DecidableEq D]
variable [Add D] [Sub D] [Mul D] [NatCast D]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : D → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : D) = (n : K))
variable (sign : D → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)

/-- The polynomial list interpreted from the literal replay array. -/
noncomputable def chainPolys (c : SignedRemainderChain D) : List (Polynomial K) :=
  c.chain.toList.map (interpret f hz)

omit [Add D] [Sub D] [Mul D] [NatCast D] [LinearOrder K] [IsStrictOrderedRing K] in
theorem chainPolys_getD (c : SignedRemainderChain D) (i : Nat) :
    (chainPolys f hz c).getD i 0 = interpret f hz (c.chain.getD i 0) := by
  simp only [chainPolys, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  cases c.chain[i]? <;> simp [interpret_zero]

include ha hs hm hpos in
/-- Literal signed replay supplies all the abstract chain relations, including
termination at a possibly nonconstant gcd. -/
theorem check_signed (p g : DensePoly D) (c : SignedRemainderChain D)
    (hc : SignedRemainderChain.check sign p g c = true) :
    TauCeti.Sturm.IsSignedRemainderSeq (chainPolys f hz c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact check_nonzero f hz sign p g c hc r (by simpa using hr)
  · intro i p₀ p₁ p₂ h₀ h₁ h₂
    have hlen : (chainPolys f hz c).length = c.chain.size := by simp [chainPolys]
    have hidx : i + 2 < c.chain.size := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.mp h₂).1
    have hn : c.chain.size ≠ 1 := by omega
    have ht := (check_tail sign p g c hc hn).1
    obtain ⟨hl, hr, he⟩ := check_step f hz ha hs hm sign hpos p g c hc hn i (by omega)
    have get (j : Nat) (q : Polynomial K) (h : (chainPolys f hz c)[j]? = some q) :
        interpret f hz (c.chain.getD j 0) = q := by
      rw [← chainPolys_getD, List.getD_eq_getElem?_getD, h]
      rfl
    refine TauCeti.Sturm.IsRemainder.of_identity _ _
      (interpret f hz (c.steps.getD i ⟨0, 0, 0⟩).quotient) hl hr ?_
    simpa only [get _ _ h₀, get _ _ h₁, get _ _ h₂] using he
  · intro pre p₀ p₁ he
    have hlen : c.chain.size = pre.length + 2 := by
      simpa [chainPolys] using congrArg List.length he
    have hn : c.chain.size ≠ 1 := by omega
    obtain ⟨_, u, q, ht⟩ := check_tail sign p g c hc hn
    obtain ⟨hu, heq⟩ := check_terminal f hz ha hs hm sign hpos p g c hc hn u q ht
    have he₀ : interpret f hz (c.chain.getD (c.chain.size - 2) 0) = p₀ := by
      rw [← chainPolys_getD, he, hlen]
      simp
    have he₁ : interpret f hz (c.chain.getD (c.chain.size - 1) 0) = p₁ := by
      rw [← chainPolys_getD, he, hlen]
      simp [List.getD_eq_getElem?_getD]
    rw [he₀, he₁] at heq
    apply (Polynomial.dvd_C_mul hu.ne').mp
    rw [heq]
    exact dvd_mul_left _ _

include ha hs hm hnat hpos in
/-- The initial reduction gives precisely the seed congruence required by
Sturm–Tarski, without assuming a constant terminal polynomial. -/
theorem check_seed (p g : DensePoly D) (c : SignedRemainderChain D)
    (hc : SignedRemainderChain.check sign p g c = true) :
    TauCeti.Sturm.IsTarskiSeed (interpret f hz p) (interpret f hz g)
      ((chainPolys f hz c).getD 1 0) := by
  rw [chainPolys_getD]
  obtain ⟨hl, hr, he⟩ := check_initial f hz ha hs hm hnat sign hpos p g c hc
  exact TauCeti.Sturm.IsTarskiSeed.of_identity _ _ _ hl hr he

/-- Sign variations of an interpreted chain at a finite or infinite endpoint. -/
noncomputable def variations (cs : List (Polynomial K)) : Endpoint K → Nat
  | .negInf => TauCeti.Sturm.signVariationsAtBot cs
  | .finite a => TauCeti.Sturm.signVariationsAt cs a
  | .posInf => TauCeti.Sturm.signVariationsAtTop cs

variable {E : Type w} (point : E → K) (ends : EndpointSigns D E)
variable (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (heval : ∀ p a, ends.evalSign p a =
  (SignType.sign ((interpret f hz p).eval (point a)) : Int))

include hsign heval in
omit [Add D] [Sub D] [Mul D] [NatCast D] in
/-- Literal endpoint signs give the abstract variations, for independent
coefficient and endpoint representations. -/
theorem signs_variations (cs : Array (DensePoly D)) (a : Endpoint E) :
    signVar (TarskiCertificate.signs sign ends cs a).toList =
      variations (cs.toList.map (interpret f hz)) (a.map point) := by
  have hcast : ∀ s : SignType, SignType.sign (s : Int) = s := by decide
  rw [HexRealRootsTheory.signVar_eq_list]
  cases a with
  | finite a =>
    change _ = TauCeti.Sturm.signVariationsAt _ _
    rw [TauCeti.Sturm.signVariationsAt_def]
    apply List.signVariations_congr
    simp only [TarskiCertificate.signs, Hex.Array.map'_eq_map, Array.toList_map,
      List.map_map]
    apply List.map_congr_left
    intro p _
    simp [Endpoint.signAt, heval, hcast]
  | posInf =>
    change _ = TauCeti.Sturm.signVariationsAtTop _
    rw [TauCeti.Sturm.signVariationsAtTop_def]
    apply List.signVariations_congr
    simp only [TarskiCertificate.signs, Hex.Array.map'_eq_map, Array.toList_map,
      List.map_map]
    apply List.map_congr_left
    intro p _
    simp [Endpoint.signAt, leadingCoeff_interpret, hsign, hcast]
  | negInf =>
    change _ = TauCeti.Sturm.signVariationsAtBot _
    rw [TauCeti.Sturm.signVariationsAtBot_def]
    apply List.signVariations_congr
    simp only [TarskiCertificate.signs, Hex.Array.map'_eq_map, Array.toList_map,
      List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, Endpoint.signAt, leadingCoeff_interpret,
      natDegree_interpret, hsign, sign_mul, hcast]
    rw [neg_one_pow_eq_ite]
    simp only [Nat.even_iff]
    split_ifs <;> simp_all

variable [IsRealClosed K]

omit [DecidableEq K] in
/-- The shared signed-remainder theorem on an open interval with structural
infinite endpoints. Positive scalings and nonconstant terminal gcds are allowed. -/
theorem variation_eq (p g : Polynomial K) (cs : List (Polynomial K))
    (hc : TauCeti.Sturm.IsSignedRemainderSeq (p :: cs))
    (seed : TauCeti.Sturm.IsTarskiSeed p g (cs.head?.getD 0))
    (sf : Squarefree p) (a b : Endpoint K)
    (hab : match a, b with
      | .negInf, .finite _ | .negInf, .posInf | .finite _, .posInf => True
      | .finite x, .finite y => x < y
      | _, _ => False)
    (ha : ∀ x, a = .finite x → p.eval x ≠ 0)
    (hb : ∀ x, b = .finite x → p.eval x ≠ 0) :
    (variations (p :: cs) a : Int) - variations (p :: cs) b = rootSum p g a b := by
  classical
  have simple (r : K) (hr : p.eval r = 0) : p.derivative.eval r ≠ 0 :=
    sf.eval_derivative_ne_zero hr
  cases a <;> cases b <;> simp only at hab
  · simpa [variations, rootSum, rootsIn, Finset.sum_filter, InInterval] using
      TauCeti.Sturm.sum_sign_Iio hc seed (fun r _ => simple r) (hb _ rfl)
  · simpa [variations, rootSum, rootsIn, Finset.sum_filter, InInterval] using
      TauCeti.Sturm.sum_sign_univ hc seed simple
  · rw [rootSum_eq_sum]
    convert TauCeti.Sturm.sum_sign hc seed (fun r _ _ => simple r) hab
      (ha _ rfl) (hb _ rfl) using 1
    · rfl
    · apply Finset.sum_congr
      · ext r
        simp [mem_rootsIn]
      · intro r _
        rfl
  · simpa [variations, rootSum, rootsIn, Finset.sum_filter, InInterval] using
      TauCeti.Sturm.sum_sign_Ioi hc seed (fun r _ => simple r) (ha _ rfl)

end HexRealRootsTheory.Tarski
