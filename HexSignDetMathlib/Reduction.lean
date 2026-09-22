/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.MomentReplay
public import HexPolyMathlib.Interpret
public import Mathlib.Basic.Sign.Basic

public section

/-! Algebraic soundness of reduced moments under the shared noninjective
coefficient interpretation. These identities require no real-closed-field
foundation or Tarski root-sum theorem. -/
namespace Hex.SignDet

open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable [Add E] [Sub E] [Mul E]
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (sign : E → Int) (hsign : ∀ a, sign a = 1 ↔ 0 < f a)

include ha hs hm hsign in
/-- Every accepted reduction preserves the product sign at every root of the
head, including roots shared with either factor. The certificate need not
have come from the producer. -/
theorem ReductionStep.check_sign (p prev factor : DensePoly E) (index : Nat)
    (s : ReductionStep E) (h : s.check sign p prev factor index = true)
    (a : K) (hp : (interpret f hz p).eval a = 0) :
    SignType.sign ((interpret f hz s.next).eval a) =
      SignType.sign ((interpret f hz prev).eval a) *
        SignType.sign ((interpret f hz factor).eval a) := by
  obtain ⟨_, hl, hr, _, he⟩ := ReductionStep.check_eq h
  have heq := (sub_isZero f hz hs _ _).mp he
  simp only [interpret_scale f hz hm, interpret_mul f hz ha hm,
    interpret_add f hz ha] at heq
  have hv := congrArg (Polynomial.eval a) heq
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, hp,
    mul_zero, zero_add] at hv
  have hleft : SignType.sign (f s.witness.leftScale) = 1 :=
    sign_eq_one_iff.mpr ((hsign _).mp hl)
  have hright : SignType.sign (f s.witness.rightScale) = 1 :=
    sign_eq_one_iff.mpr ((hsign _).mp hr)
  have h := congrArg SignType.sign hv
  simpa only [sign_mul, hleft, hright, one_mul] using h.symm

include ha hs hm hsign in
/-- The complete accepted chain preserves signs of its ordered factors,
without expanding their polynomial product during replay. -/
theorem Reduction.checkFrom_sign (p prev : DensePoly E)
    (fs : List (Nat × DensePoly E)) (steps : List (ReductionStep E)) (result : DensePoly E)
    (h : Reduction.checkFrom sign p prev fs steps result = true)
    (a : K) (hp : (interpret f hz p).eval a = 0) :
    SignType.sign ((interpret f hz result).eval a) =
      SignType.sign ((interpret f hz prev).eval a) *
        (fs.map fun item => SignType.sign ((interpret f hz item.2).eval a)).prod := by
  induction fs generalizing prev steps with
  | nil =>
    cases steps with
    | nil =>
      have he := (sub_isZero f hz hs _ _).mp h
      simp [he]
    | cons s ss => simp [Reduction.checkFrom] at h
  | cons item fs ih =>
    obtain ⟨i, q⟩ := item
    cases steps with
    | nil => simp [Reduction.checkFrom] at h
    | cons s ss =>
      have hh : s.check sign p prev q i = true ∧
          Reduction.checkFrom sign p s.next fs ss result = true := by
        simpa only [Reduction.checkFrom, Bool.and_eq_true] using h
      obtain ⟨hstep, htail⟩ := hh
      rw [ih s.next ss htail,
        ReductionStep.check_sign f hz ha hs hm sign hsign p prev q i s hstep a hp]
      simp only [List.map_cons, List.prod_cons, mul_assoc]

variable [One E] (h1 : f (1 : E) = 1)

include ha hm h1 in
omit [LinearOrder K] [IsStrictOrderedRing K] [Sub E] in
private theorem interpret_power (p : DensePoly E) (n : Nat) :
    interpret f hz (p.natPow n) = (interpret f hz p) ^ n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    rw [DensePoly.natPow]
    split
    · rename_i hn
      rw [interpret_one f hz h1, hn, pow_zero]
    · rename_i hn
      have hlt : n / 2 < n := by omega
      split
      · rename_i he
        rw [ih (n / 2) hlt, interpret_mul f hz ha hm, ← pow_two, ← pow_mul]
        congr 1
        omega
      · rename_i he
        rw [interpret_mul f hz ha hm, ih (n / 2) hlt,
          interpret_mul f hz ha hm, ← pow_two, ← pow_mul, ← pow_succ]
        congr 1
        omega

include ha hm in
omit [Sub E] [One E] in
private theorem fold_sign (ps : List (DensePoly E)) (init : DensePoly E) (a : K) :
    SignType.sign ((interpret f hz (ps.foldl (· * ·) init)).eval a) =
      SignType.sign ((interpret f hz init).eval a) *
        (ps.map fun p => SignType.sign ((interpret f hz p).eval a)).prod := by
  induction ps generalizing init with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, ih, interpret_mul f hz ha hm, Polynomial.eval_mul,
      sign_mul, List.map_cons, List.prod_cons, mul_assoc]

include ha hm h1 in
omit [Sub E] in
private theorem moment_sign (qs : List (DensePoly E)) (es : List Nat) (a : K) :
    SignType.sign ((interpret f hz (moment qs es)).eval a) =
      ((factors qs es).map fun item => SignType.sign ((interpret f hz item.2).eval a)).prod := by
  have hf (ps : List (DensePoly E × Nat)) (start : Nat) :
      (((ps.zipIdx start).flatMap fun ((p, k), i) => List.replicate k (i, p)).map
        fun item => SignType.sign ((interpret f hz item.2).eval a)).prod =
      (ps.map fun (p, k) => SignType.sign ((interpret f hz p).eval a) ^ k).prod := by
    induction ps generalizing start with
    | nil => simp
    | cons pk ps ih =>
      obtain ⟨p, k⟩ := pk
      simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append, List.prod_append,
        List.map_replicate, List.prod_replicate, ih, List.map_cons, List.prod_cons]
  rw [moment, fold_sign f hz ha hm, interpret_one f hz h1]
  simp only [Polynomial.eval_one, sign_one, one_mul, List.map_map,
    Function.comp_def, interpret_power f hz ha hm h1, Polynomial.eval_pow, sign_pow]
  exact (hf (qs.zip es) 0).symm

include ha hm h1 in
omit [Sub E] in
/-- Replacing each indexed query by one with the same sign preserves every
moment sign, without requiring equality of polynomial values. -/
theorem moment_congr (qs rs : List (DensePoly E)) (es : List Nat) (a : K)
    (h : qs.map (fun q => SignType.sign ((interpret f hz q).eval a)) =
      rs.map (fun q => SignType.sign ((interpret f hz q).eval a))) :
    SignType.sign ((interpret f hz (moment qs es)).eval a) =
      SignType.sign ((interpret f hz (moment rs es)).eval a) := by
  have hh := congrArg (fun xs : List SignType =>
    ((xs.zip es).map fun (s, e) => s ^ e).prod) h
  simp only [List.zip_map_left, List.map_map, Function.comp_def, Prod.map_fst,
    Prod.map_snd, id_eq] at hh
  simpa only [moment, fold_sign f hz ha hm, interpret_one f hz h1,
    Polynomial.eval_one, sign_one, one_mul, List.map_map, Function.comp_def,
    interpret_power f hz ha hm h1, Polynomial.eval_pow, sign_pow] using hh

include ha hs hm hsign h1 in
/-- An arbitrary accepted reduced-moment certificate has the same sign as the
specified full moment at every root. Positive scaling changes values but not
signs; no numerical isolation or root-sum theorem is used. -/
theorem Reduction.check_sign (p : DensePoly E) (qs : List (DensePoly E)) (es : List Nat)
    (r : Reduction E) (h : r.check sign p qs es = true)
    (a : K) (hp : (interpret f hz p).eval a = 0) :
    SignType.sign ((interpret f hz r.result).eval a) =
      SignType.sign ((interpret f hz (moment qs es)).eval a) := by
  simp only [Reduction.check, Bool.and_eq_true] at h
  have hc := Reduction.checkFrom_sign f hz ha hs hm sign hsign p 1
    (factors qs es) r.steps r.result h.2 a hp
  rw [interpret_one f hz h1, Polynomial.eval_one, sign_one, one_mul] at hc
  rw [moment_sign f hz ha hm h1]
  exact hc

include ha hs hm hsign h1 in
/-- The operand of every accepted moment query has the requested moment's
sign at every root, whether supplied directly or through arbitrary reduction
evidence. Root-sum correspondence is a separate theorem. -/
theorem checkMoment_sign {Ctx : Type w} [DecidableEq Ctx] [NatCast E]
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E)
    (qs : List (DensePoly E)) (es : List Nat) (value : Int)
    (cert : TarskiCertificate E E Ctx) (reduction : Option (Reduction E))
    (h : checkMoment sign context p lo hi qs es value cert reduction = true)
    (a : K) (hp : (interpret f hz p).eval a = 0) :
    SignType.sign ((interpret f hz (queryPoly qs es reduction)).eval a) =
      SignType.sign ((interpret f hz (moment qs es)).eval a) := by
  cases reduction with
  | none => rfl
  | some r =>
    exact Reduction.check_sign f hz ha hs hm sign hsign h1 p qs es r
      (checkMoment_reduction h) a hp

end Hex.SignDet
