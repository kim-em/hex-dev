/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Domain
public import HexRealRoots.Map
public import HexRealRootsMathlib.TarskiSigns

public section
namespace HexSturmMathlib

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib Polynomial

variable {D : Type u} {E : Type v} {K : Type w}
variable [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : D → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (ha : ∀ a b, f (a + b) = f a + f b) (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b) (hn : ∀ n : Nat, f (n : D) = (n : K))
variable (j : E → K) (jz : ∀ a, j a = 0 ↔ a = 0)
variable (ja : ∀ a b, j (a + b) = j a + j b) (js : ∀ a b, j (a - b) = j a - j b)
variable (jm : ∀ a b, j (a * b) = j a * j b) (jn : ∀ n : Nat, j (n : E) = (n : K))
variable (sign : D → Int) (sign' : E → Int)
variable (hpos : ∀ a, sign a = 1 ↔ 0 < f a) (jpos : ∀ a, sign' a = 1 ↔ 0 < j a)
variable (hneg : ∀ a, sign a < 0 ↔ f a < 0) (jneg : ∀ a, sign' a < 0 ↔ j a < 0)
variable (hzero : ∀ a, sign a = 0 ↔ f a = 0) (jzero : ∀ a, sign' a = 0 ↔ j a = 0)
variable (hbound : ∀ a, -1 ≤ sign a ∧ sign a ≤ 1) (jbound : ∀ a, -1 ≤ sign' a ∧ sign' a ≤ 1)

omit [One D] [NatCast D] [One E] [NatCast E] in
include ha hm ja jm hneg jneg hzero jzero hbound jbound in
/-- Corresponding positively scaled chains have identical signs at any
corresponding finite or infinite endpoints of the field frontend. -/
theorem signs_eq (chain : Array (DensePoly D)) (chain' : Array (DensePoly E))
    (hsize : chain.size = chain'.size)
    (hscale : ∀ i, ∃ c : K, 0 < c ∧
      interpret j jz (chain'.getD i 0) = C c * interpret f hz (chain.getD i 0))
    (a : Endpoint D) (b : Endpoint E) (hab : a.map f = b.map j) :
    TarskiCertificate.signs sign (EndpointSigns.ofSign sign) chain a =
      TarskiCertificate.signs sign' (EndpointSigns.ofSign sign') chain' b := by
  have hinf := Tarski.infinite_signs_eq f hz j jz sign sign'
    (EndpointSigns.ofSign sign) (EndpointSigns.ofSign sign') hbound jbound hneg jneg hzero jzero
    chain chain' hsize hscale
  cases a <;> cases b <;> simp only [Endpoint.map, Endpoint.finite.injEq, reduceCtorEq] at hab
  case negInf.negInf => exact hinf.1
  case posInf.posInf => exact hinf.2
  case finite.finite a b =>
    apply Tarski.finite_signs_eq f hz j jz sign sign'
      (EndpointSigns.ofSign sign) (EndpointSigns.ofSign sign') a b (f a)
      (fun p => hbound (p.eval a)) (fun p => jbound (p.eval b))
      _ _ _ _ chain chain' hsize hscale
    · intro p
      change sign (p.eval a) < 0 ↔ _
      rw [hneg, eval_interpret f hz ha hm]
    · intro p
      change sign' (p.eval b) < 0 ↔ _
      rw [jneg, hab, eval_interpret j jz ja jm]
    · intro p
      change sign (p.eval a) = 0 ↔ _
      rw [hzero, eval_interpret f hz ha hm]
    · intro p
      change sign' (p.eval b) = 0 ↔ _
      rw [jzero, hab, eval_interpret j jz ja jm]

include ha hs hm hn ja js jm jn hpos jpos hneg jneg hzero jzero hbound jbound in
/-- Arbitrary accepted field certificates agree whenever their polynomial
inputs differ by positive factors and their interpreted endpoints agree.
The coefficient representations, contexts, and normalization choices may differ. -/
theorem check_congr {Ctx : Type u₁} {Ctx' : Type u₂} [DecidableEq Ctx] [DecidableEq Ctx']
    (context : Ctx) (context' : Ctx') (p g : DensePoly D) (p' g' : DensePoly E)
    (a b : Endpoint D) (a' b' : Endpoint E) (v v' : Int)
    (cert : TarskiCertificate D D Ctx) (cert' : TarskiCertificate E E Ctx')
    (h : Sturm.check sign context p g a b v cert = true)
    (h' : Sturm.check sign' context' p' g' a' b' v' cert' = true)
    (cp cg : K) (hcp : 0 < cp) (hcg : 0 < cg)
    (hp : interpret j jz p' = C cp * interpret f hz p)
    (hg : interpret j jz g' = C cg * interpret f hz g)
    (hal : a.map f = a'.map j) (hbu : b.map f = b'.map j) : v = v' := by
  obtain ⟨hc, hv⟩ := Tarski.check_value sign (EndpointSigns.ofSign sign) context p g a b v cert h
  obtain ⟨hc', hv'⟩ := Tarski.check_value sign' (EndpointSigns.ofSign sign') context' p' g' a' b' v' cert' h'
  have hcompare := Tarski.check_compare f hz ha hs hm hn sign hpos j jz ja js jm jn sign' jpos
    p g cert.remainders hc p' g' cert'.remainders hc' cp cg hcp hcg hp hg
  rw [hv, hv', signs_eq f hz ha hm j jz ja jm sign sign' hneg jneg hzero jzero hbound jbound
    _ _ hcompare.1 hcompare.2 a a' hal,
    signs_eq f hz ha hm j jz ja jm sign sign' hneg jneg hzero jzero hbound jbound
    _ _ hcompare.1 hcompare.2 b b' hbu]

omit [One D] [Add D] [Sub D] [Mul D] [NatCast D]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] in
/-- The domain depends only on the interpreted endpoints and the head up to
a nonzero constant factor. -/
theorem domain_congr (p : DensePoly D) (p' : DensePoly E)
    (a b : Endpoint D) (a' b' : Endpoint E) (c : K) (hc : c ≠ 0)
    (hp : interpret j jz p' = C c * interpret f hz p)
    (hal : a.map f = a'.map j) (hbu : b.map f = b'.map j) :
    Domain f hz p a b ↔ Domain j jz p' a' b' := by
  have hlt : EndpointLt f a b ↔ EndpointLt j a' b' := by
    have hleft : EndpointLt f a b ↔ EndpointLt id (a.map f) (b.map f) := by
      cases a <;> cases b <;> rfl
    have hright : EndpointLt j a' b' ↔ EndpointLt id (a'.map j) (b'.map j) := by
      cases a' <;> cases b' <;> rfl
    rw [hleft, hright, hal, hbu]
  have heval (x : Endpoint D) (y : Endpoint E) (he : x.map f = y.map j) :
      Nonvanishing f (interpret f hz p) x ↔ Nonvanishing j (interpret j jz p') y := by
    cases x <;> cases y <;> simp only [Endpoint.map, Endpoint.finite.injEq, reduceCtorEq] at he
    case negInf.negInf => rfl
    case posInf.posInf => rfl
    case finite.finite x y =>
      rw [Nonvanishing, Nonvanishing, hp, Polynomial.eval_mul, Polynomial.eval_C, mul_ne_zero_iff, he]
      exact (and_iff_right hc).symm
  have hsf := (associated_unit_mul_left (interpret f hz p) (C c)
    ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C)).squarefree_iff
  have hhead : interpret j jz p' ≠ 0 ↔ interpret f hz p ≠ 0 := by
    rw [hp, mul_ne_zero_iff]
    exact and_iff_right (C_ne_zero.mpr hc)
  simp only [Domain]
  rw [hhead, ← heval a a' hal, ← heval b b' hbu, ← hlt, hp, hsf]

variable [Neg D] [Inv D] [Neg E] [Inv E]
variable (h1 : f 1 = 1) (hnegate : ∀ a, f (-a) = -f a) (hinv : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (j1 : j 1 = 1) (jnegate : ∀ a, j (-a) = -j a) (jinv : ∀ a, j a⁻¹ = (j a)⁻¹)

include ha hs hm hn ja js jm jn hpos jpos hneg jneg hzero jzero hbound jbound
  h1 hnegate hinv j1 jnegate jinv in
/-- The whole query result is independent of the coefficient representation
and positive input scaling, at corresponding finite or infinite endpoints.
Both rejected domains and successful values are included. -/
theorem query_congr (p g : DensePoly D) (p' g' : DensePoly E)
    (a b : Endpoint D) (a' b' : Endpoint E) (cp cg : K) (hcp : 0 < cp) (hcg : 0 < cg)
    (hp : interpret j jz p' = C cp * interpret f hz p)
    (hg : interpret j jz g' = C cg * interpret f hz g)
    (hal : a.map f = a'.map j) (hbu : b.map f = b'.map j) :
    Sturm.query sign p g a b = Sturm.query sign' p' g' a' b' := by
  have hd : (Sturm.query sign p g a b).isSome = (Sturm.query sign' p' g' a' b').isSome := by
    apply Bool.eq_iff_iff.mpr
    rw [query_isSome f hz ha hs hm sign hneg hzero h1 hnegate hinv hn hpos,
      query_isSome j jz ja js jm sign' jneg jzero j1 jnegate jinv jn jpos]
    exact domain_congr f hz j jz p p' a b a' b' cp (ne_of_gt hcp) hp hal hbu
  have hv := Sturm.certify_value sign () p g a b
  have hv' := Sturm.certify_value sign' () p' g' a' b'
  rw [← hv, ← hv'] at hd ⊢
  cases hc : Sturm.certify sign () p g a b with
  | none =>
    cases hc' : Sturm.certify sign' () p' g' a' b' with
    | none => rfl
    | some cert' => simp only [hc, hc', Option.map_none, Option.map_some,
        Option.isSome_none, Option.isSome_some, Bool.false_eq_true] at hd
  | some cert =>
    cases hc' : Sturm.certify sign' () p' g' a' b' with
    | none => simp only [hc, hc', Option.map_none, Option.map_some,
        Option.isSome_none, Option.isSome_some, Bool.true_eq_false] at hd
    | some cert' =>
      simp only [Option.map_some, Option.some.injEq]
      apply check_congr f hz ha hs hm hn j jz ja js jm jn sign sign' hpos jpos hneg jneg
        hzero jzero hbound jbound () () p g p' g' a b a' b' cert.value cert'.value cert cert'
        _ _ cp cg hcp hcg hp hg hal hbu
      · exact certify_checks f hz ha hs hm sign hneg h1 hnegate hinv hpos hbound () p g a b cert hc
      · exact certify_checks j jz ja js jm sign' jneg j1 jnegate jinv jpos jbound () p' g' a' b' cert' hc'

end HexSturmMathlib
