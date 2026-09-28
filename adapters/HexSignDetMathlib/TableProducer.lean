/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootProducer

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include hz h1 ha hs hm hnat hn hi hsign in
/-- The actual prepared sparse-table producer succeeds for every query list
under lawful coefficients, including empty lists and root domains. -/
theorem buildTablePrepared_success (context : Ctx) (domain : Sturm.PreparedDomain E)
    (binding : domain.sign = sign) (qs : List (DensePoly E)) (reduced : Bool) :
    ∃ table, buildTablePrepared context domain qs reduced = .ok table := by
  obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
    context domain binding qs reduced
  exact ⟨t.val.table t.property,
    buildTablePrepared_ofReplay context domain qs reduced t ht⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- The total prepared operation returns a successful checked table,
excluding its empty-table diagnostic fallback. -/
theorem determinePrepared_success (context : Ctx) (domain : Sturm.PreparedDomain E)
    (binding : domain.sign = sign) (qs : List (DensePoly E)) (reduced : Bool) :
    ∃ table, buildTablePrepared context domain qs reduced = .ok table ∧
      determinePrepared context domain qs reduced = table := by
  obtain ⟨table, ht⟩ := buildTablePrepared_success f hz h1 ha hs hm hnat hn hi sign hsign
    context domain binding qs reduced
  exact ⟨table, ht, determinePrepared_ofBuild context domain qs reduced table ht⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- Every count returned by the actual total prepared operation equals the
number of roots realizing that ordered sign word, including omitted words. -/
theorem determinePrepared_correct (context : Ctx) (domain : Sturm.PreparedDomain E)
    (binding : domain.sign = sign) (qs : List (DensePoly E)) (reduced : Bool)
    (word : List Int) :
    (determinePrepared context domain qs reduced).count word =
      ((Tarski.rootsIn (interpret f hz domain.head)
        (domain.lower.map f) (domain.upper.map f)).filter
          (fun x => signsAt f hz qs x = word)).card := by
  obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
    context domain binding qs reduced
  have hb : buildTablePrepared context domain qs reduced = .ok (t.val.table t.property) := by
    exact buildTablePrepared_ofReplay context domain qs reduced t ht
  rw [determinePrepared_ofBuild context domain qs reduced _ hb, Replay.table_lookup]
  have hc : t.val.check sign context domain.head domain.lower domain.upper qs = true := by
    simpa only [binding] using t.property
  exact t.val.count_roots f hz h1 ha hs hm hnat sign hsign
    context domain.head domain.lower domain.upper qs hc word

omit [IsRealClosed K] in
include hz h1 ha hs hm hnat hn hi hsign in
/-- The public option-valued operation returns a table exactly for a valid
squarefree root domain; internal producer errors cannot become `none`. -/
theorem determine_isSome (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (reduced : Bool) :
    (determine sign context p a b qs reduced).isSome = true ↔
      HexSturmMathlib.Domain f hz p a b := by
  have he : (determine sign context p a b qs reduced).isSome =
      (Sturm.prepare sign p a b).isSome := by
    unfold determine
    cases Sturm.prepare sign p a b <;> rfl
  rw [he]
  have hsg := HexSturmMathlib.sign_spec f sign hsign
  exact HexSturmMathlib.prepare_isSome f hz ha hs hm sign
    (fun x => (hsg x).2.1) (fun x => (hsg x).2.2.1)
    h1 hn hi hnat (fun x => (hsg x).1) p a b

include hz h1 ha hs hm hnat hn hi hsign in
/-- A returned table has the exact mathematical root counts on the supplied
polynomial and interval. Queries retain their order, repetitions and zeros. -/
theorem determine_correct (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (reduced : Bool) (table : SignTable qs.length)
    (h : determine sign context p a b qs reduced = some table) :
    HexSturmMathlib.Domain f hz p a b ∧ ∀ word,
      table.count word = ((Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).filter
        (fun x => signsAt f hz qs x = word)).card := by
  have hv : (determine sign context p a b qs reduced).isSome = true := by rw [h]; rfl
  refine ⟨(determine_isSome f hz h1 ha hs hm hnat hn hi sign hsign
    context p a b qs reduced).mp hv, ?_⟩
  intro word
  cases hd : Sturm.prepare sign p a b with
  | none => simp only [determine, hd, reduceCtorEq] at h
  | some domain =>
    have he : determinePrepared context domain qs reduced = table := by
      simpa only [determine, hd, Option.some.injEq] using h
    have bindings := Sturm.prepare_eq_some sign p a b domain hd
    rw [← he]
    simpa only [bindings.2.1, bindings.2.2.1, bindings.2.2.2] using
      determinePrepared_correct f hz h1 ha hs hm hnat hn hi sign hsign
        context domain bindings.1 qs reduced word

end Hex.SignDet
