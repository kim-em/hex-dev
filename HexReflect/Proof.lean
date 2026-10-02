/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Provider
public import HexBasic.Fold

public section

/-!
Conversion commutes with interpretation.

The theorems here relate `Hex.MvPoly.eval₂` of a converted polynomial to the
Grind denotation of the reflected source. They are proved from the public
`Lean.Grind.CommRing` denotation theorems (`Expr.denote_toPoly` and
`Expr.denote_toPolyC`) together with the evaluation laws of `Hex.MvPoly`.
The valuation of the sealed atoms is read from the same `RArray` context that
denotes the reflected syntax, so no side condition relates the two.
-/

namespace Hex.Reflect

open Lean.Grind.CommRing

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

universe u

variable {α : Type u} {n : Nat}

/-- A translated monomial evaluates to the Grind monomial's denotation. -/
theorem prod_monoOfMon [Lean.Grind.CommSemiring α] (ctx : Lean.RArray α) (x : Fin n → α)
    (hx : ∀ i : Fin n, x i = ctx.get i.val) :
    ∀ (m : Mon) (mo : Mono n), monoOfMon? n m = some mo →
      Mono.prod x mo = m.denote ctx
  | .unit, mo, h => by
    simp only [monoOfMon?, Option.some.injEq] at h
    subst h
    simp [Mon.denote, Mono.prod_zero]
  | .mult pw m, mo, h => by
    unfold monoOfMon? at h
    split at h
    · rename_i hlt
      cases hrest : monoOfMon? n m with
      | none => simp [hrest] at h
      | some rest =>
        simp only [hrest, Option.map_some, Option.some.injEq] at h
        subst h
        rw [Mono.prod_mul, Mono.prod_scale_unit, prod_monoOfMon ctx x hx m rest hrest]
        simp [Mon.denote, Power.denote_eq, hx]
        rfl
    · cases h

/-- A translated term list sums to the Grind polynomial's denotation. -/
theorem foldl_polyTerms [Lean.Grind.CommRing α] (ctx : Lean.RArray α) (x : Fin n → α)
    (hx : ∀ i : Fin n, x i = ctx.get i.val) :
    ∀ (p : Poly) (ts : List (Mono n × Int)), polyTerms? n p = some ts →
      ts.foldl (fun acc t => acc + (t.2 : α) * Mono.prod x t.1) 0 = p.denote ctx
  | .num k, ts, h => by
    simp only [polyTerms?, Option.some.injEq] at h
    subst h
    by_cases hk : k = 0
    · subst hk
      simp [Poly.denote, Lean.Grind.Ring.intCast_zero]
    · simp [hk, Poly.denote, Mono.prod_zero, Lean.Grind.Semiring.mul_one,
        Lean.Grind.AddCommMonoid.zero_add]
  | .add k m p, ts, h => by
    simp only [polyTerms?, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨mo, hmo, rest, hrest, rfl⟩ := h
    rw [List.foldl_cons, List.foldl_add_eq_add_foldl, foldl_polyTerms ctx x hx p rest hrest]
    simp [Poly.denote, Lean.Grind.Ring.zsmul_eq_intCast_mul,
      prod_monoOfMon ctx x hx m mo hmo, Lean.Grind.AddCommMonoid.zero_add]

section Conversion

variable {C : Type} [Zero C] [Add C] [BEq C] [LawfulBEq C]
  {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {ofInt : Int → C} {interp : C → α}

/-- Evaluating the polynomial built from a translated term list through a
lawful coefficient interpretation gives the Grind polynomial's
denotation. -/
theorem eval₂_ofIntTerms [Lean.Grind.CommRing α] (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) (x : Fin n → α) (hx : ∀ i : Fin n, x i = ctx.get i.val)
    {p : Poly} {ts : List (Mono n × Int)} (h : polyTerms? n p = some ts) :
    MvPoly.eval₂ interp x (ofIntTerms (cmp := cmp) ofInt ts) = p.denote ctx := by
  letI : DecidableEq C := instDecidableEqOfLawfulBEq
  unfold ofIntTerms
  rw [MvPoly.eval₂_ofTerms interp x laws.interp_zero laws.interp_add, List.foldl_map,
    ← foldl_polyTerms ctx x hx p ts h]
  apply List.foldl_congr
  intro acc t _
  rw [laws.interp_ofInt]

/-- Conversion without characteristic evidence commutes with
interpretation. -/
theorem eval₂_convertTerms [Lean.Grind.CommRing α] (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) (x : Fin n → α) (hx : ∀ i : Fin n, x i = ctx.get i.val)
    {e : RingExpr} {ts : List (Mono n × Int)} (h : convertTerms? n none e = some ts) :
    MvPoly.eval₂ interp x (ofIntTerms (cmp := cmp) ofInt ts) = e.denote ctx := by
  rw [eval₂_ofIntTerms laws ctx x hx h]
  exact Expr.denote_toPoly ctx e

/-- Conversion modulo the characteristic commutes with interpretation. -/
theorem eval₂_convertTermsC [Lean.Grind.CommRing α] {c : Nat} [Lean.Grind.IsCharP α c]
    (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) (x : Fin n → α) (hx : ∀ i : Fin n, x i = ctx.get i.val)
    {e : RingExpr} {ts : List (Mono n × Int)} (h : convertTerms? n (some c) e = some ts) :
    MvPoly.eval₂ interp x (ofIntTerms (cmp := cmp) ofInt ts) = e.denote ctx := by
  rw [eval₂_ofIntTerms laws ctx x hx h]
  exact Expr.denote_toPolyC ctx e

/-- The `convert?` form of `eval₂_convertTerms`. -/
theorem eval₂_convert [Lean.Grind.CommRing α] (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) (x : Fin n → α) (hx : ∀ i : Fin n, x i = ctx.get i.val)
    {e : RingExpr} {q : MvPoly n C cmp} (h : convert? n none cmp ofInt e = some q) :
    MvPoly.eval₂ interp x q = e.denote ctx := by
  unfold convert? at h
  cases hts : convertTerms? n none e with
  | none => rw [hts] at h; cases h
  | some ts =>
    rw [hts, Option.map_some, Option.some.injEq] at h
    subst h
    exact eval₂_convertTerms laws ctx x hx hts

/-- The `convert?` form of `eval₂_convertTermsC`. -/
theorem eval₂_convertC [Lean.Grind.CommRing α] {c : Nat} [Lean.Grind.IsCharP α c]
    (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) (x : Fin n → α) (hx : ∀ i : Fin n, x i = ctx.get i.val)
    {e : RingExpr} {q : MvPoly n C cmp} (h : convert? n (some c) cmp ofInt e = some q) :
    MvPoly.eval₂ interp x q = e.denote ctx := by
  unfold convert? at h
  cases hts : convertTerms? n (some c) e with
  | none => rw [hts] at h; cases h
  | some ts =>
    rw [hts, Option.map_some, Option.some.injEq] at h
    subst h
    exact eval₂_convertTermsC laws ctx x hx hts

/-- The valuation read directly from the denotation context. -/
abbrev ctxValuation (ctx : Lean.RArray α) (n : Nat) : Fin n → α :=
  fun i => ctx.get i.val

/-- `eval₂_convertTerms` at the context valuation, the form used by proof
reconstruction. -/
theorem eval₂_convertTerms_ctx [Lean.Grind.CommRing α] (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) {e : RingExpr} {ts : List (Mono n × Int)}
    (h : convertTerms? n none e = some ts) :
    MvPoly.eval₂ interp (ctxValuation ctx n) (ofIntTerms (cmp := cmp) ofInt ts) =
      e.denote ctx :=
  eval₂_convertTerms laws ctx _ (fun _ => rfl) h

/-- `eval₂_convertTermsC` at the context valuation, the form used by proof
reconstruction. -/
theorem eval₂_convertTermsC_ctx [Lean.Grind.CommRing α] {c : Nat} [Lean.Grind.IsCharP α c]
    (laws : CoeffLaws ofInt interp)
    (ctx : Lean.RArray α) {e : RingExpr} {ts : List (Mono n × Int)}
    (h : convertTerms? n (some c) e = some ts) :
    MvPoly.eval₂ interp (ctxValuation ctx n) (ofIntTerms (cmp := cmp) ofInt ts) =
      e.denote ctx :=
  eval₂_convertTermsC laws ctx _ (fun _ => rfl) h

end Conversion

end Hex.Reflect
