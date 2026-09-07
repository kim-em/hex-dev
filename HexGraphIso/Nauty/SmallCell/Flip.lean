/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Count
public import HexGraphIso.Nauty.Spec.Descent
import all HexGraphIso.Nauty.Equitable.Basic
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
Disjoint transpositions preserve adjacency precisely when fixed vertices
see the members of every pair alike and adjacency between pairs agrees
under simultaneous exchange. Cell preservation is closed under composition
and converts a bounded involution into a cell-stabilizing renaming.
-/

namespace Hex.GraphIso.Nauty

/-- A fixed point is distinct from either member of a nontrivial swap. -/
theorem fixed_ne {α : Type} {f : α → α} {z u v : α}
    (hz : f z = z) (hu : f u = v) (hne : u ≠ v) : z ≠ u := by
  intro h
  subst z
  exact hne (hz.symm.trans hu)

/-- A map given by transpositions preserves adjacency exactly when fixed
vertices see each pair alike and the adjacency between pairs agrees under
simultaneous exchange. The cross conditions include a pair compared with
itself, expressing equal loops and symmetry on that pair. -/
theorem flip_iff {α : Type} {R : α → α → Bool} {f : α → α}
    {P : α → α → Prop}
    (hsymm : ∀ u v, R u v = R v u)
    (hswap : ∀ u v, P u v → f u = v ∧ f v = u)
    (hcover : ∀ z, f z = z ∨ ∃ u v, P u v ∧ (z = u ∨ z = v)) :
    (∀ z w, R (f z) (f w) = R z w) ↔
      (∀ z, f z = z → ∀ u v, P u v → R z u = R z v) ∧
      (∀ u v x y, P u v → P x y →
        R u x = R v y ∧ R u y = R v x) := by
  constructor
  · intro h
    constructor
    · intro z hz u v hp
      have h' := h z u
      rw [hz, (hswap u v hp).1] at h'
      exact h'.symm
    · intro u v x y hp hq
      obtain ⟨hu, hv⟩ := hswap u v hp
      obtain ⟨hx, hy⟩ := hswap x y hq
      exact ⟨by simpa only [hu, hx] using (h u x).symm,
        by simpa only [hu, hy] using (h u y).symm⟩
  · rintro ⟨hfix, hcross⟩ z w
    rcases hcover z with hz | ⟨u, v, hp, hz⟩
    · rcases hcover w with hw | ⟨x, y, hq, hw⟩
      · rw [hz, hw]
      · have hs := hswap x y hq
        have hf := hfix z hz x y hq
        rcases hw with hw | hw <;> rw [hw] <;> grind
    · have hs := hswap u v hp
      rcases hcover w with hw | ⟨x, y, hq, hw⟩
      · have hf := hfix w hw u v hp
        have hu := hsymm w u
        have hv := hsymm w v
        rcases hz with hz | hz <;> rw [hz] <;> grind
      · have ht := hswap x y hq
        have hc := hcross u v x y hp hq
        rcases hz with hz | hz <;> rcases hw with hw | hw <;>
          rw [hz, hw] <;> grind

/-- The transposition criterion on the bounded vertex indices of a graph. -/
theorem flip_bits {ctx : Ctx n} {f : Nat → Nat} {P : Nat → Nat → Prop}
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hbound : ∀ z, z < n → f z < n)
    (hswap : ∀ u v, P u v → f u = v ∧ f v = u)
    (hcover : ∀ z, z < n →
      f z = z ∨ ∃ u v, u < n ∧ v < n ∧ P u v ∧ (z = u ∨ z = v))
    (hfix : ∀ z, z < n → f z = z → ∀ u v, P u v →
      (ctx.g[z]!).mem u = (ctx.g[z]!).mem v)
    (hcross : ∀ u v x y, P u v → P x y →
      (ctx.g[u]!).mem x = (ctx.g[v]!).mem y ∧
      (ctx.g[u]!).mem y = (ctx.g[v]!).mem x) :
    ∀ z w, z < n → w < n →
      (ctx.g[f z]!).mem (f w) = (ctx.g[z]!).mem w := by
  let f' : Fin n → Fin n := fun z => ⟨f z, hbound z z.isLt⟩
  have hs : ∀ u v : Fin n, P u v → f' u = v ∧ f' v = u := by
    intro u v hp
    obtain ⟨hu, hv⟩ := hswap u v hp
    exact ⟨Fin.ext hu, Fin.ext hv⟩
  have hc : ∀ z : Fin n,
      f' z = z ∨ ∃ u v : Fin n, P u v ∧ (z = u ∨ z = v) := by
    intro z
    rcases hcover z z.isLt with hz | ⟨u, v, hu, hv, hp, hz⟩
    · exact Or.inl (Fin.ext hz)
    · refine Or.inr ⟨⟨u, hu⟩, ⟨v, hv⟩, hp, ?_⟩
      exact hz.elim (fun h => Or.inl (Fin.ext h))
        (fun h => Or.inr (Fin.ext h))
  have hb := (flip_iff (R := fun z w : Fin n => (ctx.g[z.val]!).mem w)
    (fun u v => hsymm u v u.isLt v.isLt) hs hc).mpr
      ⟨fun z hz u v hp => hfix z z.isLt (congrArg Fin.val hz) u v hp,
        fun u v x y hp hq => hcross u v x y hp hq⟩
  exact fun z w hz hw => hb ⟨z, hz⟩ ⟨w, hw⟩

variable {ctx : Ctx n}

/-- Image membership under a bounded involution reads off the preimage. -/
theorem mem_image_invol {f : Nat → Nat} {s : VSet n}
    (hfb : ∀ v, v < n → f v < n) (hinvol : ∀ v, v < n → f (f v) = v)
    {z : Nat} (hz : z < n) :
    (s.image f).mem z = s.mem (f z) := by
  rw [VSet.mem_image]
  rcases hb : s.mem (f z) with _ | _
  · refine List.any_eq_false.mpr fun u hu hcontra => ?_
    have hun := List.mem_range.mp hu
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hcontra
    obtain ⟨⟨hb1, hb2⟩, _⟩ := hcontra
    have huz : u = f z := by rw [← hb2, hinvol u hun]
    rw [huz, hb] at hb1
    exact Bool.false_ne_true hb1
  · refine List.any_eq_true.mpr ⟨f z, List.mem_range.mpr (hfb z hz), ?_⟩
    rw [hb, hinvol z hz]
    simp [hz]

/-- Rows from value-level bit invariance. -/
theorem rows_of_bits {f : Nat → Nat}
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hbits : ∀ z z', z < n → z' < n →
      (ctx.g[f z]!).mem (f z') = (ctx.g[z]!).mem z') :
    ∀ v, v < n → ctx.g[f v]! = (ctx.g[v]!).image f := by
  intro v hv
  refine VSet.ext fun z => ?_
  rcases Decidable.em (z < n) with hz | hz
  · rw [mem_image_invol hfb hinvol hz]
    have h := hbits v (f z) hv (hfb z hz)
    rw [hinvol z hz] at h
    exact h
  · rw [VSet.mem_of_ge (by omega), VSet.mem_of_ge (by omega)]

@[expose] def sw1 (u v z : Nat) : Nat :=
  if z = u then v else if z = v then u else z

theorem sw1_lt {n u v : Nat} (hun : u < n) (hvn : v < n) :
    ∀ z, z < n → sw1 u v z < n := by
  intro z hz
  rw [sw1]
  split
  · exact hvn
  · split
    · exact hun
    · exact hz

theorem sw1_u {u v : Nat} : sw1 u v u = v := by
  rw [sw1, ite_eq_left rfl]

theorem sw1_v {u v : Nat} (huv : u ≠ v) : sw1 u v v = u := by
  rw [sw1, ite_eq_right (fun h => huv h.symm), ite_eq_left rfl]

theorem sw1_fix {u v z : Nat} (hzu : z ≠ u) (hzv : z ≠ v) :
    sw1 u v z = z := by
  rw [sw1, ite_eq_right hzu, ite_eq_right hzv]

theorem sw1_invol {u v : Nat} (huv : u ≠ v) :
    ∀ z, sw1 u v (sw1 u v z) = z := by
  intro z
  rcases Decidable.em (z = u) with rfl | hzu
  · rw [sw1_u, sw1_v huv]
  rcases Decidable.em (z = v) with rfl | hzv
  · rw [sw1_v huv, sw1_u]
  · rw [sw1_fix hzu hzv, sw1_fix hzu hzv]

/-- Bit invariance of a single swap: every other vertex has equal bits
at the two swapped ones. -/
theorem sw1_bits {u v : Nat}
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hun : u < n) (hvn : v < n) (huv : u ≠ v)
    (hfix : ∀ z, z < n → z ≠ u → z ≠ v →
      (ctx.g[z]!).mem u = (ctx.g[z]!).mem v) :
    ∀ z z', z < n → z' < n →
      (ctx.g[sw1 u v z]!).mem (sw1 u v z') =
        (ctx.g[z]!).mem z' := by
  apply flip_bits (P := fun a b => a = u ∧ b = v) hsymm (sw1_lt hun hvn)
  · rintro _ _ ⟨rfl, rfl⟩
    exact ⟨sw1_u, sw1_v huv⟩
  · intro z hz
    by_cases hzu : z = u
    · exact Or.inr ⟨u, v, hun, hvn, ⟨rfl, rfl⟩, Or.inl hzu⟩
    by_cases hzv : z = v
    · exact Or.inr ⟨u, v, hun, hvn, ⟨rfl, rfl⟩, Or.inr hzv⟩
    exact Or.inl (sw1_fix hzu hzv)
  · rintro z hz hf _ _ ⟨rfl, rfl⟩
    exact hfix z hz (fixed_ne hf sw1_u huv)
      (fixed_ne hf (sw1_v huv) (Ne.symm huv))
  · rintro _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨by rw [hloop _ hun, hloop _ hvn], hsymm _ _ hun hvn⟩

@[expose] def sw2 (u v x y z : Nat) : Nat :=
  if z = u then v else if z = v then u
  else if z = x then y else if z = y then x else z

section Sw2

variable {u v x y : Nat}

/-- The distinctness bundle of an active double swap. -/
@[expose] def Sw2Ok (n u v x y : Nat) : Prop :=
  u < n ∧ v < n ∧ x < n ∧ y < n ∧ u ≠ v ∧ u ≠ x ∧ u ≠ y ∧
    v ≠ x ∧ v ≠ y ∧ x ≠ y

theorem sw2_u : sw2 u v x y u = v := by
  rw [sw2, ite_eq_left rfl]

theorem sw2_v {n : Nat} (h : Sw2Ok n u v x y) :
    sw2 u v x y v = u := by
  obtain ⟨-, -, -, -, huv, -⟩ := h
  rw [sw2, ite_eq_right (fun hc => huv hc.symm), ite_eq_left rfl]

theorem sw2_x {n : Nat} (h : Sw2Ok n u v x y) :
    sw2 u v x y x = y := by
  obtain ⟨-, -, -, -, -, hux, -, hvx, -⟩ := h
  rw [sw2, ite_eq_right (fun hc => hux hc.symm),
    ite_eq_right (fun hc => hvx hc.symm), ite_eq_left rfl]

theorem sw2_y {n : Nat} (h : Sw2Ok n u v x y) :
    sw2 u v x y y = x := by
  obtain ⟨-, -, -, -, -, -, huy, -, hvy, hxy⟩ := h
  rw [sw2, ite_eq_right (fun hc => huy hc.symm),
    ite_eq_right (fun hc => hvy hc.symm),
    ite_eq_right (fun hc => hxy hc.symm), ite_eq_left rfl]

theorem sw2_fix {z : Nat} (hzu : z ≠ u) (hzv : z ≠ v)
    (hzx : z ≠ x) (hzy : z ≠ y) : sw2 u v x y z = z := by
  rw [sw2, ite_eq_right hzu, ite_eq_right hzv, ite_eq_right hzx,
    ite_eq_right hzy]

theorem sw2_lt {n : Nat} (h : Sw2Ok n u v x y) :
    ∀ z, z < n → sw2 u v x y z < n := by
  obtain ⟨hun, hvn, hxn, hyn, -⟩ := h
  intro z hz
  rw [sw2]
  split
  · exact hvn
  split
  · exact hun
  split
  · exact hyn
  split
  · exact hxn
  · exact hz

theorem sw2_invol {n : Nat} (h : Sw2Ok n u v x y) :
    ∀ z, sw2 u v x y (sw2 u v x y z) = z := by
  intro z
  rcases Decidable.em (z = u) with rfl | hzu
  · rw [sw2_u, sw2_v h]
  rcases Decidable.em (z = v) with rfl | hzv
  · rw [sw2_v h, sw2_u]
  rcases Decidable.em (z = x) with rfl | hzx
  · rw [sw2_x h, sw2_y h]
  rcases Decidable.em (z = y) with rfl | hzy
  · rw [sw2_y h, sw2_x h]
  · rw [sw2_fix hzu hzv hzx hzy, sw2_fix hzu hzv hzx hzy]

/-- Bit invariance of a double swap: fixed vertices have equal bits at
both swapped pairs, and the cross bits between the pairs match
diagonally. -/
theorem sw2_bits
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (h : Sw2Ok n u v x y)
    (hfix : ∀ z, z < n → z ≠ u → z ≠ v → z ≠ x → z ≠ y →
      (ctx.g[z]!).mem u = (ctx.g[z]!).mem v ∧
      (ctx.g[z]!).mem x = (ctx.g[z]!).mem y)
    (hc1 : (ctx.g[u]!).mem x = (ctx.g[v]!).mem y)
    (hc2 : (ctx.g[u]!).mem y = (ctx.g[v]!).mem x) :
    ∀ z z', z < n → z' < n →
      (ctx.g[sw2 u v x y z]!).mem (sw2 u v x y z') =
        (ctx.g[z]!).mem z' := by
  apply flip_bits (P := fun a b => (a = u ∧ b = v) ∨ (a = x ∧ b = y))
    hsymm (sw2_lt h)
  · rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨sw2_u, sw2_v h⟩
    · exact ⟨sw2_x h, sw2_y h⟩
  · intro z hz
    obtain ⟨hun, hvn, hxn, hyn, -⟩ := h
    by_cases hzu : z = u
    · exact Or.inr ⟨u, v, hun, hvn, Or.inl ⟨rfl, rfl⟩, Or.inl hzu⟩
    by_cases hzv : z = v
    · exact Or.inr ⟨u, v, hun, hvn, Or.inl ⟨rfl, rfl⟩, Or.inr hzv⟩
    by_cases hzx : z = x
    · exact Or.inr ⟨x, y, hxn, hyn, Or.inr ⟨rfl, rfl⟩, Or.inl hzx⟩
    by_cases hzy : z = y
    · exact Or.inr ⟨x, y, hxn, hyn, Or.inr ⟨rfl, rfl⟩, Or.inr hzy⟩
    exact Or.inl (sw2_fix hzu hzv hzx hzy)
  · intro z hz hf a b hp
    have hOk := h
    obtain ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩ := h
    have he := hfix z hz (fixed_ne hf sw2_u huv)
      (fixed_ne hf (sw2_v hOk) (Ne.symm huv))
      (fixed_ne hf (sw2_x hOk) hxy) (fixed_ne hf (sw2_y hOk) (Ne.symm hxy))
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he.1
    · exact he.2
  · rintro a b c d (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      obtain ⟨hun, hvn, hxn, hyn, -⟩ := h
      grind

end Sw2

@[expose] def sw3 (u v x y a b z : Nat) : Nat :=
  if z = u then v else if z = v then u
  else if z = x then y else if z = y then x
  else if z = a then b else if z = b then a else z

section Sw3

variable {u v x y a b : Nat}

/-- The distinctness bundle of an active triple swap. -/
@[expose] def Sw3Ok (n u v x y a b : Nat) : Prop :=
  u < n ∧ v < n ∧ x < n ∧ y < n ∧ a < n ∧ b < n ∧
    u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ u ≠ a ∧ u ≠ b ∧
    v ≠ x ∧ v ≠ y ∧ v ≠ a ∧ v ≠ b ∧
    x ≠ y ∧ x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧ a ≠ b

theorem sw3_u : sw3 u v x y a b u = v := by
  rw [sw3, ite_eq_left rfl]

theorem sw3_v {n : Nat} (h : Sw3Ok n u v x y a b) :
    sw3 u v x y a b v = u := by
  obtain ⟨-, -, -, -, -, -, huv, -⟩ := h
  rw [sw3, ite_eq_right (fun hc => huv hc.symm), ite_eq_left rfl]

theorem sw3_x {n : Nat} (h : Sw3Ok n u v x y a b) :
    sw3 u v x y a b x = y := by
  obtain ⟨-, -, -, -, -, -, -, hux, -, -, -, hvx, -⟩ := h
  rw [sw3, ite_eq_right (fun hc => hux hc.symm),
    ite_eq_right (fun hc => hvx hc.symm), ite_eq_left rfl]

theorem sw3_y {n : Nat} (h : Sw3Ok n u v x y a b) :
    sw3 u v x y a b y = x := by
  obtain ⟨-, -, -, -, -, -, -, -, huy, -, -, -, hvy, -, -,
    hxy, -⟩ := h
  rw [sw3, ite_eq_right (fun hc => huy hc.symm),
    ite_eq_right (fun hc => hvy hc.symm),
    ite_eq_right (fun hc => hxy hc.symm), ite_eq_left rfl]

theorem sw3_a {n : Nat} (h : Sw3Ok n u v x y a b) :
    sw3 u v x y a b a = b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hua, -, -, -, hva, -, -,
    hxa, -, hya, -⟩ := h
  rw [sw3, ite_eq_right (fun hc => hua hc.symm),
    ite_eq_right (fun hc => hva hc.symm),
    ite_eq_right (fun hc => hxa hc.symm),
    ite_eq_right (fun hc => hya hc.symm), ite_eq_left rfl]

theorem sw3_b {n : Nat} (h : Sw3Ok n u v x y a b) :
    sw3 u v x y a b b = a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hub, -, -, -, hvb, -, -,
    hxb, -, hyb, hab⟩ := h
  rw [sw3, ite_eq_right (fun hc => hub hc.symm),
    ite_eq_right (fun hc => hvb hc.symm),
    ite_eq_right (fun hc => hxb hc.symm),
    ite_eq_right (fun hc => hyb hc.symm),
    ite_eq_right (fun hc => hab hc.symm), ite_eq_left rfl]

theorem sw3_fix {z : Nat} (hzu : z ≠ u) (hzv : z ≠ v)
    (hzx : z ≠ x) (hzy : z ≠ y) (hza : z ≠ a) (hzb : z ≠ b) :
    sw3 u v x y a b z = z := by
  rw [sw3, ite_eq_right (fun hc => hzu hc),
    ite_eq_right (fun hc => hzv hc), ite_eq_right (fun hc => hzx hc),
    ite_eq_right (fun hc => hzy hc), ite_eq_right (fun hc => hza hc),
    ite_eq_right (fun hc => hzb hc)]

theorem sw3_lt {n : Nat} (h : Sw3Ok n u v x y a b) :
    ∀ z, z < n → sw3 u v x y a b z < n := by
  have hun := h.1
  have hvn := h.2.1
  have hxn := h.2.2.1
  have hyn := h.2.2.2.1
  have han := h.2.2.2.2.1
  have hbn := h.2.2.2.2.2.1
  intro z hz
  rcases Decidable.em (z = u) with hzu | hzu
  · rw [hzu, sw3_u]; exact hvn
  rcases Decidable.em (z = v) with hzv | hzv
  · rw [hzv, sw3_v h]; exact hun
  rcases Decidable.em (z = x) with hzx | hzx
  · rw [hzx, sw3_x h]; exact hyn
  rcases Decidable.em (z = y) with hzy | hzy
  · rw [hzy, sw3_y h]; exact hxn
  rcases Decidable.em (z = a) with hza | hza
  · rw [hza, sw3_a h]; exact hbn
  rcases Decidable.em (z = b) with hzb | hzb
  · rw [hzb, sw3_b h]; exact han
  · rw [sw3_fix hzu hzv hzx hzy hza hzb]; exact hz

theorem sw3_invol {n : Nat} (h : Sw3Ok n u v x y a b) :
    ∀ z, sw3 u v x y a b (sw3 u v x y a b z) = z := by
  have hun := h.1
  have hvn := h.2.1
  obtain ⟨-, -, hxn, hyn, han, hbn, huv, hux, huy, hua, hub,
    hvx, hvy, hva, hvb, hxy, hxa, hxb, hya, hyb, hab⟩ := h
  have hOk : Sw3Ok n u v x y a b :=
    ⟨hun, hvn, hxn, hyn, han, hbn, huv, hux, huy, hua, hub,
      hvx, hvy, hva, hvb, hxy, hxa, hxb, hya, hyb, hab⟩
  intro z
  rcases Decidable.em (z = u) with hzu | hzu
  · rw [hzu, sw3_u, sw3_v hOk]
  rcases Decidable.em (z = v) with hzv | hzv
  · rw [hzv, sw3_v hOk, sw3_u]
  rcases Decidable.em (z = x) with hzx | hzx
  · rw [hzx, sw3_x hOk, sw3_y hOk]
  rcases Decidable.em (z = y) with hzy | hzy
  · rw [hzy, sw3_y hOk, sw3_x hOk]
  rcases Decidable.em (z = a) with hza | hza
  · rw [hza, sw3_a hOk, sw3_b hOk]
  rcases Decidable.em (z = b) with hzb | hzb
  · rw [hzb, sw3_b hOk, sw3_a hOk]
  · rw [sw3_fix hzu hzv hzx hzy hza hzb,
      sw3_fix hzu hzv hzx hzy hza hzb]

/-- A triple swap preserves every row when each swapped pair looks
alike from outside and the three pairs cross each other coherently. -/
theorem sw3_bits
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (h : Sw3Ok n u v x y a b)
    (hfix : ∀ z, z < n → z ≠ u → z ≠ v → z ≠ x → z ≠ y →
      z ≠ a → z ≠ b →
      (ctx.g[z]!).mem u = (ctx.g[z]!).mem v ∧
      (ctx.g[z]!).mem x = (ctx.g[z]!).mem y ∧
      (ctx.g[z]!).mem a = (ctx.g[z]!).mem b)
    (h1 : (ctx.g[u]!).mem x = (ctx.g[v]!).mem y)
    (h2 : (ctx.g[u]!).mem y = (ctx.g[v]!).mem x)
    (h3 : (ctx.g[u]!).mem a = (ctx.g[v]!).mem b)
    (h4 : (ctx.g[u]!).mem b = (ctx.g[v]!).mem a)
    (h5 : (ctx.g[x]!).mem a = (ctx.g[y]!).mem b)
    (h6 : (ctx.g[x]!).mem b = (ctx.g[y]!).mem a) :
    ∀ z z', z < n → z' < n →
      (ctx.g[sw3 u v x y a b z]!).mem (sw3 u v x y a b z') =
        (ctx.g[z]!).mem z' := by
  apply flip_bits (P := fun c d =>
    (c = u ∧ d = v) ∨ (c = x ∧ d = y) ∨ (c = a ∧ d = b)) hsymm (sw3_lt h)
  · rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨sw3_u, sw3_v h⟩
    · exact ⟨sw3_x h, sw3_y h⟩
    · exact ⟨sw3_a h, sw3_b h⟩
  · intro z hz
    obtain ⟨hun, hvn, hxn, hyn, han, hbn, -⟩ := h
    by_cases hzu : z = u
    · exact Or.inr ⟨u, v, hun, hvn, Or.inl ⟨rfl, rfl⟩, Or.inl hzu⟩
    by_cases hzv : z = v
    · exact Or.inr ⟨u, v, hun, hvn, Or.inl ⟨rfl, rfl⟩, Or.inr hzv⟩
    by_cases hzx : z = x
    · exact Or.inr ⟨x, y, hxn, hyn, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl hzx⟩
    by_cases hzy : z = y
    · exact Or.inr ⟨x, y, hxn, hyn, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr hzy⟩
    by_cases hza : z = a
    · exact Or.inr ⟨a, b, han, hbn, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl hza⟩
    by_cases hzb : z = b
    · exact Or.inr ⟨a, b, han, hbn, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr hzb⟩
    exact Or.inl (sw3_fix hzu hzv hzx hzy hza hzb)
  · intro z hz hf c d hp
    have hOk := h
    obtain ⟨hun, hvn, hxn, hyn, han, hbn, huv, hux, huy, hua, hub,
      hvx, hvy, hva, hvb, hxy, hxa, hxb, hya, hyb, hab⟩ := h
    have he := hfix z hz (fixed_ne hf sw3_u huv)
      (fixed_ne hf (sw3_v hOk) (Ne.symm huv))
      (fixed_ne hf (sw3_x hOk) hxy) (fixed_ne hf (sw3_y hOk) (Ne.symm hxy))
      (fixed_ne hf (sw3_a hOk) hab) (fixed_ne hf (sw3_b hOk) (Ne.symm hab))
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he.1
    · exact he.2.1
    · exact he.2.2
  · rintro c d e f (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      obtain ⟨hun, hvn, hxn, hyn, han, hbn, -⟩ := h
      grind

end Sw3

/-- Disjoint transpositions compose to the double swap. -/
theorem sw2_comp {n u v x y : Nat} (h : Sw2Ok n u v x y) (z : Nat) :
    sw2 u v x y z = sw1 u v (sw1 x y z) := by
  grind [Sw2Ok, sw1, sw2]

/-- A disjoint double swap and transposition compose to the triple swap. -/
theorem sw3_comp {n u v x y a b : Nat} (h : Sw3Ok n u v x y a b) (z : Nat) :
    sw3 u v x y a b z = sw2 u v x y (sw1 a b z) := by
  grind [Sw3Ok, sw1, sw2, sw3]

private theorem mapNodup {f : Nat → Nat}
    (hinj : ∀ a b, f a = f b → a = b) :
    ∀ (l : List Nat), l.Nodup → (l.map f).Nodup
  | [], _ => by simp
  | a :: t, h => by
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at h
    refine ⟨fun hmem => ?_, mapNodup hinj t h.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    rw [hinj b a hfb] at hb
    exact h.1 hb

/-- A duplicate-free list included in a list of no greater length is a
permutation of it. -/
theorem perm_of_nodup_subset :
    ∀ (l₁ l₂ : List Nat), l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) →
      l₂.length ≤ l₁.length → l₁.Perm l₂
  | [], l₂, _, _, hlen => by
    have h0 : l₂.length = 0 := by
      simp only [List.length_nil] at hlen
      omega
    rw [List.length_eq_zero_iff.mp h0]
  | a :: t, l₂, hnd, hsub, hlen => by
    have ha : a ∈ l₂ := hsub a List.mem_cons_self
    have hperm2 := List.perm_cons_erase ha
    rw [List.nodup_cons] at hnd
    have hsub' : ∀ x ∈ t, x ∈ l₂.erase a := by
      intro x hx
      have hxl : x ∈ l₂ := hsub x (List.mem_cons_of_mem _ hx)
      have hxa : x ≠ a := fun hcon => hnd.1 (hcon ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr hxl
    have hlen2 : l₂.length = (l₂.erase a).length + 1 :=
      hperm2.length_eq
    have hrec := perm_of_nodup_subset t (l₂.erase a) hnd.2 hsub'
      (by simp only [List.length_cons] at hlen; omega)
    exact (hrec.cons a).trans hperm2.symm

/-- Sums are invariant under permutation. -/
theorem sum_of_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [List.sum_cons, List.sum_cons, ih]
  | swap a b l =>
    rw [List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons]
    omega
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

private theorem countP_pos_extract {p : Nat → Bool} :
    ∀ (l : List Nat), 0 < l.countP p → ∃ w ∈ l, p w = true
  | a :: t, h => by
    rw [List.countP_cons] at h
    rcases Decidable.em (p a = true) with hpa | hpa
    · exact ⟨a, List.mem_cons_self, hpa⟩
    · rw [ite_eq_right hpa] at h
      obtain ⟨w, hw, hpw⟩ := countP_pos_extract t (by omega)
      exact ⟨w, List.mem_cons_of_mem _ hw, hpw⟩

/-- A permutation of `range k` from `k` distinct bounded values. -/
theorem range_perm_of_distinct {l : List Nat} {k : Nat}
    (hlen : l.length = k) (hnd : l.Nodup)
    (hbd : ∀ x ∈ l, x < k) : l.Perm (List.range k) :=
  perm_of_nodup_subset l (List.range k) hnd
    (fun x hx => List.mem_range.mpr (hbd x hx))
    (by rw [List.length_range, hlen]; exact Nat.le_refl _)

/-- A sum over `range k` rewritten through `k` distinct bounded
indices. -/
theorem sum_range_of_distinct {l : List Nat} {k : Nat}
    (F : Nat → Nat) (hlen : l.length = k) (hnd : l.Nodup)
    (hbd : ∀ x ∈ l, x < k) :
    ((List.range k).map F).sum = (l.map F).sum :=
  (sum_of_perm ((range_perm_of_distinct hlen hnd hbd).map F)).symm

private theorem segN_nodup {lab : Array Nat} {n lo : Nat}
    (hinj : LabInj lab n) :
    ∀ len, lo + len ≤ n → (segN lab lo len).Nodup := by
  intro len
  induction len generalizing lo with
  | zero => intro _; rw [segN_zero]; simp
  | succ len ih =>
    intro hbd
    rw [segN_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih (lo := lo + 1) (by omega)⟩
    obtain ⟨o, ho, heq⟩ := mem_segN_iff.mp hmem
    have := hinj (lo + 1 + o) lo (by omega) (by omega) heq
    omega

/-- A renaming permuting every cell's members within the cell is a
cell-contents self-equivalence of the labelling. -/
theorem cellsPerm_self_setwise {lab ptn : Array Nat} {level : Nat}
    {σ : Renaming n}
    (hps : ptn.size = n) (hlsz : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : LabInj lab n)
    (hset : ∀ p ∈ cells ptn level n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        σ.toFun lab[p.1 + o]! = lab[p.1 + o']!) :
    cellsPerm ptn level lab (lab.map σ.toFun) := by
  intro α len hIs
  rcases Decidable.em (α < n) with han | han
  · have hcross : α + len ≤ n := by
      have := isCell_no_cross hend hIs (by omega)
      omega
    have hlen0 : 0 < len := hIs.1
    have hmem : (α, α + len - 1) ∈ cells ptn level n :=
      mem_cells_of_isCell (by omega) hend hIs han (by omega)
    have hsegm : segN (lab.map σ.toFun) α len =
        (segN lab α len).map σ.toFun := segN_map (by omega)
    rw [hsegm]
    refine (perm_of_nodup_subset _ _
      (mapNodup σ.inj _ (segN_nodup hinj len hcross)) ?_ ?_).symm
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hz
      obtain ⟨o', ho', heq⟩ := hset _ hmem o (by omega)
      rw [heq]
      exact mem_segN_iff.mpr ⟨o', by omega, rfl⟩
    · rw [segN_length, List.length_map, segN_length]
      exact Nat.le_refl _
  · have hlen1 : len = 1 := isCell_oob hIs (by omega)
    rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero,
      getElem!_oob (by omega : lab.size ≤ α),
      getElem!_oob (by rw [Array.size_map]; omega :
        (lab.map σ.toFun).size ≤ α)]

/-- The setwise self-equivalence packaged as `StPerm`, for a raw
involution. -/
theorem stPerm_self_setwise {f : Nat → Nat} {st : RefineSt n}
    {level : Nat}
    (hok : StOk n level st) (hinj : LabInj st.lab n)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hset : ∀ p ∈ cells st.ptn level n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        f st.lab[p.1 + o]! = st.lab[p.1 + o']!) :
    StPerm level st (mapSt (renamingOfFlip f n hfb hinvol) st) := by
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hok.labOk i (by rw [hok.labSize]; omega)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (st.lab.map _).size = st.lab.size
    rw [Array.size_map]
  · show cellsPerm st.ptn level st.lab
      (st.lab.map (renamingOfFlip f n hfb hinvol).toFun)
    refine cellsPerm_self_setwise hok.ptnSize hok.labSize hok.ptnEnd
      hinj ?_
    intro p hp o ho
    obtain ⟨o', ho', heq⟩ := hset p hp o ho
    have hbd : p.2 < st.ptn.size :=
      cells_bound (by rw [hok.ptnSize]; exact Nat.le_refl _)
        hok.ptnEnd _ hp
    have hle := cells_le _ hp
    rw [hok.ptnSize] at hbd
    refine ⟨o', ho', ?_⟩
    rw [renamingOfFlip_at hfb hinvol (hlb (p.1 + o) (by omega))]
    exact heq

/-- A vertex map sends every cell into itself. -/
@[expose] def CellMap (st : RefineSt n) (level : Nat) (f : Nat → Nat) : Prop :=
  ∀ p ∈ cells st.ptn level n, ∀ o, o < p.2 + 1 - p.1 →
    ∃ o', o' < p.2 + 1 - p.1 ∧ f st.lab[p.1 + o]! = st.lab[p.1 + o']!

/-- Composing maps that preserve each cell preserves each cell. -/
theorem CellMap.comp {st : RefineSt n} {level : Nat} {f g : Nat → Nat}
    (hf : CellMap st level f) (hg : CellMap st level g) :
    CellMap st level (fun v => f (g v)) := by
  intro p hp o ho
  obtain ⟨a, ha, he⟩ := hg p hp o ho
  obtain ⟨b, hb, he'⟩ := hf p hp a ha
  exact ⟨b, hb, (congrArg f he).trans he'⟩

/-- Swapping two members of one cell preserves all cells. -/
theorem sw1_cells {st : RefineSt n} {level c e a b : Nat}
    (hok : StOk n level st) (hinj : LabInj st.lab n)
    (hc : (c, e) ∈ cells st.ptn level n)
    (ha : a ≤ e - c) (hb : b ≤ e - c) (hab : a ≠ b) :
    CellMap st level (sw1 st.lab[c + a]! st.lab[c + b]!) := by
  have hpsz := hok.ptnSize
  have hce := cells_le _ hc
  have he : e < n := by
    have := cells_bound (by omega) hok.ptnEnd _ hc
    rw [hok.ptnSize] at this
    exact this
  have huv : st.lab[c + a]! ≠ st.lab[c + b]! := by
    intro h
    have := hinj _ _ (by omega) (by omega) h
    omega
  intro p hp o ho
  have hpbd : p.2 < n := by
    have := cells_bound (by omega) hok.ptnEnd _ hp
    rw [hok.ptnSize] at this
    exact this
  have hple := cells_le _ hp
  have hsame : ∀ t, t ≤ e - c → st.lab[p.1 + o]! = st.lab[c + t]! → p = (c, e) := by
    intro t ht h
    have hpos := hinj _ _ (by omega) (by omega) h
    exact cells_eq_of_shared (by omega) hok.ptnEnd hp hc
      (j := p.1 + o) (by omega) (by omega) (by omega) (by omega)
  by_cases hua : st.lab[p.1 + o]! = st.lab[c + a]!
  · have hpc := hsame a ha hua
    subst p
    exact ⟨b, by omega, by rw [hua, sw1_u]⟩
  by_cases hub : st.lab[p.1 + o]! = st.lab[c + b]!
  · have hpc := hsame b hb hub
    subst p
    exact ⟨a, by omega, by rw [hub, sw1_v huv]⟩
  exact ⟨o, ho, sw1_fix hua hub⟩

/-- A disjoint double swap preserves cells when its two swaps do. -/
theorem sw2_cells {st : RefineSt n} {level u v x y : Nat}
    (h : Sw2Ok n u v x y)
    (h1 : CellMap st level (sw1 u v)) (h2 : CellMap st level (sw1 x y)) :
    CellMap st level (sw2 u v x y) := by
  simpa only [CellMap, sw2_comp h] using h1.comp h2

/-- A disjoint triple swap preserves cells when its three swaps do. -/
theorem sw3_cells {st : RefineSt n} {level u v x y a b : Nat}
    (h : Sw3Ok n u v x y a b)
    (h1 : CellMap st level (sw1 u v)) (h2 : CellMap st level (sw1 x y))
    (h3 : CellMap st level (sw1 a b)) : CellMap st level (sw3 u v x y a b) := by
  have h2ok : Sw2Ok n u v x y := by
    unfold Sw3Ok at h
    unfold Sw2Ok
    omega
  simpa only [CellMap, sw3_comp h] using (sw2_cells h2ok h1 h2).comp h3

section Flip

variable {lab ptn : Array Nat} {level : Nat} {S : Nat → Prop}
  {f : Nat → Nat}

/-- The members of a flipped pair have identical bits at every member
of an unflipped cell, given matching closure and odd unflipped
sizes. -/
private theorem flip_bit_aux
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hSclosed : ∀ p ∈ cells ptn level n,
      ∀ q ∈ cells ptn level n, S p.1 → q.2 = q.1 + 1 →
        PairMatch ctx.g lab[p.1]! lab[p.1 + 1]! lab[q.1]! lab[q.1 + 1]! →
        S q.1)
    (hOdd : ∀ q ∈ cells ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1)
    {c : Nat} (hP : (c, c + 1) ∈ cells ptn level n) (hSc : S c)
    {q : Nat × Nat} (hq : q ∈ cells ptn level n) (hnq : ¬ S q.1)
    {j : Nat} (hj1 : q.1 ≤ j) (hj2 : j ≤ q.2) :
    (ctx.g[lab[c]!]!).mem lab[j]! =
      (ctx.g[lab[c + 1]!]!).mem lab[j]! := by
  rcases Classical.em (q.2 = q.1 + 1) with hqp | hqnp
  · have hq' : (q.1, q.1 + 1) ∈ cells ptn level n := by
      rw [← hqp]
      exact hq
    have hnm : ¬ PairMatch ctx.g lab[c]! lab[c + 1]!
        lab[q.1]! lab[q.1 + 1]! :=
      fun hm => hnq (hSclosed _ hP _ hq hSc hqp hm)
    obtain ⟨h1, h2⟩ :=
      pair_eq_of_not_match hE hps hend hinj hlb hsymm hP hq' hnm
    rcases Decidable.em (j = q.1) with rfl | hne
    · exact h1
    · have : j = q.1 + 1 := by omega
      rw [this]
      exact h2
  · have hodd := hOdd _ hq hqnp
    have h := pair_odd_eq hE hps hend hinj hlb hsymm hP hq hodd
      (j - q.1) (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at h
    exact h

/-- The flip theorem: an involution swapping the vertices of a
matching-closed set of pair cells and fixing every other vertex
preserves the adjacency rows. -/
theorem flip_rows
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsurj : ∀ v, v < n → ∃ i, i < n ∧ lab[i]! = v)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (_hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hSpair : ∀ p ∈ cells ptn level n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level n, S p.1 →
      f lab[p.1]! = lab[p.1 + 1]! ∧ f lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f lab[p.1 + o]! = lab[p.1 + o]!)
    (hSclosed : ∀ p ∈ cells ptn level n,
      ∀ q ∈ cells ptn level n, S p.1 → q.2 = q.1 + 1 →
        PairMatch ctx.g lab[p.1]! lab[p.1 + 1]! lab[q.1]! lab[q.1 + 1]! →
        S q.1)
    (hOdd : ∀ q ∈ cells ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1) :
    ∀ v, v < n → ctx.g[f v]! = (ctx.g[v]!).image f := by
  let P : Nat → Nat → Prop := fun u v => ∃ c,
    (c, c + 1) ∈ cells ptn level n ∧ S c ∧ u = lab[c]! ∧ v = lab[c + 1]!
  have hbound : ∀ c, (c, c + 1) ∈ cells ptn level n → c + 1 < n := by
    intro c hc
    have := cells_bound (by omega) hend _ hc
    omega
  apply rows_of_bits hfb hinvol
  apply flip_bits (P := P) hsymm hfb
  · rintro u v ⟨c, hc, hSc, rfl, rfl⟩
    exact hSswap _ hc hSc
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := hsurj z hz
    obtain ⟨p, hp, hpi, hip⟩ := cells_cover (ptn := ptn) (level := level) i hi
    by_cases hs : S p.1
    · have hpe := hSpair p hp hs
      have hc : (p.1, p.1 + 1) ∈ cells ptn level n := by rw [← hpe]; exact hp
      have hcbd := hbound _ hc
      refine Or.inr ⟨lab[p.1]!, lab[p.1 + 1]!, hlb _ (by omega), hlb _ hcbd,
        ⟨p.1, hc, hs, rfl, rfl⟩, ?_⟩
      have hpos : i = p.1 ∨ i = p.1 + 1 := by omega
      exact hpos.elim (fun h => Or.inl (congrArg (fun j => lab[j]!) h))
        (fun h => Or.inr (congrArg (fun j => lab[j]!) h))
    · have h := hSfix p hp hs (i - p.1) (by omega)
      simpa only [Nat.add_sub_of_le hpi] using Or.inl h
  · rintro z hz hf u v ⟨c, hc, hSc, rfl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hsurj z hz
    obtain ⟨q, hq, hqj, hjq⟩ := cells_cover (ptn := ptn) (level := level) j hj
    have hnot : ¬ S q.1 := by
      intro hSq
      have hqe := hSpair q hq hSq
      have hqc : (q.1, q.1 + 1) ∈ cells ptn level n := by rw [← hqe]; exact hq
      have hqb := hbound _ hqc
      have hne : lab[q.1]! ≠ lab[q.1 + 1]! := by
        intro he
        have := hinj _ _ (by omega) hqb he
        omega
      have hs := hSswap _ hqc hSq
      have hpos : j = q.1 ∨ j = q.1 + 1 := by omega
      rcases hpos with hpos | hpos
      · rw [hpos, hs.1] at hf
        exact hne hf.symm
      · rw [hpos, hs.2] at hf
        exact hne hf
    have hcb := hbound _ hc
    rw [hsymm _ _ (hlb j hj) (hlb c (by omega)),
      hsymm _ _ (hlb j hj) (hlb (c + 1) hcb)]
    exact flip_bit_aux hE hps hend hinj hlb hsymm hSclosed hOdd hc hSc hq hnot hqj hjq
  · rintro u v x y ⟨c, hc, _, rfl, rfl⟩ ⟨d, hd, _, rfl, rfl⟩
    exact pair_swap_eq hE hps hend hinj hlb hsymm hc hd

end Flip

end Hex.GraphIso.Nauty
