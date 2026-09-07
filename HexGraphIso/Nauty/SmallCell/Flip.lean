/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable.Basic

public section

/-!
Adjacency preservation by disjoint transpositions. A pair relation specifies
the two members of each transposition. Fixed vertices must have equal
adjacency to those members, and adjacency between pairs must agree under
simultaneous exchange.
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



/-! # The single swap -/

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

/-! # The triple swap -/

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

end Hex.GraphIso.Nauty
