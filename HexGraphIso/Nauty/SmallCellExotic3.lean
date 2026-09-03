/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellExotic
import all HexGraphIso.Nauty.Equitable

public section

/-!
The four-cell-beside-a-pair configuration (SPEC § Verified search
refinement, the code-1 arm of the store-validity obligation).

Under a defect-four cheapautom pass the last shape is a four-cell
coexisting with a pair. The four-cell's members carry a constant count
into the pair; a uniform count (`0` or `2`) leaves the pair fixed, and
the matched count `1` splits the four-cell into the two pairs of
neighbours of the pair's members, so a flip across that split has to
carry the pair along. The triple swap `sw3` is the resulting map.

Every internal condition comes from one counting fact: in a cell of
four whose members have equal internal degrees, complementary pairs
are equally adjacent (`reg4_comp`). That makes the double swap of any
two complementary pairs bit-invariant with no case analysis on the
four-cell's internal structure, which is otherwise empty, a perfect
matching, a four-cycle or complete.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # Complementary pairs in a cell of four

A four-element cell of an equitable partition induces a regular graph
on its members. Writing the six internal adjacencies as `e₀₁ … e₂₃`,
the four degree equations force the three complementary pairings to
agree: `e₀₁ = e₂₃`, `e₀₂ = e₁₃`, `e₀₃ = e₁₂`. The proof is the
subtraction of degree sums, which `omega` performs directly. -/

/-- Equal internal degrees in a four-element cell make complementary
pairs equally adjacent. -/
private theorem reg4_comp {e01 e02 e03 e12 e13 e23 : Nat}
    (h01 : e01 + e02 + e03 = e01 + e12 + e13)
    (h02 : e01 + e02 + e03 = e02 + e12 + e23)
    (h03 : e01 + e02 + e03 = e03 + e13 + e23) :
    e01 = e23 ∧ e02 = e13 ∧ e03 = e12 := by
  omega

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
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (h : Sw3Ok ctx.n u v x y a b)
    (hfix : ∀ z, z < ctx.n → z ≠ u → z ≠ v → z ≠ x → z ≠ y →
      z ≠ a → z ≠ b →
      (ctx.g[z]!).testBit u = (ctx.g[z]!).testBit v ∧
      (ctx.g[z]!).testBit x = (ctx.g[z]!).testBit y ∧
      (ctx.g[z]!).testBit a = (ctx.g[z]!).testBit b)
    (h1 : (ctx.g[u]!).testBit x = (ctx.g[v]!).testBit y)
    (h2 : (ctx.g[u]!).testBit y = (ctx.g[v]!).testBit x)
    (h3 : (ctx.g[u]!).testBit a = (ctx.g[v]!).testBit b)
    (h4 : (ctx.g[u]!).testBit b = (ctx.g[v]!).testBit a)
    (h5 : (ctx.g[x]!).testBit a = (ctx.g[y]!).testBit b)
    (h6 : (ctx.g[x]!).testBit b = (ctx.g[y]!).testBit a) :
    ∀ z z', z < ctx.n → z' < ctx.n →
      (ctx.g[sw3 u v x y a b z]!).testBit (sw3 u v x y a b z') =
        (ctx.g[z]!).testBit z' := by
  have hun := h.1
  have hvn := h.2.1
  have hxn := h.2.2.1
  have hyn := h.2.2.2.1
  have han := h.2.2.2.2.1
  have hbn := h.2.2.2.2.2.1
  -- the six moved rows against an arbitrary second argument
  have key : ∀ z', z' < ctx.n →
      ((ctx.g[v]!).testBit (sw3 u v x y a b z') =
        (ctx.g[u]!).testBit z' ∧
       (ctx.g[u]!).testBit (sw3 u v x y a b z') =
        (ctx.g[v]!).testBit z') ∧
      ((ctx.g[y]!).testBit (sw3 u v x y a b z') =
        (ctx.g[x]!).testBit z' ∧
       (ctx.g[x]!).testBit (sw3 u v x y a b z') =
        (ctx.g[y]!).testBit z') ∧
      ((ctx.g[b]!).testBit (sw3 u v x y a b z') =
        (ctx.g[a]!).testBit z' ∧
       (ctx.g[a]!).testBit (sw3 u v x y a b z') =
        (ctx.g[b]!).testBit z') := by
    intro z' hz'
    rcases Decidable.em (z' = u) with hz'u | hz'u
    · rw [hz'u, sw3_u]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hloop _ hvn, hloop _ hun]
      · exact hsymm _ _ hun hvn
      · rw [hsymm _ _ hyn hvn, hsymm _ _ hxn hun]; exact h1.symm
      · rw [hsymm _ _ hxn hvn, hsymm _ _ hyn hun]; exact h2.symm
      · rw [hsymm _ _ hbn hvn, hsymm _ _ han hun]; exact h3.symm
      · rw [hsymm _ _ han hvn, hsymm _ _ hbn hun]; exact h4.symm
    rcases Decidable.em (z' = v) with hz'v | hz'v
    · rw [hz'v, sw3_v h]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact hsymm _ _ hvn hun
      · rw [hloop _ hun, hloop _ hvn]
      · rw [hsymm _ _ hyn hun, hsymm _ _ hxn hvn]; exact h2
      · rw [hsymm _ _ hxn hun, hsymm _ _ hyn hvn]; exact h1
      · rw [hsymm _ _ hbn hun, hsymm _ _ han hvn]; exact h4
      · rw [hsymm _ _ han hun, hsymm _ _ hbn hvn]; exact h3
    rcases Decidable.em (z' = x) with hz'x | hz'x
    · rw [hz'x, sw3_x h]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact h1.symm
      · exact h2
      · rw [hloop _ hyn, hloop _ hxn]
      · exact hsymm _ _ hxn hyn
      · rw [hsymm _ _ hbn hyn, hsymm _ _ han hxn]; exact h5.symm
      · rw [hsymm _ _ han hyn, hsymm _ _ hbn hxn]; exact h6.symm
    rcases Decidable.em (z' = y) with hz'y | hz'y
    · rw [hz'y, sw3_y h]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact h2.symm
      · exact h1
      · exact hsymm _ _ hyn hxn
      · rw [hloop _ hxn, hloop _ hyn]
      · rw [hsymm _ _ hbn hxn, hsymm _ _ han hyn]; exact h6
      · rw [hsymm _ _ han hxn, hsymm _ _ hbn hyn]; exact h5
    rcases Decidable.em (z' = a) with hz'a | hz'a
    · rw [hz'a, sw3_a h]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact h3.symm
      · exact h4
      · exact h5.symm
      · exact h6
      · rw [hloop _ hbn, hloop _ han]
      · exact hsymm _ _ han hbn
    rcases Decidable.em (z' = b) with hz'b | hz'b
    · rw [hz'b, sw3_b h]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact h4.symm
      · exact h3
      · exact h6.symm
      · exact h5
      · exact hsymm _ _ hbn han
      · rw [hloop _ han, hloop _ hbn]
    · rw [sw3_fix hz'u hz'v hz'x hz'y hz'a hz'b]
      obtain ⟨hf1, hf2, hf3⟩ := hfix z' hz' hz'u hz'v hz'x hz'y hz'a
        hz'b
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hsymm _ _ hvn hz', hsymm _ _ hun hz']; exact hf1.symm
      · rw [hsymm _ _ hun hz', hsymm _ _ hvn hz']; exact hf1
      · rw [hsymm _ _ hyn hz', hsymm _ _ hxn hz']; exact hf2.symm
      · rw [hsymm _ _ hxn hz', hsymm _ _ hyn hz']; exact hf2
      · rw [hsymm _ _ hbn hz', hsymm _ _ han hz']; exact hf3.symm
      · rw [hsymm _ _ han hz', hsymm _ _ hbn hz']; exact hf3
  intro z z' hz hz'
  rcases Decidable.em (z = u) with hzu | hzu
  · rw [hzu, sw3_u]; exact (key z' hz').1.1
  rcases Decidable.em (z = v) with hzv | hzv
  · rw [hzv, sw3_v h]; exact (key z' hz').1.2
  rcases Decidable.em (z = x) with hzx | hzx
  · rw [hzx, sw3_x h]; exact (key z' hz').2.1.1
  rcases Decidable.em (z = y) with hzy | hzy
  · rw [hzy, sw3_y h]; exact (key z' hz').2.1.2
  rcases Decidable.em (z = a) with hza | hza
  · rw [hza, sw3_a h]; exact (key z' hz').2.2.1
  rcases Decidable.em (z = b) with hzb | hzb
  · rw [hzb, sw3_b h]; exact (key z' hz').2.2.2
  · rw [sw3_fix hzu hzv hzx hzy hza hzb]
    obtain ⟨hf1, hf2, hf3⟩ := hfix z hz hzu hzv hzx hzy hza hzb
    rcases Decidable.em (z' = u) with hz'u | hz'u
    · rw [hz'u, sw3_u]; exact hf1.symm
    rcases Decidable.em (z' = v) with hz'v | hz'v
    · rw [hz'v, sw3_v h]; exact hf1
    rcases Decidable.em (z' = x) with hz'x | hz'x
    · rw [hz'x, sw3_x h]; exact hf2.symm
    rcases Decidable.em (z' = y) with hz'y | hz'y
    · rw [hz'y, sw3_y h]; exact hf2
    rcases Decidable.em (z' = a) with hz'a | hz'a
    · rw [hz'a, sw3_a h]; exact hf3.symm
    rcases Decidable.em (z' = b) with hz'b | hz'b
    · rw [hz'b, sw3_b h]; exact hf3
    · rw [sw3_fix hz'u hz'v hz'x hz'y hz'a hz'b]

end Sw3

end Hex.GraphIso.Nauty
