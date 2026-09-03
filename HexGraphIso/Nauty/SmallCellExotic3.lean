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

/-! # The four-cell's internal structure

Equitability makes the four members of a four-cell equal in internal
degree, and `reg4_comp` turns that into the three complementary-pair
equalities. The four-cell's induced graph is empty, a perfect
matching, a four-cycle or complete, and this one statement covers all
four without naming them. -/

section FourCell

variable {st : RefineSt} {level tc d2 oU oV w1 w2 : Nat}

/-- Complementary pairs of a four-cell are equally adjacent. -/
theorem fourCell_comp
    (hIt : IterOk ctx level st)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level ctx.n)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hnd : ([oU, oV, w1, w2] : List Nat).Nodup) :
    (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[tc + w1]! =
      (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[tc + w2]! ∧
    (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[tc + w2]! =
      (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[tc + w1]! ∧
    (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[tc + oV]! =
      (ctx.g[st.lab[tc + w1]!]!).testBit st.lab[tc + w2]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hbd : ∀ x ∈ ([oU, oV, w1, w2] : List Nat), x < 4 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have : x = w2 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  have hm : tc + 3 + 1 - tc = 4 := by omega
  -- each member's count into the cell, reindexed by the four names
  have hdeg : ∀ o, o ≤ 3 →
      popCount (worksetOf st.lab tc (tc + 3) &&&
          ctx.g[st.lab[tc + o]!]!) =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oU]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oV]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w1]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w2]! := by
    intro o ho
    have h := count_into_cell hpsz hend hinj hlb hC
      (hg _ (hlb (tc + o) (by omega)))
    rw [hm] at h
    rw [h, sum_range_of_distinct _ (by simp) hnd hbd]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  -- the diagonal terms vanish and the off-diagonal ones are symmetric
  have hz : ∀ o, o ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + o]! = 0 := by
    intro o ho
    exact bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsy : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + o']! =
        bitCnt ctx.g[st.lab[tc + o']!]! st.lab[tc + o]! := by
    intro o o' ho ho'
    exact bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  -- the four degrees agree
  have hUV := hE _ hC _ hC oU oV (by omega) (by omega)
  have hUw1 := hE _ hC _ hC oU w1 (by omega) (by omega)
  have hUw2 := hE _ hC _ hC oU w2 (by omega) (by omega)
  rw [hdeg oU hoU, hdeg oV hoV] at hUV
  rw [hdeg oU hoU, hdeg w1 hw1] at hUw1
  rw [hdeg oU hoU, hdeg w2 hw2] at hUw2
  have e1 := hz oU hoU
  have e2 := hz oV hoV
  have e3 := hz w1 hw1
  have e4 := hz w2 hw2
  have s1 := hsy oV oU hoV hoU
  have s2 := hsy w1 oU hw1 hoU
  have s3 := hsy w1 oV hw1 hoV
  have s4 := hsy w2 oU hw2 hoU
  have s5 := hsy w2 oV hw2 hoV
  have s6 := hsy w2 w1 hw2 hw1
  obtain ⟨c1, c2, c3⟩ :=
    reg4_comp (e01 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + oV]!)
      (e02 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + w1]!)
      (e03 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + w2]!)
      (e12 := bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + w1]!)
      (e13 := bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + w2]!)
      (e23 := bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[tc + w2]!)
      (by omega) (by omega) (by omega)
  exact ⟨bitCnt_inj.mp c2, bitCnt_inj.mp c3, bitCnt_inj.mp c1⟩

/-! # The four-cell target beside a pair

The double swap of the chosen members and their complementary pair
serves whenever the pair's two members cannot tell the swapped
members apart, which is every uniform cross-count and the matched
cross-count restricted to one of its two sides. -/

/-- The double-swap route at a four-cell beside a pair. -/
theorem fourPair_sw2
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = ctx.n)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level ctx.n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level ctx.n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level ctx.n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hPfix : ∀ q, q ≤ 1 →
      (ctx.g[st.lab[d2 + q]!]!).testBit st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + q]!]!).testBit st.lab[tc + oV]! ∧
      (ctx.g[st.lab[d2 + q]!]!).testBit st.lab[tc + w1]! =
        (ctx.g[st.lab[d2 + q]!]!).testBit st.lab[tc + w2]!) :
    ∃ σ : Renaming ctx.n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hUV, hUw1, hUw2, hVw1, hVw2, h12]
  have hcover : ∀ o, o ≤ 3 → o = oU ∨ o = oV ∨ o = w1 ∨ o = w2 := by
    intro o ho
    omega
  -- distinct labels inside the cell and across the two cells
  have hin1 : ∀ o o' : Nat, o ≤ 3 → o' ≤ 3 → o ≠ o' →
      st.lab[tc + o]! ≠ st.lab[tc + o']! := by
    intro o o' ho ho' hne' hcon
    have := hinj (tc + o) (tc + o') (by omega) (by omega) hcon
    omega
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < ctx.n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < ctx.n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < ctx.n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < ctx.n := hlb _ (by omega)
  have hOk : Sw2Ok ctx.n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + w1]! st.lab[tc + w2]! :=
    ⟨hun, hvn, hxn, hyn, hin1 _ _ hoU hoV hUV,
      hin1 _ _ hoU hw1 hUw1, hin1 _ _ hoU hw2 hUw2,
      hin1 _ _ hoV hw1 hVw1, hin1 _ _ hoV hw2 hVw2,
      hin1 _ _ hw1 hw2 h12⟩
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hg hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- everything outside the four moved members treats them in pairs
  have hfix : ∀ z, z < ctx.n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! →
      (ctx.g[z]!).testBit st.lab[tc + oU]! =
        (ctx.g[z]!).testBit st.lab[tc + oV]! ∧
      (ctx.g[z]!).testBit st.lab[tc + w1]! =
        (ctx.g[z]!).testBit st.lab[tc + w2]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := ctx.n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · -- a member of the four-cell is one of the four moved labels
      have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rcases hcover (j - tc) hw with h | h | h | h <;>
        rw [hjt, h] at hzu hzv hzx hzy
      · exact absurd rfl hzu
      · exact absurd rfl hzv
      · exact absurd rfl hzx
      · exact absurd rfl hzy
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      rw [hjd]
      exact hPfix (j - d2) hq
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level ctx.n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hc := cell_const_into_singleton hE hC hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      have hd := cell_const_into_singleton hE hC hpmem
        (o := w1) (o' := w2) (by omega) (by omega)
      rw [← hjp] at hc hd
      have hjn : st.lab[j]! < ctx.n := hlb j hj
      constructor
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]
        exact hc
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]
        exact hd
  have hset : ∀ p ∈ cells st.ptn level ctx.n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
            st.lab[tc + w2]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    intro p hp o ho
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have ho' : o < tc + 3 + 1 - tc := ho
      rcases hcover o (by omega) with h | h | h | h
      · exact ⟨oV, by omega, by rw [h, sw2_u]⟩
      · exact ⟨oU, by omega, by rw [h, sw2_v hOk]⟩
      · exact ⟨w2, by omega, by rw [h, sw2_x hOk]⟩
      · exact ⟨w1, by omega, by rw [h, sw2_y hOk]⟩
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have ho' : o < d2 + 1 + 1 - d2 := ho
      exact ⟨o, ho, sw2_fix
        (fun h => hcross oU o hoU (by omega) h.symm)
        (fun h => hcross oV o hoV (by omega) h.symm)
        (fun h => hcross w1 o hw1 (by omega) h.symm)
        (fun h => hcross w2 o hw2 (by omega) h.symm)⟩
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have ho1 : o = 0 := by omega
      have hbd : p.1 < ctx.n := by
        have h1 := cells_bound (by rw [hpsz]; exact Nat.le_refl _)
          hend _ hp
        have h2 := cells_le _ hp
        rw [hpsz] at h1
        omega
      have hother : ∀ o' : Nat, o' ≤ 3 →
          st.lab[p.1 + o]! ≠ st.lab[tc + o']! := by
        intro o' ho'' hcon
        have := hinj (p.1 + o) (tc + o') (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpC (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hC
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      exact ⟨o, ho, sw2_fix (hother oU hoU) (hother oV hoV)
        (hother w1 hw1) (hother w2 hw2)⟩
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
      st.lab[tc + w2]!) hIt hgsz hg (sw2_lt hOk)
    (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

/-! # The matched cross-count

When each member of the four-cell meets exactly one member of the
pair, the four-cell splits into the two members met by the first and
the two met by the second. A flip across that split has to carry the
pair along, and the resulting map is the triple swap. -/

/-- The triple-swap route at a four-cell beside a pair, with the
chosen members on opposite sides of the matched split. -/
theorem fourPair_sw3
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = ctx.n)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level ctx.n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level ctx.n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level ctx.n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hUa : (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[d2 + 0]! = true)
    (hUb : (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[d2 + 1]! = false)
    (hVa : (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[d2 + 0]! = false)
    (hVb : (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[d2 + 1]! = true)
    (hXa : (ctx.g[st.lab[tc + w1]!]!).testBit st.lab[d2 + 0]! = true)
    (hXb : (ctx.g[st.lab[tc + w1]!]!).testBit st.lab[d2 + 1]! = false)
    (hYa : (ctx.g[st.lab[tc + w2]!]!).testBit st.lab[d2 + 0]! = false)
    (hYb : (ctx.g[st.lab[tc + w2]!]!).testBit st.lab[d2 + 1]! = true) :
    ∃ σ : Renaming ctx.n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hUV, hUw1, hUw2, hVw1, hVw2, h12]
  have hcover : ∀ o, o ≤ 3 → o = oU ∨ o = oV ∨ o = w1 ∨ o = w2 := by
    intro o ho
    omega
  have hin1 : ∀ o o' : Nat, o ≤ 3 → o' ≤ 3 → o ≠ o' →
      st.lab[tc + o]! ≠ st.lab[tc + o']! := by
    intro o o' ho ho' hne' hcon
    have := hinj (tc + o) (tc + o') (by omega) (by omega) hcon
    omega
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hpne : st.lab[d2 + 0]! ≠ st.lab[d2 + 1]! := by
    intro hcon
    have := hinj (d2 + 0) (d2 + 1) (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < ctx.n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < ctx.n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < ctx.n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < ctx.n := hlb _ (by omega)
  have han : st.lab[d2 + 0]! < ctx.n := hlb _ (by omega)
  have hbn : st.lab[d2 + 1]! < ctx.n := hlb _ (by omega)
  have hOk : Sw3Ok ctx.n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + w1]! st.lab[tc + w2]! st.lab[d2 + 0]!
      st.lab[d2 + 1]! :=
    ⟨hun, hvn, hxn, hyn, han, hbn,
      hin1 _ _ hoU hoV hUV, hin1 _ _ hoU hw1 hUw1,
      hin1 _ _ hoU hw2 hUw2, hcross oU 0 hoU (by omega),
      hcross oU 1 hoU (by omega),
      hin1 _ _ hoV hw1 hVw1, hin1 _ _ hoV hw2 hVw2,
      hcross oV 0 hoV (by omega), hcross oV 1 hoV (by omega),
      hin1 _ _ hw1 hw2 h12, hcross w1 0 hw1 (by omega),
      hcross w1 1 hw1 (by omega), hcross w2 0 hw2 (by omega),
      hcross w2 1 hw2 (by omega), hpne⟩
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hg hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- only the singletons remain outside the six moved members
  have hfix : ∀ z, z < ctx.n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! → z ≠ st.lab[d2 + 0]! →
      z ≠ st.lab[d2 + 1]! →
      (ctx.g[z]!).testBit st.lab[tc + oU]! =
        (ctx.g[z]!).testBit st.lab[tc + oV]! ∧
      (ctx.g[z]!).testBit st.lab[tc + w1]! =
        (ctx.g[z]!).testBit st.lab[tc + w2]! ∧
      (ctx.g[z]!).testBit st.lab[d2 + 0]! =
        (ctx.g[z]!).testBit st.lab[d2 + 1]! := by
    intro z hz hzu hzv hzx hzy hza hzb
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := ctx.n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rcases hcover (j - tc) hw with h | h | h | h <;>
        rw [hjt, h] at hzu hzv hzx hzy
      · exact absurd rfl hzu
      · exact absurd rfl hzv
      · exact absurd rfl hzx
      · exact absurd rfl hzy
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      have hq2 : j - d2 = 0 ∨ j - d2 = 1 := by omega
      rcases hq2 with h | h <;> rw [hjd, h] at hza hzb
      · exact absurd rfl hza
      · exact absurd rfl hzb
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level ctx.n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hcU := cell_const_into_singleton hE hC hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      have hcW := cell_const_into_singleton hE hC hpmem
        (o := w1) (o' := w2) (by omega) (by omega)
      have hcP := cell_const_into_singleton hE hP hpmem
        (o := 0) (o' := 1) (by omega) (by omega)
      rw [← hjp] at hcU hcW hcP
      have hjn : st.lab[j]! < ctx.n := hlb j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]; exact hcU
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]; exact hcW
      · rw [hsymm _ _ hjn han, hsymm _ _ hjn hbn]; exact hcP
  have hset : ∀ p ∈ cells st.ptn level ctx.n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw3 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
            st.lab[tc + w2]! st.lab[d2 + 0]! st.lab[d2 + 1]!
            st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    intro p hp o ho
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have ho' : o < tc + 3 + 1 - tc := ho
      rcases hcover o (by omega) with h | h | h | h
      · exact ⟨oV, by omega, by rw [h, sw3_u]⟩
      · exact ⟨oU, by omega, by rw [h, sw3_v hOk]⟩
      · exact ⟨w2, by omega, by rw [h, sw3_x hOk]⟩
      · exact ⟨w1, by omega, by rw [h, sw3_y hOk]⟩
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have ho' : o < d2 + 1 + 1 - d2 := ho
      have ho2 : o = 0 ∨ o = 1 := by omega
      rcases ho2 with h | h
      · exact ⟨1, by omega, by rw [h, sw3_a hOk]⟩
      · exact ⟨0, by omega, by rw [h, sw3_b hOk]⟩
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have ho1 : o = 0 := by omega
      have hbd : p.1 < ctx.n := by
        have h1 := cells_bound (by rw [hpsz]; exact Nat.le_refl _)
          hend _ hp
        have h2 := cells_le _ hp
        rw [hpsz] at h1
        omega
      have hotherC : ∀ o' : Nat, o' ≤ 3 →
          st.lab[p.1 + o]! ≠ st.lab[tc + o']! := by
        intro o' ho'' hcon
        have := hinj (p.1 + o) (tc + o') (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpC (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hC
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      have hotherP : ∀ q : Nat, q ≤ 1 →
          st.lab[p.1 + o]! ≠ st.lab[d2 + q]! := by
        intro q hq hcon
        have := hinj (p.1 + o) (d2 + q) (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpP (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hP
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      exact ⟨o, ho, sw3_fix (hotherC oU hoU) (hotherC oV hoV)
        (hotherC w1 hw1) (hotherC w2 hw2) (hotherP 0 (by omega))
        (hotherP 1 (by omega))⟩
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw3 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
      st.lab[tc + w2]! st.lab[d2 + 0]! st.lab[d2 + 1]!)
    hIt hgsz hg (sw3_lt hOk) (fun w _ => sw3_invol hOk w)
    (sw3_bits hsymm hloop hOk hfix hc1 hc2
      (by rw [hUa, hVb]) (by rw [hUb, hVa])
      (by rw [hXa, hYb]) (by rw [hXb, hYa])) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw3_u]

end FourCell

end Hex.GraphIso.Nauty
