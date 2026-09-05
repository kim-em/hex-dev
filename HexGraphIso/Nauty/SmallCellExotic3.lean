/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellExotic2
import all HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
import all HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.EquitableFix

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

variable {ctx : Ctx n}

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
  have hun := h.1
  have hvn := h.2.1
  have hxn := h.2.2.1
  have hyn := h.2.2.2.1
  have han := h.2.2.2.2.1
  have hbn := h.2.2.2.2.2.1
  -- the six moved rows against an arbitrary second argument
  have key : ∀ z', z' < n →
      ((ctx.g[v]!).mem (sw3 u v x y a b z') =
        (ctx.g[u]!).mem z' ∧
       (ctx.g[u]!).mem (sw3 u v x y a b z') =
        (ctx.g[v]!).mem z') ∧
      ((ctx.g[y]!).mem (sw3 u v x y a b z') =
        (ctx.g[x]!).mem z' ∧
       (ctx.g[x]!).mem (sw3 u v x y a b z') =
        (ctx.g[y]!).mem z') ∧
      ((ctx.g[b]!).mem (sw3 u v x y a b z') =
        (ctx.g[a]!).mem z' ∧
       (ctx.g[a]!).mem (sw3 u v x y a b z') =
        (ctx.g[b]!).mem z') := by
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

variable {st : RefineSt n} {level tc d2 oU oV w1 w2 : Nat}

/-- Complementary pairs of a four-cell are equally adjacent. -/
theorem fourCell_comp
    (hIt : IterOk ctx level st)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hnd : ([oU, oV, w1, w2] : List Nat).Nodup) :
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w1]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w2]! ∧
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w2]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w1]! ∧
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + oV]! =
      (ctx.g[st.lab[tc + w1]!]!).mem st.lab[tc + w2]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
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
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oU]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oV]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w1]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w2]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hC
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
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hPfix : ∀ q, q ≤ 1 →
      (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + oV]! ∧
      (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + w1]! =
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + w2]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
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
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < n := hlb _ (by omega)
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + w1]! st.lab[tc + w2]! :=
    ⟨hun, hvn, hxn, hyn, hin1 _ _ hoU hoV hUV,
      hin1 _ _ hoU hw1 hUw1, hin1 _ _ hoU hw2 hUw2,
      hin1 _ _ hoV hw1 hVw1, hin1 _ _ hoV hw2 hVw2,
      hin1 _ _ hw1 hw2 h12⟩
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- everything outside the four moved members treats them in pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + w1]! =
        (ctx.g[z]!).mem st.lab[tc + w2]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
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
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
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
      have hjn : st.lab[j]! < n := hlb j hj
      constructor
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]
        exact hc
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]
        exact hd
  have hset : ∀ p ∈ cells st.ptn level n,
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
      have hbd : p.1 < n := by
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
      st.lab[tc + w2]!) hIt hgsz (sw2_lt hOk)
    (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

/-! # The matched cross-count

When each member of the four-cell meets exactly one member of the
pair, the four-cell splits into the two members met by the first and
the two met by the second. A flip across that split has to carry the
pair along, and the resulting map is the triple swap. -/

/-- The triple-swap route at a four-cell beside a pair: the chosen
members cross the pair coherently, as they do on opposite sides of a
matched split. -/
theorem fourPair_sw3
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hUV0 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + 0]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + 1]!)
    (hUV1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + 1]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + 0]!)
    (hW0 : (ctx.g[st.lab[tc + w1]!]!).mem st.lab[d2 + 0]! =
      (ctx.g[st.lab[tc + w2]!]!).mem st.lab[d2 + 1]!)
    (hW1 : (ctx.g[st.lab[tc + w1]!]!).mem st.lab[d2 + 1]! =
      (ctx.g[st.lab[tc + w2]!]!).mem st.lab[d2 + 0]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! ∧
      st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
      st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
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
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < n := hlb _ (by omega)
  have han : st.lab[d2 + 0]! < n := hlb _ (by omega)
  have hbn : st.lab[d2 + 1]! < n := hlb _ (by omega)
  have hOk : Sw3Ok n st.lab[tc + oU]! st.lab[tc + oV]!
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
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- only the singletons remain outside the six moved members
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! → z ≠ st.lab[d2 + 0]! →
      z ≠ st.lab[d2 + 1]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + w1]! =
        (ctx.g[z]!).mem st.lab[tc + w2]! ∧
      (ctx.g[z]!).mem st.lab[d2 + 0]! =
        (ctx.g[z]!).mem st.lab[d2 + 1]! := by
    intro z hz hzu hzv hzx hzy hza hzb
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
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
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
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
      have hjn : st.lab[j]! < n := hlb j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]; exact hcU
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]; exact hcW
      · rw [hsymm _ _ hjn han, hsymm _ _ hjn hbn]; exact hcP
  have hset : ∀ p ∈ cells st.ptn level n,
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
      have hbd : p.1 < n := by
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
    hIt hgsz (sw3_lt hOk) (fun w _ => sw3_invol hOk w)
    (sw3_bits hsymm hloop hOk hfix hc1 hc2 hUV0 hUV1 hW0 hW1) hset
  refine ⟨σ, hrm, hsp, ?_, ?_, ?_⟩
  · rw [hat (tc + oU) (by omega), sw3_u]
  · rw [hat (d2 + 0) (by omega), sw3_a hOk]
  · rw [hat (d2 + 1) (by omega), sw3_b hOk]

/-! # The dispatcher

The cross-count between the four-cell and the pair is constant and at
most two. Zero and two leave the pair unable to tell any two members
apart; one splits the four-cell into two matched pairs, and the two
chosen members are either on the same side, where the pair again sees
no difference, or on opposite sides, where the pair travels with the
flip. -/

private theorem sum_range_succ₄ (f : Nat → Nat) (m : Nat) :
    ((List.range (m + 1)).map f).sum =
      ((List.range m).map f).sum + f m := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

private theorem sum_range_two₄ (f : Nat → Nat) :
    ((List.range 2).map f).sum = f 0 + f 1 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, sum_range_succ₄,
    show (1 : Nat) = 0 + 1 from rfl, sum_range_succ₄]
  simp

/-- Two distinct offsets below four leave two more. -/
private theorem other_two {p q : Nat} (hp : p ≤ 3) (hq : q ≤ 3)
    (hpq : p ≠ q) :
    ∃ r s, r ≤ 3 ∧ s ≤ 3 ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧
      r ≠ s := by
  have hp3 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  have hq3 : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hp3 with rfl | rfl | rfl | rfl <;>
    rcases hq3 with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hpq
      | exact ⟨2, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨1, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨1, 2, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 2, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 1, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
/-- The flip data at a four-cell target beside a pair, all other cells
singletons. -/
theorem fourPair_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  obtain ⟨w1, w2, hw1, hw2, hUw1, hUw2, hVw1, hVw2, h12⟩ :=
    other_two hoU hoV hne
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hne, hUw1, hUw2, hVw1, hVw2, h12]
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
  -- the forward counts into the pair
  have hfwd : ∀ o, o ≤ 3 →
      (worksetOf n st.lab d2 (d2 + 1)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hP
    rw [show d2 + 1 + 1 - d2 = 2 by omega, sum_range_two₄] at h
    exact h
  -- the reverse counts into the four-cell
  have hrev : ∀ q, q ≤ 1 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[d2 + q]!]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + oU]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + oV]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + w1]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + w2]! := by
    intro q hq
    have h := count_into_cell (ctx := ctx) (u := st.lab[d2 + q]!) hpsz hend hinj hC
    rw [show tc + 3 + 1 - tc = 4 by omega] at h
    rw [h, sum_range_of_distinct _ (by simp) hnd hbd]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  -- forward constancy across the four-cell, reverse across the pair
  have hfc : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! =
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 1]! := by
    intro o o' ho ho'
    have h := hE _ hC _ hP o o' (by omega) (by omega)
    rw [hfwd o ho, hfwd o' ho'] at h
    exact h
  have hrc := hE _ hP _ hC 0 1 (by omega) (by omega)
  rw [hrev 0 (by omega), hrev 1 (by omega)] at hrc
  -- the two directions agree termwise
  have hsy : ∀ o q, o ≤ 3 → q ≤ 1 →
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! :=
    fun o q ho hq => bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hle : ∀ o q : Nat,
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! ≤ 1 :=
    fun o q => bitCnt_le_one _ _
  -- the pair's view of the four members, in the two useful shapes
  have hbit : ∀ o q, o ≤ 3 → q ≤ 1 →
      ((ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + q]! = true ↔
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! = 1) :=
    fun o q ho hq => ⟨fun h => bitCnt_eq_one.mpr h,
      fun h => bitCnt_eq_one.mp h⟩
  have hPof : ∀ o o', o ≤ 3 → o' ≤ 3 →
      (∀ q, q ≤ 1 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! =
          bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + q]!) →
      ∀ q, q ≤ 1 →
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + o]! =
          (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + o']! := by
    intro o o' ho ho' h q hq
    have h1 := hsy o q ho hq
    have h2 := hsy o' q ho' hq
    exact bitCnt_inj.mp (by rw [h1, h2]; exact h q hq)
  -- the constant cross-count is zero, one or two
  have hsum : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 0 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 1 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 2 := by
    have := hle oU 0
    have := hle oU 1
    omega
  have hUVc := hfc oU oV hoU hoV
  have hUw1c := hfc oU w1 hoU hw1
  have hUw2c := hfc oU w2 hoU hw2
  rcases hsum with h0 | h1 | h2
  · -- no edges between the two cells
    refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
    intro q hq
    have e1 := hle oU 0
    have e2 := hle oU 1
    have e3 := hle oV 0
    have e4 := hle oV 1
    have e5 := hle w1 0
    have e6 := hle w1 1
    have e7 := hle w2 0
    have e8 := hle w2 1
    constructor
    · exact hPof oU oV hoU hoV (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
    · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
  · -- each member meets exactly one of the pair
    have hr0 : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + w2]!]! st.lab[d2 + 0]! = 2 := by
      have s1 := hsy oU 0 hoU (by omega)
      have s2 := hsy oV 0 hoV (by omega)
      have s3 := hsy w1 0 hw1 (by omega)
      have s4 := hsy w2 0 hw2 (by omega)
      have s5 := hsy oU 1 hoU (by omega)
      have s6 := hsy oV 1 hoV (by omega)
      have s7 := hsy w1 1 hw1 (by omega)
      have s8 := hsy w2 1 hw2 (by omega)
      omega
    rcases Decidable.em
        (bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! =
          bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + 0]!)
      with hsame | hdiff
    · -- the chosen members sit on the same side of the split
      refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
        hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
      intro q hq
      have e1 := hle oU 0
      have e2 := hle oU 1
      have e3 := hle oV 0
      have e4 := hle oV 1
      have e5 := hle w1 0
      have e6 := hle w1 1
      have e7 := hle w2 0
      have e8 := hle w2 1
      constructor
      · exact hPof oU oV hoU hoV (fun q' hq' => by
          rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
          q hq
      · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
          rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
          q hq
    · -- opposite sides: name the partner of each chosen member
      have e1 := hle oU 0
      have e2 := hle oU 1
      have e3 := hle oV 0
      have e4 := hle oV 1
      have e5 := hle w1 0
      have e6 := hle w1 1
      have e7 := hle w2 0
      have e8 := hle w2 1
      have hVc := hfc oV w1 hoV hw1
      rcases Decidable.em
          (bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[d2 + 0]! =
            bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]!)
        with hw1U | hw1V
      · obtain ⟨σ, hrm, hsp, hfl, -, -⟩ :=
          fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP
            hsing hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        exact ⟨σ, hrm, hsp, hfl⟩
      · obtain ⟨σ, hrm, hsp, hfl, -, -⟩ :=
          fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP
            hsing hoU hoV hw2 hw1 hne hUw2 hUw1 hVw2 hVw1
            (Ne.symm h12)
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        exact ⟨σ, hrm, hsp, hfl⟩
  · -- every member meets both of the pair
    refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
    intro q hq
    have e1 := hle oU 0
    have e2 := hle oU 1
    have e3 := hle oV 0
    have e4 := hle oV 1
    have e5 := hle w1 0
    have e6 := hle w1 1
    have e7 := hle w2 0
    have e8 := hle w2 1
    constructor
    · exact hPof oU oV hoU hoV (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
    · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq

/-! # The pair target beside a four-cell

The same configuration with the pair as the target. A uniform
cross-count leaves the four-cell fixed and the bare transposition of
the pair serves; the matched count carries the four-cell along, which
is again the triple swap. -/

/-- The transposition route at a pair target beside a four-cell. -/
theorem pairFour_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hqU : qU ≤ 1) (hqV : qV ≤ 1) (hqne : qU ≠ qV)
    (huni : ∀ o, o ≤ 3 →
      (ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + qU]! =
        (ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + qV]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[d2 + qV]! = σ.toFun st.lab[d2 + qU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
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
  have hin2 : ∀ q q' : Nat, q ≤ 1 → q' ≤ 1 → q ≠ q' →
      st.lab[d2 + q]! ≠ st.lab[d2 + q']! := by
    intro q q' hq hq' hne' hcon
    have := hinj (d2 + q) (d2 + q') (by omega) (by omega) hcon
    omega
  have hun : st.lab[d2 + qU]! < n := hlb _ (by omega)
  have hvn : st.lab[d2 + qV]! < n := hlb _ (by omega)
  have huv := hin2 _ _ hqU hqV hqne
  have hfix : ∀ z, z < n → z ≠ st.lab[d2 + qU]! →
      z ≠ st.lab[d2 + qV]! →
      (ctx.g[z]!).mem st.lab[d2 + qU]! =
        (ctx.g[z]!).mem st.lab[d2 + qV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    have hjn : st.lab[j]! < n := hlb j hj
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rw [hjt]
      exact huni (j - tc) hw
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      have hq2 : j - d2 = qU ∨ j - d2 = qV := by omega
      rcases hq2 with h | h <;> rw [hjd, h] at hzu hzv
      · exact absurd rfl hzu
      · exact absurd rfl hzv
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hc := cell_const_into_singleton hE hP hpmem
        (o := qU) (o' := qV) (by omega) (by omega)
      rw [← hjp] at hc
      rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]
      exact hc
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[d2 + qU]! st.lab[d2 + qV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    intro p hp o ho
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have ho' : o < d2 + 1 + 1 - d2 := ho
      rcases Decidable.em (o = qU) with rfl | hou
      · exact ⟨qV, by omega, by rw [sw1_u]⟩
      rcases Decidable.em (o = qV) with rfl | hov
      · exact ⟨qU, by omega, by rw [sw1_v huv]⟩
      · exact ⟨o, ho, sw1_fix (hin2 o qU (by omega) hqU hou)
          (hin2 o qV (by omega) hqV hov)⟩
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have ho' : o < tc + 3 + 1 - tc := ho
      exact ⟨o, ho, sw1_fix (hcross o qU (by omega) hqU)
        (hcross o qV (by omega) hqV)⟩
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have ho1 : o = 0 := by omega
      have hbd : p.1 < n := by
        have h1 := cells_bound (by rw [hpsz]; exact Nat.le_refl _)
          hend _ hp
        have h2 := cells_le _ hp
        rw [hpsz] at h1
        omega
      have hother : ∀ q : Nat, q ≤ 1 →
          st.lab[p.1 + o]! ≠ st.lab[d2 + q]! := by
        intro q hq hcon
        have := hinj (p.1 + o) (d2 + q) (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpP (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hP
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      exact ⟨o, ho, sw1_fix (hother qU hqU) (hother qV hqV)⟩
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[d2 + qU]! st.lab[d2 + qV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (d2 + qU) (by omega), sw1_u]

set_option maxHeartbeats 1000000 in
/-- The flip data at a pair target beside a four-cell, all other cells
singletons. -/
theorem pairFour_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hqU : qU ≤ 1) (hqV : qV ≤ 1) (hqne : qU ≠ qV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[d2 + qV]! = σ.toFun st.lab[d2 + qU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hfwd : ∀ o, o ≤ 3 →
      (worksetOf n st.lab d2 (d2 + 1)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hP
    rw [show d2 + 1 + 1 - d2 = 2 by omega, sum_range_two₄] at h
    exact h
  have hrev : ∀ q, q ≤ 1 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[d2 + q]!]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 0]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 1]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 2]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 3]! := by
    intro q hq
    have h := count_into_cell (ctx := ctx) (u := st.lab[d2 + q]!) hpsz hend hinj hC
    rw [show tc + 3 + 1 - tc = 4 by omega] at h
    rw [h, sum_range_of_distinct _ (l := [0, 1, 2, 3]) (by simp)
      (by simp) (by intro x hx; simp at hx; omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  have hfc : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! =
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 1]! := by
    intro o o' ho ho'
    have h := hE _ hC _ hP o o' (by omega) (by omega)
    rw [hfwd o ho, hfwd o' ho'] at h
    exact h
  have hrc := hE _ hP _ hC 0 1 (by omega) (by omega)
  rw [hrev 0 (by omega), hrev 1 (by omega)] at hrc
  have hsy : ∀ o q, o ≤ 3 → q ≤ 1 →
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! :=
    fun o q ho hq => bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hle : ∀ o q : Nat,
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! ≤ 1 :=
    fun o q => bitCnt_le_one _ _
  -- the matched route, given the split named explicitly
  have route : ∀ a b c d : Nat, a ≤ 3 → b ≤ 3 → c ≤ 3 → d ≤ 3 →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      bitCnt ctx.g[st.lab[tc + a]!]! st.lab[d2 + 0]! = 1 →
      bitCnt ctx.g[st.lab[tc + b]!]! st.lab[d2 + 0]! = 1 →
      bitCnt ctx.g[st.lab[tc + c]!]! st.lab[d2 + 0]! = 0 →
      bitCnt ctx.g[st.lab[tc + d]!]! st.lab[d2 + 0]! = 0 →
      (∀ o, o ≤ 3 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! = 1) →
      ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
        StPerm level st (mapSt σ st) ∧
        st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
        st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
    intro a b c d ha hb hc hd hab hac had hbc hbd hcd hAa hAb hAc
      hAd hone
    have o1 := hone a ha
    have o2 := hone b hb
    have o3 := hone c hc
    have o4 := hone d hd
    obtain ⟨σ, hrm, hsp, -, hp1, hp2⟩ :=
      fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP hsing
        ha hc hb hd hac hab had (Ne.symm hbc) hcd hbd
        (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
    exact ⟨σ, hrm, hsp, hp1, hp2⟩
  have hsum : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 0 ∨
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 1 ∨
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 2 := by
    have := hle 0 0
    have := hle 0 1
    omega
  have c1 := hfc 0 1 (by omega) (by omega)
  have c2 := hfc 0 2 (by omega) (by omega)
  have c3 := hfc 0 3 (by omega) (by omega)
  have e1 := hle 0 0
  have e2 := hle 0 1
  have e3 := hle 1 0
  have e4 := hle 1 1
  have e5 := hle 2 0
  have e6 := hle 2 1
  have e7 := hle 3 0
  have e8 := hle 3 1
  rcases hsum with h0 | h1 | h2
  · -- the pair meets no member of the four-cell
    refine pairFour_sw1 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hqU hqV hqne ?_
    intro o ho
    have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases ho4 with rfl | rfl | rfl | rfl <;>
      exact bitCnt_inj.mp (by omega)
  · -- each member meets exactly one, so the four-cell splits in two
    have hone : ∀ o, o ≤ 3 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! = 1 := by
      intro o ho
      have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      rcases ho4 with rfl | rfl | rfl | rfl <;> omega
    have hr0 : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 2 := by
      have s1 := hsy 0 0 (by omega) (by omega)
      have s2 := hsy 1 0 (by omega) (by omega)
      have s3 := hsy 2 0 (by omega) (by omega)
      have s4 := hsy 3 0 (by omega) (by omega)
      have s5 := hsy 0 1 (by omega) (by omega)
      have s6 := hsy 1 1 (by omega) (by omega)
      have s7 := hsy 2 1 (by omega) (by omega)
      have s8 := hsy 3 1 (by omega) (by omega)
      omega
    have hpick : ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
        StPerm level st (mapSt σ st) ∧
        st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
        st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
      have v0 : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v1 : bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v2 : bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v3 : bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 1 := by
        omega
      rcases v0 with q0 | q0 <;> rcases v1 with q1 | q1 <;>
        rcases v2 with q2 | q2 <;> rcases v3 with q3 | q3 <;>
        first
          | (exfalso; omega)
          | exact route 0 1 2 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 0 2 1 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 0 3 1 2 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 1 2 0 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 1 3 0 2 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 2 3 0 1 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
    obtain ⟨σ, hrm, hsp, hp1, hp2⟩ := hpick
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨σ, hrm, hsp, hp1⟩
    · exact ⟨σ, hrm, hsp, hp2⟩
  · -- the pair meets every member of the four-cell
    refine pairFour_sw1 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hqU hqV hqne ?_
    intro o ho
    have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases ho4 with rfl | rfl | rfl | rfl <;>
      exact bitCnt_inj.mp (by omega)

end FourCell

/-! # The shape of a defect-four partition

The excesses of the cells sum to the defect, so a defect of at most
four bounds every cell at five members and leaves very little room
beside a large cell. The four shapes the first guard branch misses are
a lone four-cell, a lone five-cell, a four-cell beside a pair, and two
triples, and each has its flip data above. -/

section Shape

private theorem exc_ge_one {q : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), q ∈ l →
      (l.map fun p => p.2 - p.1).sum ≥ q.2 - q.1
  | [], hq => absurd hq (by simp)
  | a :: l, hq => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · omega
    · have := exc_ge_one l hmem
      omega

private theorem exc_ge_two {q q' : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), q ∈ l → q' ∈ l → q ≠ q' →
      (l.map fun p => p.2 - p.1).sum ≥ (q.2 - q.1) + (q'.2 - q'.1)
  | [], hq, _, _ => absurd hq (by simp)
  | a :: l, hq, hq', hne => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · have hq'l : q' ∈ l := by
        rcases List.mem_cons.mp hq' with rfl | h
        · exact absurd rfl hne
        · exact h
      have := exc_ge_one l hq'l
      omega
    · rcases List.mem_cons.mp hq' with rfl | hmem'
      · have := exc_ge_one l hmem
        omega
      · have := exc_ge_two l hmem hmem' hne
        omega

private theorem exc_ge_three {q q' q'' : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), q ∈ l → q' ∈ l → q'' ∈ l →
      q ≠ q' → q ≠ q'' → q' ≠ q'' →
      (l.map fun p => p.2 - p.1).sum ≥
        (q.2 - q.1) + (q'.2 - q'.1) + (q''.2 - q''.1)
  | [], hq, _, _, _, _, _ => absurd hq (by simp)
  | a :: l, hq, hq', hq'', hne, hne', hne'' => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · have h1 : q' ∈ l := by
        rcases List.mem_cons.mp hq' with rfl | h
        · exact absurd rfl hne
        · exact h
      have h2 : q'' ∈ l := by
        rcases List.mem_cons.mp hq'' with rfl | h
        · exact absurd rfl hne'
        · exact h
      have := exc_ge_two l h1 h2 hne''
      omega
    · rcases List.mem_cons.mp hq' with rfl | hmem'
      · have h2 : q'' ∈ l := by
          rcases List.mem_cons.mp hq'' with rfl | h
          · exact absurd rfl hne''
          · exact h
        have := exc_ge_two l hmem h2 hne'
        omega
      · rcases List.mem_cons.mp hq'' with rfl | hmem''
        · have := exc_ge_two l hmem hmem' hne
          omega
        · have := exc_ge_three l hmem hmem' hmem'' hne hne' hne''
          omega

private theorem sizes_split :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) →
      (l.map fun p => p.2 + 1 - p.1).sum =
        (l.map fun p => p.2 - p.1).sum + l.length
  | [], _ => rfl
  | a :: l, hwf => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      List.length_cons,
      sizes_split l fun p hp => hwf p (List.mem_cons_of_mem _ hp)]
    have := hwf a List.mem_cons_self
    omega

/-- The cells' excesses sum to the defect. -/
theorem exc_sum_eq_defect {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level) :
    ((cells ptn level nn).map fun p => p.2 - p.1).sum =
      nn - (cells ptn level nn).length := by
  have hwf : ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 :=
    fun p hp => cells_le p hp
  have hsum : ((cells ptn level nn).map fun p =>
      p.2 + 1 - p.1).sum = nn := by
    rw [cells]
    have h := cells_go_sizes_sum hps hend nn 0 (by omega)
    rw [show nn - 0 = nn by omega] at h
    exact h
  have hsplit := sizes_split (cells ptn level nn) hwf
  omega

end Shape

section Dispatch

variable {st : RefineSt n} {level tc te oU oV : Nat}

set_option maxHeartbeats 1000000 in
/-- Flip data at every cell of a partition whose defect is at most
four. This is the shape the cheapautom guard's second branch admits;
it dispatches to the pair and triple routes of the first branch
together with the four exotic routes. -/
theorem defect4_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hdef : n - (cells st.ptn level n).length ≤ 4)
    (hT : (tc, te) ∈ cells st.ptn level n)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hend := hIt.ok.ptnEnd
  have hnn : n ≤ st.ptn.size := by rw [hpsz]; exact Nat.le_refl _
  have hexc := exc_sum_eq_defect (nn := n) (level := level)
    (ptn := st.ptn) hpsz hend
  have hle : tc ≤ te := cells_le _ hT
  have hsize5 : ∀ q ∈ cells st.ptn level n, q.2 - q.1 ≤ 4 := by
    intro q hq
    have := exc_ge_one (q := q) _ hq
    omega
  have hpair2 : ∀ q ∈ cells st.ptn level n,
      ∀ q' ∈ cells st.ptn level n, q ≠ q' →
        (q.2 - q.1) + (q'.2 - q'.1) ≤ 4 := by
    intro q hq q' hq' hqq
    have := exc_ge_two (q := q) (q' := q') _ hq hq' hqq
    omega
  have htri3 : ∀ q ∈ cells st.ptn level n,
      ∀ q' ∈ cells st.ptn level n,
      ∀ q'' ∈ cells st.ptn level n, q ≠ q' → q ≠ q'' → q' ≠ q'' →
        (q.2 - q.1) + (q'.2 - q'.1) + (q''.2 - q''.1) ≤ 4 := by
    intro q hq q' hq' q'' hq'' h1 h2 h3
    have := exc_ge_three (q := q) (q' := q') (q'' := q'') _ hq hq'
      hq'' h1 h2 h3
    omega
  have hT5 := hsize5 _ hT
  have hs : te - tc = 1 ∨ te - tc = 2 ∨ te - tc = 3 ∨ te - tc = 4 := by
    omega
  rcases hs with hs | hs | hs | hs
  · -- a pair target
    have hte : te = tc + 1 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 1)) - (Prod.fst (tc, tc + 1)) = 1 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        3 ≤ q.2 - q.1) with ⟨C, hC, hCbig⟩ | hnobig
    · -- a four-cell beside it: the exotic route
      have hCle : C.1 ≤ C.2 := cells_le _ hC
      have hCne : C ≠ (tc, tc + 1) := by
        intro hcon
        rw [hcon] at hCbig
        omega
      have hCex : C.2 - C.1 = 3 := by
        have := hpair2 _ hC _ hT hCne
        omega
      have hCform : C = (C.1, C.1 + 3) := by
        obtain ⟨ca, cb⟩ := C
        simp only at hCex ⊢
        have hcb : cb = ca + 3 := by omega
        rw [hcb]
      have hC' : (C.1, C.1 + 3) ∈ cells st.ptn level n :=
        hCform ▸ hC
      have hCP : C.1 ≠ tc := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hC' hT (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        simp only [Prod.mk.injEq] at heq
        omega
      refine pairFour_flip_data hIt hgsz hsymm hloop hE hC' hT
        hCP ?_ (by omega) (by omega) hne
      intro q hq hqC hqP
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hCq : C ≠ q := fun hcon => hqC (by rw [← hcon, ← hCform])
        have h3 := htri3 _ hC _ hT _ hq hCne hCq
          (fun hcon => hqP hcon.symm)
        omega
    · -- no large cell: the first branch's pair route applies
      refine pair_flip_data hIt hgsz hsymm hloop hE hT ?_
        (by omega) (by omega) hne
      intro q hq hqp
      have hql := cells_le _ hq
      have hq2 : q.2 - q.1 ≤ 2 := by
        rcases Nat.lt_or_ge (q.2 - q.1) 3 with h | h
        · omega
        · exact absurd ⟨q, hq, h⟩ hnobig
      omega
  · -- a triple target
    have hte : te = tc + 2 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 2)) - (Prod.fst (tc, tc + 2)) = 2 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        q ≠ (tc, tc + 2) ∧ q.2 - q.1 = 2) with ⟨D, hD, hDne, hDex⟩ |
      hnotri
    · -- two triples: the exotic route
      have hDform : D = (D.1, D.1 + 2) := by
        obtain ⟨da, db⟩ := D
        simp only at hDex ⊢
        have hdb : db = da + 2 := by omega
        rw [hdb]
      have hD' : (D.1, D.1 + 2) ∈ cells st.ptn level n :=
        hDform ▸ hD
      have hTD : tc ≠ D.1 := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hT hD' (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        exact hDne (by rw [hDform, ← heq])
      refine twoTriple_flip_data hIt hgsz hsymm hloop hE hT hD'
        hTD ?_ (by omega) (by omega) hne
      intro q hq hqT hqD
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hDq : D ≠ q := fun hcon => hqD (by rw [← hcon, ← hDform])
        have h3 := htri3 _ hT _ hD _ hq (Ne.symm hDne) 
          (fun hcon => hqT hcon.symm) hDq
        omega
    · -- a unique triple with everything else small
      refine triple_flip_data hIt hgsz hsymm hloop hE hT ?_
        (by omega) (by omega) hne
      intro q hq hqT
      have hql := cells_le _ hq
      rcases Decidable.em (q.2 - q.1 = 2) with h2 | h2
      · exact absurd ⟨q, hq, hqT, h2⟩ hnotri
      · have := hpair2 _ hq _ hT hqT
        omega
  · -- a four-cell target
    have hte : te = tc + 3 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 3)) - (Prod.fst (tc, tc + 3)) = 3 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        q ≠ (tc, tc + 3) ∧ q.1 < q.2) with ⟨P, hP, hPne, hPnt⟩ |
      hnopair
    · -- a pair beside it: the exotic route
      have hPle := cells_le _ hP
      have hPex : P.2 - P.1 = 1 := by
        have := hpair2 _ hT _ hP (fun hcon => hPne hcon.symm)
        omega
      have hPform : P = (P.1, P.1 + 1) := by
        obtain ⟨pa, pb⟩ := P
        simp only at hPex ⊢
        have hpb : pb = pa + 1 := by omega
        rw [hpb]
      have hP' : (P.1, P.1 + 1) ∈ cells st.ptn level n :=
        hPform ▸ hP
      have hCP : tc ≠ P.1 := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hT hP' (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        simp only [Prod.mk.injEq] at heq
        omega
      refine fourPair_flip_data hIt hgsz hsymm hloop hE hT hP'
        hCP ?_ (by omega) (by omega) hne
      intro q hq hqT hqP
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hPq : P ≠ q := fun hcon => hqP (by rw [← hcon, ← hPform])
        have h3 := htri3 _ hT _ hP _ hq (Ne.symm hPne)
          (fun hcon => hqT hcon.symm) hPq
        omega
    · -- a lone four-cell
      refine oneCell_flip_data hIt hgsz hsymm hloop hE hT
        (by omega) ?_ (by omega) (by omega) hne
      intro q hq hqT
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exact absurd ⟨q, hq, hqT, hlt⟩ hnopair
  · -- a five-cell target: nothing else can be nontrivial
    have hte : te = tc + 4 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 4)) - (Prod.fst (tc, tc + 4)) = 4 :=
      by omega
    refine oneCell_flip_data hIt hgsz hsymm hloop hE hT
      (by omega) ?_ (by omega) (by omega) hne
    intro q hq hqT
    rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
    · exact heq.symm
    · exfalso
      have := hpair2 _ hT _ hq (fun h => hqT h.symm)
      omega

end Dispatch

end Hex.GraphIso.Nauty
