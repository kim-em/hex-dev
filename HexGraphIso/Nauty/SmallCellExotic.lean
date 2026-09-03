/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellLeaves
import all HexGraphIso.Nauty.Equitable

public section

/-!
The exotic defect-four flip data (SPEC § Verified search refinement,
the code-1 arm of the store-validity obligation).

`cheapautom`'s second branch passes on partitions whose defect
(vertices minus cells) is at most four without the all-pairs-and-one-
triple shape of the first branch; the possible nontrivial cell
multisets are `{4}`, `{5}`, `{4,2}` and `{3,3}`, and the probe showed
admissions governed by such passes are pervasive on the conformance
corpus. This file proves the flip data for those configurations: for
any two members of any nontrivial cell, a row-preserving self-symmetry
of the node carrying one to the other, entering the deviation doors
exactly as the pair and triple instances do.

No shape enumeration is needed; everything is forced by counting:

* the differ set of two cell members (the other members whose bits at
  the two differ) always has even size, one half adjacent to the
  first, so with at most three other members it is empty or a single
  crossed pair (`differ` classification);
* in a five-cell the internal degree is even (the handshake), so the
  members outside a crossed pair have equal bits at the pair;
* in a four-cell the equitability row equations force full invariance
  under every double transposition (the `vlemma`);
* between two triples and between a four-cell and a pair, the constant
  cross-counts pair the members up by their minority bit, and swapping
  matched partners preserves every cross bit.

The constructions share one generic involution `sw` (up to three
simultaneous swaps, degenerate swaps allowed) with one bit-invariance
lemma (`sw_bits`), one generic rows conclusion (`rows_of_label_bits`,
the factored tail of `flip_rows`), and one generic self-equivalence
(`cellsPerm_self_setwise`: a renaming permuting every cell's members
within the cell is a cell-contents self-equivalence).
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # List toolkit -/

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
private theorem perm_of_nodup_subset :
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
private theorem sum_of_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
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

private theorem countP_le_one_unique {p : Nat → Bool} :
    ∀ (l : List Nat), l.countP p ≤ 1 →
      ∀ w ∈ l, p w = true → ∀ w' ∈ l, p w' = true → w = w'
  | a :: t, h, w, hw, hpw, w', hw', hpw' => by
    rw [List.countP_cons] at h
    rcases Decidable.em (p a = true) with hpa | hpa
    · rw [ite_eq_left hpa] at h
      have ht0 : t.countP p = 0 := by omega
      have hnt : ∀ x ∈ t, ¬ p x = true := by
        intro x hx hpx
        have : 0 < t.countP p := by
          have := countP_zero_none t ht0 x hx
          exact absurd hpx this
        omega
      have hwa : w = a := by
        rcases List.mem_cons.mp hw with rfl | hmem
        · rfl
        · exact absurd hpw (hnt w hmem)
      have hwa' : w' = a := by
        rcases List.mem_cons.mp hw' with rfl | hmem
        · rfl
        · exact absurd hpw' (hnt w' hmem)
      rw [hwa, hwa']
    · rw [ite_eq_right hpa] at h
      have hwt : w ∈ t := by
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact absurd hpw hpa
        · exact hmem
      have hwt' : w' ∈ t := by
        rcases List.mem_cons.mp hw' with rfl | hmem
        · exact absurd hpw' hpa
        · exact hmem
      exact countP_le_one_unique t h w hwt hpw w' hwt' hpw'
where
  countP_zero_none : ∀ (l : List Nat), l.countP p = 0 →
      ∀ x ∈ l, ¬ p x = true
    | a :: t, h0, x, hx => by
      rw [List.countP_cons] at h0
      rcases Decidable.em (p a = true) with hpa | hpa
      · rw [ite_eq_left hpa] at h0
        omega
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact fun hpx => hpa hpx
        · rw [ite_eq_right hpa] at h0
          exact countP_zero_none t h0 x hmem

/-- A permutation of `range k` from `k` distinct bounded values. -/
private theorem range_perm_of_distinct {l : List Nat} {k : Nat}
    (hlen : l.length = k) (hnd : l.Nodup)
    (hbd : ∀ x ∈ l, x < k) : l.Perm (List.range k) :=
  perm_of_nodup_subset l (List.range k) hnd
    (fun x hx => List.mem_range.mpr (hbd x hx))
    (by rw [List.length_range, hlen]; exact Nat.le_refl _)

/-- A sum over `range k` rewritten through `k` distinct bounded
indices. -/
private theorem sum_range_of_distinct {l : List Nat} {k : Nat}
    (F : Nat → Nat) (hlen : l.length = k) (hnd : l.Nodup)
    (hbd : ∀ x ∈ l, x < k) :
    ((List.range k).map F).sum = (l.map F).sum :=
  (sum_of_perm ((range_perm_of_distinct hlen hnd hbd).map F)).symm

/-! # The generic setwise self-equivalence -/

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
    {σ : Renaming ctx.n}
    (hps : ptn.size = ctx.n) (hlsz : lab.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : LabInj lab ctx.n)
    (hset : ∀ p ∈ cells ptn level ctx.n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        σ.toFun lab[p.1 + o]! = lab[p.1 + o']!) :
    cellsPerm ptn level lab (lab.map σ.toFun) := by
  intro α len hIs
  rcases Decidable.em (α < ctx.n) with han | han
  · have hcross : α + len ≤ ctx.n := by
      have := isCell_no_cross hend hIs (by omega)
      omega
    have hlen0 : 0 < len := hIs.1
    have hmem : (α, α + len - 1) ∈ cells ptn level ctx.n :=
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
theorem stPerm_self_setwise {f : Nat → Nat} {st : RefineSt}
    {level : Nat}
    (hok : StOk ctx.n level st) (hinj : LabInj st.lab ctx.n)
    (hfb : ∀ v, v < ctx.n → f v < ctx.n)
    (hinvol : ∀ v, v < ctx.n → f (f v) = v)
    (hset : ∀ p ∈ cells st.ptn level ctx.n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        f st.lab[p.1 + o]! = st.lab[p.1 + o']!) :
    StPerm level st (mapSt (renamingOfFlip f ctx.n hfb hinvol) st) := by
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
    hok.labOk i (by rw [hok.labSize]; omega)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (st.lab.map _).size = st.lab.size
    rw [Array.size_map]
  · show cellsPerm st.ptn level st.lab
      (st.lab.map (renamingOfFlip f ctx.n hfb hinvol).toFun)
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

/-! # Bit invariance to rows

A value-level bit-invariant involution preserves the adjacency rows;
with the involution available no surjectivity is needed, since the
image bit at `z` reads off the bit at `f z`. -/

/-- Rows from value-level bit invariance. -/
theorem rows_of_bits {f : Nat → Nat}
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hfb : ∀ v, v < ctx.n → f v < ctx.n)
    (hinvol : ∀ v, v < ctx.n → f (f v) = v)
    (hbits : ∀ z z', z < ctx.n → z' < ctx.n →
      (ctx.g[f z]!).testBit (f z') = (ctx.g[z]!).testBit z') :
    ∀ v, v < ctx.n → ctx.g[f v]! = image f ctx.n ctx.g[v]! := by
  intro v hv
  refine Nat.eq_of_testBit_eq fun z => ?_
  rcases Decidable.em (z < ctx.n) with hz | hz
  · rw [testBit_image_invol hfb hinvol hz]
    have h := hbits v (f z) hv (hfb z hz)
    rw [hinvol z hz] at h
    exact h
  · have h1 : (ctx.g[f v]!).testBit z = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg _ (hfb v hv))
        (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, testBit_image]
    refine (List.any_eq_false.mpr fun w hw hcontra => ?_).symm
    have hwn := List.mem_range.mp hw
    rw [Bool.and_eq_true, beq_iff_eq] at hcontra
    have := hfb w hwn
    omega

/-! # The generic swaps

Up to three simultaneous transpositions of vertex values, with the
bit-invariance hypotheses each configuration discharges by counting.
The two-swap and three-swap forms take all participating values
distinct; the smaller forms are separate to keep the case analyses
readable. -/

private def sw1 (u v z : Nat) : Nat :=
  if z = u then v else if z = v then u else z

private theorem sw1_lt {n u v : Nat} (hun : u < n) (hvn : v < n) :
    ∀ z, z < n → sw1 u v z < n := by
  intro z hz
  rw [sw1]
  split
  · exact hvn
  · split
    · exact hun
    · exact hz

private theorem sw1_u {u v : Nat} : sw1 u v u = v := by
  rw [sw1, ite_eq_left rfl]

private theorem sw1_v {u v : Nat} (huv : u ≠ v) : sw1 u v v = u := by
  rw [sw1, ite_eq_right (fun h => huv h.symm), ite_eq_left rfl]

private theorem sw1_fix {u v z : Nat} (hzu : z ≠ u) (hzv : z ≠ v) :
    sw1 u v z = z := by
  rw [sw1, ite_eq_right hzu, ite_eq_right hzv]

private theorem sw1_invol {u v : Nat} (huv : u ≠ v) :
    ∀ z, sw1 u v (sw1 u v z) = z := by
  intro z
  rcases Decidable.em (z = u) with rfl | hzu
  · rw [sw1_u, sw1_v huv]
  rcases Decidable.em (z = v) with rfl | hzv
  · rw [sw1_v huv, sw1_u]
  · rw [sw1_fix hzu hzv, sw1_fix hzu hzv]

/-- Bit invariance of a single swap: every other vertex has equal bits
at the two swapped ones. -/
private theorem sw1_bits {u v : Nat}
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hun : u < ctx.n) (hvn : v < ctx.n) (huv : u ≠ v)
    (hfix : ∀ z, z < ctx.n → z ≠ u → z ≠ v →
      (ctx.g[z]!).testBit u = (ctx.g[z]!).testBit v) :
    ∀ z z', z < ctx.n → z' < ctx.n →
      (ctx.g[sw1 u v z]!).testBit (sw1 u v z') =
        (ctx.g[z]!).testBit z' := by
  intro z z' hz hz'
  rcases Decidable.em (z = u) with hzu | hzu
  · rw [hzu, sw1_u]
    rcases Decidable.em (z' = u) with hz'u | hz'u
    · rw [hz'u, sw1_u, hloop _ hvn, hloop _ hun]
    rcases Decidable.em (z' = v) with hz'v | hz'v
    · rw [hz'v, sw1_v huv]
      exact hsymm _ _ hvn hun
    · rw [sw1_fix hz'u hz'v, hsymm _ _ hvn hz', hsymm _ _ hun hz']
      exact (hfix z' hz' hz'u hz'v).symm
  rcases Decidable.em (z = v) with hzv | hzv
  · rw [hzv, sw1_v huv]
    rcases Decidable.em (z' = u) with hz'u | hz'u
    · rw [hz'u, sw1_u]
      exact hsymm _ _ hun hvn
    rcases Decidable.em (z' = v) with hz'v | hz'v
    · rw [hz'v, sw1_v huv, hloop _ hun, hloop _ hvn]
    · rw [sw1_fix hz'u hz'v, hsymm _ _ hun hz', hsymm _ _ hvn hz']
      exact hfix z' hz' hz'u hz'v
  · rw [sw1_fix hzu hzv]
    rcases Decidable.em (z' = u) with hz'u | hz'u
    · rw [hz'u, sw1_u]
      exact (hfix z hz hzu hzv).symm
    rcases Decidable.em (z' = v) with hz'v | hz'v
    · rw [hz'v, sw1_v huv]
      exact hfix z hz hzu hzv
    · rw [sw1_fix hz'u hz'v]

private def sw2 (u v x y z : Nat) : Nat :=
  if z = u then v else if z = v then u
  else if z = x then y else if z = y then x else z

section Sw2

variable {u v x y : Nat}

/-- The distinctness bundle of an active double swap. -/
private def Sw2Ok (n u v x y : Nat) : Prop :=
  u < n ∧ v < n ∧ x < n ∧ y < n ∧ u ≠ v ∧ u ≠ x ∧ u ≠ y ∧
    v ≠ x ∧ v ≠ y ∧ x ≠ y

private theorem sw2_u : sw2 u v x y u = v := by
  rw [sw2, ite_eq_left rfl]

private theorem sw2_v {n : Nat} (h : Sw2Ok n u v x y) :
    sw2 u v x y v = u := by
  obtain ⟨-, -, -, -, huv, -⟩ := h
  rw [sw2, ite_eq_right (fun hc => huv hc.symm), ite_eq_left rfl]

private theorem sw2_x {n : Nat} (h : Sw2Ok n u v x y) :
    sw2 u v x y x = y := by
  obtain ⟨-, -, -, -, -, hux, -, hvx, -⟩ := h
  rw [sw2, ite_eq_right (fun hc => hux hc.symm),
    ite_eq_right (fun hc => hvx hc.symm), ite_eq_left rfl]

private theorem sw2_y {n : Nat} (h : Sw2Ok n u v x y) :
    sw2 u v x y y = x := by
  obtain ⟨-, -, -, -, -, -, huy, -, hvy, hxy⟩ := h
  rw [sw2, ite_eq_right (fun hc => huy hc.symm),
    ite_eq_right (fun hc => hvy hc.symm),
    ite_eq_right (fun hc => hxy hc.symm), ite_eq_left rfl]

private theorem sw2_fix {z : Nat} (hzu : z ≠ u) (hzv : z ≠ v)
    (hzx : z ≠ x) (hzy : z ≠ y) : sw2 u v x y z = z := by
  rw [sw2, ite_eq_right hzu, ite_eq_right hzv, ite_eq_right hzx,
    ite_eq_right hzy]

private theorem sw2_lt {n : Nat} (h : Sw2Ok n u v x y) :
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

private theorem sw2_invol {n : Nat} (h : Sw2Ok n u v x y) :
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
private theorem sw2_bits
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (h : Sw2Ok ctx.n u v x y)
    (hfix : ∀ z, z < ctx.n → z ≠ u → z ≠ v → z ≠ x → z ≠ y →
      (ctx.g[z]!).testBit u = (ctx.g[z]!).testBit v ∧
      (ctx.g[z]!).testBit x = (ctx.g[z]!).testBit y)
    (hc1 : (ctx.g[u]!).testBit x = (ctx.g[v]!).testBit y)
    (hc2 : (ctx.g[u]!).testBit y = (ctx.g[v]!).testBit x) :
    ∀ z z', z < ctx.n → z' < ctx.n →
      (ctx.g[sw2 u v x y z]!).testBit (sw2 u v x y z') =
        (ctx.g[z]!).testBit z' := by
  obtain ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩ := h
  have hOk : Sw2Ok ctx.n u v x y :=
    ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩
  -- the four moved rows against an arbitrary second argument
  have key : ∀ z', z' < ctx.n →
      ((ctx.g[v]!).testBit (sw2 u v x y z') =
        (ctx.g[u]!).testBit z' ∧
       (ctx.g[u]!).testBit (sw2 u v x y z') =
        (ctx.g[v]!).testBit z') ∧
      ((ctx.g[y]!).testBit (sw2 u v x y z') =
        (ctx.g[x]!).testBit z' ∧
       (ctx.g[x]!).testBit (sw2 u v x y z') =
        (ctx.g[y]!).testBit z') := by
    intro z' hz'
    rcases Decidable.em (z' = u) with hz'u | hz'u
    · rw [hz'u, sw2_u]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hloop _ hvn, hloop _ hun]
      · exact hsymm _ _ hun hvn
      · rw [hsymm _ _ hyn hvn, hsymm _ _ hxn hun]
        exact hc1.symm
      · rw [hsymm _ _ hxn hvn, hsymm _ _ hyn hun]
        exact hc2.symm
    rcases Decidable.em (z' = v) with hz'v | hz'v
    · rw [hz'v, sw2_v hOk]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact hsymm _ _ hvn hun
      · rw [hloop _ hun, hloop _ hvn]
      · rw [hsymm _ _ hyn hun, hsymm _ _ hxn hvn]
        exact hc2
      · rw [hsymm _ _ hxn hun, hsymm _ _ hyn hvn]
        exact hc1
    rcases Decidable.em (z' = x) with hz'x | hz'x
    · rw [hz'x, sw2_x hOk]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact hc1.symm
      · exact hc2
      · rw [hloop _ hyn, hloop _ hxn]
      · exact hsymm _ _ hxn hyn
    rcases Decidable.em (z' = y) with hz'y | hz'y
    · rw [hz'y, sw2_y hOk]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact hc2.symm
      · exact hc1
      · exact hsymm _ _ hyn hxn
      · rw [hloop _ hxn, hloop _ hyn]
    · rw [sw2_fix hz'u hz'v hz'x hz'y]
      obtain ⟨hf1, hf2⟩ := hfix z' hz' hz'u hz'v hz'x hz'y
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hsymm _ _ hvn hz', hsymm _ _ hun hz']
        exact hf1.symm
      · rw [hsymm _ _ hun hz', hsymm _ _ hvn hz']
        exact hf1
      · rw [hsymm _ _ hyn hz', hsymm _ _ hxn hz']
        exact hf2.symm
      · rw [hsymm _ _ hxn hz', hsymm _ _ hyn hz']
        exact hf2
  intro z z' hz hz'
  rcases Decidable.em (z = u) with hzu | hzu
  · rw [hzu, sw2_u]
    exact (key z' hz').1.1
  rcases Decidable.em (z = v) with hzv | hzv
  · rw [hzv, sw2_v hOk]
    exact (key z' hz').1.2
  rcases Decidable.em (z = x) with hzx | hzx
  · rw [hzx, sw2_x hOk]
    exact (key z' hz').2.1
  rcases Decidable.em (z = y) with hzy | hzy
  · rw [hzy, sw2_y hOk]
    exact (key z' hz').2.2
  · rw [sw2_fix hzu hzv hzx hzy]
    obtain ⟨hf1, hf2⟩ := hfix z hz hzu hzv hzx hzy
    rcases Decidable.em (z' = u) with hz'u | hz'u
    · rw [hz'u, sw2_u]
      exact hf1.symm
    rcases Decidable.em (z' = v) with hz'v | hz'v
    · rw [hz'v, sw2_v hOk]
      exact hf1
    rcases Decidable.em (z' = x) with hz'x | hz'x
    · rw [hz'x, sw2_x hOk]
      exact hf2.symm
    rcases Decidable.em (z' = y) with hz'y | hz'y
    · rw [hz'y, sw2_y hOk]
      exact hf2
    · rw [sw2_fix hz'u hz'v hz'x hz'y]

end Sw2

end Hex.GraphIso.Nauty
