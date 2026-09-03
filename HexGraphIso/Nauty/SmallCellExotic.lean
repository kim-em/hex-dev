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

/-! # The flip-data assembly

A raw bit-invariant involution permuting every cell's members within
the cell packages into the renaming, rows map and state
self-equivalence the deviation doors consume. -/

private theorem flip_data_of_bits {st : RefineSt} {level : Nat}
    {f : Nat → Nat}
    (hIt : IterOk ctx level st) (hgsz : ctx.g.size = ctx.n)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hfb : ∀ w, w < ctx.n → f w < ctx.n)
    (hinvol : ∀ w, w < ctx.n → f (f w) = w)
    (hbits : ∀ z z', z < ctx.n → z' < ctx.n →
      (ctx.g[f z]!).testBit (f z') = (ctx.g[z]!).testBit z')
    (hset : ∀ p ∈ cells st.ptn level ctx.n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        f st.lab[p.1 + o]! = st.lab[p.1 + o']!) :
    ∃ σ : Renaming ctx.n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      ∀ i, i < ctx.n → σ.toFun st.lab[i]! = f st.lab[i]! := by
  refine ⟨renamingOfFlip f ctx.n hfb hinvol, ?_, ?_, ?_⟩
  · exact rowsMap_of_flip_rows hgsz hfb hinvol
      (rows_of_bits hg hfb hinvol hbits)
  · exact stPerm_self_setwise hIt.ok hIt.inj hfb hinvol hset
  · intro i hi
    exact renamingOfFlip_at hfb hinvol
      (hIt.ok.labOk i (by rw [hIt.ok.labSize]; omega))

/-! # Position and counting toolkit for the configurations -/

private theorem mem_erase_nodup :
    ∀ {l : List Nat}, l.Nodup → ∀ a w,
      (w ∈ l.erase a ↔ w ∈ l ∧ w ≠ a)
  | [], _, a, w => by simp
  | b :: t, hnd, a, w => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      constructor
      · intro hw
        exact ⟨List.mem_cons_of_mem _ hw,
          fun hcon => hnd.1 (hcon ▸ hw)⟩
      · rintro ⟨hw, hne⟩
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact absurd rfl hne
        · exact hmem
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba)]
      rw [List.mem_cons, List.mem_cons,
        mem_erase_nodup hnd.2 a w]
      constructor
      · rintro (rfl | ⟨hw, hne⟩)
        · exact ⟨Or.inl rfl, hba⟩
        · exact ⟨Or.inr hw, hne⟩
      · rintro ⟨rfl | hw, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hw, hne⟩

/-- Two cells of the partition list sharing a position coincide. -/
private theorem cells_eq_of_shared {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {p q : Nat × Nat} (hp : p ∈ cells ptn level nn)
    (hq : q ∈ cells ptn level nn)
    {j : Nat} (hjp1 : p.1 ≤ j) (hjp2 : j ≤ p.2)
    (hjq1 : q.1 ≤ j) (hjq2 : j ≤ q.2) : p = q := by
  have hIp := cells_isCell hnn hend _ hp
  have hIq := cells_isCell hnn hend _ hq
  have hple := cells_le _ hp
  have hqle := cells_le _ hq
  rcases isCell_disj_or_eq hIp hIq with ⟨h1, h2⟩ | hd | hd
  · obtain ⟨pa, pb⟩ := p
    obtain ⟨qa, qb⟩ := q
    simp only at h1 h2 hple hqle
    have : pb = qb := by omega
    rw [h1, this]
  · omega
  · omega

/-- The count of one row into a singleton cell is its bit there, so
equitability makes the bits of all members of a cell agree at every
singleton-cell vertex. -/
private theorem cell_const_into_singleton {lab ptn : Array Nat}
    {level : Nat}
    (hE : Equitable ctx level lab ptn)
    {tc te : Nat} (hC : (tc, te) ∈ cells ptn level ctx.n)
    {s : Nat} (hS : (s, s) ∈ cells ptn level ctx.n)
    {o o' : Nat} (ho : o ≤ te - tc) (ho' : o' ≤ te - tc) :
    (ctx.g[lab[tc + o]!]!).testBit lab[s]! =
      (ctx.g[lab[tc + o']!]!).testBit lab[s]! := by
  have hle : tc ≤ te := cells_le _ hC
  have h := hE _ hC _ hS o o' (by omega) (by omega)
  rw [worksetOf_singleton, popCount_and_single,
    popCount_and_single] at h
  rcases hb : (ctx.g[lab[tc + o]!]!).testBit lab[s]! with _ | _ <;>
    rcases hb' : (ctx.g[lab[tc + o']!]!).testBit lab[s]! with _ | _ <;>
      rw [hb, hb'] at h <;> simp_all

/-! # The single-nontrivial-cell configurations

With every other cell a singleton, the flip at a target cell of size
at most five is a transposition of the two chosen members, together
with the crossed transposition of the differ pair when the counting
classification produces one. -/

section OneCell

variable {st : RefineSt} {level tc te oU oV : Nat}

/-- The transposition route: every other window member has equal bits
at the two swapped ones. -/
private theorem oneCell_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = ctx.n)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level ctx.n)
    (hsing : ∀ q ∈ cells st.ptn level ctx.n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hAllEq : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV →
      (ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + oV]!) :
    ∃ σ : Renaming ctx.n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hun : st.lab[tc + oU]! < ctx.n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < ctx.n := hlb _ (by omega)
  have huv : st.lab[tc + oU]! ≠ st.lab[tc + oV]! := by
    intro hcon
    have := hinj (tc + oU) (tc + oV) (by omega) (by omega) hcon
    omega
  -- every other reachable vertex has equal bits at the pair
  have hfix : ∀ z, z < ctx.n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! →
      (ctx.g[z]!).testBit st.lab[tc + oU]! =
        (ctx.g[z]!).testBit st.lab[tc + oV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := ctx.n) j (by omega)
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · -- j sits in the target window
      have hw : j - tc ≤ te - tc := by
        have h2 : j ≤ te := hj2
        omega
      have hwu : j - tc ≠ oU := by
        intro hcon
        refine hzu ?_
        have h1 : tc ≤ j := hj1
        have : j = tc + oU := by omega
        rw [this]
      have hwv : j - tc ≠ oV := by
        intro hcon
        refine hzv ?_
        have h1 : tc ≤ j := hj1
        have : j = tc + oV := by omega
        rw [this]
      have h := hAllEq (j - tc) hw hwu hwv
      have h1 : tc ≤ j := hj1
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    · -- j sits in a singleton cell
      have hps : p.2 = p.1 := hsing p hp hpC
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level ctx.n := by
        have : p = (p.1, p.1) := by
          obtain ⟨pa, pb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      have hconst := cell_const_into_singleton hE hC hpmem hoU hoV
      rw [← hjp] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
      exact hconst
  -- the swap permutes every cell within itself
  have hset : ∀ p ∈ cells st.ptn level ctx.n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    intro p hp o ho
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · have ho' : o < te + 1 - tc := ho
      rcases Decidable.em (o = oU) with rfl | hou
      · exact ⟨oV, show oV < te + 1 - tc by omega,
          show sw1 _ _ st.lab[tc + o]! = st.lab[tc + oV]! by
            rw [sw1_u]⟩
      · rcases Decidable.em (o = oV) with rfl | hov
        · exact ⟨oU, show oU < te + 1 - tc by omega,
            show sw1 _ _ st.lab[tc + o]! = st.lab[tc + oU]! by
              rw [sw1_v huv]⟩
        · refine ⟨o, ho, sw1_fix ?_ ?_⟩
          · intro hcon
            have := hinj (tc + o) (tc + oU) (by omega) (by omega) hcon
            omega
          · intro hcon
            have := hinj (tc + o) (tc + oV) (by omega) (by omega) hcon
            omega
    · -- a singleton cell: its member is fixed
      have hps : p.2 = p.1 := hsing p hp hpC
      have ho1 : o = 0 := by omega
      refine ⟨o, ho, ?_⟩
      have hbd : p.1 < ctx.n := by
        have h1 := cells_bound (by rw [hpsz]; exact Nat.le_refl _)
          hend _ hp
        have h2 := cells_le _ hp
        rw [hpsz] at h1
        omega
      refine sw1_fix ?_ ?_
      · intro hcon
        have := hinj (p.1 + o) (tc + oU) (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpC (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hC
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      · intro hcon
        have := hinj (p.1 + o) (tc + oV) (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpC (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hC
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[tc + oU]! st.lab[tc + oV]!) hIt hgsz hg
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw1_u]

set_option maxHeartbeats 4000000 in
/-- The crossed-pair route: the two chosen members swap together with
the differ pair, every other window member having equal bits at both
pairs. -/
private theorem oneCell_sw2 {wa wb : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = ctx.n)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level ctx.n)
    (hsing : ∀ q ∈ cells st.ptn level ctx.n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hwa : wa ≤ te - tc) (hwb : wb ≤ te - tc) (hab : wa ≠ wb)
    (hau : wa ≠ oU) (hav : wa ≠ oV) (hbu : wb ≠ oU) (hbv : wb ≠ oV)
    (htau : (ctx.g[st.lab[tc + wa]!]!).testBit st.lab[tc + oU]! =
      true)
    (htav : (ctx.g[st.lab[tc + wa]!]!).testBit st.lab[tc + oV]! =
      false)
    (htbu : (ctx.g[st.lab[tc + wb]!]!).testBit st.lab[tc + oU]! =
      false)
    (htbv : (ctx.g[st.lab[tc + wb]!]!).testBit st.lab[tc + oV]! =
      true)
    (hRestEq : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV → w ≠ wa → w ≠ wb →
      (ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + oV]!)
    (hWfix : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV → w ≠ wa → w ≠ wb →
      (ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + wa]! =
        (ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + wb]!) :
    ∃ σ : Renaming ctx.n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hvne : ∀ w w' : Nat, w ≤ te - tc → w' ≤ te - tc → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hOk : Sw2Ok ctx.n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + wa]! st.lab[tc + wb]! :=
    ⟨hlb _ (by omega), hlb _ (by omega), hlb _ (by omega),
      hlb _ (by omega), hvne _ _ hoU hoV hne,
      hvne _ _ hoU hwa (fun h => hau h.symm),
      hvne _ _ hoU hwb (fun h => hbu h.symm),
      hvne _ _ hoV hwa (fun h => hav h.symm),
      hvne _ _ hoV hwb (fun h => hbv h.symm),
      hvne _ _ hwa hwb hab⟩
  obtain ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩ := hOk
  have hOk2 : Sw2Ok ctx.n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + wa]! st.lab[tc + wb]! :=
    ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩
  -- fixed vertices have equal bits at both pairs
  have hfix : ∀ z, z < ctx.n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + wa]! →
      z ≠ st.lab[tc + wb]! →
      (ctx.g[z]!).testBit st.lab[tc + oU]! =
        (ctx.g[z]!).testBit st.lab[tc + oV]! ∧
      (ctx.g[z]!).testBit st.lab[tc + wa]! =
        (ctx.g[z]!).testBit st.lab[tc + wb]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := ctx.n) j (by omega)
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ te := hj2
      have hw : j - tc ≤ te - tc := by omega
      have hwneq : ∀ w' : Nat, w' ≤ te - tc →
          st.lab[j]! ≠ st.lab[tc + w']! → j - tc ≠ w' := by
        intro w' hw' hne' hcon
        exact hne' (by rw [show j = tc + w' by omega])
      have hwu := hwneq oU hoU hzu
      have hwv := hwneq oV hoV hzv
      have hwx := hwneq wa hwa hzx
      have hwy := hwneq wb hwb hzy
      have hr := hRestEq (j - tc) hw hwu hwv hwx hwy
      have hf := hWfix (j - tc) hw hwu hwv hwx hwy
      rw [show tc + (j - tc) = j by omega] at hr hf
      exact ⟨hr, hf⟩
    · have hps : p.2 = p.1 := hsing p hp hpC
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level ctx.n := by
        have : p = (p.1, p.1) := by
          obtain ⟨pa, pb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      constructor
      · have hconst := cell_const_into_singleton hE hC hpmem hoU hoV
        rw [← hjp] at hconst
        rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
        rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
        rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
        exact hconst
      · have hconst := cell_const_into_singleton hE hC hpmem hwa hwb
        rw [← hjp] at hconst
        rw [hsymm _ _ hz hxn, hsymm _ _ hz hyn]
        rw [hsymm _ _ hxn hz, hsymm _ _ hyn hz] at hconst
        rw [hsymm _ _ hz hxn, hsymm _ _ hz hyn] at hconst
        exact hconst
  -- the cross bits between the two pairs match diagonally
  have hc1 : (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[tc + wa]! =
      (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[tc + wb]! := by
    rw [hsymm _ _ hun hxn, hsymm _ _ hvn hyn, htau, htbv]
  have hc2 : (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[tc + wb]! =
      (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[tc + wa]! := by
    rw [hsymm _ _ hun hyn, hsymm _ _ hvn hxn, htbu, htav]
  -- the double swap permutes every cell within itself
  have hset : ∀ p ∈ cells st.ptn level ctx.n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + wa]!
          st.lab[tc + wb]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    intro p hp o ho
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · have ho' : o < te + 1 - tc := ho
      rcases Decidable.em (o = oU) with rfl | hou
      · refine ⟨oV, show oV < te + 1 - tc by omega, ?_⟩
        rw [sw2_u]
      rcases Decidable.em (o = oV) with rfl | hov
      · refine ⟨oU, show oU < te + 1 - tc by omega, ?_⟩
        rw [sw2_v hOk2]
      rcases Decidable.em (o = wa) with rfl | hoa
      · refine ⟨wb, show wb < te + 1 - tc by omega, ?_⟩
        rw [sw2_x hOk2]
      rcases Decidable.em (o = wb) with rfl | hob
      · refine ⟨wa, show wa < te + 1 - tc by omega, ?_⟩
        rw [sw2_y hOk2]
      · refine ⟨o, ho, sw2_fix (hvne o oU (by omega) hoU hou)
          (hvne o oV (by omega) hoV hov)
          (hvne o wa (by omega) hwa hoa)
          (hvne o wb (by omega) hwb hob)⟩
    · have hps : p.2 = p.1 := hsing p hp hpC
      have ho1 : o = 0 := by omega
      have hbd : p.1 < ctx.n := by
        have h1 := cells_bound (by rw [hpsz]; exact Nat.le_refl _)
          hend _ hp
        have h2 := cells_le _ hp
        rw [hpsz] at h1
        omega
      have hother : ∀ w' : Nat, w' ≤ te - tc →
          st.lab[p.1 + o]! ≠ st.lab[tc + w']! := by
        intro w' hw' hcon
        have := hinj (p.1 + o) (tc + w') (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpC (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hC
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      exact ⟨o, ho, sw2_fix (hother oU hoU) (hother oV hoV)
        (hother wa hwa) (hother wb hwb)⟩
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + wa]!
      st.lab[tc + wb]!) hIt hgsz hg
    (sw2_lt hOk2) (fun w _ => sw2_invol hOk2 w)
    (sw2_bits hsymm hloop hOk2 hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

private theorem nodup_erase :
    ∀ {l : List Nat}, l.Nodup → ∀ a, (l.erase a).Nodup
  | [], _, _ => by simp
  | b :: t, hnd, a => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      exact hnd.2
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba),
        List.nodup_cons]
      refine ⟨fun hmem => ?_, nodup_erase hnd.2 a⟩
      exact hnd.1 ((mem_erase_nodup hnd.2 a b).mp hmem).1

private theorem nodup_subset_length :
    ∀ (l r : List Nat), l.Nodup → (∀ x ∈ l, x ∈ r) →
      l.length ≤ r.length
  | [], r, _, _ => by simp
  | a :: t, r, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ r := hsub a List.mem_cons_self
    have hlen := (List.perm_cons_erase ha).length_eq
    have hsub' : ∀ x ∈ t, x ∈ r.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun hcon => hnd.1
        (by rw [← hcon]; exact hx))).mpr
        (hsub x (List.mem_cons_of_mem _ hx))
    have h := nodup_subset_length t (r.erase a) hnd.2 hsub'
    simp only [List.length_cons] at hlen ⊢
    omega

set_option maxHeartbeats 1000000 in
/-- In a five-member window, the member outside a crossed pair has
equal bits at the pair: the pair's two row sums expand over the five
named offsets, the crossed types cancel, and the shared internal bit
cancels by symmetry. -/
private theorem oneCell_wfix {wa wb wf : Nat}
    (hIt : IterOk ctx level st)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level ctx.n)
    (hm : te + 1 - tc = 5)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hwa : wa ≤ te - tc) (hwb : wb ≤ te - tc) (hwf : wf ≤ te - tc)
    (hab : wa ≠ wb) (haf : wa ≠ wf) (hbf : wb ≠ wf)
    (hau : wa ≠ oU) (hav : wa ≠ oV) (hbu : wb ≠ oU) (hbv : wb ≠ oV)
    (hfu : wf ≠ oU) (hfv : wf ≠ oV)
    (htau : (ctx.g[st.lab[tc + wa]!]!).testBit st.lab[tc + oU]! =
      true)
    (htav : (ctx.g[st.lab[tc + wa]!]!).testBit st.lab[tc + oV]! =
      false)
    (htbu : (ctx.g[st.lab[tc + wb]!]!).testBit st.lab[tc + oU]! =
      false)
    (htbv : (ctx.g[st.lab[tc + wb]!]!).testBit st.lab[tc + oV]! =
      true) :
    (ctx.g[st.lab[tc + wf]!]!).testBit st.lab[tc + wa]! =
      (ctx.g[st.lab[tc + wf]!]!).testBit st.lab[tc + wb]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hnd : ([oU, oV, wa, wb, wf] : List Nat).Nodup := by
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro (h | h | h | h | h) <;> omega
    · rintro (h | h | h | h) <;> omega
    · rintro (h | h | h) <;> omega
    · rintro (h | h) <;> omega
    · simp
  have hbd : ∀ x ∈ ([oU, oV, wa, wb, wf] : List Nat),
      x < te + 1 - tc := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have hxf : x = wf := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  have hcic : ∀ o : Nat, o ≤ te - tc →
      popCount (worksetOf st.lab tc te &&&
          ctx.g[st.lab[tc + o]!]!) =
        ((List.range (te + 1 - tc)).map fun w =>
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w]!).sum := by
    intro o ho
    exact count_into_cell hpsz hend hinj hlb hC
      (hg _ (hlb _ (by omega)))
  have hrow := hE _ hC _ hC wa wb (by omega) (by omega)
  rw [hcic wa hwa, hcic wb hwb, hm] at hrow
  rw [sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd),
    sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd)] at hrow
  simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hrow
  have hloopa : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wa]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hloopb : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wb]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsymab : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wb]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wa]! :=
    bitCnt_inj.mpr (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have h1 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oU]! = 1 :=
    bitCnt_eq_one.mpr htau
  have h2 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oV]! = 0 :=
    bitCnt_eq_zero.mpr htav
  have h3 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oU]! = 0 :=
    bitCnt_eq_zero.mpr htbu
  have h4 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oV]! = 1 :=
    bitCnt_eq_one.mpr htbv
  have hkey : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wf]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wf]! := by
    omega
  have hbit := bitCnt_inj.mp hkey
  rw [hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wa) (by omega)),
    hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wb) (by omega))]
  exact hbit

end OneCell

end Hex.GraphIso.Nauty
