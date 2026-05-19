import HexPolyFp.Basic

/-!
Finite enumerations of bounded-degree `FpPoly` values.

The quotient-cardinality arguments need a Mathlib-free way to list all
canonical representatives with degree below a fixed bound.  This module
enumerates fixed-length coefficient vectors over `ZMod64 p` and maps them to
normalized dense polynomials.
-/

namespace Hex
namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

namespace Enumeration

private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hxy' : x = y := hinj x (by simp) y (by simp [hy]) hxy.symm
        exact hxs.1 (by simpa [hxy'] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

private theorem nodup_flatMap_of_disjoint
    {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup)
    (hrow : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisj :
      ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
        ∀ z, z ∈ f x → z ∈ f y → False) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hrow x (by simp), ?_, ?_⟩
      · exact ih hxs.2
          (by intro y hy; exact hrow y (by simp [hy]))
          (by
            intro y hy z hz hyz t hty htz
            exact hdisj y (by simp [hy]) z (by simp [hz]) hyz t hty htz)
      · intro a ha b hb hab
        rcases List.mem_flatMap.mp hb with ⟨y, hy, hby⟩
        exact hdisj x (by simp) y (by simp [hy]) (by
          intro hxy
          exact hxs.1 (hxy ▸ hy)) a ha (hab ▸ hby)

/-- All coefficient lists of length `d`, with entries ranging over `ZMod64 p`. -/
def coeffLists (p : Nat) [ZMod64.Bounds p] : Nat → List (List (ZMod64 p))
  | 0 => [[]]
  | d + 1 =>
      (ZMod64.values p).flatMap fun c =>
        (coeffLists p d).map fun coeffs => c :: coeffs

@[simp] theorem coeffLists_zero :
    coeffLists p 0 = ([[]] : List (List (ZMod64 p))) :=
  rfl

@[simp] theorem coeffLists_succ (d : Nat) :
    coeffLists p (d + 1) =
      (ZMod64.values p).flatMap fun c =>
        (coeffLists p d).map fun coeffs => c :: coeffs :=
  rfl

/-- Every list produced by `coeffLists p d` has length exactly `d`. -/
theorem length_of_mem_coeffLists {d : Nat} {coeffs : List (ZMod64 p)}
    (hmem : coeffs ∈ coeffLists p d) :
    coeffs.length = d := by
  induction d generalizing coeffs with
  | zero =>
      simpa [coeffLists] using hmem
  | succ d ih =>
      rw [coeffLists_succ] at hmem
      rcases List.mem_flatMap.mp hmem with ⟨c, _hc, htail⟩
      rcases List.mem_map.mp htail with ⟨tail, htail_mem, hcoeffs⟩
      subst coeffs
      simp [ih htail_mem]

/-- Membership in `coeffLists` is exactly fixed length plus residue membership. -/
theorem mem_coeffLists_iff {d : Nat} {coeffs : List (ZMod64 p)} :
    coeffs ∈ coeffLists p d ↔
      coeffs.length = d ∧ ∀ c ∈ coeffs, c ∈ ZMod64.values p := by
  induction d generalizing coeffs with
  | zero =>
      constructor
      · intro h
        have hnil : coeffs = [] := by simpa [coeffLists] using h
        subst coeffs
        simp
      · intro h
        have hnil : coeffs = [] := List.eq_nil_of_length_eq_zero h.1
        subst coeffs
        simp [coeffLists]
  | succ d ih =>
      constructor
      · intro h
        rw [coeffLists_succ] at h
        rcases List.mem_flatMap.mp h with ⟨c, hc, htail⟩
        rcases List.mem_map.mp htail with ⟨tail, htail_mem, hcoeffs⟩
        subst coeffs
        have htail := (ih (coeffs := tail)).mp htail_mem
        constructor
        · simp [htail.1]
        · intro x hx
          cases hx with
          | head =>
            exact hc
          | tail _ hx =>
            exact htail.2 x hx
      · intro h
        cases coeffs with
        | nil =>
            simp at h
        | cons c tail =>
            rw [coeffLists_succ]
            apply List.mem_flatMap.mpr
            refine ⟨c, h.2 c (by simp), ?_⟩
            apply List.mem_map.mpr
            refine ⟨tail, ?_, rfl⟩
            apply (ih (coeffs := tail)).mpr
            constructor
            · simpa using Nat.succ.inj h.1
            · intro x hx
              exact h.2 x (by simp [hx])

/-- The coefficient-list enumeration has exactly `p ^ d` entries. -/
@[simp] theorem coeffLists_length (d : Nat) :
    (coeffLists p d).length = p ^ d := by
  induction d with
  | zero =>
      simp [coeffLists]
  | succ d ih =>
      rw [coeffLists_succ]
      calc
        ((ZMod64.values p).flatMap fun _c =>
            (coeffLists p d).map fun coeffs => _c :: coeffs).length =
            (ZMod64.values p).length * (coeffLists p d).length := by
              induction (ZMod64.values p) with
              | nil => simp
              | cons c cs ihcs =>
                  simp [ihcs, Nat.add_mul, Nat.add_comm]
        _ = p * p ^ d := by simp [ih]
        _ = p ^ (d + 1) := by
          rw [Nat.pow_succ]
          exact Nat.mul_comm p (p ^ d)

private theorem coeffLists_nodup_cons_branch
    {c : ZMod64 p} {tail : List (ZMod64 p)}
    (hmem : tail ∈ coeffLists p d) :
    c :: tail ∈ (coeffLists p d).map fun coeffs => c :: coeffs := by
  exact List.mem_map.mpr ⟨tail, hmem, rfl⟩

/-- The fixed-length coefficient-list enumeration has no duplicate lists. -/
theorem coeffLists_nodup (d : Nat) :
    (coeffLists p d).Nodup := by
  induction d with
  | zero =>
      simp [coeffLists]
  | succ d ih =>
      rw [coeffLists_succ]
      apply nodup_flatMap_of_disjoint
      · exact ZMod64.values_nodup (p := p)
      · intro c _hc
        apply nodup_map_of_injective
        · exact ih
        · intro a _ha b _hb h
          exact List.cons.inj h |>.2
      · intro c hc c' hc' hne x hx hx'
        rcases List.mem_map.mp hx with ⟨tail, _htail, hxtail⟩
        rcases List.mem_map.mp hx' with ⟨tail', _htail', hxtail'⟩
        subst x
        have hhead : c = c' := (List.cons.inj hxtail' |>.1).symm
        exact hne hhead

/-- Turn a fixed coefficient list into an `FpPoly`. -/
def ofCoeffList (coeffs : List (ZMod64 p)) : FpPoly p :=
  FpPoly.ofCoeffs coeffs.toArray

/-- All `FpPoly p` values whose degree is below `d`, represented by length-`d`
coefficient lists. -/
def polysBelowDegree (p : Nat) [ZMod64.Bounds p] (d : Nat) : List (FpPoly p) :=
  (coeffLists p d).map ofCoeffList

private theorem list_getD_map_range {α : Type} [Zero α] (d n : Nat) (f : Nat → α) :
    ((List.range d).map f).getD n 0 =
      if n < d then f n else 0 := by
  by_cases hn : n < d
  · simp [hn, List.getD]
  · simp [hn, List.getD]

private theorem size_le_of_degree_getD_lt {f : FpPoly p} {d : Nat}
    (hdeg : f.degree?.getD 0 < d) :
    f.size ≤ d := by
  by_cases hsize : f.size = 0
  · omega
  · have hdeg_eq : f.degree?.getD 0 = f.size - 1 := by
      simp [DensePoly.degree?, hsize]
    omega

/-- The polynomial built from its first `d` coefficients is the original
polynomial when the original degree is below `d`. -/
theorem of_first_coeffs_eq_of_degree_getD_lt {f : FpPoly p} {d : Nat}
    (hdeg : f.degree?.getD 0 < d) :
    ofCoeffList ((List.range d).map fun i => f.coeff i) = f := by
  apply DensePoly.ext_coeff
  intro n
  unfold ofCoeffList FpPoly.ofCoeffs
  rw [DensePoly.coeff_ofCoeffs_list]
  change ((List.range d).map (fun i => f.coeff i)).getD n 0 = f.coeff n
  have hget :
      ((List.range d).map (fun i => f.coeff i)).getD n 0 =
        if n < d then f.coeff n else 0 := by
    simpa using (list_getD_map_range (α := ZMod64 p) d n (fun i => f.coeff i))
  rw [hget]
  by_cases hn : n < d
  · simp [hn]
  · have hsize_le : f.size ≤ d := size_le_of_degree_getD_lt hdeg
    have hn_size : f.size ≤ n := Nat.le_trans hsize_le (Nat.le_of_not_gt hn)
    rw [if_neg hn]
    exact (DensePoly.coeff_eq_zero_of_size_le f hn_size).symm

/-- Every polynomial with degree below `d` appears in the bounded-degree list. -/
theorem mem_polysBelowDegree_of_degree_getD_lt {f : FpPoly p} {d : Nat}
    (hdeg : f.degree?.getD 0 < d) :
    f ∈ polysBelowDegree p d := by
  unfold polysBelowDegree
  apply List.mem_map.mpr
  let coeffs : List (ZMod64 p) := (List.range d).map fun i => f.coeff i
  refine ⟨coeffs, ?_, ?_⟩
  · apply (mem_coeffLists_iff (p := p) (d := d) (coeffs := coeffs)).mpr
    constructor
    · simp [coeffs]
    · intro c hc
      rcases List.mem_map.mp hc with ⟨i, _hi, rfl⟩
      exact ZMod64.mem_values (f.coeff i)
  · exact of_first_coeffs_eq_of_degree_getD_lt hdeg

private theorem ofCoeffList_degree_getD_lt_of_length_eq
    {coeffs : List (ZMod64 p)} {d : Nat}
    (hd : 0 < d) (hlen : coeffs.length = d) :
    (ofCoeffList coeffs).degree?.getD 0 < d := by
  have hzero_ge : ∀ i, d ≤ i → (ofCoeffList coeffs).coeff i = 0 := by
    intro i hi
    unfold ofCoeffList FpPoly.ofCoeffs
    rw [DensePoly.coeff_ofCoeffs_list]
    have hlen_le : coeffs.length ≤ i := by omega
    change coeffs.getD i (0 : ZMod64 p) = (0 : ZMod64 p)
    simp [List.getD, hlen_le]
  have hsize_le : (ofCoeffList coeffs).size ≤ d := by
    by_cases hle : (ofCoeffList coeffs).size ≤ d
    · exact hle
    · exfalso
      have hd_lt_size : d < (ofCoeffList coeffs).size := Nat.lt_of_not_ge hle
      let i := (ofCoeffList coeffs).size - 1
      have hi_ge : d ≤ i := by omega
      have hi_pos : 0 < (ofCoeffList coeffs).size := by omega
      have hzero : (ofCoeffList coeffs).coeff i = 0 := hzero_ge i hi_ge
      have hne : (ofCoeffList coeffs).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (ofCoeffList coeffs) hi_pos
      exact hne hzero
  by_cases hsize : (ofCoeffList coeffs).size = 0
  · simp [DensePoly.degree?, hsize, hd]
  · have hdeg : (ofCoeffList coeffs).degree?.getD 0 =
        (ofCoeffList coeffs).size - 1 := by
      simp [DensePoly.degree?, hsize]
    rw [hdeg]
    omega

/-- Every polynomial in the bounded-degree enumeration has degree below the
bound, provided the bound is positive. -/
theorem degree_getD_lt_of_mem_polysBelowDegree {f : FpPoly p} {d : Nat}
    (hd : 0 < d) (hmem : f ∈ polysBelowDegree p d) :
    f.degree?.getD 0 < d := by
  unfold polysBelowDegree at hmem
  rcases List.mem_map.mp hmem with ⟨coeffs, hcoeffs, hf⟩
  rw [← hf]
  exact ofCoeffList_degree_getD_lt_of_length_eq hd
    (length_of_mem_coeffLists hcoeffs)

/-- Membership in the bounded-degree enumeration is exactly the degree bound,
provided the bound is positive. -/
theorem mem_polysBelowDegree_iff_degree_getD_lt {f : FpPoly p} {d : Nat}
    (hd : 0 < d) :
    f ∈ polysBelowDegree p d ↔ f.degree?.getD 0 < d := by
  constructor
  · exact degree_getD_lt_of_mem_polysBelowDegree hd
  · exact mem_polysBelowDegree_of_degree_getD_lt

@[simp] theorem mem_polysBelowDegree_succ_iff_degree_getD_lt {f : FpPoly p} {d : Nat} :
    f ∈ polysBelowDegree p (d + 1) ↔ f.degree?.getD 0 < d + 1 :=
  mem_polysBelowDegree_iff_degree_getD_lt (Nat.succ_pos d)

private theorem list_eq_of_length_eq_of_getD_eq
    {α : Type} [Zero α] {xs ys : List α}
    (hlen : xs.length = ys.length)
    (hget : ∀ i, i < xs.length → xs.getD i 0 = ys.getD i 0) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hhead : x = y := by
            have h := hget 0 (by simp)
            simpa using h
          have hlen_tail : xs.length = ys.length := Nat.succ.inj hlen
          have htail : xs = ys := by
            apply ih hlen_tail
            intro i hi
            have h := hget (i + 1) (by simp [hi])
            simpa using h
          rw [hhead, htail]

private theorem coeffList_eq_of_ofCoeffList_eq
    {d : Nat} {xs ys : List (ZMod64 p)}
    (hxs : xs.length = d) (hys : ys.length = d)
    (hpoly : ofCoeffList xs = ofCoeffList ys) :
    xs = ys := by
  apply list_eq_of_length_eq_of_getD_eq
  · exact hxs.trans hys.symm
  · intro i hi
    have hcoeff := congrArg (fun f : FpPoly p => f.coeff i) hpoly
    unfold ofCoeffList FpPoly.ofCoeffs at hcoeff
    change (DensePoly.ofCoeffs xs.toArray).coeff i =
      (DensePoly.ofCoeffs ys.toArray).coeff i at hcoeff
    rw [DensePoly.coeff_ofCoeffs_list, DensePoly.coeff_ofCoeffs_list] at hcoeff
    exact hcoeff

/-- The bounded-degree polynomial enumeration has no duplicate polynomial
values. -/
theorem polysBelowDegree_nodup (d : Nat) :
    (polysBelowDegree p d).Nodup := by
  unfold polysBelowDegree
  apply nodup_map_of_injective
  · exact coeffLists_nodup (p := p) d
  · intro xs hxs ys hys hpoly
    exact coeffList_eq_of_ofCoeffList_eq
      (length_of_mem_coeffLists hxs)
      (length_of_mem_coeffLists hys)
      hpoly

/-- There are exactly `p ^ d` entries in the bounded-degree polynomial
enumeration. -/
@[simp] theorem polysBelowDegree_length (d : Nat) :
    (polysBelowDegree p d).length = p ^ d := by
  simp [polysBelowDegree]

end Enumeration
end FpPoly
end Hex
