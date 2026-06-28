module

public import HexMatrix.Determinant.Expansion
import all HexMatrix.Determinant.Expansion

public section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-! ### Strictly-increasing column-tuple enumeration

The Cauchy-Binet sum-of-squares formula needs a Mathlib-free enumeration of the
"essentially distinct" column choices: each strictly increasing length-`n`
selection from `Fin m` represents one orbit of injective ordered tuples under
the action of permutations of `Fin n`. The enumeration below builds these
tuples by appending the new largest element, recursing on a `bound` parameter
that constrains the next entry to be strictly less than `bound`.
-/

/-- All strictly increasing length-`n` column tuples in `Fin m` whose entries
are all `< bound`. The recursion appends a new largest element `c < bound` and
recurses on the remaining prefix with the smaller bound `c.val`. -/
@[expose]
def selectedColumnTuplesUpTo (m : Nat) :
    (n : Nat) → (bound : Nat) → List (Vector (Fin m) n)
  | 0, _ => [#v[]]
  | n + 1, bound =>
      ((List.finRange m).filter (fun c : Fin m => decide (c.val < bound))).flatMap
        fun c =>
          (selectedColumnTuplesUpTo m n c.val).map fun pref => pref.push c

/-- Enumerate all strictly increasing length-`n` column selections from `Fin m`.
This list of orbit representatives drives the Cauchy-Binet grouping argument
that re-folds the ordered-tuple Gram expansion as a sum of squared minors. -/
@[expose]
def selectedColumnTuples (n m : Nat) : List (Vector (Fin m) n) :=
  selectedColumnTuplesUpTo m n m

/-- A column tuple is strictly increasing as a function `Fin n → Fin m`. -/
@[expose]
def IsStrictlyIncreasingColumnTuple {m n : Nat} (cols : Vector (Fin m) n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → cols[i].val < cols[j].val

private theorem isStrictlyIncreasingColumnTuple_nil {m : Nat} :
    IsStrictlyIncreasingColumnTuple (m := m) (n := 0) #v[] := by
  intro i _ _
  exact i.elim0

private theorem getElem_push_castSucc {α : Type u} {n : Nat}
    (v : Vector α n) (x : α) (i : Fin n) :
    (v.push x)[i.castSucc] = v[i] := by
  rcases i with ⟨i, hi⟩
  simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Vector.getElem_push_lt, hi]

private theorem getElem_push_last_index {α : Type u} {n : Nat}
    (v : Vector α n) (x : α) :
    (v.push x)[Fin.last n] = x := by
  simp [Fin.last, Vector.getElem_push_eq]

/-- Pushing a new largest element preserves strict increase as long as the
old largest entry was still smaller than the new element. -/
private theorem isStrictlyIncreasingColumnTuple_push {m n : Nat}
    (pref : Vector (Fin m) n) (c : Fin m)
    (hpref : IsStrictlyIncreasingColumnTuple pref)
    (hbound : ∀ i : Fin n, pref[i].val < c.val) :
    IsStrictlyIncreasingColumnTuple (pref.push c) := by
  intro i j hij
  rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with hjlt | hjeq
  · -- j < n, so both i, j are inside `pref`.
    have hilt : i.val < n := by omega
    have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    have hj_eq : j = (⟨j.val, hjlt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    rw [hi_eq, hj_eq, getElem_push_castSucc, getElem_push_castSucc]
    exact hpref ⟨i.val, hilt⟩ ⟨j.val, hjlt⟩ hij
  · -- j.val = n, so j is the last index.
    have hilt : i.val < n := by omega
    have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    have hj_eq : j = Fin.last n := by
      apply Fin.ext; simpa using hjeq
    rw [hi_eq, hj_eq, getElem_push_castSucc, getElem_push_last_index]
    exact hbound ⟨i.val, hilt⟩

/-- Forward characterization: every enumerated tuple is strictly increasing and
its entries are all bounded by the recursion bound. -/
private theorem mem_selectedColumnTuplesUpTo_imp {m : Nat} :
    ∀ (n bound : Nat) (v : Vector (Fin m) n),
      v ∈ selectedColumnTuplesUpTo m n bound →
        IsStrictlyIncreasingColumnTuple v ∧
          ∀ i : Fin n, v[i].val < bound
  | 0, _, v, hv => by
      simp [selectedColumnTuplesUpTo] at hv
      refine ⟨?_, ?_⟩
      · intro i _ _
        exact i.elim0
      · intro i
        exact i.elim0
  | n + 1, bound, v, hv => by
      rw [selectedColumnTuplesUpTo, List.mem_flatMap] at hv
      rcases hv with ⟨c, hc, hmem⟩
      have hclt : c.val < bound := by
        rw [List.mem_filter] at hc
        simpa using hc.2
      rw [List.mem_map] at hmem
      rcases hmem with ⟨pref, hpref, rfl⟩
      have ih := mem_selectedColumnTuplesUpTo_imp n c.val pref hpref
      refine ⟨?_, ?_⟩
      · -- strict increase of `pref.push c`
        apply isStrictlyIncreasingColumnTuple_push pref c ih.1
        intro i
        exact ih.2 i
      · -- every entry of `pref.push c` is `< bound`
        intro i
        rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hilt | hieq
        · have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
            apply Fin.ext; rfl
          rw [hi_eq, getElem_push_castSucc]
          exact Nat.lt_of_lt_of_le (ih.2 ⟨i.val, hilt⟩) (Nat.le_of_lt hclt)
        · have hi_eq : i = Fin.last n := by
            apply Fin.ext; simpa using hieq
          rw [hi_eq, getElem_push_last_index]
          exact hclt

/-- Backward characterization: every strictly increasing tuple whose entries
are all `< bound` is enumerated by the recursive helper. -/
private theorem mem_selectedColumnTuplesUpTo_of_strictly_increasing {m : Nat} :
    ∀ (n bound : Nat) (v : Vector (Fin m) n),
      IsStrictlyIncreasingColumnTuple v →
        (∀ i : Fin n, v[i].val < bound) →
        v ∈ selectedColumnTuplesUpTo m n bound
  | 0, _, v, _, _ => by
      have hv : v = #v[] := by
        ext i hi
        exact absurd hi (by omega)
      simp [selectedColumnTuplesUpTo, hv]
  | n + 1, bound, v, hsi, hbound => by
      -- factor v as `(v.pop).push v[n]`
      have hpush : (v.pop).push (v[Fin.last n]) = v := by
        have hback : v.back = v[Fin.last n] := by
          simp [Vector.back, Fin.last]
        rw [← hback]
        exact Vector.push_pop_back v
      have hpop_get : ∀ i : Fin n,
          v.pop[i] = v[(⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1))] := by
        intro i
        rcases i with ⟨i, hi⟩
        change v.pop[i]'(by simp; omega) = v[i]'(by omega)
        exact Vector.getElem_pop (h := by simp; omega)
      rw [selectedColumnTuplesUpTo, List.mem_flatMap]
      refine ⟨v[Fin.last n], ?_, ?_⟩
      · -- v[last] is in the filtered finRange
        rw [List.mem_filter]
        refine ⟨List.mem_finRange _, ?_⟩
        simpa using hbound (Fin.last n)
      · rw [List.mem_map]
        refine ⟨v.pop, ?_, hpush⟩
        apply mem_selectedColumnTuplesUpTo_of_strictly_increasing n (v[Fin.last n]).val
        · -- pop preserves strict increase
          intro i j hij
          have h1 := hpop_get i
          have h2 := hpop_get j
          have base := hsi
            (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1))
            (⟨j.val, by have := j.isLt; omega⟩ : Fin (n + 1)) hij
          rw [← h1, ← h2] at base
          exact base
        · -- bound: pop entries < v[Fin.last n]
          intro i
          have h1 := hpop_get i
          have hilt : i.val < n + 1 := by have := i.isLt; omega
          have hi_lt_last :
              (⟨i.val, hilt⟩ : Fin (n + 1)).val < (Fin.last n).val := by
            have := i.isLt
            simp [Fin.last]
          have base := hsi (⟨i.val, hilt⟩ : Fin (n + 1)) (Fin.last n) hi_lt_last
          rw [← h1] at base
          exact base

/-- Public membership characterization: a column tuple lies in
`selectedColumnTuples n m` iff it is strictly increasing. -/
theorem mem_selectedColumnTuples_iff {n m : Nat} (cols : Vector (Fin m) n) :
    cols ∈ selectedColumnTuples n m ↔ IsStrictlyIncreasingColumnTuple cols := by
  refine ⟨?_, ?_⟩
  · intro hmem
    exact (mem_selectedColumnTuplesUpTo_imp n m cols hmem).1
  · intro hsi
    apply mem_selectedColumnTuplesUpTo_of_strictly_increasing n m cols hsi
    intro i
    exact cols[i].isLt

/-- Strictly increasing column tuples induce injective `Fin n → Fin m` selection
functions, so each enumerated tuple yields an injective `columnTupleVectorFn`. -/
theorem isStrictlyIncreasingColumnTuple_injective {n m : Nat}
    {cols : Vector (Fin m) n} (hsi : IsStrictlyIncreasingColumnTuple cols) :
    Function.Injective (columnTupleVectorFn cols) := by
  intro i j hij
  -- Either i.val < j.val, j.val < i.val, or i.val = j.val. Strict increase rules out the first two.
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- i.val < j.val ⇒ cols[i].val < cols[j].val ⇒ cols[i] ≠ cols[j], contradiction.
    have : cols[i].val < cols[j].val := hsi i j hlt
    exact absurd (congrArg Fin.val hij) (Nat.ne_of_lt this)
  · exact Fin.ext heq
  · have : cols[j].val < cols[i].val := hsi j i hgt
    exact absurd (congrArg Fin.val hij.symm) (Nat.ne_of_lt this)

/-- Convenience corollary: every column tuple enumerated by `selectedColumnTuples`
yields an injective column-selection function. -/
theorem mem_selectedColumnTuples_injective {n m : Nat}
    {cols : Vector (Fin m) n} (hmem : cols ∈ selectedColumnTuples n m) :
    Function.Injective (columnTupleVectorFn cols) :=
  isStrictlyIncreasingColumnTuple_injective ((mem_selectedColumnTuples_iff cols).mp hmem)

/-- The push map `pref ↦ pref.push c` is injective on prefixes for any fixed
last element `c`, since the popped vector recovers the prefix. -/
private theorem push_left_injective {α : Type u} {n : Nat} (c : α) :
    Function.Injective fun pref : Vector α n => pref.push c := by
  intro pref pref' h
  have := congrArg Vector.pop h
  simpa using this

/-- Outer-list version of `Nodup` for the `flatMap` body that builds
`selectedColumnTuplesUpTo` from a list of "last column" candidates. -/
private theorem selectedColumnTuplesUpTo_flatMap_nodup (m n : Nat) :
    ∀ (cs : List (Fin m)), cs.Nodup →
      (∀ c ∈ cs, (selectedColumnTuplesUpTo m n c.val).Nodup) →
      (cs.flatMap fun c =>
        (selectedColumnTuplesUpTo m n c.val).map fun pref => pref.push c).Nodup
  | [], _, _ => by simp
  | c :: cs, hnodup, hinner => by
      simp only [List.flatMap_cons]
      simp only [List.nodup_cons] at hnodup
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · -- inner `(map ...)` for the head `c` is Nodup
        apply list_nodup_map_of_injective (push_left_injective c)
        exact hinner c (by simp)
      · -- suffix Nodup by IH
        exact selectedColumnTuplesUpTo_flatMap_nodup m n cs hnodup.2
          (fun c' hc' => hinner c' (List.mem_cons_of_mem c hc'))
      · -- disjointness: head produces last-element c, suffix produces last-element c' ∈ cs ⇒ c' ≠ c
        intro a hahead b hbsuffix hab
        rcases List.mem_map.mp hahead with ⟨pref, _, rfl⟩
        rcases List.mem_flatMap.mp hbsuffix with ⟨c', hc', hb⟩
        rcases List.mem_map.mp hb with ⟨pref', _, rfl⟩
        -- last entries match c and c' respectively, but c ≠ c'
        have hlast : (pref.push c)[Fin.last n] = (pref'.push c')[Fin.last n] := by
          rw [hab]
        rw [getElem_push_last_index, getElem_push_last_index] at hlast
        exact hnodup.1 (hlast ▸ hc')

private theorem selectedColumnTuplesUpTo_nodup (m : Nat) :
    ∀ (n bound : Nat), (selectedColumnTuplesUpTo m n bound).Nodup
  | 0, _ => by simp [selectedColumnTuplesUpTo]
  | n + 1, bound => by
      rw [selectedColumnTuplesUpTo]
      apply selectedColumnTuplesUpTo_flatMap_nodup
      · exact (List.nodup_finRange m).filter _
      · intro c _hc
        exact selectedColumnTuplesUpTo_nodup m n c.val

/-- The strictly-increasing column-tuple enumeration has no duplicates. -/
theorem selectedColumnTuples_nodup {n m : Nat} :
    (selectedColumnTuples n m).Nodup :=
  selectedColumnTuplesUpTo_nodup m n m

/-! ### Canonical sort and orbit factorization for injective column tuples

For the Cauchy-Binet orbit-grouping argument we need, for every injective
ordered column tuple `cols : Vector (Fin m) n`, a canonical factorization

```
cols[i] = (sortInjTuple cols)[(sortInjPerm cols)[i]]
```

where `sortInjTuple cols` is strictly increasing (i.e. lives in
`selectedColumnTuples n m`) and `sortInjPerm cols` is a permutation of
`Fin n` (i.e. lives in `permutationVectors n`). This gives a bijection
between injective `columnTupleVectors n m` entries and the product
`selectedColumnTuples n m × permutationVectors n`, which lets the orbit
sum group ordered minors by their canonical sorted column choice.

The implementation is rank-based: `sortInjPerm cols i` is the number of
columns in `cols` strictly smaller in value than `cols[i]`. For any
`cols`, this is `< n` because `cols[i]` is never strictly less than
itself; for *injective* `cols`, the rank is moreover a bijection on
`Fin n`. -/

/-- Count of indices whose `cols`-image has strictly smaller `Fin.val`
than that at `i`. This is the natural-number form of the rank. -/
@[expose]
def columnRankNat {m n : Nat} (cols : Vector (Fin m) n) (i : Fin n) : Nat :=
  ((List.finRange n).filter fun j => decide (cols[j].val < cols[i].val)).length

/-- The rank is always strictly less than `n`: index `i` itself is never
in the filter, so the filter is a strict sublist of `finRange n`. -/
theorem columnRankNat_lt {m n : Nat} (cols : Vector (Fin m) n) (i : Fin n) :
    columnRankNat cols i < n := by
  have hwit :
      ∃ x ∈ List.finRange n, ¬ (decide (cols[x].val < cols[i].val) = true) := by
    refine ⟨i, List.mem_finRange i, ?_⟩
    simp
  have hlt :=
    (List.length_filter_lt_length_iff_exists
      (p := fun j => decide (cols[j].val < cols[i].val))
      (l := List.finRange n)).mpr hwit
  simpa [columnRankNat, List.length_finRange] using hlt

/-- Canonical sorting permutation: for each index `i`, output the rank of
`cols[i]` (number of strictly smaller positions). For an injective `cols`
this is genuinely a permutation of `Fin n`; for a non-injective `cols` it
is still well-defined but may have repeated values. -/
@[expose]
def sortInjPerm {m n : Nat} (cols : Vector (Fin m) n) : Vector (Fin n) n :=
  Vector.ofFn fun i => ⟨columnRankNat cols i, columnRankNat_lt cols i⟩

/-- The `i`-th value of the sorting permutation is the rank `columnRankNat cols i`
of `cols[i]` (the number of strictly smaller positions). -/
@[grind =] theorem sortInjPerm_getElem_val {m n : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    (sortInjPerm cols)[i].val = columnRankNat cols i := by
  simp [sortInjPerm]

/-- The canonical sorted version of `cols`: read `cols` through the inverse
of `sortInjPerm`. For an injective `cols` this is strictly increasing; for
a non-injective `cols` the value is well-defined but not meaningful. -/
@[expose]
def sortInjTuple {m n : Nat} (cols : Vector (Fin m) n) : Vector (Fin m) n :=
  Vector.ofFn fun r => cols[(inversePermutationVector (sortInjPerm cols))[r]]

/-- Strict version of `List.countP_mono_left`: a single witness where
`q` holds but `p` doesn't forces strict inequality. -/
private theorem countP_lt_countP {α : Type u}
    (p q : α → Bool)
    (hle_all : ∀ (xs : List α) (x : α), x ∈ xs → p x = true → q x = true) :
    ∀ (xs : List α) (k : α), k ∈ xs → q k = true → p k = false →
      xs.countP p < xs.countP q
  | [], _k, hkmem, _, _ => by exact absurd hkmem List.not_mem_nil
  | x :: xs, k, hkmem, hqk, hpk => by
      simp only [List.mem_cons] at hkmem
      rcases hkmem with heq | hk_in_xs
      · -- x = k: at the head, `p k = false` and `q k = true`.
        subst heq
        have hxs_le : xs.countP p ≤ xs.countP q :=
          List.countP_mono_left
            (fun y hy => hle_all _ y (List.mem_cons_of_mem k hy))
        simp [hqk, hpk]
        omega
      · -- k ∈ xs: recurse on the tail.
        have ih :=
          countP_lt_countP p q hle_all xs k hk_in_xs hqk hpk
        by_cases hpx : p x = true
        · have hqx : q x = true := hle_all (x :: xs) x List.mem_cons_self hpx
          simp [hpx, hqx]; omega
        · have hpx' : p x = false := by
            cases hpe : p x with
            | true => exact absurd hpe hpx
            | false => rfl
          by_cases hqx : q x = true
          · simp [hpx', hqx]; omega
          · have hqx' : q x = false := by
              cases hqe : q x with
              | true => exact absurd hqe hqx
              | false => rfl
            simp [hpx', hqx']; exact ih

/-- Monotonicity of the rank: if `cols[i].val < cols[j].val` then the
rank strictly increases from `i` to `j`. Holds for any `cols`, no
injectivity assumption needed. -/
private theorem columnRankNat_strictMono {m n : Nat} (cols : Vector (Fin m) n)
    {i j : Fin n} (hij : cols[i].val < cols[j].val) :
    columnRankNat cols i < columnRankNat cols j := by
  -- Switch from `length filter` to `countP`.
  have hlen_eq_p :
      ((List.finRange n).filter fun k => decide (cols[k].val < cols[i].val)).length
        = (List.finRange n).countP (fun k => decide (cols[k].val < cols[i].val)) := by
    rw [List.countP_eq_length_filter]
  have hlen_eq_q :
      ((List.finRange n).filter fun k => decide (cols[k].val < cols[j].val)).length
        = (List.finRange n).countP (fun k => decide (cols[k].val < cols[j].val)) := by
    rw [List.countP_eq_length_filter]
  unfold columnRankNat
  rw [hlen_eq_p, hlen_eq_q]
  -- Strict comparison via element `i`.
  refine countP_lt_countP
    (fun k => decide (cols[k].val < cols[i].val))
    (fun k => decide (cols[k].val < cols[j].val))
    ?_ (List.finRange n) i (List.mem_finRange i)
    (decide_eq_true hij) ?_
  · intro _ k _hkmem hpk
    have hkk : cols[k].val < cols[i].val := by simpa using hpk
    exact decide_eq_true (Nat.lt_trans hkk hij)
  · simp

/-- For an injective `cols`, the rank function is itself injective: two
positions with the same rank must agree as `Fin n`. -/
private theorem columnRankNat_injective_of_injective {m n : Nat}
    (cols : Vector (Fin m) n) (hinj : Function.Injective (columnTupleVectorFn cols)) :
    Function.Injective (columnRankNat cols) := by
  intro i j hrank
  rcases Nat.lt_trichotomy cols[i].val cols[j].val with hlt | heq | hgt
  · exact absurd (columnRankNat_strictMono cols hlt) (by omega)
  · -- cols[i].val = cols[j].val ⇒ cols[i] = cols[j] ⇒ i = j by injectivity.
    have hcol_eq : cols[i] = cols[j] := Fin.ext heq
    exact hinj hcol_eq
  · exact absurd (columnRankNat_strictMono cols hgt) (by omega)

/-- For an injective `cols`, `sortInjPerm cols` is a permutation as a list. -/
private theorem sortInjPerm_toList_nodup {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    (sortInjPerm cols).toList.Nodup := by
  rw [vector_toList_eq]
  apply list_nodup_map_of_injective ?_ (List.nodup_finRange n)
  intro i j hij
  have hval : columnRankNat cols i = columnRankNat cols j := by
    have := congrArg Fin.val hij
    simpa [sortInjPerm] using this
  exact columnRankNat_injective_of_injective cols hinj hval

/-- For an injective `cols`, `sortInjPerm cols ∈ permutationVectors n`. -/
theorem sortInjPerm_mem_permutationVectors {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    sortInjPerm cols ∈ permutationVectors n :=
  permutationVectors_complete (sortInjPerm_toList_nodup cols hinj)

/-- Converse of `columnRankNat_strictMono` for injective `cols`: a strict
rank comparison implies the underlying value comparison. -/
private theorem cols_val_lt_of_rank_lt {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols))
    {i j : Fin n} (hij : columnRankNat cols i < columnRankNat cols j) :
    cols[i].val < cols[j].val := by
  rcases Nat.lt_trichotomy cols[i].val cols[j].val with hlt | heq | hgt
  · exact hlt
  · have hcol_eq : cols[i] = cols[j] := Fin.ext heq
    have hij' : i = j := hinj hcol_eq
    subst hij'
    omega
  · have := columnRankNat_strictMono cols hgt
    omega

/-- `Vector.ofFn`-indexed access at a `Fin n` argument, packaged so that
the result is the function applied to the original `Fin n` index rather
than to its repackaged Nat-value form. -/
private theorem vector_ofFn_getElem_fin {α : Type u} {n : Nat}
    (f : Fin n → α) (k : Fin n) :
    (Vector.ofFn f)[k] = f k := by
  rw [show ((Vector.ofFn f)[k] : α) = (Vector.ofFn f)[k.val]'(by simp [k.isLt]) from rfl]
  rw [Vector.getElem_ofFn]

/-- Every length-`n` tuple of column indices appears in
`columnTupleVectors n m`. -/
theorem mem_columnTupleVectors {n m : Nat} (cols : Vector (Fin m) n) :
    cols ∈ columnTupleVectors n m := by
  have hcols : cols = Vector.ofFn (fun i : Fin n => cols[i]) := by
    ext i hi
    apply Fin.val_eq_of_eq
    let k : Fin n := ⟨i, hi⟩
    change cols[k] = (Vector.ofFn fun i : Fin n => cols[i])[k]
    rw [vector_ofFn_getElem_fin]
  rw [hcols]
  exact columnTupleVectors_mem_ofFn (fun i : Fin n => cols[i])

/-- Factorization equation: each entry of `cols` is recovered through the
canonical sort/permutation pair. Requires injectivity of `cols`. -/
theorem cols_getElem_eq_sortInjTuple_sortInjPerm {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols))
    (i : Fin n) :
    cols[i] = (sortInjTuple cols)[(sortInjPerm cols)[i]] := by
  have hnodup := sortInjPerm_toList_nodup cols hinj
  have hidx :=
    inversePermutationValues_get_index (sortInjPerm cols) hnodup i
  have hinv_eq : inversePermutationVector (sortInjPerm cols)
                   = inversePermutationValues (sortInjPerm cols) hnodup :=
    inversePermutationVector_eq (sortInjPerm cols) hnodup
  have hstep :
      (inversePermutationVector (sortInjPerm cols))[(sortInjPerm cols)[i]]
        = (inversePermutationValues (sortInjPerm cols) hnodup)[(sortInjPerm cols)[i]] :=
    congrArg (fun v : Vector (Fin n) n => v[(sortInjPerm cols)[i]]) hinv_eq
  have hcompose :
      (inversePermutationVector (sortInjPerm cols))[(sortInjPerm cols)[i]] = i :=
    hstep.trans hidx
  rw [sortInjTuple, vector_ofFn_getElem_fin]
  exact (congrArg (fun k : Fin n => cols[k]) hcompose).symm

/-- For an injective `cols`, applying `sortInjPerm` after the inverse
returns the input rank. -/
private theorem sortInjPerm_inv_apply {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) (r : Fin n) :
    (sortInjPerm cols)[(inversePermutationVector (sortInjPerm cols))[r]] = r := by
  have hnodup := sortInjPerm_toList_nodup cols hinj
  have hval := inversePermutationValues_get_value (sortInjPerm cols) hnodup r
  have hinv_eq : inversePermutationVector (sortInjPerm cols)
                   = inversePermutationValues (sortInjPerm cols) hnodup :=
    inversePermutationVector_eq (sortInjPerm cols) hnodup
  have hstep :
      (sortInjPerm cols)[(inversePermutationVector (sortInjPerm cols))[r]]
        = (sortInjPerm cols)[(inversePermutationValues (sortInjPerm cols) hnodup)[r]] :=
    congrArg (fun v : Vector (Fin n) n => (sortInjPerm cols)[v[r]]) hinv_eq
  exact hstep.trans hval

/-- For an injective `cols`, the column-rank at the inverse-perm image
of `r` is exactly `r.val`. -/
private theorem columnRankNat_inv_apply {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) (r : Fin n) :
    columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r] = r.val := by
  have hval' := sortInjPerm_inv_apply cols hinj r
  have := congrArg Fin.val hval'
  simpa [sortInjPerm] using this

/-- For an injective `cols`, the canonical sorted tuple is strictly
increasing. -/
theorem isStrictlyIncreasingColumnTuple_sortInjTuple {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    IsStrictlyIncreasingColumnTuple (sortInjTuple cols) := by
  intro r r' hrr'
  have hrank_r := columnRankNat_inv_apply cols hinj r
  have hrank_r' := columnRankNat_inv_apply cols hinj r'
  have hrank_lt :
      columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r] <
        columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r'] := by
    rw [hrank_r, hrank_r']; exact hrr'
  have hval_lt :
      cols[(inversePermutationVector (sortInjPerm cols))[r]].val <
        cols[(inversePermutationVector (sortInjPerm cols))[r']].val :=
    cols_val_lt_of_rank_lt cols hinj hrank_lt
  show (sortInjTuple cols)[r].val < (sortInjTuple cols)[r'].val
  rw [sortInjTuple, vector_ofFn_getElem_fin, vector_ofFn_getElem_fin]
  exact hval_lt

/-- For an injective `cols`, the canonical sorted tuple is enumerated by
`selectedColumnTuples n m`. -/
theorem sortInjTuple_mem_selectedColumnTuples {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    sortInjTuple cols ∈ selectedColumnTuples n m :=
  (mem_selectedColumnTuples_iff (sortInjTuple cols)).mpr
    (isStrictlyIncreasingColumnTuple_sortInjTuple cols hinj)

/-! ### Forward injectivity of the sort/permutation pair -/

/-- Pairwise distinctness: two injective column tuples that map to the
same `(sortInjTuple, sortInjPerm)` pair must be equal. -/
theorem sortInj_pair_injective {m n : Nat} {cols cols' : Vector (Fin m) n}
    (hinj : Function.Injective (columnTupleVectorFn cols))
    (hinj' : Function.Injective (columnTupleVectorFn cols'))
    (hsort : sortInjTuple cols = sortInjTuple cols')
    (hperm : sortInjPerm cols = sortInjPerm cols') :
    cols = cols' := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  show cols[i] = cols'[i]
  rw [cols_getElem_eq_sortInjTuple_sortInjPerm cols hinj i,
      cols_getElem_eq_sortInjTuple_sortInjPerm cols' hinj' i]
  -- Use congrArg to swap `sortInjPerm cols` for `sortInjPerm cols'`.
  have hperm_apply :
      (sortInjPerm cols)[i] = (sortInjPerm cols')[i] :=
    congrArg (fun v : Vector (Fin n) n => v[i]) hperm
  -- And use hsort to swap `sortInjTuple cols` for `sortInjTuple cols'`.
  rw [hsort]
  exact congrArg (fun k : Fin n => (sortInjTuple cols')[k]) hperm_apply

/-! ### Reconstruction from `selectedColumnTuples × permutationVectors`

For a strictly-increasing `sel` and a permutation `perm`, the
"reconstruction" `Vector.ofFn (fun i => sel[perm[i]])` is itself
injective, and its canonical sort/permutation pair recovers
`(sel, perm)`. This is the inverse map of `sortInjTuple`/`sortInjPerm`. -/

/-- Reconstruction map: given a sorted choice and a permutation, build
an ordered column tuple. -/
@[expose]
def reconstructInjTuple {m n : Nat}
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) : Vector (Fin m) n :=
  Vector.ofFn fun i => sel[perm[i]]

/-- The `i`-th entry of the reconstructed tuple is `sel[perm[i]]`: read the
sorted choice `sel` through the permutation `perm`. -/
@[grind =] theorem reconstructInjTuple_getElem {m n : Nat}
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) (i : Fin n) :
    (reconstructInjTuple sel perm)[i] = sel[perm[i]] := by
  rw [reconstructInjTuple, vector_ofFn_getElem_fin]

/-- Selecting columns via the reconstructed tuple equals selecting via `sel`
with the column index permuted by `perm`: entry `(r, c)` agrees with entry
`(r, perm[c])` of the `sel`-selected minor. -/
@[grind =] theorem columnTupleMatrix_reconstructInjTuple_entry
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n)
    (r c : Fin n) :
    (columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)))[r][c] =
      (columnTupleMatrix A (columnTupleVectorFn sel))[r][perm[c]] := by
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact congrArg (fun col : Fin m => A[r][col])
    (reconstructInjTuple_getElem sel perm c)

private theorem columnTupleMatrix_reconstructInjTuple_eq
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) :
    columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)) =
      columnTupleMatrix A (fun i => sel[perm[i]]) := by
  ext r hr c hc
  change
    (columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)))[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix A (fun i => sel[perm[i]]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact congrArg (fun col : Fin m => A[(⟨r, hr⟩ : Fin n)][col])
    (reconstructInjTuple_getElem sel perm (⟨c, hc⟩ : Fin n))

/-- Reconstructing an injective tuple from a selected tuple and a permutation
turns the coefficient product into the corresponding determinant product. -/
theorem columnTupleCoeff_reconstructInjTuple
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) :
    columnTupleCoeff A (reconstructInjTuple sel perm) =
      detProduct (columnTupleMatrix A (columnTupleVectorFn sel)) perm := by
  unfold columnTupleCoeff detProduct
  apply foldl_det_product_congr
  intro i _hmem
  rw [columnTupleMatrix_entry]
  exact congrArg (fun col : Fin m => A[i][col])
    (reconstructInjTuple_getElem sel perm i)

/-- Counting how many entries of `List.finRange n` have value `< k`. -/
private theorem countP_finRange_val_lt :
    ∀ (n k : Nat), (List.finRange n).countP (fun x : Fin n => decide (x.val < k)) = min n k
  | 0, k => by simp
  | n + 1, k => by
      rw [List.finRange_succ_last, List.countP_append, List.countP_map]
      -- The induction hypothesis applies to the `map Fin.castSucc` part.
      -- `(castSucc x).val = x.val`, so the composed predicate matches.
      have ih := countP_finRange_val_lt n k
      have hmap_eq :
          (List.finRange n).countP ((fun x : Fin (n + 1) => decide (x.val < k)) ∘ Fin.castSucc) =
            (List.finRange n).countP (fun x : Fin n => decide (x.val < k)) := rfl
      rw [hmap_eq, ih]
      -- Singleton contribution.
      simp only [List.countP_singleton, Fin.last]
      -- Goal: min n k + (if decide (n < k) then 1 else 0) = min (n+1) k.
      by_cases hnk : n < k
      · rw [if_pos (by simpa using hnk)]
        omega
      · rw [if_neg (by simpa using hnk)]
        omega

/-- A permutation as a `Vector` acts as an injective function on `Fin n`. -/
private theorem permutationVectors_getElem_injective {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    Function.Injective (fun i : Fin n => perm[i]) := by
  intro i j hij
  have hnodup := permutationVectors_nodup hmem
  -- Apply the inverse-permutation to both sides.
  have hstep :
      (inversePermutationValues perm hnodup)[perm[i]]
        = (inversePermutationValues perm hnodup)[perm[j]] :=
    congrArg (fun k : Fin n => (inversePermutationValues perm hnodup)[k]) hij
  have hi := inversePermutationValues_get_index perm hnodup i
  have hj := inversePermutationValues_get_index perm hnodup j
  exact hi.symm.trans (hstep.trans hj)

/-- The reconstructed column tuple is itself injective when `sel` is
strictly increasing and `perm` is a permutation. -/
theorem reconstructInjTuple_injective {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    Function.Injective (columnTupleVectorFn (reconstructInjTuple sel perm)) := by
  intro i j hij
  have hsel_inj := isStrictlyIncreasingColumnTuple_injective hsel
  have hperm_inj := permutationVectors_getElem_injective hperm
  -- `hij` is equality of reconstructed entries; extract `sel[perm[i]] = sel[perm[j]]`.
  have hval : sel[perm[i]] = sel[perm[j]] := by
    have hi := reconstructInjTuple_getElem sel perm i
    have hj := reconstructInjTuple_getElem sel perm j
    have hij' :
        (reconstructInjTuple sel perm)[i] = (reconstructInjTuple sel perm)[j] := hij
    exact hi.symm.trans (hij'.trans hj)
  exact hperm_inj (hsel_inj hval)

/-- For a strictly-increasing `sel`, value comparison agrees with index
comparison. -/
private theorem isStrictlyIncreasingColumnTuple_val_lt_iff {m n : Nat}
    {sel : Vector (Fin m) n} (hsel : IsStrictlyIncreasingColumnTuple sel)
    (a b : Fin n) :
    sel[a].val < sel[b].val ↔ a.val < b.val := by
  refine ⟨?_, hsel a b⟩
  intro hlt
  rcases Nat.lt_trichotomy a.val b.val with hltab | heqab | hgtab
  · exact hltab
  · have : a = b := Fin.ext heqab
    subst this; omega
  · have := hsel b a hgtab; omega

/-- For a permutation `perm`, the `toList` is a `List.Perm` of `List.finRange n`. -/
private theorem permutationVectors_toList_perm_finRange {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    perm.toList.Perm (List.finRange n) := by
  have hnodup := permutationVectors_nodup hmem
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).mpr
  intro x
  refine ⟨fun _ => List.mem_finRange x, fun _ => ?_⟩
  exact fin_mem_of_full_nodup x (by simp [Vector.length_toList]) hnodup

/-- Count of indices `j` for which `perm[j].val < k.val` is exactly `k.val`
when `perm` is a permutation. -/
private theorem permutationVectors_count_val_lt {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) (k : Fin n) :
    (List.finRange n).countP (fun j : Fin n => decide (perm[j].val < k.val)) = k.val := by
  -- Reduce to counting on perm.toList via `countP_map`.
  have hmap :
      (List.finRange n).countP (fun j : Fin n => decide (perm[j].val < k.val)) =
        ((List.finRange n).map fun j : Fin n => perm[j]).countP
          (fun x : Fin n => decide (x.val < k.val)) := by
    rw [List.countP_map]
    rfl
  have htoList : perm.toList = (List.finRange n).map (fun j : Fin n => perm[j]) :=
    vector_toList_eq perm
  rw [hmap, ← htoList]
  rw [List.Perm.countP_eq _ (permutationVectors_toList_perm_finRange hmem)]
  rw [countP_finRange_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt k.isLt)

/-- For a strictly-increasing `sel` and a permutation `perm`, the column
rank of the reconstruction at index `i` agrees with `perm[i].val`. -/
private theorem columnRankNat_reconstructInjTuple {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) (i : Fin n) :
    columnRankNat (reconstructInjTuple sel perm) i = (perm[i]).val := by
  unfold columnRankNat
  -- Convert filter to countP, replace predicate using strict monotonicity, then
  -- apply the permutation count lemma.
  rw [← List.countP_eq_length_filter]
  have hpred :
      (fun j : Fin n => decide ((reconstructInjTuple sel perm)[j].val
                                   < (reconstructInjTuple sel perm)[i].val)) =
        (fun j : Fin n => decide ((perm[j]).val < (perm[i]).val)) := by
    funext j
    rw [reconstructInjTuple_getElem, reconstructInjTuple_getElem]
    exact decide_eq_decide.mpr (isStrictlyIncreasingColumnTuple_val_lt_iff hsel _ _)
  rw [hpred]
  exact permutationVectors_count_val_lt hperm (perm[i])

/-- `sortInjPerm` of a reconstructed tuple recovers the original permutation. -/
theorem sortInjPerm_reconstructInjTuple {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    sortInjPerm (reconstructInjTuple sel perm) = perm := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  show (sortInjPerm (reconstructInjTuple sel perm))[i] = perm[i]
  apply Fin.ext
  rw [sortInjPerm_getElem_val]
  exact columnRankNat_reconstructInjTuple hsel hperm i

/-- `sortInjTuple` of a reconstructed tuple recovers the original selection. -/
theorem sortInjTuple_reconstructInjTuple {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    sortInjTuple (reconstructInjTuple sel perm) = sel := by
  -- Use the factorization equation on the reconstructed tuple, which is injective.
  have hinj : Function.Injective (columnTupleVectorFn (reconstructInjTuple sel perm)) :=
    reconstructInjTuple_injective hsel hperm
  ext k hk
  apply Fin.val_eq_of_eq
  let r : Fin n := ⟨k, hk⟩
  show (sortInjTuple (reconstructInjTuple sel perm))[r] = sel[r]
  -- The reconstruction at index `inv perm [r]` equals sel[perm[(inv perm) r]] = sel[r].
  -- And by the factorization equation, this equals sortInjTuple cols at sortInjPerm cols [(inv perm) r]
  -- which is just r by the permutation identity. Hmm, this is circular.
  -- Direct: sortInjTuple cols [r] = cols[inv (sortInjPerm cols) [r]]
  --                                = cols[inv perm [r]]                    -- by sortInjPerm_reconstructInjTuple
  --                                = sel[perm[(inv perm) r]]               -- by reconstruction defn
  --                                = sel[r]                                -- by perm ∘ inv perm = id
  have hsortPerm := sortInjPerm_reconstructInjTuple hsel hperm
  -- Substitute sortInjPerm with perm in the sortInjTuple definition.
  rw [sortInjTuple, vector_ofFn_getElem_fin]
  -- Goal: cols[inv (sortInjPerm cols) [r]] = sel[r]
  -- where cols := reconstructInjTuple sel perm.
  have hinv_eq : inversePermutationVector (sortInjPerm (reconstructInjTuple sel perm))
                   = inversePermutationVector perm :=
    congrArg inversePermutationVector hsortPerm
  have hstep :
      (reconstructInjTuple sel perm)[(inversePermutationVector
                                        (sortInjPerm (reconstructInjTuple sel perm)))[r]]
        = (reconstructInjTuple sel perm)[(inversePermutationVector perm)[r]] :=
    congrArg
      (fun v : Vector (Fin n) n => (reconstructInjTuple sel perm)[v[r]])
      hinv_eq
  rw [hstep]
  -- Now: reconstruction at (inv perm)[r] = sel[perm[(inv perm)[r]]] = sel[r].
  rw [reconstructInjTuple_getElem]
  -- Use that perm ∘ inv perm = id (i.e., perm[(inv perm)[r]] = r).
  have hnodup := permutationVectors_nodup hperm
  have hinv_perm : inversePermutationVector perm
                     = inversePermutationValues perm hnodup :=
    inversePermutationVector_eq perm hnodup
  have hval := inversePermutationValues_get_value perm hnodup r
  -- hval : perm[(inv perm) [r]] = r (where inv perm = inversePermutationValues perm hnodup)
  have hstep' :
      perm[(inversePermutationVector perm)[r]]
        = perm[(inversePermutationValues perm hnodup)[r]] :=
    congrArg (fun v : Vector (Fin n) n => perm[v[r]]) hinv_perm
  have hperm_apply : perm[(inversePermutationVector perm)[r]] = r := hstep'.trans hval
  -- Therefore: sel[perm[(inv perm)[r]]] = sel[r] via congrArg.
  exact congrArg (fun k : Fin n => sel[k]) hperm_apply

/-! ### Bijection wrappers -/

/-- Forward-then-backward identity: reconstruction inverts the canonical
sort/permutation pair on injective column tuples. -/
theorem reconstructInjTuple_sortInj {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    reconstructInjTuple (sortInjTuple cols) (sortInjPerm cols) = cols := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  show (reconstructInjTuple (sortInjTuple cols) (sortInjPerm cols))[i] = cols[i]
  rw [reconstructInjTuple_getElem]
  exact (cols_getElem_eq_sortInjTuple_sortInjPerm cols hinj i).symm

/-- For each fixed `sel`, the inner `map (reconstructInjTuple sel)` list
is `Nodup` over `permutationVectors n`. -/
private theorem permutationVectors_map_reconstruct_nodup {m n : Nat}
    {sel : Vector (Fin m) n} (hsel : IsStrictlyIncreasingColumnTuple sel) :
    ((permutationVectors n).map (reconstructInjTuple sel)).Nodup := by
  apply list_nodup_map_on permutationVectors_nodup_list
  intro a ha b hb hab
  -- Apply sortInjPerm to both sides to recover the permutation.
  have := congrArg sortInjPerm hab
  rw [sortInjPerm_reconstructInjTuple hsel ha,
      sortInjPerm_reconstructInjTuple hsel hb] at this
  exact this

/-- The flat list of reconstructed column tuples, indexed by
`selectedColumnTuples × permutationVectors`, has no duplicates. -/
theorem selPerm_reconstructed_list_nodup {m n : Nat} :
    ((selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)).Nodup := by
  -- Generalize so we can induct on the outer list (selectedColumnTuples).
  suffices h : ∀ (sels : List (Vector (Fin m) n)), sels.Nodup →
      (∀ sel ∈ sels, IsStrictlyIncreasingColumnTuple sel) →
      (sels.flatMap fun sel =>
        (permutationVectors n).map (reconstructInjTuple sel)).Nodup by
    exact h _ selectedColumnTuples_nodup
      (fun sel hmem => (mem_selectedColumnTuples_iff sel).mp hmem)
  intro sels hsels_nodup hsels_inc
  induction sels with
  | nil => simp
  | cons s ss ih =>
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      simp only [List.nodup_cons] at hsels_nodup
      refine ⟨?_, ?_, ?_⟩
      · -- Inner head list is Nodup.
        exact permutationVectors_map_reconstruct_nodup (hsels_inc s (by simp))
      · -- Tail Nodup by IH.
        exact ih hsels_nodup.2 (fun sel' hsel' => hsels_inc sel' (List.mem_cons_of_mem s hsel'))
      · -- Disjointness: a reconstruction with `sel = s` and a reconstruction
        -- with `sel = s' ∈ ss` agree only if `s = s'` by `sortInjTuple`.
        intro a ha_head b hb_suffix hab
        rcases List.mem_map.mp ha_head with ⟨perm, hperm_mem, rfl⟩
        rcases List.mem_flatMap.mp hb_suffix with ⟨s', hs'_mem, hb_in⟩
        rcases List.mem_map.mp hb_in with ⟨perm', hperm'_mem, hb_eq⟩
        -- hab : (reconstructInjTuple s perm) = b; hb_eq : reconstructInjTuple s' perm' = b
        have hrec_eq : reconstructInjTuple s perm = reconstructInjTuple s' perm' :=
          hab.trans hb_eq.symm
        have hs_inc := hsels_inc s (by simp)
        have hs'_inc := hsels_inc s' (List.mem_cons_of_mem s hs'_mem)
        have hsort := congrArg sortInjTuple hrec_eq
        rw [sortInjTuple_reconstructInjTuple hs_inc hperm_mem,
            sortInjTuple_reconstructInjTuple hs'_inc hperm'_mem] at hsort
        subst hsort
        exact hsels_nodup.1 hs'_mem

/-- A column tuple is injective iff it is enumerated by the
`selectedColumnTuples × permutationVectors` reconstruction. This is the
bijection statement in membership form. -/
theorem mem_selPerm_reconstructed_iff {m n : Nat} (cols : Vector (Fin m) n) :
    cols ∈ ((selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)) ↔
      Function.Injective (columnTupleVectorFn cols) := by
  refine ⟨?_, ?_⟩
  · -- Backward: every reconstruction is injective.
    intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨sel, hsel_mem, hinner⟩
    rcases List.mem_map.mp hinner with ⟨perm, hperm_mem, rfl⟩
    have hsel_inc : IsStrictlyIncreasingColumnTuple sel :=
      (mem_selectedColumnTuples_iff sel).mp hsel_mem
    exact reconstructInjTuple_injective hsel_inc hperm_mem
  · -- Forward: every injective tuple is in the reconstruction list, via
    -- (sortInjTuple cols, sortInjPerm cols).
    intro hinj
    rw [List.mem_flatMap]
    refine ⟨sortInjTuple cols, sortInjTuple_mem_selectedColumnTuples cols hinj, ?_⟩
    rw [List.mem_map]
    refine ⟨sortInjPerm cols, sortInjPerm_mem_permutationVectors cols hinj, ?_⟩
    exact reconstructInjTuple_sortInj cols hinj

private theorem foldl_det_sum_filter_of_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Prop) [DecidablePred p]
    (f : β → R) (z : R)
    (hzero : ∀ x, x ∈ xs → ¬ p x → f x = 0) :
    xs.foldl (fun acc x => acc + f x) z =
      (xs.filter p).foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : p x
      · simp [List.filter, hx]
        apply ih
        intro y hy hpy
        exact hzero y (List.mem_cons_of_mem x hy) hpy
      · simp [List.filter, hx]
        have hxzero : f x = 0 := hzero x (by simp) hx
        rw [hxzero]
        have hacc : z + (0 : R) = z := by grind
        rw [hacc]
        apply ih
        intro y hy hpy
        exact hzero y (List.mem_cons_of_mem x hy) hpy

/-- Refold the ordered column-tuple Gram expansion over the canonical
`selectedColumnTuples × permutationVectors` reconstruction list. Non-injective
ordered tuples contribute zero determinants, and the remaining injective tuples
are exactly the reconstructed selected/permutation tuples. -/
theorem columnTupleExpansion_refold_selectedPerm
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    (columnTupleVectors n m).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 =
      (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
  classical
  let reconstructed :=
    (selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)
  let term := columnTupleExpansionTerm A
  have hfilter :
      (columnTupleVectors n m).foldl (fun acc cols => acc + term cols) 0 =
        ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).foldl
            (fun acc cols => acc + term cols) 0 := by
    apply foldl_det_sum_filter_of_zero
    intro cols hmem hnot
    unfold term columnTupleExpansionTerm
    have hdet :
        det (columnTupleMatrix A (columnTupleVectorFn cols)) = 0 :=
      det_columnTupleMatrix_eq_zero_of_not_injective A (columnTupleVectorFn cols) hnot
    rw [hdet]
    grind
  have hperm :
      ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).Perm
        reconstructed := by
    apply (List.perm_ext_iff_of_nodup
      ((columnTupleVectors_nodup (n := n) (m := m)).filter _)
      (by simpa [reconstructed] using (selPerm_reconstructed_list_nodup (m := m) (n := n)))).mpr
    intro cols
    constructor
    · intro hmem
      rw [List.mem_filter] at hmem
      exact (mem_selPerm_reconstructed_iff cols).mpr (of_decide_eq_true hmem.2)
    · intro hmem
      rw [List.mem_filter]
      exact ⟨mem_columnTupleVectors cols,
        decide_eq_true ((mem_selPerm_reconstructed_iff cols).mp hmem)⟩
  calc
    (columnTupleVectors n m).foldl (fun acc cols => acc + columnTupleExpansionTerm A cols) 0
        = (columnTupleVectors n m).foldl (fun acc cols => acc + term cols) 0 := rfl
    _ = ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).foldl
            (fun acc cols => acc + term cols) 0 := hfilter
    _ = reconstructed.foldl (fun acc cols => acc + term cols) 0 := by
          exact foldl_det_sum_perm term hperm 0
    _ = (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := rfl

private theorem columnTupleExpansionTerm_reconstructInjTuple
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) (perm : Vector (Fin n) n)
    (hperm : perm ∈ permutationVectors n) :
    columnTupleExpansionTerm A (reconstructInjTuple sel perm) =
      detTerm (columnTupleMatrix A (columnTupleVectorFn sel)) perm *
        det (columnTupleMatrix A (columnTupleVectorFn sel)) := by
  unfold columnTupleExpansionTerm detTerm
  rw [columnTupleCoeff_reconstructInjTuple]
  rw [columnTupleMatrix_reconstructInjTuple_eq A sel perm]
  rw [det_columnTupleMatrix_compose_perm A sel perm hperm]
  grind

private theorem columnTupleExpansion_reconstruct_orbit_sum
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) :
    (permutationVectors n).foldl
        (fun acc perm => acc + columnTupleExpansionTerm A (reconstructInjTuple sel perm)) 0 =
      det (columnTupleMatrix A (columnTupleVectorFn sel)) ^ 2 := by
  let minor := columnTupleMatrix A (columnTupleVectorFn sel)
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + columnTupleExpansionTerm A (reconstructInjTuple sel perm)) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + detTerm minor perm * det minor) 0 := by
        apply foldl_det_sum_congr
        intro perm hperm
        exact columnTupleExpansionTerm_reconstructInjTuple A sel perm hperm
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm minor perm) 0 *
        det minor := by
        exact foldl_det_sum_mul_right_zero (permutationVectors n) (fun perm => detTerm minor perm)
          (det minor)
    _ = det minor ^ 2 := by
        unfold det
        grind

private theorem columnTupleExpansion_selectedPerm_collapse
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    (((selectedColumnTuples n m).flatMap fun sel =>
        (permutationVectors n).map (reconstructInjTuple sel))).foldl
      (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 =
    (selectedColumnTuples n m).foldl
      (fun acc sel => acc + det (columnTupleMatrix A (columnTupleVectorFn sel)) ^ 2) 0 := by
  rw [foldl_det_sum_flatMap]
  apply foldl_acc_congr
  intro acc sel _hsel
  rw [foldl_det_sum_start]
  congr 1
  rw [foldl_det_sum_map]
  rw [columnTupleExpansion_reconstruct_orbit_sum A sel]

/-- Cauchy-Binet for the row Gram matrix: the Gram determinant is the finite
sum of squares of the selected column minors. -/
theorem det_gramMatrix_eq_sum_minors_sq
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    det (gramMatrix A) =
      (selectedColumnTuples n m).foldl
        (fun acc cols => acc + det (columnTupleMatrix A (columnTupleVectorFn cols)) ^ 2) 0 := by
  calc
    det (gramMatrix A) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
        exact det_gramMatrix_eq_sum_columnTuples A
    _ =
      (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
        exact columnTupleExpansion_refold_selectedPerm A
    _ =
      (selectedColumnTuples n m).foldl
        (fun acc cols => acc + det (columnTupleMatrix A (columnTupleVectorFn cols)) ^ 2) 0 := by
        exact columnTupleExpansion_selectedPerm_collapse A

private theorem foldl_int_sum_sq_nonneg_start {β : Type v}
    (xs : List β) (f : β → Int) (acc : Int) (hacc : 0 ≤ acc) :
    0 ≤ xs.foldl (fun acc x => acc + f x ^ 2) acc := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : 0 ≤ f x ^ 2 := by
        simpa [Lean.Grind.Semiring.pow_two] using
          (Lean.Grind.OrderedRing.sq_nonneg (a := f x))
      exact ih (acc + f x ^ 2) (Int.add_nonneg hacc hx)

private theorem foldl_int_sum_sq_nonneg {β : Type v} (xs : List β) (f : β → Int) :
    0 ≤ xs.foldl (fun acc x => acc + f x ^ 2) 0 :=
  foldl_int_sum_sq_nonneg_start xs f 0 (by simp)

private theorem foldl_int_sum_sq_pos_of_acc {β : Type v}
    (xs : List β) (f : β → Int) (acc : Int) (hacc : 0 < acc) :
    0 < xs.foldl (fun acc x => acc + f x ^ 2) acc := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : 0 ≤ f x ^ 2 := by
        simpa [Lean.Grind.Semiring.pow_two] using
          (Lean.Grind.OrderedRing.sq_nonneg (a := f x))
      exact ih (acc + f x ^ 2) (Int.add_pos_of_pos_of_nonneg hacc hx)

private theorem foldl_int_sum_sq_pos_start {β : Type v}
    (xs : List β) (f : β → Int) (acc : Int) (hacc : 0 ≤ acc)
    (target : β) (hx : target ∈ xs) (hpos : 0 < f target ^ 2) :
    0 < xs.foldl (fun acc x => acc + f x ^ 2) acc := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hx
      cases hx with
      | inl hxy =>
          subst hxy
          exact foldl_int_sum_sq_pos_of_acc ys f (acc + f target ^ 2)
            (Int.add_pos_of_nonneg_of_pos hacc hpos)
      | inr htail =>
          have hy : 0 ≤ f y ^ 2 := by
            simpa [Lean.Grind.Semiring.pow_two] using
              (Lean.Grind.OrderedRing.sq_nonneg (a := f y))
          exact ih (acc + f y ^ 2) (Int.add_nonneg hacc hy) htail

private theorem foldl_int_sum_sq_pos_of_mem {β : Type v}
    (xs : List β) (f : β → Int) (x : β) (hx : x ∈ xs) (hpos : 0 < f x ^ 2) :
    0 < xs.foldl (fun acc x => acc + f x ^ 2) 0 :=
  foldl_int_sum_sq_pos_start xs f 0 (by simp) x hx hpos

/-- Integer row Gram determinants are nonnegative, by Cauchy-Binet as a finite
sum of integer squares. -/
theorem det_gramMatrix_nonneg {n m : Nat} (A : Matrix Int n m) :
    0 ≤ det (gramMatrix A) := by
  rw [det_gramMatrix_eq_sum_minors_sq A]
  exact foldl_int_sum_sq_nonneg (selectedColumnTuples n m)
    (fun cols => det (columnTupleMatrix A (columnTupleVectorFn cols)))

/-- The identity selection of the first `k` columns of an `n`-column matrix. -/
@[expose]
def firstColumns (k n : Nat) (hk : k ≤ n) : Vector (Fin n) k :=
  Vector.ofFn fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- The `i`-th entry of the first-`k`-columns selection is the index `i` itself,
embedded into `Fin n`. -/
@[grind =] theorem firstColumns_entry (k n : Nat) (hk : k ≤ n) (i : Fin k) :
    (firstColumns k n hk)[i] = (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin n) := by
  simp [firstColumns]

/-- The first `k` columns form a strictly increasing selected column tuple. -/
theorem firstColumns_mem_selectedColumnTuples (k n : Nat) (hk : k ≤ n) :
    firstColumns k n hk ∈ selectedColumnTuples k n := by
  rw [mem_selectedColumnTuples_iff]
  intro i j hij
  simp [firstColumns]
  exact hij

/-- Selecting the first `k` columns from the leading `k` rows of a square
matrix gives exactly its leading `k × k` prefix. -/
theorem columnTupleMatrix_leadingRows_firstColumns_eq_leadingPrefix
    {R : Type u} {n : Nat} (M : Matrix R n n) (k : Nat) (hk : k ≤ n) :
    columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn (firstColumns k n hk)) =
      leadingPrefix M k hk := by
  ext i hi j hj
  change
    (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn (firstColumns k n hk)))[
        (⟨i, hi⟩ : Fin k)][(⟨j, hj⟩ : Fin k)] =
      (leadingPrefix M k hk)[(⟨i, hi⟩ : Fin k)][(⟨j, hj⟩ : Fin k)]
  simp [columnTupleMatrix, leadingRows, leadingPrefix, columnTupleVectorFn, firstColumns, ofFn]

/-- The Gram determinant of the first `k` rows of a positive-diagonal integer
upper-triangular matrix is strictly positive. The leading-principal minor
provides a positive square term in the Cauchy-Binet expansion. -/
theorem det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i])
    (k : Nat) (hk : k ≤ n) :
    0 < det (gramMatrix (leadingRows M k hk)) := by
  rw [det_gramMatrix_eq_sum_minors_sq (leadingRows M k hk)]
  let cols := firstColumns k n hk
  have hmem : cols ∈ selectedColumnTuples k n :=
    firstColumns_mem_selectedColumnTuples k n hk
  have hminor_eq :
      det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)) =
        det (leadingPrefix M k hk) := by
    dsimp [cols]
    rw [columnTupleMatrix_leadingRows_firstColumns_eq_leadingPrefix M k hk]
  have hprefixZero :
      ∀ i j : Fin k, j.val < i.val → (leadingPrefix M k hk)[i][j] = 0 := by
    intro i j hij
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    have hentry : (leadingPrefix M k hk)[i][j] = M[ii][jj] := by
      simp [leadingPrefix, ofFn, ii, jj]
    rw [hentry]
    exact hzero ii jj hij
  have hprefixDiag :
      ∀ i : Fin k, 0 < (leadingPrefix M k hk)[i][i] := by
    intro i
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    have hentry : (leadingPrefix M k hk)[i][i] = M[ii][ii] := by
      simp [leadingPrefix, ofFn, ii]
    rw [hentry]
    exact hdiag ii
  have hminor_pos :
      0 < det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)) := by
    rw [hminor_eq]
    exact det_upperTriangular_pos_diag (leadingPrefix M k hk) hprefixZero hprefixDiag
  have hminor_sq_pos :
      0 < det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)) ^ 2 := by
    simpa [Lean.Grind.Semiring.pow_two] using Int.mul_pos hminor_pos hminor_pos
  exact foldl_int_sum_sq_pos_of_mem
    (xs := selectedColumnTuples k n)
    (f := fun cols => det (columnTupleMatrix (leadingRows M k hk) (columnTupleVectorFn cols)))
    (x := cols) hmem hminor_sq_pos


end Matrix
end Hex
