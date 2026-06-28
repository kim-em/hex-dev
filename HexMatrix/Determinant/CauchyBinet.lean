module

public import HexMatrix.Determinant.ColumnLinear
public import HexMatrix.Gram
import all HexMatrix.Determinant.ColumnLinear

public section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Square submatrix obtained by selecting an ordered tuple of columns. -/
@[expose]
def columnTupleMatrix {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) : Matrix R n n :=
  ofFn fun r c => A[r][cols c]

/-- Entry `(r, c)` of the column-selected minor is the source entry
`A[r][cols c]`. -/
@[grind =] theorem columnTupleMatrix_entry {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) (r c : Fin n) :
    (columnTupleMatrix A cols)[r][c] = A[r][cols c] := by
  simp [columnTupleMatrix, ofFn]

/-- Interpret an ordered column tuple vector as its column-selection function. -/
@[expose]
def columnTupleVectorFn {n m : Nat} (cols : Vector (Fin m) n) : Fin n → Fin m :=
  fun i => cols[i]

/-- Applying the column-selection function at `i` reads the `i`-th entry
`cols[i]` of the tuple vector. -/
@[simp, grind =] theorem columnTupleVectorFn_apply {n m : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    columnTupleVectorFn cols i = cols[i] := rfl

/-- Reindexing the selected columns by a permutation is entrywise the generic
column permutation of the selected minor.

Unattributed: the LHS `[r][c]` is not in simp-normal form (`Fin.getElem_fin`
rewrites the `Fin` indices to `↑r`/`↑c`), and `grind =` rejects the pattern
because the columns `s sigma` appear only under the `fun i => s[sigma[i]]`
binder, so the LHS cannot instantiate them. Invoked explicitly via `rw`. -/
theorem columnTupleMatrix_compose_perm_entry
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (r c : Fin n) :
    (columnTupleMatrix A (fun i => s[sigma[i]]))[r][c] =
      (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]] := by
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact (congrArg (fun col : Fin m => A[r][col])
    (columnTupleVectorFn_apply s (sigma[c]))).symm

/-- Reindexing the selected columns by a permutation is the generic column
permutation of the selected minor. -/
theorem columnTupleMatrix_compose_perm_eq_colPermute
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n) :
    columnTupleMatrix A (fun i => s[sigma[i]]) =
      (ofFn fun r c => (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]]) := by
  ext r hr c hc
  change
    (columnTupleMatrix A (fun i => s[sigma[i]]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (ofFn fun r c =>
        (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]])[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnTupleMatrix_compose_perm_entry]
  simp [Matrix.ofFn]

/-- Specialization of the generic column-permutation determinant sign theorem
to selected-minor matrices. -/
theorem det_columnTupleMatrix_compose_perm
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n) :
    det (columnTupleMatrix A (fun i => s[sigma[i]])) =
      detSign (R := R) sigma * det (columnTupleMatrix A (columnTupleVectorFn s)) := by
  rw [columnTupleMatrix_compose_perm_eq_colPermute A s sigma]
  exact det_colPermute_vector (columnTupleMatrix A (columnTupleVectorFn s)) sigma hsigma

/-- Enumerate all ordered `n`-tuples of columns from `Fin m`. -/
@[expose]
def columnTupleVectors : (n m : Nat) → List (Vector (Fin m) n)
  | 0, _ => [#v[]]
  | n + 1, m =>
      (columnTupleVectors n m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last n)

private theorem columnTupleVectors_ofFn_succ
    {n m : Nat} (cols : Fin (n + 1) → Fin m) :
    Vector.ofFn cols =
      insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
        (Fin.last n) := by
  ext i hi
  apply Fin.val_eq_of_eq
  change (Vector.ofFn cols)[(⟨i, hi⟩ : Fin (n + 1))] =
    (insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
      (Fin.last n))[(⟨i, hi⟩ : Fin (n + 1))]
  by_cases hlast : i = n
  · subst i
    simp [insertAt, List.getElem_insertIdx_self]
    exact congrArg cols (Fin.ext rfl)
  · have hi_lt : i < n := by omega
    simp [insertAt, List.getElem_insertIdx_of_lt, hi_lt]

/-- Every ordered column-selection function occurs in `columnTupleVectors`. -/
theorem columnTupleVectors_mem_ofFn {n m : Nat} (cols : Fin n → Fin m) :
    Vector.ofFn cols ∈ columnTupleVectors n m := by
  induction n with
  | zero =>
      simp [columnTupleVectors]
  | succ n ih =>
      rw [columnTupleVectors_ofFn_succ cols]
      rw [columnTupleVectors, List.mem_flatMap]
      refine ⟨Vector.ofFn fun i : Fin n => cols i.castSucc, ih (fun i => cols i.castSucc), ?_⟩
      rw [List.mem_map]
      exact ⟨cols (Fin.last n), List.mem_finRange (cols (Fin.last n)), rfl⟩

private theorem insertAt_last_injective_pair {α : Type u} {n : Nat}
    {c c' : α} {pref pref' : Vector α n}
    (h : insertAt c pref (Fin.last n) = insertAt c' pref' (Fin.last n)) :
    c = c' ∧ pref = pref' := by
  constructor
  · have hlast :
        (insertAt c pref (Fin.last n))[Fin.last n] =
          (insertAt c' pref' (Fin.last n))[Fin.last n] := by
      rw [h]
    rw [insertAt_get_self, insertAt_get_self] at hlast
    exact hlast
  · ext i hi
    let idx : Fin n := ⟨i, hi⟩
    have hidx :
        (insertAt c pref (Fin.last n))[idx.castSucc] =
          (insertAt c' pref' (Fin.last n))[idx.castSucc] := by
      rw [h]
    rw [insertAt_last_get_castSucc, insertAt_last_get_castSucc] at hidx
    exact hidx

private theorem columnTupleVectors_flatMap_last_nodup {n m : Nat} :
    ∀ (prefs : List (Vector (Fin m) n)), prefs.Nodup →
      (prefs.flatMap fun pref =>
        (List.finRange m).map fun c => insertAt c pref (Fin.last n)).Nodup
  | [], _ => by simp
  | pref :: prefs, hnodup => by
      simp only [List.flatMap_cons]
      simp only [List.nodup_cons] at hnodup
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · apply list_nodup_map_on (List.nodup_finRange m)
        intro c _hc c' _hc' h
        exact (insertAt_last_injective_pair h).1
      · exact columnTupleVectors_flatMap_last_nodup prefs hnodup.2
      · intro a hahead b hbsuffix hab
        rcases List.mem_map.mp hahead with ⟨c, _hc, rfl⟩
        rcases List.mem_flatMap.mp hbsuffix with ⟨pref', hpref', hb⟩
        rcases List.mem_map.mp hb with ⟨c', _hc', hb_eq⟩
        have hrec :
            insertAt c pref (Fin.last n) =
              insertAt c' pref' (Fin.last n) := hab.trans hb_eq.symm
        have hpref_eq := (insertAt_last_injective_pair hrec).2
        subst hpref_eq
        exact hnodup.1 hpref'

private theorem columnTupleVectors_nodup {n m : Nat} :
    (columnTupleVectors n m).Nodup := by
  induction n with
  | zero =>
      simp [columnTupleVectors]
  | succ n ih =>
      rw [columnTupleVectors]
      exact columnTupleVectors_flatMap_last_nodup (columnTupleVectors n m) ih

/-- Product coefficient attached to an ordered column tuple in the Gram expansion. -/
@[expose]
def columnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * A[i][cols[i]]) 1

/-- The determinant summand associated to an ordered column tuple. -/
@[expose]
def columnTupleExpansionTerm {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  columnTupleCoeff A cols * det (columnTupleMatrix A (columnTupleVectorFn cols))

/-- An ordered column-tuple minor with a repeated selected column has determinant zero. -/
theorem det_columnTupleMatrix_eq_zero_of_col_eq
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    {src dst : Fin n} (h : src ≠ dst) (hcols : cols src = cols dst) :
    det (columnTupleMatrix A cols) = 0 := by
  apply det_eq_zero_of_col_eq (columnTupleMatrix A cols) src dst h
  intro r
  rw [columnTupleMatrix_entry, columnTupleMatrix_entry]
  exact congrArg (fun c : Fin m => A[r][c]) hcols

/-- An ordered column-tuple minor with a non-injective selected-column map has
determinant zero. -/
theorem det_columnTupleMatrix_eq_zero_of_not_injective
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    (hcols : ¬ Function.Injective cols) :
    det (columnTupleMatrix A cols) = 0 := by
  classical
  have hdup : ∃ src dst : Fin n, cols src = cols dst ∧ src ≠ dst := by
    rw [Function.Injective] at hcols
    rcases Classical.not_forall.mp hcols with ⟨src, hsrc⟩
    rcases Classical.not_forall.mp hsrc with ⟨dst, hdst⟩
    exact ⟨src, dst, (not_imp.mp hdst).1, fun h => (not_imp.mp hdst).2 h⟩
  rcases hdup with ⟨src, dst, hsame, hne⟩
  exact det_columnTupleMatrix_eq_zero_of_col_eq A cols hne hsame

/-- The square matrix obtained from `columnSumMatrix source coeff` by replacing
the first `chosen.length` columns with selected `source` columns indexed by
`chosen`. The remaining columns stay in finite-sum form. -/
private def columnSumMatrixWithPrefix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) : Matrix R n n :=
  ofFn fun r j =>
    if h : j.val < chosen.length then
      source[r][chosen[j.val]'h]
    else
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrixWithPrefix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (columnSumMatrixWithPrefix source coeff chosen)[r][j] =
      if h : j.val < chosen.length then
        source[r][chosen[j.val]'h]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrixWithPrefix, ofFn]

/-! ### Suffix-based partial assignment

We use a SUFFIX-based parametrization (chosen represents right-fixed columns)
to align with the natural recursion of `columnTupleVectors`, which factors out
the LAST element of the suffix. After Fubini sum-swap, the inductive step
reduces to identity matching of the per-term values. -/

/-- Square matrix where the last `chosen.length` columns are fixed to selected
`source` columns indexed by `chosen` (in order), and the remaining left columns
stay in finite-sum form. -/
private def columnSumMatrixWithSuffix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) : Matrix R n n :=
  ofFn fun r j =>
    if h : n - chosen.length ≤ j.val then
      source[r][chosen[j.val - (n - chosen.length)]'(by
        have : j.val < n := j.isLt; omega)]
    else
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[grind =] private theorem columnSumMatrixWithSuffix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (columnSumMatrixWithSuffix source coeff chosen)[r][j] =
      if h : n - chosen.length ≤ j.val then
        source[r][chosen[j.val - (n - chosen.length)]'(by
          have : j.val < n := j.isLt; omega)]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrixWithSuffix, ofFn]

private theorem columnSumMatrixWithSuffix_nil
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    columnSumMatrixWithSuffix source coeff [] = columnSumMatrix source coeff := by
  ext r hr c hc
  change (columnSumMatrixWithSuffix source coeff [])[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithSuffix_entry, columnSumMatrix_entry]
  rw [dif_neg (show ¬ n - ([] : List (Fin m)).length ≤ c by simp; omega)]

private theorem columnSumMatrixWithSuffix_eq
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hfull : chosen.length = n) :
    columnSumMatrixWithSuffix source coeff chosen =
      columnTupleMatrix source (fun j => chosen[j.val]'(by omega)) := by
  ext r hr c hc
  change (columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix source (fun j => chosen[j.val]'(by omega)))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithSuffix_entry, dif_pos (by omega : n - chosen.length ≤ c)]
  simp [columnTupleMatrix, ofFn, hfull]

/-- Replacing the rightmost sum column of the suffix-partial matrix with a fixed
`source` column extends the suffix by prepending that selection. -/
private theorem setCol_columnSumMatrixWithSuffix_extend
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) (c : Fin m) :
    setCol (columnSumMatrixWithSuffix source coeff chosen)
        (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]) =
      columnSumMatrixWithSuffix source coeff (c :: chosen) := by
  ext r hr k hk2
  change (setCol (columnSumMatrixWithSuffix source coeff chosen)
      (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)] =
    (columnSumMatrixWithSuffix source coeff (c :: chosen))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)]
  rw [setCol_getElem]
  simp only [columnSumMatrixWithSuffix_entry]
  have hccons_len : (c :: chosen).length = chosen.length + 1 := rfl
  by_cases hkd : (⟨k, hk2⟩ : Fin n) = (⟨n - chosen.length - 1, by omega⟩ : Fin n)
  · have hkeq : k = n - chosen.length - 1 := by
      have := congrArg Fin.val hkd; simpa using this
    rw [if_pos hkd]
    rw [dif_pos (show n - (c :: chosen).length ≤ k by rw [hccons_len]; omega)]
    have hsub0 : k - (n - (c :: chosen).length) = 0 := by rw [hccons_len]; omega
    have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
        have : k < n := hk2; rw [hccons_len]; omega) = c := by
      have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        (c :: chosen)[(0 : Nat)]'(by simp) := by
        congr 1
      rw [h1]
      rfl
    exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
  · rw [if_neg hkd]
    have hkne : k ≠ n - chosen.length - 1 := fun h => hkd (Fin.ext h)
    by_cases hkge : n - chosen.length ≤ k
    · rw [dif_pos hkge]
      have hkge' : n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_pos hkge']
      have hidx_eq : k - (n - (c :: chosen).length) = (k - (n - chosen.length)) + 1 := by
        rw [hccons_len]; omega
      have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        chosen[k - (n - chosen.length)]'(by have : k < n := hk2; omega) := by
        have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
            have : k < n := hk2; rw [hccons_len]; omega) =
          (c :: chosen)[(k - (n - chosen.length)) + 1]'(by
            have : k < n := hk2; rw [hccons_len]; omega) := by
          congr 1
        rw [h1]
        rfl
      exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
    · rw [dif_neg hkge]
      have hkge' : ¬ n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_neg hkge']

/-- One-step expansion of the suffix-partial matrix: peel off the rightmost sum
column as a sum over `Fin m`. -/
private theorem det_columnSumMatrixWithSuffix_expand
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    det (columnSumMatrixWithSuffix source coeff chosen) =
      (List.finRange m).foldl
        (fun acc c => acc + coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          det (columnSumMatrixWithSuffix source coeff (c :: chosen))) 0 := by
  let dst : Fin n := ⟨n - chosen.length - 1, by omega⟩
  have hself :
      setCol (columnSumMatrixWithSuffix source coeff chosen) dst
          (fun r => (List.finRange m).foldl
            (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
        columnSumMatrixWithSuffix source coeff chosen := by
    ext r hr c hc
    change (setCol (columnSumMatrixWithSuffix source coeff chosen) dst _)[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [setCol_getElem, columnSumMatrixWithSuffix_entry]
    by_cases hcd : (⟨c, hc⟩ : Fin n) = dst
    · rw [if_pos hcd, hcd]
      rw [dif_neg (show ¬ n - chosen.length ≤ dst.val by simp [dst]; omega)]
    · rw [if_neg hcd]
  have hsum := det_setCol_sum_list
      (columnSumMatrixWithSuffix source coeff chosen) dst
      (List.finRange m) (fun k => coeff[dst][k]) (fun k r => source[r][k])
  rw [hself] at hsum
  rw [hsum]
  apply foldl_det_sum_congr
  intro c _hc
  congr 2
  exact setCol_columnSumMatrixWithSuffix_extend source coeff chosen hk c

private def assembleColumnsSuffix {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n) :
    Vector (Fin m) n :=
  ⟨(pref.toList ++ chosen).toArray, by
    simp [hk]⟩

@[grind =] private theorem assembleColumnsSuffix_left
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin (n - chosen.length)) :
    (assembleColumnsSuffix chosen pref hk)[
        (⟨i.val, by
          have hi : i.val < n - chosen.length := i.isLt
          omega⟩ : Fin n)] = pref[i] := by
  simp [assembleColumnsSuffix]

@[grind =] private theorem assembleColumnsSuffix_right
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin chosen.length) :
    (assembleColumnsSuffix chosen pref hk)[
        (⟨n - chosen.length + i.val, by
          have hi : i.val < chosen.length := i.isLt
          omega⟩ : Fin n)] = chosen[i] := by
  unfold assembleColumnsSuffix
  simp [List.getElem_append_right]

private def vectorLengthCast {α : Type u} {n k : Nat} (h : n = k)
    (v : Vector α n) : Vector α k :=
  match v with
  | ⟨xs, hx⟩ => ⟨xs, by simpa [h] using hx⟩

private theorem columnTupleVectors_foldl_vectorLengthCast
    {α : Type u} {m k l : Nat} (h : k = l)
    (f : α → Vector (Fin m) l → α) (init : α) :
    (columnTupleVectors l m).foldl f init =
      (columnTupleVectors k m).foldl
        (fun acc pref => f acc (vectorLengthCast h pref)) init := by
  subst h
  rfl

private theorem assembleColumnsSuffix_insertAt_last
    {n m : Nat} (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    assembleColumnsSuffix chosen
        (vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length))))
        (by
          have hcons : (c :: chosen).length = chosen.length + 1 := rfl
          omega) =
      assembleColumnsSuffix (c :: chosen) pref hk := by
  apply Vector.toArray_inj.mp
  unfold assembleColumnsSuffix
  simp only [vectorLengthCast, Vector.toList, insertAt]
  have hidx : (Fin.last (n - (c :: chosen).length)).val = pref.toArray.toList.length := by
    simp
  rw [hidx, list_insertIdx_length]
  simp [List.append_assoc]

private theorem det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
    {R : Type u} [Lean.Grind.Ring R] {n m : Nat} (source : Matrix R n m)
    (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    det (columnTupleMatrix source
        (columnTupleVectorFn
          (assembleColumnsSuffix chosen
            (vectorLengthCast hlen
              (insertAt c pref (Fin.last (n - (c :: chosen).length))))
            (by
              have hcons : (c :: chosen).length = chosen.length + 1 := rfl
              omega)))) =
      det (columnTupleMatrix source
        (columnTupleVectorFn (assembleColumnsSuffix (c :: chosen) pref hk))) := by
  rw [assembleColumnsSuffix_insertAt_last chosen c pref hk hlen]

private def partialColumnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) : R :=
  (List.finRange (n - chosen.length)).foldl
    (fun acc i => acc * coeff[(⟨i.val, by
      have hi : i.val < n - chosen.length := i.isLt
      omega⟩ : Fin n)][pref[i]]) 1

private theorem partialColumnTupleCoeff_nil
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (cols : Vector (Fin m) n) :
    partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols := by
  unfold partialColumnTupleCoeff columnTupleCoeff
  apply foldl_det_product_congr
  intro i _hmem
  congr 2

private theorem partialColumnTupleCoeff_insertAt_last_fold
    {R : Type u} [Mul R] [OfNat R 1] {n m rem : Nat}
    (coeff : Matrix R n m) (c : Fin m) (pref : Vector (Fin m) rem)
    (hrem : rem < n) :
    (List.finRange (rem + 1)).foldl
        (fun acc i => acc * coeff[(⟨i.val, by
          have hi : i.val < rem + 1 := i.isLt
          omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i]]) 1 =
      (List.finRange rem).foldl
          (fun acc i => acc * coeff[(⟨i.val, by
            have hi : i.val < rem := i.isLt
            omega⟩ : Fin n)][pref[i]]) 1 *
        coeff[(⟨rem, hrem⟩ : Fin n)][c] := by
  rw [List.finRange_succ_last]
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 1
  · simp only [List.foldl_map]
    apply foldl_det_product_congr
    intro i _hmem
    change
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i.castSucc]] =
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][pref[i]]
    exact congrArg
      (fun x : Fin m => coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][x])
      (insertAt_last_get_castSucc c pref i)
  · change
      coeff[(⟨rem, hrem⟩ : Fin n)][(insertAt c pref (Fin.last rem))[Fin.last rem]] =
        coeff[(⟨rem, hrem⟩ : Fin n)][c]
    exact congrArg (fun x : Fin m => coeff[(⟨rem, hrem⟩ : Fin n)][x])
      (insertAt_get_self c pref (Fin.last rem))

private theorem partialColumnTupleCoeff_vectorLengthCast
    {R : Type u} [Mul R] [OfNat R 1] {n m k : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : k = n - chosen.length) (hkn : k ≤ n) (v : Vector (Fin m) k) :
    partialColumnTupleCoeff coeff chosen (vectorLengthCast hk v) =
    (List.finRange k).foldl
      (fun acc (i : Fin k) => acc *
        coeff[(⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩ : Fin n)][v[i]]) 1 := by
  subst hk
  unfold partialColumnTupleCoeff
  rcases v with ⟨xs, hx⟩
  rfl

private theorem partialColumnTupleCoeff_insertAt_last
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    partialColumnTupleCoeff coeff chosen
        (vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length)))) =
      coeff[(⟨n - chosen.length - 1, by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega⟩ : Fin n)][c] *
        partialColumnTupleCoeff coeff (c :: chosen) pref := by
  have hcons : (c :: chosen).length = chosen.length + 1 := rfl
  have hrem_lt : n - (c :: chosen).length < n := by omega
  have hlen_le : (n - (c :: chosen).length) + 1 ≤ n := by omega
  rw [partialColumnTupleCoeff_vectorLengthCast coeff chosen hlen hlen_le
      (insertAt c pref (Fin.last (n - (c :: chosen).length)))]
  rw [partialColumnTupleCoeff_insertAt_last_fold coeff c pref hrem_lt]
  unfold partialColumnTupleCoeff
  refine Eq.trans (Lean.Grind.CommSemiring.mul_comm _ _) ?_
  congr 1

private theorem columnTupleVectors_suffix_rhs_step
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors ((n - (chosen.length + 1)) + 1) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen
            (vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
              n - chosen.length) pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen
                  (vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
                    n - chosen.length) pref) (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  have hlen :
      n - chosen.length = (n - (chosen.length + 1)) + 1 := by
    omega
  change
    (((columnTupleVectors (n - (chosen.length + 1)) m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last (n - (chosen.length + 1)))).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen (vectorLengthCast hlen.symm pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen (vectorLengthCast hlen.symm pref) (by omega))))) 0) =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0
  rw [foldl_det_sum_flatMap]
  simp only [List.foldl_map]
  rw [foldl_det_sum_nested_zero]
  rw [foldl_det_sum_swap]
  apply foldl_det_sum_congr
  intro c _hc
  have hfactor :
      (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
              (partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega)))))) 0 =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          (columnTupleVectors (n - (chosen.length + 1)) m).foldl
            (fun acc pref => acc +
              partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega))))) 0 := by
    exact foldl_det_sum_mul_left_zero
      (columnTupleVectors (n - (chosen.length + 1)) m)
      (coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c])
      (fun pref =>
        partialColumnTupleCoeff coeff (c :: chosen) pref *
          det (columnTupleMatrix source
            (columnTupleVectorFn
              (assembleColumnsSuffix (c :: chosen) pref (by
                have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                omega)))))
  change
    (columnTupleVectors (n - (chosen.length + 1)) m).foldl
        (fun acc' x => acc' +
          partialColumnTupleCoeff coeff chosen
              (vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1))))) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen
                  (vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1)))))
                  (by omega))))) 0 =
      coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
        (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            partialColumnTupleCoeff coeff (c :: chosen) pref *
              det (columnTupleMatrix source
                (columnTupleVectorFn
                  (assembleColumnsSuffix (c :: chosen) pref (by
                    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                    omega))))) 0
  rw [← hfactor]
  apply foldl_det_sum_congr
  intro pref _hpref
  have hcast :
      (n - (chosen.length + 1)) + 1 = n - chosen.length := by
    omega
  have hkcons : (c :: chosen).length ≤ n := by
    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
    omega
  have hcoeff :
      partialColumnTupleCoeff coeff chosen
          (vectorLengthCast hcast
            (insertAt c pref (Fin.last (n - (chosen.length + 1))))) =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          partialColumnTupleCoeff coeff (c :: chosen) pref := by
    simpa only [List.length_cons] using
      (partialColumnTupleCoeff_insertAt_last coeff chosen c pref hkcons hcast)
  have hdet :
      det (columnTupleMatrix source
          (columnTupleVectorFn
            (assembleColumnsSuffix chosen
              (vectorLengthCast hcast
                (insertAt c pref (Fin.last (n - (chosen.length + 1)))))
              (by omega)))) =
        det (columnTupleMatrix source
          (columnTupleVectorFn (assembleColumnsSuffix (c :: chosen) pref hkcons))) := by
    simpa only [List.length_cons] using
      (det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
        source chosen c pref hkcons hcast)
  rw [hcoeff, hdet]
  grind

private theorem columnTupleVectors_suffix_rhs_step_natural
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen pref (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  rw [columnTupleVectors_foldl_vectorLengthCast
    (by omega : (n - (chosen.length + 1)) + 1 = n - chosen.length)]
  exact columnTupleVectors_suffix_rhs_step source coeff chosen hk

private theorem assembleColumnsSuffix_full
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hk : chosen.length ≤ n) (hfull : chosen.length = n) :
    assembleColumnsSuffix chosen pref hk =
      Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)) := by
  ext i hi
  apply Fin.val_eq_of_eq
  change (assembleColumnsSuffix chosen pref hk)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)))[(⟨i, hi⟩ : Fin n)]
  simpa [hfull] using
    (assembleColumnsSuffix_right chosen pref hk (⟨i, by omega⟩ : Fin chosen.length))

private theorem partialColumnTupleCoeff_full
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hfull : chosen.length = n) :
    partialColumnTupleCoeff coeff chosen pref = 1 := by
  subst n
  unfold partialColumnTupleCoeff
  have hlist : List.finRange (chosen.length - chosen.length) = [] := by simp
  rw [hlist]
  rfl

private theorem det_columnSumMatrixWithSuffix_eq_sum
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length ≤ n) :
    det (columnSumMatrixWithSuffix source coeff chosen) =
      (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen pref hk)))) 0 := by
  by_cases hfull : chosen.length = n
  ·
      have hfull : chosen.length = n := by omega
      subst n
      rw [columnSumMatrixWithSuffix_eq source coeff chosen hfull]
      let hcast : 0 = chosen.length - chosen.length := by omega
      rw [columnTupleVectors_foldl_vectorLengthCast hcast]
      simp only [columnTupleVectors, List.foldl_cons, List.foldl_nil]
      rw [partialColumnTupleCoeff_full coeff chosen (vectorLengthCast hcast #v[]) hfull]
      have hdet :
          det (columnTupleMatrix source (fun j : Fin chosen.length => chosen[j.val]'(by omega))) =
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (assembleColumnsSuffix chosen (vectorLengthCast hcast #v[]) hk))) := by
        apply congrArg det
        apply congrArg (columnTupleMatrix source)
        funext j
        simp [columnTupleVectorFn]
        rw [assembleColumnsSuffix_full chosen (vectorLengthCast hcast #v[]) hk hfull]
        simp
      rw [hdet]
      grind
  ·
      have hklt : chosen.length < n := by omega
      rw [det_columnSumMatrixWithSuffix_expand source coeff chosen hklt]
      rw [columnTupleVectors_suffix_rhs_step_natural source coeff chosen hklt]
      apply foldl_det_sum_congr
      intro c _hc
      congr 2
      have hkcons : (c :: chosen).length ≤ n := by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega
      exact det_columnSumMatrixWithSuffix_eq_sum source coeff (c :: chosen) hkcons
termination_by n - chosen.length
decreasing_by
  simp_wf
  omega

/-- Expand the determinant of a matrix whose columns are linear combinations
of source columns as a finite sum over all ordered column tuples. This is the
Mathlib-free multilinearity form behind Cauchy-Binet. -/
theorem det_columnSumMatrix_eq_sum_columnTuples
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    det (columnSumMatrix source coeff) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff coeff cols *
            det (columnTupleMatrix source (columnTupleVectorFn cols))) 0 := by
  rw [← columnSumMatrixWithSuffix_nil source coeff]
  rw [det_columnSumMatrixWithSuffix_eq_sum source coeff [] (by simp)]
  apply foldl_det_sum_congr
  intro cols _hcols
  have hcoeff : partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols :=
    partialColumnTupleCoeff_nil coeff cols
  have hdet :
      det (columnTupleMatrix source (columnTupleVectorFn (assembleColumnsSuffix [] cols (by simp)))) =
        det (columnTupleMatrix source (columnTupleVectorFn cols)) := by
    apply congrArg det
    ext i hi j hj
    simp [columnTupleMatrix, columnTupleVectorFn, ofFn]
    change source[(⟨i, hi⟩ : Fin n)][
        (assembleColumnsSuffix [] cols (by simp))[(⟨j, hj⟩ : Fin n)]] =
      source[(⟨i, hi⟩ : Fin n)][cols[(⟨j, hj⟩ : Fin n)]]
    exact congrArg (fun x : Fin m => source[(⟨i, hi⟩ : Fin n)][x])
      (assembleColumnsSuffix_left ([] : List (Fin m)) cols (by simp) (⟨j, by simp [hj]⟩))
  rw [hcoeff, hdet]

/-- The determinant of a row Gram matrix expands as the ordered-column tuple
sum induced by the generic column-sum determinant expansion. -/
theorem det_gramMatrix_eq_sum_columnTuples
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    det (gramMatrix A) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff A cols *
            det (columnTupleMatrix A (columnTupleVectorFn cols))) 0 := by
  have hgram : gramMatrix A = columnSumMatrix A A := by
    ext r hr c hc
    change (gramMatrix A)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix A A)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [columnSumMatrix_entry]
    simp [gramMatrix, ofFn, row, Hex.Vector.dotProduct]
    apply foldl_det_sum_congr
    intro k _hk
    exact Lean.Grind.CommSemiring.mul_comm A[(⟨r, hr⟩ : Fin n)][k] A[(⟨c, hc⟩ : Fin n)][k]
  rw [hgram]
  exact det_columnSumMatrix_eq_sum_columnTuples A A


end Matrix
end Hex
