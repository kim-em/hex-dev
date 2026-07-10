/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic

public section

/-!
Core dense matrix definitions for `hex-matrix`.

This module models matrices with a **flat row-major** backing `Vector R (n * m)`
and provides the basic executable operations needed by later linear-algebra
algorithms: row/column accessors, zero and identity matrices, dot products,
matrix-vector multiplication, matrix-matrix multiplication, and norm-squared
helpers.

The backing is a single contiguous buffer holding the `n * m` entries in
row-major order: entry `(i, j)` lives at flat index `i * m + j`. The structure
stays an opaque one-field record so this representation is invisible to
consumers, who go through `ofFn`/`ofRows`/`getRow`/`rows` and the entry accessor
`M[(i, j)]` (see `HexMatrix/SPEC/hex-matrix.md`).
-/
namespace Hex

universe u v

/-- Dense `n × m` matrices over `R`, backed by a flat row-major buffer of the
`n * m` entries: entry `(i, j)` is stored at flat index `i * m + j`. Opaque
one-field structure; consumers go through `rows`/`getRow`/`ofRows`/`ofFn` and
`M[i]` / `M[(i,j)]`, never the `data` projection, so the representation can
change. -/
structure Matrix (R : Type u) (n m : Nat) where
  /-- Build a matrix from its flat row-major backing buffer. Implementation
  detail — use `ofRows`/`ofFn`, never this constructor. -/
  mk ::
  /-- Implementation detail — the flat row-major backing buffer. Use
  `Matrix.rows`/`getRow`, never this projection. -/
  data : Vector R (n * m)
deriving DecidableEq, BEq

end Hex

namespace Vector

/-- Dot product of two vectors.

This `List.finRange` form is the reference definition the entry lemmas reason
about; crucially it kernel-reduces, so `#guard`/`decide` checks over
`dotProduct` (e.g. `memLattice` membership) stay evaluable — core `Fin.foldl`
does not reduce in the kernel. Compiled code runs the allocation-free
`Fin.foldl` loop `dotProductImpl` via the `@[csimp]` below.

TODO: once https://github.com/leanprover/lean4/pull/14267 (make `Fin.foldl`
reduce in the kernel) lands and this project's toolchain is bumped past it,
collapse this reference/compiled split: define
`dotProduct` directly as the native `Fin.foldl` loop and delete `dotProductImpl`
and `dotProduct_eq_impl`. The native form will then kernel-reduce on its own, so
the `memLattice` `decide` checks keep working without the `List.finRange`
reference allocation. -/
@[expose]
noncomputable def dotProduct [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

/-- Allocation-free implementation of `dotProduct`: a `Fin.foldl` loop that never
materializes the `List.finRange n` index list. Swapped in for compiled code by the
`@[csimp]` lemma; `dotProduct` remains the reference form for proofs. -/
@[expose]
def dotProductImpl [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  Fin.foldl n (fun acc i => acc + u[i] * v[i]) 0

@[csimp] theorem dotProduct_eq_impl : @dotProduct = @dotProductImpl := by
  funext R n iMul iAdd iZero u v
  rw [dotProduct, dotProductImpl, Fin.foldl_eq_finRange_foldl]

/-- Squared Euclidean norm of a vector. -/
@[expose]
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  dotProduct v v

/-- The standard basis vector with value `1` at index `i` and `0` elsewhere. -/
@[expose]
def unit (R : Type u) [Zero R] [One R] (i : Fin n) : Vector R n :=
  Vector.ofFn fun j => if i = j then One.one else Zero.zero

/-- Entry formula for a standard basis vector. -/
@[grind =] theorem getElem_unit [Zero R] [One R] (i j : Fin n) :
    (unit R i)[j] = if i = j then One.one else Zero.zero := by
  simp [unit]

end Vector

namespace Hex

namespace Matrix

variable {R : Type u} {n m k : Nat}

/-! ### Flat-index arithmetic

Row-major flattening sends entry `(i, j)` to flat index `i * m + j`. These
helpers give the in-range bound and recover `i`, `j` from the flat index. -/

/-- The flat row-major index `i * m + j` of an in-range entry is in range. -/
theorem flatIdx_lt {i j : Nat} (hi : i < n) (hj : j < m) : i * m + j < n * m := by
  calc i * m + j < i * m + m := Nat.add_lt_add_left hj _
    _ = (i + 1) * m := by rw [Nat.succ_mul]
    _ ≤ n * m := Nat.mul_le_mul_right m hi

/-- Recover the row index from a flat index: `(i * m + j) / m = i` when `j < m`. -/
theorem flatIdx_div {i j m : Nat} (hj : j < m) : (i * m + j) / m = i := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]

/-- Recover the column index from a flat index: `(i * m + j) % m = j` when
`j < m`. -/
theorem flatIdx_mod {i j m : Nat} (hj : j < m) : (i * m + j) % m = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- The row index recovered from any in-range flat index is in range. -/
theorem row_of_lt {n m : Nat} (p : Fin (n * m)) : p.val / m < n :=
  Nat.div_lt_of_lt_mul (Nat.mul_comm n m ▸ p.isLt)

/-- The column index recovered from any in-range flat index is in range. -/
theorem col_of_lt {n m : Nat} (p : Fin (n * m)) : p.val % m < m := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd p.isLt (by simp)
    · exact h
  exact Nat.mod_lt _ hm

/-! ### Entry and row access

Both entry accessors and `getRow` read the flat buffer directly at `i * m + j`,
so a single-entry read is `O(1)` and never materializes a row. -/

/-- Entry access by a `Fin n × Fin m` index: the `O(1)` flat read. -/
instance : GetElem (Matrix R n m) (Fin n × Fin m) R (fun _ _ => True) where
  getElem M p _ := M.data[p.1.val * m + p.2.val]'(flatIdx_lt p.1.isLt p.2.isLt)

/-- Entry access by a `Nat × Nat` index. -/
instance : GetElem (Matrix R n m) (Nat × Nat) R (fun _ p => p.1 < n ∧ p.2 < m) where
  getElem M p h := M.data[p.1 * m + p.2]'(flatIdx_lt h.1 h.2)

/-- The `i`-th row of a matrix, materialized from the flat buffer. This copies the
`m` contiguous entries of row `i`; it is the computable row accessor compiled code
uses (single entries go through `M[(i, j)]`, which does not materialize a row). -/
@[inline, expose] def getRow (M : Matrix R n m) (i : Fin n) : Vector R m :=
  Vector.ofFn fun j => M.data[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt)

/-- Row access `M[i]` for `i : Fin n`. **Deliberately `noncomputable`**: with the
flat (`Vector R (n*m)`) representation, materializing a whole row just to read it
— and especially `M[i][j]` to read one entry — is the wrong cost model. This
instance exists only so *proofs* may write `M[i]` / `M[i][j]`; executable code
must use the computable `getRow` for rows and `M[(i, j)]` (O(1)) for single
entries. Any compiled definition that reaches for `M[i]` will fail to compile,
which is the intended guard. -/
noncomputable instance : GetElem (Matrix R n m) (Fin n) (Vector R m) (fun _ _ => True) where
  getElem M i _ := getRow M i

/-- Row access by a `Nat` index. Also `noncomputable`; see the `Fin n` instance. -/
noncomputable instance : GetElem (Matrix R n m) Nat (Vector R m) (fun _ i => i < n) where
  getElem M i h := getRow M ⟨i, h⟩

/-- The rows of a matrix as a vector of row-vectors, materialized from the flat
buffer. The only sanctioned way to observe the full row data; `O(n * m)`. -/
@[expose] def rows (M : Matrix R n m) : Vector (Vector R m) n :=
  Vector.ofFn fun i => getRow M i

/-- Build a matrix from a vector of its rows, flattening into the row-major
backing buffer. -/
@[expose] def ofRows (v : Vector (Vector R m) n) : Matrix R n m :=
  ⟨Vector.ofFn fun p : Fin (n * m) => (v[p.val / m]'(row_of_lt p))[p.val % m]'(col_of_lt p)⟩

/-- Build a matrix from an entry function, filling the flat backing buffer. -/
@[expose]
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  ⟨Vector.ofFn fun p : Fin (n * m) => f ⟨p.val / m, row_of_lt p⟩ ⟨p.val % m, col_of_lt p⟩⟩

/-! ### Core reduction lemmas -/

/-- Row access `M[i]` normalizes to the computable `getRow M i`. -/
@[simp, grind =] theorem getElem_eq_getRow (M : Matrix R n m) (i : Fin n) : M[i] = getRow M i := rfl

/-- `Nat`-indexed row access normalizes to `getRow`. -/
@[simp, grind =] theorem getElem_nat_eq_getRow (M : Matrix R n m) (i : Nat) (h : i < n) :
    M[i]'h = getRow M ⟨i, h⟩ := rfl

/-- Reading entry `j` of `getRow M i` is the flat read at `i * m + j`. -/
@[grind =] theorem getElem_getRow (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (getRow M i)[j] = M.data[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt) := by
  simp [getRow]

/-- `Nat`-indexed form of `getElem_getRow`, for `Vector.ext` proofs. -/
theorem getElem_getRow_nat (M : Matrix R n m) (i : Fin n) {j : Nat} (hj : j < m) :
    (getRow M i)[j]'hj = M.data[i.val * m + j]'(flatIdx_lt i.isLt hj) := by
  simp [getRow]

/-- The pair entry access (computable, O(1)) agrees with the nested row-then-element
form. The nested form is the simp-normal form the entry lemmas are stated in. -/
@[simp, grind =] theorem getElem_pair_eq_nested (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    M[(i, j)] = M[i][j] := by
  rw [getElem_eq_getRow, getElem_getRow]; rfl

/-- `Nat`-pair entry access, normalized to the row lookup (concrete-index form).
The statement observes rows, not the backing buffer, so it is representation-
independent; the flat read behind it is `getElem_pair_data` below. -/
@[simp] theorem getElem_pair_nat (M : Matrix R n m) (p : Nat × Nat)
    (h : p.1 < n ∧ p.2 < m) : M[p]'h = (M.rows[p.1]'h.1)[p.2]'h.2 := by
  simp only [rows, Vector.getElem_ofFn, getElem_getRow_nat]
  rfl

/-- The representation-level form of `getElem_pair_nat`: a `Nat`-pair entry
access is one flat read at `i * m + j`. Internal proofs that genuinely need the
buffer may use it; public statements should observe rows or entries instead. -/
private theorem getElem_pair_data (M : Matrix R n m) (p : Nat × Nat)
    (h : p.1 < n ∧ p.2 < m) : M[p]'h = M.data[p.1 * m + p.2]'(flatIdx_lt h.1 h.2) := rfl

/-- Two matrices are equal when their flat backing buffers are equal. -/
theorem ext_data {M N : Matrix R n m} (h : M.data = N.data) : M = N := by
  cases M; cases N; simp_all

/-- Two matrices are equal when they agree entrywise. -/
theorem ext_getElem {M N : Matrix R n m}
    (h : ∀ (i : Fin n) (j : Fin m), M[i][j] = N[i][j]) : M = N := by
  apply ext_data
  apply Vector.ext
  intro p hp
  have hi : p / m < n := row_of_lt ⟨p, hp⟩
  have hj : p % m < m := col_of_lt ⟨p, hp⟩
  have hrec : (p / m) * m + p % m = p := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod p m
  have hh := h ⟨p / m, hi⟩ ⟨p % m, hj⟩
  rw [getElem_eq_getRow, getElem_eq_getRow, getElem_getRow, getElem_getRow] at hh
  simp only [hrec] at hh
  exact hh

/-- Entry access for a matrix built from an entry function. -/
@[grind =] theorem getElem_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    (ofFn f)[i][j] = f i j := by
  rw [getElem_eq_getRow, getElem_getRow]
  simp only [ofFn, Vector.getElem_ofFn]
  exact congr (congrArg f (Fin.ext (flatIdx_div j.isLt))) (Fin.ext (flatIdx_mod j.isLt))

/-- `getRow` on `ofRows` reduces to the underlying vector. -/
@[simp, grind =] theorem getRow_ofRows (v : Vector (Vector R m) n) (i : Fin n) :
    getRow (ofRows v) i = v[i] := by
  apply Vector.ext
  intro j hj
  rw [getElem_getRow_nat]
  simp only [ofRows, Vector.getElem_ofFn, flatIdx_div hj, flatIdx_mod hj, Fin.getElem_fin]

/-- Entry access for a matrix built from a vector of rows. -/
@[grind =] theorem getElem_ofRows (v : Vector (Vector R m) n) (i : Fin n) (j : Fin m) :
    (ofRows v)[i][j] = v[i][j] := by
  rw [getElem_eq_getRow, getRow_ofRows]

@[simp, grind =] theorem rows_ofRows (v : Vector (Vector R m) n) : (ofRows v).rows = v := by
  apply Vector.ext
  intro i hi
  simp only [rows, Vector.getElem_ofFn]
  exact getRow_ofRows v ⟨i, hi⟩

/-- Two matrices are equal when their rows are equal. -/
@[ext] theorem ext {M N : Matrix R n m} (h : M.rows = N.rows) : M = N := by
  apply ext_getElem
  intro i j
  rw [getElem_eq_getRow, getElem_eq_getRow]
  have hrow : getRow M i = getRow N i := by
    have := congrArg (fun v => v[i.val]'(by simp) ) h
    simpa only [rows, Vector.getElem_ofFn] using this
  rw [hrow]

/-- The `i`-th row of a matrix. -/
@[expose]
def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  getRow M i

/-- Entry access for a selected matrix row. -/
@[grind =] theorem getElem_row (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (row M i)[j] = M[i][j] := by
  rfl

/-- The `j`-th column of a matrix. -/
@[expose]
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn fun i => M[(i, j)]

/-- Entry access for a selected matrix column. -/
@[grind =] theorem getElem_col (M : Matrix R n m) (j : Fin m) (i : Fin n) :
    (col M j)[i] = M[i][j] := by
  simp [col]

/-! ### In-place row mutation

The elementary operations update the single backing buffer in place when the
matrix is uniquely referenced. `writeRow` overwrites the `m` entries of one row;
`swapRows` exchanges two rows; both mutate the buffer through `Vector.set` /
`Vector.swap`, which reuse the store rather than copying it when the buffer is
owned. -/

/-- Overwrite the `m` entries of row `dst` of the flat buffer `d` with the entries
of `v`, in place when `d` is uniquely referenced. -/
@[inline]
def writeRow (d : Vector R (n * m)) (dst : Nat) (hdst : dst < n) (v : Vector R m) :
    Vector R (n * m) :=
  Fin.foldl m (fun d (t : Fin m) => d.set (dst * m + t.val) v[t] (flatIdx_lt hdst t.isLt)) d

/-- Replace row `dst` of `M` with the vector `v`. Linear in `M`: the matrix is
consumed, so the backing buffer is owned and `writeRow` updates it in place. -/
@[expose]
def setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨writeRow d dst.val dst.isLt v⟩

/-- Modification of row `i`. The matrix is consumed; the row is read out once
(a borrowed read into a fresh `m`-vector, before the buffer is written), `f` is
applied, and the result is written back through `writeRow`, in place when the
runtime sees the buffer uniquely referenced at the write. -/
@[expose, inline]
def modifyRow (M : Matrix R n m) (i : Nat) (f : Vector R m → Vector R m) : Matrix R n m :=
  if h : i < n then
    match M with
    | ⟨d⟩ =>
      let cur : Vector R m := Vector.ofFn fun t : Fin m => d[i * m + t.val]'(flatIdx_lt h t.isLt)
      ⟨writeRow d i h (f cur)⟩
  else M

/-- Swap rows `i` and `j`, in place when `M` is uniquely referenced. -/
@[expose, inline]
def swap (M : Matrix R n m) (i j : Nat) (hi : i < n := by get_elem_tactic)
    (hj : j < n := by get_elem_tactic) : Matrix R n m :=
  match M with
  | ⟨d⟩ =>
    ⟨Fin.foldl m (fun d (t : Fin m) =>
      d.swap (i * m + t.val) (j * m + t.val) (flatIdx_lt hi t.isLt) (flatIdx_lt hj t.isLt)) d⟩

/-- Map a function over every row. The row width may change, so this materializes
the rows, maps, and reflattens. -/
@[expose, inline]
def mapRows (M : Matrix R n m) (f : Vector R m → Vector R m') : Matrix R n m' :=
  ofRows (M.rows.map f)

/-- Reading a row out of `rows` is `getRow`. The bridge between the
`Vector (Vector R m) n` observation and the flat accessor. -/
@[simp] theorem getElem_rows (M : Matrix R n m) (i : Nat) (hi : i < n) :
    M.rows[i]'hi = getRow M ⟨i, hi⟩ := by
  simp only [rows, Vector.getElem_ofFn]

/-! ### Scatter characterizations of the in-place row loops

`writeRow` and the `swap` loop are `Fin.foldl`s of per-column single-index
updates into the flat buffer. Distinct fold steps touch distinct flat indices
(`i * m + t` determines `(i, t)` by `flatIdx_div` / `flatIdx_mod`), so each loop
is characterized by an entrywise read lemma, proved by the same
list-induction-over-`finRange` scheme as `Vector.getElem_finFoldl_modify`. -/

/-- A left fold of per-index `set`s leaves untouched every position not among
the written indices. -/
private theorem foldl_set_ne {N : Nat} (idx : Fin m → Nat) (val : Fin m → R)
    (bd : ∀ t, idx t < N) {p : Nat} (hp : p < N) :
    ∀ (xs : List (Fin m)) (d0 : Vector R N), (∀ t ∈ xs, idx t ≠ p) →
      (xs.foldl (fun d t => d.set (idx t) (val t) (bd t)) d0)[p]'hp = d0[p]'hp := by
  intro xs
  induction xs with
  | nil => intro d0 _; rfl
  | cons x xs ih =>
    intro d0 hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht)),
      Vector.getElem_set_ne (bd x) hp (hne x List.mem_cons_self)]

/-- A left fold of per-index `set`s at injectively-indexed positions over a
`Nodup` list writes `val r` at position `idx r` for every member `r`. -/
private theorem foldl_set_mem {N : Nat} (idx : Fin m → Nat) (val : Fin m → R)
    (bd : ∀ t, idx t < N) (hinj : ∀ a b : Fin m, idx a = idx b → a = b) :
    ∀ (xs : List (Fin m)), xs.Nodup → ∀ (d0 : Vector R N) (r : Fin m), r ∈ xs →
      (xs.foldl (fun d t => d.set (idx t) (val t) (bd t)) d0)[idx r]'(bd r) = val r := by
  intro xs
  induction xs with
  | nil => intro _ d0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd d0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [foldl_set_ne idx val bd (bd r) xs _ (fun t ht heq =>
        (List.nodup_cons.mp hnd).1 ((hinj t r heq) ▸ ht))]
      exact Vector.getElem_set_self (bd r)
    · rw [ih (List.nodup_cons.mp hnd).2 _ r hr']

/-- `List.finRange k` has no repeated indices (core-only proof; the Batteries
`nodup_finRange` is outside this Mathlib-free module's import closure). -/
private theorem nodup_finRange (k : Nat) : (List.finRange k).Nodup := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨by simp [Fin.ext_iff],
      List.Pairwise.map _ (fun _ _ hab h => hab (Fin.succ_inj.mp h)) ih⟩

/-- Flat row-major indices are injective in the column for a fixed row. -/
private theorem flatIdx_col_inj {i : Nat} :
    ∀ a b : Fin m, i * m + a.val = i * m + b.val → a = b :=
  fun _ _ h => Fin.ext (by omega)

/-- A left fold of per-index `modify`s leaves untouched every position not among
the modified indices. -/
private theorem foldl_modify_ne {N : Nat} (idx : Fin m → Nat) (g : Fin m → R → R)
    {p : Nat} (hp : p < N) :
    ∀ (xs : List (Fin m)) (d0 : Vector R N), (∀ t ∈ xs, idx t ≠ p) →
      (xs.foldl (fun d t => d.modify (idx t) (g t)) d0)[p]'hp = d0[p]'hp := by
  intro xs
  induction xs with
  | nil => intro d0 _; rfl
  | cons x xs ih =>
    intro d0 hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht)),
      Vector.getElem_modify_of_ne hp (hne x List.mem_cons_self)]

/-- A left fold of per-index `modify`s at injectively-indexed positions over a
`Nodup` list applies `g r` to the original value at position `idx r` for every
member `r`. -/
private theorem foldl_modify_mem {N : Nat} (idx : Fin m → Nat) (g : Fin m → R → R)
    (bd : ∀ t, idx t < N) (hinj : ∀ a b : Fin m, idx a = idx b → a = b) :
    ∀ (xs : List (Fin m)), xs.Nodup → ∀ (d0 : Vector R N) (r : Fin m), r ∈ xs →
      (xs.foldl (fun d t => d.modify (idx t) (g t)) d0)[idx r]'(bd r)
        = g r (d0[idx r]'(bd r)) := by
  intro xs
  induction xs with
  | nil => intro _ d0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd d0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [foldl_modify_ne idx g (bd r) xs _ (fun t ht heq =>
        (List.nodup_cons.mp hnd).1 ((hinj t r heq) ▸ ht))]
      exact Vector.getElem_modify_self (bd r)
    · rw [ih (List.nodup_cons.mp hnd).2 _ r hr',
        Vector.getElem_modify_of_ne (bd r) (fun heq =>
          (List.nodup_cons.mp hnd).1 ((hinj x r heq) ▸ hr'))]

/-- Entrywise read of `writeRow`: position `(r, t)` reads `v[t]` in the written
row and the old buffer everywhere else. -/
theorem getElem_writeRow (d : Vector R (n * m)) (dst : Nat) (hdst : dst < n) (v : Vector R m)
    {r t : Nat} (hr : r < n) (ht : t < m) :
    (writeRow d dst hdst v)[r * m + t]'(flatIdx_lt hr ht) =
      if r = dst then v[t]'ht else d[r * m + t]'(flatIdx_lt hr ht) := by
  unfold writeRow
  rw [Fin.foldl_eq_finRange_foldl]
  by_cases hrd : r = dst
  · subst hrd
    rw [if_pos rfl]
    exact foldl_set_mem (fun s : Fin m => r * m + s.val) (fun s => v[s])
      (fun s => flatIdx_lt hr s.isLt) flatIdx_col_inj
      (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩ (List.mem_finRange _)
  · rw [if_neg hrd]
    exact foldl_set_ne (fun s : Fin m => dst * m + s.val) (fun s => v[s])
      (fun s => flatIdx_lt hdst s.isLt) (flatIdx_lt hr ht)
      (List.finRange m) d (fun s _ heq => by
        have hds : (dst * m + s.val) / m = dst := flatIdx_div s.isLt
        have hrt : (r * m + t) / m = r := flatIdx_div ht
        rw [heq, hrt] at hds
        exact hrd hds)

@[simp, grind =] theorem rows_setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v).rows = M.rows.set dst v := by
  apply Vector.ext
  intro r hr
  rw [Vector.getElem_set, getElem_rows]
  apply Vector.ext
  intro t ht
  rw [getElem_getRow_nat]
  show (writeRow M.data dst.val dst.isLt v)[r * m + t]'(flatIdx_lt hr ht) = _
  rw [getElem_writeRow M.data dst.val dst.isLt v hr ht]
  by_cases hrd : r = dst.val
  · rw [if_pos hrd, if_pos hrd.symm]
  · rw [if_neg hrd, if_neg (fun h => hrd h.symm), getElem_rows, getElem_getRow_nat]

/-- Reading back the replaced row `dst` of `setRow M dst v` yields `v`. -/
@[grind =] theorem setRow_get_self (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v)[dst] = v := by
  show getRow (setRow M dst v) dst = v
  rw [← getElem_rows (setRow M dst v) dst.val dst.isLt, rows_setRow,
    Vector.getElem_set_self dst.isLt]

/-- Replacing row `dst` leaves every other row unchanged. -/
theorem setRow_row_ne (M : Matrix R n m) (dst r : Fin n) (v : Vector R m)
    (h : r ≠ dst) :
    (setRow M dst v)[r] = M[r] := by
  show getRow (setRow M dst v) r = getRow M r
  rw [← getElem_rows (setRow M dst v) r.val r.isLt, rows_setRow,
    Vector.getElem_set_ne dst.isLt r.isLt (fun heq => h (Fin.ext heq.symm)),
    getElem_rows]

/-- In-place per-entry update of row `i`: entry `t` becomes `g t` applied to its
old value, written directly into the flat buffer with **no row
materialization**. This is the per-entry engine the elementary row operations
(`rowScale`, `rowAdd`) and the Bareiss row elimination build on: unlike
`modifyRow`, whose whole-row function forces a row copy-out and copy-back, each
entry here is a single in-place `Vector.modify` of the backing buffer when the
matrix is uniquely referenced. -/
@[expose, inline]
def modifyEntries (M : Matrix R n m) (i : Nat) (g : Fin m → R → R) : Matrix R n m :=
  if _h : i < n then
    match M with
    | ⟨d⟩ => ⟨Fin.foldl m (fun d t => d.modify (i * m + t.val) (g t)) d⟩
  else M

/-- Entrywise read of `modifyEntries`: row `i` gets `g` applied entrywise, every
other row is unchanged. -/
@[grind =] theorem getElem_modifyEntries (M : Matrix R n m) (i : Nat) (g : Fin m → R → R)
    (r : Fin n) (c : Fin m) :
    (modifyEntries M i g)[r][c] = if r.val = i then g c M[r][c] else M[r][c] := by
  obtain ⟨d⟩ := M
  by_cases h : i < n
  · have hred : modifyEntries (⟨d⟩ : Matrix R n m) i g =
        ⟨Fin.foldl m (fun d t => d.modify (i * m + t.val) (g t)) d⟩ := by
      simp only [modifyEntries, dif_pos h]
    rw [hred, getElem_eq_getRow, getElem_getRow, getElem_eq_getRow, getElem_getRow]
    show (Fin.foldl m (fun d t => d.modify (i * m + t.val) (g t)) d)[r.val * m + c.val]'_ = _
    rw [Fin.foldl_eq_finRange_foldl]
    by_cases hri : r.val = i
    · subst hri
      rw [if_pos rfl]
      exact foldl_modify_mem (fun t : Fin m => r.val * m + t.val) g
        (fun t => flatIdx_lt r.isLt t.isLt) flatIdx_col_inj
        (List.finRange m) (nodup_finRange m) d c (List.mem_finRange _)
    · rw [if_neg hri]
      exact foldl_modify_ne (fun t : Fin m => i * m + t.val) g
        (flatIdx_lt r.isLt c.isLt) (List.finRange m) d (fun t _ heq => by
          have h1 : (i * m + t.val) / m = i := flatIdx_div t.isLt
          have h2 : (r.val * m + c.val) / m = r.val := flatIdx_div c.isLt
          rw [heq, h2] at h1
          exact hri h1)
  · have hred : modifyEntries (⟨d⟩ : Matrix R n m) i g = ⟨d⟩ := by
      simp only [modifyEntries, dif_neg h]
    rw [hred, if_neg (fun heq => h (by rw [← heq]; exact r.isLt))]

/-- The transpose of a dense matrix. -/
@[expose]
def transpose (M : Matrix R n m) : Matrix R m n :=
  ofFn fun i j => M[(j, i)]

/-- Entry access for the transpose of a dense matrix. -/
@[grind =] theorem getElem_transpose (M : Matrix R n m) (i : Fin m) (j : Fin n) :
    (transpose M)[i][j] = M[j][i] := by
  rw [transpose, getElem_ofFn, getElem_pair_eq_nested]

/-- Transposing a dense matrix twice returns the original matrix. -/
@[simp, grind =] theorem transpose_transpose (M : Matrix R n m) :
    transpose (transpose M) = M := by
  apply ext_getElem
  intro i j
  rw [getElem_transpose, getElem_transpose]

/-- The all-zero matrix. -/
@[expose]
protected def zero (n m : Nat) [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero n m

/-- Every entry of the zero matrix is `0`. -/
@[grind =] theorem getElem_zero [OfNat R 0] (i : Fin n) (j : Fin m) :
    (0 : Matrix R n m)[i][j] = 0 := by
  show (ofFn (fun _ _ => (0 : R)))[i][j] = 0
  rw [getElem_ofFn]

/-- Every row of the zero matrix is the zero vector. -/
@[simp, grind =] theorem row_zero [OfNat R 0] (i : Fin n) :
    row (0 : Matrix R n m) i = Vector.ofFn fun _ => (0 : R) := by
  ext j hj
  show (row (0 : Matrix R n m) i)[(⟨j, hj⟩ : Fin m)] =
    (Vector.ofFn fun _ => (0 : R))[(⟨j, hj⟩ : Fin m)]
  rw [getElem_row, getElem_zero]
  simp

/-- Every column of the zero matrix is the zero vector. -/
@[simp, grind =] theorem col_zero [OfNat R 0] (j : Fin m) :
    col (0 : Matrix R n m) j = Vector.ofFn fun _ => (0 : R) := by
  ext i hi
  show (col (0 : Matrix R n m) j)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn fun _ => (0 : R))[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_zero]
  simp

/-- The identity matrix. -/
@[expose]
protected def identity (n : Nat) [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

/-- Entrywise matrix addition. -/
@[expose]
protected def add [Add R] (A B : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => A[(i, j)] + B[(i, j)]

instance [Add R] : Add (Matrix R n m) where
  add := Matrix.add

/-- Entrywise matrix negation. -/
@[expose]
protected def neg [Neg R] (A : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => -A[(i, j)]

instance [Neg R] : Neg (Matrix R n m) where
  neg := Matrix.neg

/-- Entrywise matrix subtraction. -/
@[expose]
protected def sub [Sub R] (A B : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => A[(i, j)] - B[(i, j)]

instance [Sub R] : Sub (Matrix R n m) where
  sub := Matrix.sub

/-- Entry access for matrix addition. -/
@[grind =] theorem getElem_add [Add R] (A B : Matrix R n m) (i : Fin n) (j : Fin m) :
    (A + B)[i][j] = A[i][j] + B[i][j] := by
  show (ofFn (fun i j => A[(i, j)] + B[(i, j)]))[i][j] = A[i][j] + B[i][j]
  rw [getElem_ofFn, getElem_pair_eq_nested, getElem_pair_eq_nested]

/-- Entry access for matrix negation. -/
@[grind =] theorem getElem_neg [Neg R] (A : Matrix R n m) (i : Fin n) (j : Fin m) :
    (-A)[i][j] = -A[i][j] := by
  have h : (-A)[i][j] = (Matrix.neg A)[i][j] := rfl
  rw [h, Matrix.neg, getElem_ofFn, getElem_pair_eq_nested]

/-- Entry access for matrix subtraction. -/
@[grind =] theorem getElem_sub [Sub R] (A B : Matrix R n m) (i : Fin n) (j : Fin m) :
    (A - B)[i][j] = A[i][j] - B[i][j] := by
  show (ofFn (fun i j => A[(i, j)] - B[(i, j)]))[i][j] = A[i][j] - B[i][j]
  rw [getElem_ofFn, getElem_pair_eq_nested, getElem_pair_eq_nested]

/-- Multiply a matrix by a column vector. -/
@[expose]
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Vector.ofFn fun i => (row M i).dotProduct v

/-- The `j`-th row of `transpose M` is the `j`-th column of `M`. -/
@[simp, grind =] theorem row_transpose (M : Matrix R n m) (j : Fin m) :
    row (transpose M) j = col M j := by
  ext k hk
  show (row (transpose M) j)[(⟨k, hk⟩ : Fin n)] = (col M j)[(⟨k, hk⟩ : Fin n)]
  rw [getElem_row, getElem_transpose, getElem_col]

/-- The `i`-th column of `transpose M` is the `i`-th row of `M`. -/
@[simp, grind =] theorem col_transpose (M : Matrix R n m) (i : Fin n) :
    col (transpose M) i = row M i := by
  ext k hk
  show (col (transpose M) i)[(⟨k, hk⟩ : Fin m)] = (row M i)[(⟨k, hk⟩ : Fin m)]
  rw [getElem_col, getElem_transpose, getElem_row]

/--
Multiply two matrices, using the naive algorithm.

This reads each column `col N j` and is the reference definition the entry lemmas
reason about. Compiled code runs `mulImpl`, which transposes `N` once (via the
`@[csimp]` below) so each column is materialized a single time instead of being
rebuilt for every row of `M`.

Strassen-Winograd multiplication, with a customizable base kernel for small
sizes, is implemented as `mulStrassen` in `HexMatrix/Strassen.lean` and proved
equal to this `mul` by `mulStrassen_eq_mul`. It is a separate ring-level entry
point rather than a `@[csimp]` replacement of `mul`: the Winograd schedule
subtracts blocks, so `mulStrassen` needs `[Sub R]`, which this `mul` does not
have, and a `@[csimp]` replacement must preserve the declaration's type. Callers
over a ring opt into it explicitly.
-/
@[expose]
noncomputable def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => (row M i).dotProduct (col N j)

/-- Cache-friendly implementation of `mul`: transpose `N` once (turning its columns
into contiguous rows), materialize the transposed rows once, then take row-by-row
dot products, so each column is built a single time rather than once per row of
`M`. Swapped in for compiled code by the `@[csimp]` lemma; `mul` stays the
column-based reference form for proofs. -/
@[expose]
def mulImpl [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  let Ntr := N.transpose.rows
  ofRows (Vector.ofFn fun i =>
    let ri := getRow M i
    Vector.ofFn fun j => ri.dotProduct Ntr[j])

@[csimp] theorem mul_eq_mulImpl : @mul = @mulImpl := by
  funext R n m k iMul iAdd iZero M N
  apply ext_getElem
  intro i j
  show (mul M N)[i][j] = (mulImpl M N)[i][j]
  rw [mul, getElem_ofFn]
  have h : (mulImpl M N)[i][j]
      = (getRow M i).dotProduct (getRow N.transpose j) := by
    show (ofRows (Vector.ofFn fun a : Fin n =>
        Vector.ofFn fun b : Fin k => (getRow M a).dotProduct (N.transpose.rows[b])))[i][j]
      = (getRow M i).dotProduct (getRow N.transpose j)
    rw [getElem_ofRows]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, getElem_rows]
  rw [h, show getRow N.transpose j = row (transpose N) j from rfl, row_transpose]
  rfl

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVec

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Matrix R m k) (Matrix R n k) where
  hMul := mul

/-- Homogeneous multiplication on square matrices, agreeing with the
heterogeneous `HMul`. This is the `Mul` instance Mathlib's `Semiring`/`Ring`
structures build on; see `HexMatrixMathlib`. -/
instance [Mul R] [Add R] [OfNat R 0] : Mul (Matrix R n n) where
  mul := mul

/-- Entry characterization for matrix-vector multiplication. -/
@[grind =] theorem getElem_mulVec [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (v : Vector R m) (i : Fin n) :
    (M * v)[i] = (row M i).dotProduct v := by
  show (mulVec M v)[i] = (row M i).dotProduct v
  simp [mulVec]

/-- Multiply a row vector by a matrix, `v * M`. Equal to `transpose M * v`; the
`j`-th entry is `∑ i, M[i][j] * v[i]`, the combination of the rows of `M` with
coefficients `v`. -/
@[expose]
def vecMul [Mul R] [Add R] [OfNat R 0] (v : Vector R n) (M : Matrix R n m) :
    Vector R m :=
  transpose M * v

instance [Mul R] [Add R] [OfNat R 0] : HMul (Vector R n) (Matrix R n m) (Vector R m) where
  hMul := vecMul

/-- Entry characterization for vector-matrix multiplication. -/
@[grind =] theorem getElem_vecMul [Mul R] [Add R] [OfNat R 0]
    (v : Vector R n) (M : Matrix R n m) (j : Fin m) :
    (v * M)[j] = (col M j).dotProduct v := by
  show (transpose M * v)[j] = (col M j).dotProduct v
  rw [getElem_mulVec, row_transpose]

/-- Entry characterization for matrix multiplication. -/
@[grind =] theorem getElem_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) (j : Fin k) :
    (M * N)[i][j] = (row M i).dotProduct (col N j) := by
  show (mul M N)[i][j] = (row M i).dotProduct (col N j)
  rw [mul, getElem_ofFn]

/-- Row `i` of `M * N` is the row of dot products of `row M i` against the
columns of `N`. -/
@[simp, grind =] theorem row_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) :
    row (M * N) i = Vector.ofFn fun j => (row M i).dotProduct (col N j) := by
  ext j hj
  show (row (M * N) i)[(⟨j, hj⟩ : Fin k)] =
    (Vector.ofFn fun j => (row M i).dotProduct (col N j))[(⟨j, hj⟩ : Fin k)]
  rw [getElem_row, getElem_mul]
  simp

/-- Column `j` of `M * N` is the column of dot products of the rows of `M`
against `col N j`. -/
@[simp, grind =] theorem col_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (j : Fin k) :
    col (M * N) j = Vector.ofFn fun i => (row M i).dotProduct (col N j) := by
  ext i hi
  show (col (M * N) j)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn fun i => (row M i).dotProduct (col N j))[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_mul]
  simp

/-- The identity matrix entry function: `(identity n)[i][j] = 1` if `i = j`, else `0`. -/
@[grind =] theorem getElem_identity [OfNat R 0] [OfNat R 1] {n : Nat} (i j : Fin n) :
    (Matrix.identity (R := R) n)[i][j] = if i = j then (1 : R) else 0 := by
  show (ofFn (fun i j => if i = j then (1 : R) else 0))[i][j] = if i = j then (1 : R) else 0
  rw [getElem_ofFn]

/-- The identity matrix is its own transpose. -/
@[simp, grind =] theorem transpose_identity [OfNat R 0] [OfNat R 1] {n : Nat} :
    Matrix.transpose (Matrix.identity (R := R) n) = Matrix.identity n := by
  apply ext_getElem
  intro i j
  rw [getElem_transpose, getElem_identity, getElem_identity]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij.symm]
  · rw [if_neg hij, if_neg (fun h => hij h.symm)]

/-- Row `i` of the identity matrix has a `1` in position `i` and `0` elsewhere. -/
@[simp, grind =] theorem row_identity [OfNat R 0] [OfNat R 1] {n : Nat} (i : Fin n) :
    row (Matrix.identity (R := R) n) i = Vector.ofFn fun j => if i = j then (1 : R) else 0 := by
  ext j hj
  show (row (Matrix.identity (R := R) n) i)[(⟨j, hj⟩ : Fin n)] =
    (Vector.ofFn fun j => if i = j then (1 : R) else 0)[(⟨j, hj⟩ : Fin n)]
  rw [getElem_row, getElem_identity]
  simp

/-- Column `j` of the identity matrix has a `1` in position `j` and `0` elsewhere. -/
@[simp, grind =] theorem col_identity [OfNat R 0] [OfNat R 1] {n : Nat} (j : Fin n) :
    col (Matrix.identity (R := R) n) j = Vector.ofFn fun i => if i = j then (1 : R) else 0 := by
  ext i hi
  show (col (Matrix.identity (R := R) n) j)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn fun i => if i = j then (1 : R) else 0)[(⟨i, hi⟩ : Fin n)]
  rw [getElem_col, getElem_identity]
  simp

@[simp, grind =] theorem rows_modifyRow (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) : (modifyRow M i f).rows = M.rows.modify i f := by
  obtain ⟨d⟩ := M
  by_cases h : i < n
  · have hred : modifyRow (⟨d⟩ : Matrix R n m) i f =
        setRow ⟨d⟩ ⟨i, h⟩ (f (getRow ⟨d⟩ ⟨i, h⟩)) := by
      simp only [modifyRow, dif_pos h, setRow]
      rfl
    rw [hred, rows_setRow, Vector.modify_eq_set _ _ _ h, getElem_rows]
  · have hred : modifyRow (⟨d⟩ : Matrix R n m) i f = ⟨d⟩ := by
      simp only [modifyRow, dif_neg h]
    rw [hred]
    apply Vector.ext
    intro r hr
    rw [Vector.getElem_modify hr, if_neg (fun heq => h (by omega))]

/-- Row `i` of `modifyRow M i f` is `f` applied to the old row `i`. -/
@[simp, grind =] theorem getRow_modifyRow_self (M : Matrix R n m) (i : Fin n)
    (f : Vector R m → Vector R m) : getRow (modifyRow M i.val f) i = f (getRow M i) := by
  rw [← getElem_rows (modifyRow M i.val f) i.val i.isLt, rows_modifyRow,
    Vector.getElem_modify_self i.isLt, getElem_rows]

/-- Rows other than `i` are unchanged by `modifyRow M i f`. -/
@[simp, grind =] theorem getRow_modifyRow_ne (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) (j : Fin n) (h : i ≠ j.val) :
    getRow (modifyRow M i f) j = getRow M j := by
  rw [← getElem_rows (modifyRow M i f) j.val j.isLt, rows_modifyRow,
    Vector.getElem_modify_of_ne j.isLt h, getElem_rows]

/-- A left fold of per-index `swap`s leaves untouched every position not among
the swapped index pairs. -/
private theorem foldl_swap_ne {N : Nat} (idxA idxB : Fin m → Nat)
    (bdA : ∀ t, idxA t < N) (bdB : ∀ t, idxB t < N) {p : Nat} (hp : p < N) :
    ∀ (xs : List (Fin m)) (d0 : Vector R N), (∀ t ∈ xs, idxA t ≠ p ∧ idxB t ≠ p) →
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[p]'hp
        = d0[p]'hp := by
  intro xs
  induction xs with
  | nil => intro d0 _; rfl
  | cons x xs ih =>
    intro d0 hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht)),
      Vector.getElem_swap, if_neg (fun heq => (hne x List.mem_cons_self).1 heq.symm),
      if_neg (fun heq => (hne x List.mem_cons_self).2 heq.symm)]

/-- A left fold of per-index `swap`s at pairwise-disjoint index pairs over a
`Nodup` list exchanges the pair values at every member index. -/
private theorem foldl_swap_mem {N : Nat} (idxA idxB : Fin m → Nat)
    (bdA : ∀ t, idxA t < N) (bdB : ∀ t, idxB t < N)
    (hdisj : ∀ a b : Fin m, a ≠ b →
      idxA a ≠ idxA b ∧ idxA a ≠ idxB b ∧ idxB a ≠ idxA b ∧ idxB a ≠ idxB b) :
    ∀ (xs : List (Fin m)), xs.Nodup → ∀ (d0 : Vector R N) (r : Fin m), r ∈ xs →
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[idxA r]'(bdA r)
          = d0[idxB r]'(bdB r) ∧
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[idxB r]'(bdB r)
          = d0[idxA r]'(bdA r) := by
  intro xs
  induction xs with
  | nil => intro _ d0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd d0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · have hnotail : ∀ t ∈ xs, t ≠ r := fun t ht heq =>
        (List.nodup_cons.mp hnd).1 (heq ▸ ht)
      constructor
      · rw [foldl_swap_ne idxA idxB bdA bdB (bdA r) xs _ (fun t ht =>
          ⟨(hdisj t r (hnotail t ht)).1, (hdisj t r (hnotail t ht)).2.2.1⟩),
          Vector.getElem_swap, if_pos rfl]
      · rw [foldl_swap_ne idxA idxB bdA bdB (bdB r) xs _ (fun t ht =>
          ⟨(hdisj t r (hnotail t ht)).2.1, (hdisj t r (hnotail t ht)).2.2.2⟩),
          Vector.getElem_swap]
        by_cases hab : idxB r = idxA r
        · rw [if_pos hab]
          simp only [hab]
        · rw [if_neg hab, if_pos rfl]
    · have hxr : x ≠ r := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hr')
      have hd := hdisj x r hxr
      obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mp hnd).2
        (d0.swap (idxA x) (idxB x) (bdA x) (bdB x)) r hr'
      constructor
      · rw [h1, Vector.getElem_swap, if_neg (fun heq => hd.2.1 heq.symm),
          if_neg (fun heq => hd.2.2.2 heq.symm)]
      · rw [h2, Vector.getElem_swap, if_neg (fun heq => hd.1 heq.symm),
          if_neg (fun heq => hd.2.2.1 heq.symm)]

/-- Flat index pairs of two distinct rows are pairwise disjoint across distinct
columns (and within a column, across the two rows). -/
private theorem flatIdx_swap_disj {i j : Nat} (hij : i ≠ j) :
    ∀ a b : Fin m, a ≠ b →
      i * m + a.val ≠ i * m + b.val ∧ i * m + a.val ≠ j * m + b.val ∧
      j * m + a.val ≠ i * m + b.val ∧ j * m + a.val ≠ j * m + b.val := by
  intro a b hab
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine ⟨fun h => hv (by omega), fun h => ?_, fun h => ?_, fun h => hv (by omega)⟩
  · have h1 : (i * m + a.val) / m = i := flatIdx_div a.isLt
    have h2 : (j * m + b.val) / m = j := flatIdx_div b.isLt
    rw [h, h2] at h1
    exact hij h1.symm
  · have h1 : (j * m + a.val) / m = j := flatIdx_div a.isLt
    have h2 : (i * m + b.val) / m = i := flatIdx_div b.isLt
    rw [h, h2] at h1
    exact hij h1

@[simp, grind =] theorem rows_swap (M : Matrix R n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    (M.swap i j hi hj).rows = M.rows.swap i j hi hj := by
  obtain ⟨d⟩ := M
  by_cases hij : i = j
  · subst hij
    apply Vector.ext
    intro r hr
    rw [getElem_rows, Vector.getElem_swap]
    have hswap : ∀ t : Fin m, ∀ (dd : Vector R (n * m)),
        dd.swap (i * m + t.val) (i * m + t.val) (flatIdx_lt hi t.isLt) (flatIdx_lt hi t.isLt)
          = dd := by
      intro t dd
      apply Vector.ext
      intro p hp
      rw [Vector.getElem_swap]
      by_cases hpt : p = i * m + t.val
      · subst hpt
        rw [if_pos rfl]
      · rw [if_neg hpt, if_neg hpt]
    have hid : (swap (⟨d⟩ : Matrix R n m) i i hi hi).data = d := by
      show Fin.foldl m _ d = d
      rw [Fin.foldl_eq_finRange_foldl]
      generalize List.finRange m = xs
      induction xs with
      | nil => rfl
      | cons x xs ihx => rw [List.foldl_cons, hswap x d]; exact ihx
    apply Vector.ext
    intro t ht
    rw [getElem_getRow_nat]
    show (swap (⟨d⟩ : Matrix R n m) i i hi hi).data[r * m + t]'(flatIdx_lt hr ht) = _
    rw [hid]
    by_cases hri : r = i
    · rw [if_pos hri, getElem_rows, getElem_getRow_nat]
      simp only [hri]
    · rw [if_neg hri, if_neg hri, getElem_rows, getElem_getRow_nat]
  · apply Vector.ext
    intro r hr
    rw [getElem_rows, Vector.getElem_swap]
    have hfold : (swap (⟨d⟩ : Matrix R n m) i j hi hj).data =
        (List.finRange m).foldl
          (fun dd (t : Fin m) => dd.swap (i * m + t.val) (j * m + t.val)
            (flatIdx_lt hi t.isLt) (flatIdx_lt hj t.isLt)) d := by
      show Fin.foldl m _ d = _
      rw [Fin.foldl_eq_finRange_foldl]
    by_cases hri : r = i
    · subst hri
      rw [if_pos rfl]
      apply Vector.ext
      intro t ht
      rw [getElem_getRow_nat, getElem_rows, getElem_getRow_nat]
      show (swap (⟨d⟩ : Matrix R n m) r j hr hj).data[r * m + t]'(flatIdx_lt hr ht) = _
      rw [hfold]
      exact (foldl_swap_mem _ _ (fun s => flatIdx_lt hr s.isLt) (fun s => flatIdx_lt hj s.isLt)
        (flatIdx_swap_disj hij) (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩
        (List.mem_finRange _)).1
    · by_cases hrj : r = j
      · subst hrj
        rw [if_neg hri, if_pos rfl]
        apply Vector.ext
        intro t ht
        rw [getElem_getRow_nat, getElem_rows, getElem_getRow_nat]
        show (swap (⟨d⟩ : Matrix R n m) i r hi hr).data[r * m + t]'(flatIdx_lt hr ht) = _
        rw [hfold]
        exact (foldl_swap_mem _ _ (fun s => flatIdx_lt hi s.isLt) (fun s => flatIdx_lt hr s.isLt)
          (flatIdx_swap_disj hij) (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩
          (List.mem_finRange _)).2
      · rw [if_neg hri, if_neg hrj, getElem_rows]
        apply Vector.ext
        intro t ht
        rw [getElem_getRow_nat, getElem_getRow_nat]
        show (swap (⟨d⟩ : Matrix R n m) i j hi hj).data[r * m + t]'(flatIdx_lt hr ht) = _
        rw [hfold]
        exact foldl_swap_ne _ _ (fun s => flatIdx_lt hi s.isLt) (fun s => flatIdx_lt hj s.isLt)
          (flatIdx_lt hr ht) (List.finRange m) d (fun s _ => by
            constructor
            · intro heq
              have h1 : (i * m + s.val) / m = i := flatIdx_div s.isLt
              have h2 : (r * m + t) / m = r := flatIdx_div ht
              rw [heq, h2] at h1
              exact hri h1
            · intro heq
              have h1 : (j * m + s.val) / m = j := flatIdx_div s.isLt
              have h2 : (r * m + t) / m = r := flatIdx_div ht
              rw [heq, h2] at h1
              exact hrj h1)

@[simp, grind =] theorem rows_mapRows (M : Matrix R n m) (f : Vector R m → Vector R m') :
    (M.mapRows f).rows = M.rows.map f := by
  rw [mapRows, rows_ofRows]

/-- Indexed row map: replace row `i` by `f i (row i)` for every `i`, threading
`M` through a `Fin.foldl` of per-row `modifyRow`s. No intermediate index list is
allocated. The whole-row function forces each visited row to be materialized and
written back (see `modifyRow`); per-entry updates should prefer the
copy-free `modifyEntries` / `setCol` / `modifyCol`. -/
@[expose, inline]
def mapRowsIdx (M : Matrix R n m) (f : Fin n → Vector R m → Vector R m) : Matrix R n m :=
  Fin.foldl n (fun M i => M.modifyRow i.val (f i)) M

/-- The row data of `mapRowsIdx` is the corresponding `Fin.foldl` of `Vector.modify`s. -/
theorem rows_mapRowsIdx (M : Matrix R n m) (f : Fin n → Vector R m → Vector R m) :
    (mapRowsIdx M f).rows = Fin.foldl n (fun d i => d.modify i.val (f i)) M.rows := by
  unfold mapRowsIdx
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  generalize List.finRange n = xs
  induction xs generalizing M with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (M.modifyRow x.val (f x)), rows_modifyRow]

/-- Row `r` of `mapRowsIdx M f` is `f r` applied to the original row `r`. -/
@[simp, grind =] theorem getRow_mapRowsIdx (M : Matrix R n m)
    (f : Fin n → Vector R m → Vector R m) (r : Fin n) :
    getRow (mapRowsIdx M f) r = f r (getRow M r) := by
  have h := Vector.getElem_finFoldl_modify M.rows (fun i d => f i d) r
  rw [← rows_mapRowsIdx, getElem_rows, getElem_rows, Fin.eta] at h
  exact h

/-- Entry `(r, c)` of `mapRowsIdx M f` reads from the updated row `f r (row r)`. -/
@[grind =] theorem getElem_mapRowsIdx (M : Matrix R n m)
    (f : Fin n → Vector R m → Vector R m) (r : Fin n) (c : Fin m) :
    (mapRowsIdx M f)[r][c] = (f r (getRow M r))[c] := by
  rw [getElem_eq_getRow, getRow_mapRowsIdx]

/-- Replace column `dst` of `M` with the entry function `v`. In place: one
single-entry `Vector.set` of the flat buffer per row (`O(n)` writes total),
reusing the backing store when `M` is uniquely referenced, rather than
materializing any row or rebuilding the matrix. -/
@[expose]
def setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R) : Matrix R n m :=
  match M with
  | ⟨d⟩ =>
    ⟨Fin.foldl n (fun d (i : Fin n) =>
      d.set (i.val * m + dst.val) (v i) (flatIdx_lt i.isLt dst.isLt)) d⟩

/-- Flat row-major indices are injective in the row for a fixed column. -/
private theorem flatIdx_row_inj {c : Nat} (hc : c < m) :
    ∀ a b : Fin n, a.val * m + c = b.val * m + c → a = b := by
  intro a b h
  have h1 : (a.val * m + c) / m = a.val := flatIdx_div hc
  have h2 : (b.val * m + c) / m = b.val := flatIdx_div hc
  rw [h, h2] at h1
  exact Fin.ext h1.symm

/-- Entrywise characterization of `setCol`: the destination column is read from
the replacement function and every other column is read from `M`. -/
@[grind =] theorem getElem_setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R)
    (r : Fin n) (c : Fin m) :
    (setCol M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  obtain ⟨d⟩ := M
  rw [getElem_eq_getRow, getElem_getRow, getElem_eq_getRow, getElem_getRow]
  show (Fin.foldl n (fun d (i : Fin n) =>
      d.set (i.val * m + dst.val) (v i) (flatIdx_lt i.isLt dst.isLt)) d)[r.val * m + c.val]'_ = _
  rw [Fin.foldl_eq_finRange_foldl]
  by_cases hc : c = dst
  · subst hc
    rw [if_pos rfl]
    exact foldl_set_mem (fun i : Fin n => i.val * m + c.val) v
      (fun i => flatIdx_lt i.isLt c.isLt) (flatIdx_row_inj c.isLt)
      (List.finRange n) (nodup_finRange n) d r (List.mem_finRange _)
  · rw [if_neg hc]
    exact foldl_set_ne (fun i : Fin n => i.val * m + dst.val) v
      (fun i => flatIdx_lt i.isLt dst.isLt) (flatIdx_lt r.isLt c.isLt)
      (List.finRange n) d (fun i _ heq => by
        have h1 : (i.val * m + dst.val) % m = dst.val := flatIdx_mod dst.isLt
        have h2 : (r.val * m + c.val) % m = c.val := flatIdx_mod c.isLt
        rw [heq, h2] at h1
        exact hc (Fin.ext h1))

/-- Replacing a column by itself leaves the matrix unchanged. -/
@[simp] theorem setCol_self (M : Matrix R n m) (dst : Fin m) :
    setCol M dst (fun r => M[r][dst]) = M := by
  apply ext_getElem
  intro r c
  rw [getElem_setCol]
  by_cases hc' : c = dst
  · rw [if_pos hc']
    exact congrArg (fun c' : Fin m => M[r][c']) hc'.symm
  · rw [if_neg hc']

/-- Transposing a row replacement is a column replacement on the transpose:
`setRow` on `M` corresponds to `setCol` on `Mᵀ`. This is the bridge the
determinant row laws route through to reuse the column laws. -/
theorem transpose_setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    transpose (setRow M dst v) = setCol (transpose M) dst (fun a => v[a]) := by
  apply ext_getElem
  intro a b
  rw [getElem_transpose, getElem_setCol]
  by_cases hb : b = dst
  · subst hb
    rw [show (setRow M b v)[b] = v from setRow_get_self M b v]
    simp
  · rw [if_neg hb, show (setRow M dst v)[b] = M[b] from setRow_row_ne M dst b v hb,
      getElem_transpose]

/-- In-place per-entry column modify: replace each entry `M[i][dst]` by
`g i M[i][dst]`, every other column unchanged. In place: one single-entry
`Vector.modify` of the flat buffer per row, analogous to `setCol`. -/
@[expose]
def modifyCol (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨Fin.foldl n (fun d (i : Fin n) => d.modify (i.val * m + dst.val) (g i)) d⟩

/-- Entrywise characterization of `modifyCol`. -/
@[grind =] theorem getElem_modifyCol (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R)
    (r : Fin n) (c : Fin m) :
    (modifyCol M dst g)[r][c] = if c = dst then g r (M[r][dst]) else M[r][c] := by
  obtain ⟨d⟩ := M
  rw [getElem_eq_getRow, getElem_getRow, getElem_eq_getRow, getElem_getRow,
    getElem_getRow]
  show (Fin.foldl n (fun d (i : Fin n) =>
      d.modify (i.val * m + dst.val) (g i)) d)[r.val * m + c.val]'_ = _
  rw [Fin.foldl_eq_finRange_foldl]
  by_cases hc : c = dst
  · subst hc
    rw [if_pos rfl]
    exact foldl_modify_mem (fun i : Fin n => i.val * m + c.val) g
      (fun i => flatIdx_lt i.isLt c.isLt) (flatIdx_row_inj c.isLt)
      (List.finRange n) (nodup_finRange n) d r (List.mem_finRange _)
  · rw [if_neg hc]
    exact foldl_modify_ne (fun i : Fin n => i.val * m + dst.val) g
      (flatIdx_lt r.isLt c.isLt) (List.finRange n) d (fun i _ heq => by
        have h1 : (i.val * m + dst.val) % m = dst.val := flatIdx_mod dst.isLt
        have h2 : (r.val * m + c.val) % m = c.val := flatIdx_mod c.isLt
        rw [heq, h2] at h1
        exact hc (Fin.ext h1))

/-- Entries outside column `dst` are unchanged by `modifyCol`. -/
theorem getElem_modifyCol_of_ne (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R)
    (r : Fin n) {c : Fin m} (h : c ≠ dst) :
    (modifyCol M dst g)[r][c] = M[r][c] := by
  rw [getElem_modifyCol, if_neg h]

/-- Scalar action on a matrix, delegated to the flat backing buffer. The single
sanctioned `SMul` instance for matrices: the Mathlib bridge layer reuses it rather
than declaring its own, so there is no overlapping instance. -/
instance {S : Type v} [SMul S R] : SMul S (Matrix R n m) where
  smul c M := ⟨c • M.data⟩

@[simp, grind =] theorem data_smul {S : Type v} [SMul S R] (c : S) (M : Matrix R n m) :
    (c • M).data = c • M.data := rfl

/-- Scalar action pushes through a nested entry read. -/
@[simp, grind =] theorem smul_getElem {S : Type v} [SMul S R] (c : S) (M : Matrix R n m)
    (i : Fin n) (j : Fin m) : (c • M)[i][j] = c • M[i][j] := by
  rw [getElem_eq_getRow, getElem_eq_getRow, getElem_getRow, getElem_getRow, data_smul,
    Vector.getElem_smul]

@[simp, grind =] theorem rows_smul {S : Type v} [SMul S R] (c : S) (M : Matrix R n m) :
    (c • M).rows = c • M.rows := by
  apply Vector.ext
  intro r hr
  rw [Vector.getElem_smul, getElem_rows, getElem_rows]
  apply Vector.ext
  intro t ht
  rw [Vector.getElem_smul, getElem_getRow_nat, getElem_getRow_nat, data_smul,
    Vector.getElem_smul]

end Matrix
end Hex
