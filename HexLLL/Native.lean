/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Lattice

public section

/-!
The pure integer-arithmetic LLL reducer. `LLLState` carries only the
integer basis, scaled Gram-Schmidt coefficients `ν`, and Gram
determinants `d`; `lllNative` runs the fuel-bounded `d`/`ν` loop, the
trusted exact reducer at the classical `η = 1/2`.
-/

namespace Hex

namespace Internal

/-- Integer-only state for later LLL reduction steps. The proof-facing fields
connect the stored Gram determinants and scaled coefficients to the executable
Gram-Schmidt integer data for `b`. -/
structure LLLState (n m : Nat) where
  /-- The current integer basis, as a matrix of row vectors. -/
  b : Matrix Int n m
  /-- The integer scaled Gram-Schmidt coefficients of `b`. -/
  ν : Matrix Int n n
  /-- The leading Gram determinants of `b` (`d[k]` for `k ≤ n`). -/
  d : Vector Nat (n + 1)

namespace LLLState

/-- Correctness predicate for the proof-facing interpretation of an executable
`LLLState`. Keeping this separate lets core state updates remain purely
computational; Mathlib-side modules can prove preservation when they need the
Gram-Schmidt interpretation. -/
structure Valid (s : LLLState n m) : Prop where
  /-- Each below-diagonal `ν` entry equals the executable scaled Gram-Schmidt
  coefficient of `s.b`. -/
  ν_eq : ∀ i j, (hi : i < n) → (hj : j < n) → j < i →
      (s.ν.getRow ⟨i, hi⟩).get ⟨j, hj⟩ =
        ((GramSchmidt.Int.scaledCoeffs s.b).getRow ⟨i, hi⟩).get ⟨j, hj⟩
  /-- Each `d` entry equals the corresponding leading Gram determinant of
  `s.b`. -/
  d_eq : ∀ i, (hi : i < n + 1) →
      s.d.get ⟨i, hi⟩ = GramSchmidt.Int.gramDet s.b i (Nat.le_of_lt_succ hi)

/-- Integer nearest-quotient used by the LLL size-reduction test. -/
@[expose]
def nearestQuotient (νjk : Int) (dj1 : Nat) : Int :=
  Int.fdiv (2 * νjk + Int.ofNat dj1) (2 * Int.ofNat dj1)

/-- Targeted matrix entry update for LLL's integer coefficient state.

Uses `Vector.modify` rather than `M.set i ((M.get i).set j x)` so the
underlying `Array.modify` swap-with-placeholder runs the inner row update
in place when `M` is uniquely owned, avoiding the forced row copy that
`set i (… set j …)` triggers via a `lean_inc` on the borrowed row. -/
@[expose]
def setEntry (M : Matrix Int n n) (i j : Fin n) (x : Int) : Matrix Int n n :=
  M.modifyRow i (·.set j x)

/-- `foldl_set_outerSubMul_get_eq` evaluates the entry at `l` of the fold that
overwrites each index in `xs` with `outerK.get · - r * outerJ.get ·`, giving the
reduced value when `l` occurs in `xs` and the original `base` entry otherwise. -/
private theorem foldl_set_outerSubMul_get_eq
    {n : Nat} (xs : List (Fin n))
    (base outerK outerJ : Vector Int n) (r : Int) (l : Fin n) :
    (xs.foldl
        (fun (row : Vector Int n) (i : Fin n) =>
          row.set i (outerK.get i - r * outerJ.get i))
        base).get l =
      if (∃ i ∈ xs, i.val = l.val) then
        outerK.get l - r * outerJ.get l
      else
        base.get l := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases h_xs : ∃ i ∈ xs, i.val = l.val
    · simp [h_xs]
    · by_cases h_xl : x.val = l.val
      · have h_cons : ∃ i ∈ x :: xs, i.val = l.val :=
          ⟨x, List.mem_cons.mpr (Or.inl rfl), h_xl⟩
        have h_xeq : x = l := Fin.eq_of_val_eq h_xl
        subst h_xeq
        simp only [h_xs, ↓reduceIte, h_cons]
        change (base.set x.val (outerK.get x - r * outerJ.get x) x.isLt)[x.val] = _
        exact Vector.getElem_set_self x.isLt
      · have h_cons : ¬ ∃ i ∈ x :: xs, i.val = l.val := by
          rintro ⟨i, hi, hi_l⟩
          rcases List.mem_cons.mp hi with rfl | hxs
          · exact h_xl hi_l
          · exact h_xs ⟨i, hxs, hi_l⟩
        simp only [h_xs, ↓reduceIte, h_cons]
        change (base.set x.val (outerK.get x - r * outerJ.get x) x.isLt)[l.val] = base[l.val]
        exact Vector.getElem_set_ne x.isLt l.isLt h_xl

/-- Closed form for the entry-wise size-reduction sweep: folding the update
`row ← row.set l' (outerK l' − r · outerJ l')` over the first `jVal` indices
replaces exactly the entries below `jVal` by `outerK − r · outerJ` and leaves the
rest of `base` untouched. Reading position `l` afterwards gives the reduced value
when `l.val < jVal` and the original `base.get l` otherwise. -/
theorem foldl_finRange_set_outerSubMul_get_eq
    {n : Nat} (jVal : Nat) (hjn : jVal ≤ n)
    (base outerK outerJ : Vector Int n) (r : Int) (l : Fin n) :
    (Fin.foldl jVal
        (fun (row : Vector Int n) (l' : Fin jVal) =>
          let lFin : Fin n := ⟨l'.val, Nat.lt_of_lt_of_le l'.isLt hjn⟩
          row.set lFin (outerK.get lFin - r * outerJ.get lFin))
        base).get l =
      if l.val < jVal then
        outerK.get l - r * outerJ.get l
      else
        base.get l := by
  rw [Fin.foldl_eq_finRange_foldl]
  let cast : Fin jVal → Fin n :=
    fun l' => ⟨l'.val, Nat.lt_of_lt_of_le l'.isLt hjn⟩
  show ((List.finRange jVal).foldl
        (fun (row : Vector Int n) (l' : Fin jVal) =>
          row.set (cast l') (outerK.get (cast l') - r * outerJ.get (cast l')))
        base).get l = _
  rw [show ((List.finRange jVal).foldl
        (fun (row : Vector Int n) (l' : Fin jVal) =>
          row.set (cast l') (outerK.get (cast l') - r * outerJ.get (cast l')))
        base) =
      ((List.finRange jVal).map cast).foldl
        (fun (row : Vector Int n) (i : Fin n) =>
          row.set i (outerK.get i - r * outerJ.get i))
        base from
      (@List.foldl_map (Fin jVal) (Fin n) (Vector Int n) cast
        (fun row i => row.set i (outerK.get i - r * outerJ.get i))
        (List.finRange jVal) base).symm]
  rw [foldl_set_outerSubMul_get_eq]
  by_cases hlj : l.val < jVal
  · have hex : ∃ i ∈ (List.finRange jVal).map cast, i.val = l.val := by
      refine ⟨⟨l.val, Nat.lt_of_lt_of_le hlj hjn⟩, ?_, rfl⟩
      rw [List.mem_map]
      exact ⟨⟨l.val, hlj⟩, List.mem_finRange _, rfl⟩
    rw [if_pos hex, if_pos hlj]
  · have hno : ¬ ∃ i ∈ (List.finRange jVal).map cast, i.val = l.val := by
      rintro ⟨i, hi_mem, hi_eq⟩
      rw [List.mem_map] at hi_mem
      obtain ⟨l', _, hl'⟩ := hi_mem
      have hcast : (cast l').val = l'.val := rfl
      have : l.val < jVal := by
        rw [← hi_eq, ← hl', hcast]
        exact l'.isLt
      exact hlj this
    rw [if_neg hno, if_neg hlj]

/-- Single-column size reduction update for row `k` against row `j`. -/
@[expose]
def sizeReduceColumn (s : LLLState n m) (j k : Fin n) (hjk : j.val < k.val) :
    LLLState n m :=
  let νjk := (s.ν.getRow k).get j
  let dj1 := s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  if hreduce : 2 * Int.natAbs νjk > dj1 then
    let r := nearestQuotient νjk dj1
    let b' := GramSchmidt.Int.sizeReduce s.b j k r
    let rowK :=
      Fin.foldl j.val
        (fun row l =>
          let lFin : Fin n := ⟨l.val, Nat.lt_trans l.isLt j.isLt⟩
          row.set lFin ((s.ν.getRow k).get lFin - r * (s.ν.getRow j).get lFin))
        (s.ν.getRow k)
    let rowK := rowK.set j ((s.ν.getRow k).get j - r * Int.ofNat dj1)
    let ν' : Matrix Int n n :=
      s.ν.setRow k rowK
    { b := b'
      ν := ν'
      d := s.d }
  else
    s

/-- Size-reduce row `k` against each earlier row using the stored integer
scaled coefficients. -/
@[expose]
def sizeReduce (s : LLLState n m) (k : Nat) : LLLState n m :=
  if hk : k < n then
    let kFin : Fin n := ⟨k, hk⟩
    Fin.foldr k
      (fun j state =>
        let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
        LLLState.sizeReduceColumn state jFin kFin j.isLt)
      s
  else
    s

/-- `sizeReduceColumn_d` states that a single size-reduction column step leaves
the Gram determinant data `d` unchanged. -/
private theorem sizeReduceColumn_d (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) :
    (s.sizeReduceColumn j k hjk).d = s.d := by
  unfold sizeReduceColumn
  by_cases hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · simp [hreduce]
  · simp [hreduce]

/-- `sizeReduceColumn_basis` states that a single size-reduction column step
leaves the integer `basis` unchanged. -/
private theorem sizeReduceColumn_basis (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) :
    GramSchmidt.Int.basis (s.sizeReduceColumn j k hjk).b =
      GramSchmidt.Int.basis s.b := by
  unfold sizeReduceColumn
  by_cases hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · simp only [hreduce]
    exact GramSchmidt.Int.basis_sizeReduce s.b j k hjk
      (nearestQuotient ((s.ν.getRow k).get j)
        (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))
  · simp [hreduce]

/-- `sizeReduce_foldl_d` states that folding size-reduction column steps over a
list of columns leaves the Gram determinant data `d` unchanged. -/
private theorem sizeReduce_foldl_d (s : LLLState n m) (k : Nat) (hk : k < n)
    (xs : List (Fin k)) :
    (xs.foldl
        (fun state j =>
          let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
          LLLState.sizeReduceColumn state jFin ⟨k, hk⟩ j.isLt)
        s).d = s.d := by
  induction xs generalizing s with
  | nil =>
      rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, sizeReduceColumn_d]

/-- `sizeReduce_foldl_basis` states that folding size-reduction column steps over
a list of columns leaves the integer `basis` unchanged. -/
private theorem sizeReduce_foldl_basis (s : LLLState n m) (k : Nat) (hk : k < n)
    (xs : List (Fin k)) :
    GramSchmidt.Int.basis
        (xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            LLLState.sizeReduceColumn state jFin ⟨k, hk⟩ j.isLt)
          s).b =
      GramSchmidt.Int.basis s.b := by
  induction xs generalizing s with
  | nil =>
      rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, sizeReduceColumn_basis]

/-- Swap adjacent rows `k - 1` and `k`, updating the stored scaled coefficients
and Gram determinants with the integer formulas from the LLL specification. -/
@[expose]
def swapStep (s : LLLState n m) (k : Nat) : LLLState n m :=
  if hk : k < n then
    if hk0 : 0 < k then
      let kFin : Fin n := ⟨k, hk⟩
      let km1 : Fin n := GramSchmidt.prevRow kFin hk0
      let B := (s.ν.getRow kFin).get km1
      let dkPrev := s.d.get ⟨km1.val, Nat.lt_succ_of_lt km1.isLt⟩
      let dk := s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩
      let dkNext := s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩
      let dk' : Nat :=
        Int.toNat (((Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2) / Int.ofNat dk))
      let b' := GramSchmidt.Int.adjacentSwap s.b kFin hk0
      let d' : Vector Nat (n + 1) :=
        s.d.set k dk' (h := Nat.lt_succ_of_lt hk)
      let νRowsSwapped :=
        let setPrefixFrom (source : Vector Int n) (row : Vector Int n) : Vector Int n :=
          Fin.foldl km1.val
            (fun row j =>
              let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt km1.isLt⟩
              row.set jFin (source.get jFin))
            row
        s.ν.modifyRow km1 (setPrefixFrom (s.ν.getRow kFin))
          |>.modifyRow kFin (setPrefixFrom (s.ν.getRow km1))
      let νPivot := setEntry νRowsSwapped kFin km1 B
      -- Hoist (oldNu[i].kFin, oldNu[i].km1) reads out of the foldl lambda
      -- so the closure does not hold a reference to s.ν across iterations.
      -- With s.ν kept alive only for this precompute, the row-level rc on
      -- post-pivot rows drops to 1 by the time `ν.modifyRow i` runs, letting
      -- the two-`set` body inside the modify mutate in place instead of
      -- COW'ing the row on every iteration.
      let pairs : Vector (Int × Int) n :=
        Vector.ofFn fun i =>
          if _ : k < i.val then ((s.ν.getRow i).get kFin, (s.ν.getRow i).get km1)
          else (0, 0)
      let ν' : Matrix Int n n :=
        Fin.foldl n
          (fun ν i =>
            if _ : k < i.val then
              let (a, b) := pairs.get i
              let prev := (Int.ofNat dkPrev * a + B * b) / Int.ofNat dk
              let curr := (Int.ofNat dkNext * b - B * a) / Int.ofNat dk
              ν.modifyRow i fun row =>
                row.set km1 prev
                  |>.set kFin curr
            else
              ν)
          νPivot
      { b := b'
        ν := ν'
        d := d' }
    else
      s
  else
    s

/-- Size reduction leaves the stored Gram determinants unchanged. -/
@[grind =] theorem sizeReduce_d (s : LLLState n m) (k : Nat) :
    (s.sizeReduce k).d = s.d := by
  unfold sizeReduce
  by_cases hk : k < n
  · simpa [hk, Fin.foldr_eq_finRange_foldr] using
      sizeReduce_foldl_d (s := s) (k := k) (hk := hk) (xs := (List.finRange k).reverse)
  · simp [hk]

/-- Size reduction preserves the Gram-Schmidt basis of the state basis matrix. -/
@[grind =] theorem sizeReduce_basis (s : LLLState n m) (k : Nat) :
    GramSchmidt.Int.basis (s.sizeReduce k).b = GramSchmidt.Int.basis s.b := by
  unfold sizeReduce
  by_cases hk : k < n
  · simpa [hk, Fin.foldr_eq_finRange_foldr] using
      sizeReduce_foldl_basis (s := s) (k := k) (hk := hk) (xs := (List.finRange k).reverse)
  · simp [hk]

/-- Adjacent swaps preserve the generated lattice. -/
@[grind =] theorem swapStep_memLattice_iff (s : LLLState n m) (k : Nat) (v : Vector Int m) :
    Matrix.memLattice (s.swapStep k).b v ↔ Matrix.memLattice s.b v := by
  unfold swapStep
  by_cases hk : k < n
  · rw [dif_pos hk]
    by_cases hk0 : 0 < k
    · rw [dif_pos hk0]
      simpa [GramSchmidt.Int.adjacentSwap] using
        rowSwap_memLattice_iff s.b (GramSchmidt.prevRow ⟨k, hk⟩ hk0) ⟨k, hk⟩ v
    · rw [dif_neg hk0]
  · rw [dif_neg hk]

/-- A single-column size reduction preserves the generated lattice. -/
@[grind =] theorem sizeReduceColumn_memLattice_iff
    (s : LLLState n m) (j k : Fin n) (hjk : j.val < k.val) (v : Vector Int m) :
    Matrix.memLattice (s.sizeReduceColumn j k hjk).b v ↔ Matrix.memLattice s.b v := by
  unfold sizeReduceColumn
  by_cases hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
    have hne : j ≠ k := fun h => Nat.lt_irrefl j.val (h ▸ hjk)
    exact rowAdd_memLattice_iff s.b hne _ v
  · rw [dif_neg hreduce]

/-- `sizeReduce_foldl_memLattice_iff` states that folding size-reduction column
steps over a list of columns preserves the integer row-lattice membership
predicate in both directions. -/
private theorem sizeReduce_foldl_memLattice_iff (s : LLLState n m) (k : Nat) (hk : k < n)
    (xs : List (Fin k)) (v : Vector Int m) :
    Matrix.memLattice
        (xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            LLLState.sizeReduceColumn state jFin ⟨k, hk⟩ j.isLt)
          s).b v ↔ Matrix.memLattice s.b v := by
  induction xs generalizing s with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact sizeReduceColumn_memLattice_iff s _ _ j.isLt v

/-- Size reduction preserves the generated lattice. -/
@[grind =] theorem sizeReduce_memLattice_iff (s : LLLState n m) (k : Nat) (v : Vector Int m) :
    Matrix.memLattice (s.sizeReduce k).b v ↔ Matrix.memLattice s.b v := by
  unfold sizeReduce
  by_cases hk : k < n
  · rw [dif_pos hk]
    simpa [Fin.foldr_eq_finRange_foldr] using
      sizeReduce_foldl_memLattice_iff s k hk (List.finRange k).reverse v
  · rw [dif_neg hk]

/-- The updated swap state still packages the intended scaled coefficient
representation for its basis. -/
theorem swapStep_ν_eq
    (s : LLLState n m) (k : Nat) (hvalid : (s.swapStep k).Valid)
    (i j : Nat) (hi : i < n) (hj : j < n) (hji : j < i) :
    ((s.swapStep k).ν.getRow ⟨i, hi⟩).get ⟨j, hj⟩ =
      ((GramSchmidt.Int.scaledCoeffs (s.swapStep k).b).getRow ⟨i, hi⟩).get ⟨j, hj⟩ := by
  simpa using hvalid.ν_eq i j hi hj hji

/-- The updated swap state still packages the intended Gram-determinant
representation for its basis. -/
theorem swapStep_d_eq
    (s : LLLState n m) (k : Nat) (hvalid : (s.swapStep k).Valid)
    (i : Nat) (hi : i < n + 1) :
    (s.swapStep k).d.get ⟨i, hi⟩ =
      GramSchmidt.Int.gramDet (s.swapStep k).b i (Nat.le_of_lt_succ hi) := by
  simpa using hvalid.d_eq i hi

/-- Recover a single rational Gram-Schmidt coefficient from the integer state.
This exists for the proof layer; later executable code continues to work over
the stored integer data. -/
@[expose]
noncomputable def gramSchmidtCoeff (s : LLLState n m) (i j : Nat)
    (hi : i < n) (hj : j < n) : Rat :=
  (((s.ν.getRow ⟨i, hi⟩).get ⟨j, hj⟩ : Int) : Rat) / (s.d.get ⟨j + 1, Nat.succ_lt_succ hj⟩ : Rat)

/-- The multiplicative potential used by the LLL termination argument:
`d₁ * ... * dₙ₋₁`. -/
@[expose]
def potential (s : LLLState n m) : Nat :=
  Fin.foldl (n - 1)
    (fun acc i =>
      acc * s.d.get
        ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩)
    1

/-- Unfold the termination potential through the state's Gram-determinant
certificate. The product only ranges over `d₁, ..., dₙ₋₁`, so later
termination proofs do not need to reason about `dₙ`. -/
theorem potential_eq_gramDetProduct (s : LLLState n m) (hvalid : s.Valid) :
    s.potential =
      Fin.foldl (n - 1)
        (fun acc i =>
          acc * GramSchmidt.Int.gramDet s.b (i.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))))
        1 := by
  simp [potential, hvalid.d_eq]

/-- Initial `LLLState` constructor: build the integer state directly from a
basis matrix. The `ν` field is the integral scaled Gram-Schmidt coefficient
matrix and the `d` field is the leading Gram-determinant vector.

Takes no independence hypothesis: the construction is purely executable, and the
resulting state is even `Valid` unconditionally (see
`HexLLLMathlib.LLLState.ofBasis_valid`). `b.independent` enters only in the
theorems about the reducer's *output* (`lllNative_isLLLReduced` and the
short-vector bounds), never in building the state. Mathlib-free callers
(benchmarks, fixture emitters, BHKS projected-row computation) use it directly. -/
@[expose]
def ofBasis (b : Matrix Int n m) : LLLState n m :=
  let gs := GramSchmidt.Int.data b
  { b
    ν := gs.ν
    d := gs.d }

end LLLState

/-- Fuel-bounded outer LLL loop, dispatched by `lllAux`.

At row `k`, the loop size-reduces the current row, checks the integer
Lovasz condition, and either advances to `k + 1` or swaps adjacent rows and
continues from the previous position.

The `fuel = 0` branch returns the current basis as the total fallback for a
pipeline-unreachable case: issue #6567 tracks the fuel-sufficiency theorem
showing that `lllFuel` is enough for public pipeline calls. -/
@[expose]
def lllLoop (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Nat → Matrix Int n m
  | 0 =>
      s.b
  | fuel + 1 =>
      if hdone : k = n then
        s.b
      else
        have hlt : k < n := Nat.lt_of_le_of_ne hkn hdone
        have hkm1lt : k - 1 < n :=
          Nat.lt_of_le_of_lt (Nat.sub_le k 1) hlt
        let sReduced := s.sizeReduce k
        let kFin : Fin n := ⟨k, hlt⟩
        let km1Fin : Fin n := ⟨k - 1, hkm1lt⟩
        let dkPrev := sReduced.d.get
          ⟨k - 1, Nat.lt_trans hkm1lt (Nat.lt_succ_self n)⟩
        let dk := sReduced.d.get ⟨k, Nat.lt_succ_of_lt hlt⟩
        let dkNext := sReduced.d.get ⟨k + 1, Nat.succ_lt_succ hlt⟩
        let B := (sReduced.ν.getRow kFin).get km1Fin
        let lovaszLhs : Int :=
          Int.ofNat δ.den * (Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2)
        let lovaszRhs : Int :=
          δ.num * (Int.ofNat dk ^ 2)
        if lovaszLhs ≥ lovaszRhs then
          lllLoop sReduced (k + 1) δ hδ hδ' (Nat.succ_pos k) (Nat.succ_le_of_lt hlt) fuel
        else
          let sSwapped := sReduced.swapStep k
          let k' := max (k - 1) 1
          lllLoop sSwapped k' δ hδ hδ' (Nat.le_max_right (k - 1) 1)
            (by
              exact (Nat.max_le).2
                ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩)
            fuel

/-- `lllLoop` preserves the generated lattice: every iteration is either a
`sizeReduce` (preserved by `sizeReduce_memLattice_iff`) or an adjacent swap
(preserved by `swapStep_memLattice_iff`). -/
@[grind =] theorem lllLoop_memLattice_iff (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n) (fuel : Nat)
    (v : Vector Int m) :
    Matrix.memLattice (lllLoop s k δ hδ hδ' hk hkn fuel) v ↔
      Matrix.memLattice s.b v := by
  induction fuel generalizing s k hk hkn with
  | zero => rfl
  | succ f ih =>
    show Matrix.memLattice
      (if hdone : k = n then s.b else _) v ↔ _
    by_cases hdone : k = n
    · rw [dif_pos hdone]
    · rw [dif_neg hdone]
      by_cases hcond : Int.ofNat δ.den *
            (Int.ofNat ((s.sizeReduce k).d.get
                ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_le_of_ne hkn hdone)⟩) *
              Int.ofNat ((s.sizeReduce k).d.get
                ⟨k - 1, Nat.lt_trans
                  (Nat.lt_of_le_of_lt (Nat.sub_le k 1)
                    (Nat.lt_of_le_of_ne hkn hdone))
                  (Nat.lt_succ_self n)⟩) +
              ((s.sizeReduce k).ν.getRow ⟨k, Nat.lt_of_le_of_ne hkn hdone⟩).get
                ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1)
                  (Nat.lt_of_le_of_ne hkn hdone)⟩ ^ 2) ≥
          δ.num * (Int.ofNat ((s.sizeReduce k).d.get
            ⟨k, Nat.lt_succ_of_lt (Nat.lt_of_le_of_ne hkn hdone)⟩) ^ 2)
      · rw [if_pos hcond, ih, LLLState.sizeReduce_memLattice_iff]
      · rw [if_neg hcond, ih, LLLState.swapStep_memLattice_iff,
          LLLState.sizeReduce_memLattice_iff]

/-- Initial fuel bound for `lllLoop`; issue #6567 tracks the proof that this
bound is sufficient for the public LLL pipeline. -/
@[expose]
def lllFuel (s : LLLState n m) : Nat :=
  (s.potential + 1) * (n + 1)

/-- Outer LLL loop, dispatched by `lll`.

Compatibility wrapper preserving the original `lllAux` signature while the
executable recursion is structurally bounded by `lllFuel`. -/
@[expose]
def lllAux (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Matrix Int n m :=
  lllLoop s k δ hδ hδ' hk hkn (lllFuel s)

end Internal

open Hex.Internal

/-- Native (non-dispatched) executable LLL entry point. Builds the canonical
integer state via `LLLState.ofBasis` and dispatches to `lllAux`.
This is the body the public `lll` runs by default; its output achieves the
classical size-reduction bound `|μ| ≤ 1/2` (η = 1/2), so its short-vector
guarantee uses `α = 1/(δ − 1/4)` with the classical precondition `1/4 < δ`. -/
@[expose]
def lllNative (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) :
    Matrix Int n m :=
  lllAux (LLLState.ofBasis b) 1 δ hδ hδ' (Nat.le_refl 1) hn

namespace Internal

/-- `121/400 < δ` implies `1/4 < δ`: relays the public `lll` (`η = 11/20`)
precondition through to the native body (`η = 1/2`). -/
theorem one_quarter_lt_of_eta_eleven_twentieths {δ : Rat}
    (hδ : (121 / 400 : Rat) < δ) : (1 / 4 : Rat) < δ := by
  grind

end Internal

end Hex
