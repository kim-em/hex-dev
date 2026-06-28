module

public import HexGramSchmidtMathlib.Int.Swap
import all HexGramSchmidtMathlib.Int.Swap

public section

namespace Hex
namespace GramSchmidt
namespace Int
/-! ### Row-add determinant helper lemmas -/

/-- Entry-level expansion of `Matrix.rowAdd` for a rectangular matrix. -/
private theorem rowAdd_get_rect {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (k : Fin m') :
    (Matrix.rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [Matrix.rowAdd]
  · simp [Matrix.rowAdd, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] :=
      (Vector.getElem_set_ne (xs := M)
        (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
        dst.isLt r.isLt hval)
    simpa [Matrix.rowAdd] using congrArg (fun row => row[k]) hrow

private theorem foldl_dot_comm_int {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

/-- The dot product of integer vectors is commutative. -/
private theorem dot_comm_int {n' : Nat} (u v : Vector Int n') :
    Vector.dotProduct u v = Vector.dotProduct v u := by
  simpa [Hex.Vector.dotProduct] using
    foldl_dot_comm_int (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- A row of `Matrix.rowAdd M src dst c` away from `dst` is unchanged. -/
private theorem rowAdd_row_eq_of_ne {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (hr : r.val ≠ dst.val) :
    (Matrix.rowAdd M src dst c)[r] = M[r] :=
  Vector.getElem_set_ne (xs := M)
    (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
    dst.isLt r.isLt (fun heq => hr heq.symm)

/-- The row of `Matrix.rowAdd M src dst c` at index `dst` is the entry-wise
sum `M[dst] + c * M[src]`. -/
private theorem rowAdd_row_at {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst : Fin n') (c : R) :
    (Matrix.rowAdd M src dst c)[dst] =
      Vector.ofFn fun k => M[dst][k] + c * M[src][k] := by
  unfold Matrix.rowAdd
  simp

/-- Inductive helper for `dot_rowAdd_row_at_left`: distribution along a foldl. -/
private theorem foldl_dot_rowAdd_at {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m')
    (xs : List (Fin m')) (acc accX accY : Int) (hacc : acc = accX + c * accY) :
    xs.foldl (fun a i => a + (Matrix.rowAdd M src dst c)[dst][i] * w[i]) acc =
      xs.foldl (fun a i => a + M[dst][i] * w[i]) accX +
        c * xs.foldl (fun a i => a + M[src][i] * w[i]) accY := by
  induction xs generalizing acc accX accY with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      have hentry : (Matrix.rowAdd M src dst c)[dst][i] = M[dst][i] + c * M[src][i] := by
        rw [rowAdd_get_rect]
        simp
      rw [hentry, hacc]
      grind

/-- Distribute dot product on the left over the row produced by
`Matrix.rowAdd`: at index `dst`, the row is `M[dst] + c * M[src]` componentwise,
so dot with `w` distributes over the sum. -/
private theorem dot_rowAdd_row_at_left {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    Vector.dotProduct ((Matrix.rowAdd M src dst c)[dst]) w =
      Vector.dotProduct M[dst] w + c * Vector.dotProduct M[src] w := by
  simp only [Hex.Vector.dotProduct]
  exact foldl_dot_rowAdd_at M src dst c w (List.finRange m')
    0 0 0 (by show (0 : Int) = 0 + c * 0; grind)

/-- Symmetric form: dot product on the right with the modified row. -/
private theorem dot_rowAdd_row_at_right {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    Vector.dotProduct w ((Matrix.rowAdd M src dst c)[dst]) =
      Vector.dotProduct w M[dst] + c * Vector.dotProduct w M[src] := by
  rw [dot_comm_int w, dot_rowAdd_row_at_left, dot_comm_int w M[dst], dot_comm_int w M[src]]

/-- Determinant-level pivot identity for scaled Gram-Schmidt coefficients under
an elementary row addition. In the Cramer matrix computing `nu[k,j]`, replacing
row `k` by `row k + c * row j` changes the replaced last column linearly: the
new determinant is the old Cramer determinant plus `c` times the leading Gram
determinant. This formulation does not require the rational coefficient
denominator to be nonzero. -/
theorem scaledCoeffMatrix_rowAdd_pivot_det
    (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val) (c : Int) :
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
        c * Matrix.det
          (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  let t := j.val + 1
  let ht : t ≤ n := Nat.succ_le_of_lt j.isLt
  let last : Fin t := ⟨j.val, Nat.lt_succ_self j.val⟩
  let M := GramSchmidt.leadingGramMatrixInt b t ht
  let oldCol : Fin t → Int := fun p =>
    Vector.dotProduct (b.row (GramSchmidt.liftFinLE p ht)) (b.row k)
  let gramCol : Fin t → Int := fun p =>
    Vector.dotProduct (b.row (GramSchmidt.liftFinLE p ht)) (b.row j)
  have hnew :
      GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk =
        Matrix.setCol M last (fun p => oldCol p + c * gramCol p) := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    have hp_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val := by
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_iff.mp hjk))
    have hp_row :
        (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
          b[GramSchmidt.liftFinLE p ht] :=
      rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hp_ne
    by_cases hqj : qf.val = j.val
    · have hqNat : q = j.val := by
        simpa [qf] using hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.setCol, Matrix.ofFn,
        Vector.getElem_ofFn, hqNat, if_true]
      rw [if_pos (rfl : (⟨j.val, Nat.lt_succ_self j.val⟩ : Fin t) = last)]
      simp only [Matrix.row]
      change Vector.dotProduct ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht])
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      rw [hp_row]
      change Vector.dotProduct (b.row (GramSchmidt.liftFinLE p ht))
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      exact dot_rowAdd_row_at_right b j k c (b.row (GramSchmidt.liftFinLE p ht))
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : q ≠ j.val := by
        intro h
        exact hqj (by simpa [qf] using h)
      have hq_ne_k : (GramSchmidt.liftFinLE qf ht).val ≠ k.val := by
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le qf.isLt (Nat.succ_le_iff.mp hjk))
      have hq_row :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE qf ht] =
            b[GramSchmidt.liftFinLE qf ht] :=
        rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE qf ht) c hq_ne_k
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.setCol, Matrix.ofFn,
        Vector.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      simp only [Matrix.row]
      rw [hp_row, hq_row]
      dsimp [M, GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row]
      rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  have hold :
      GramSchmidt.scaledCoeffMatrix b k j hjk =
        Matrix.setCol M last oldCol := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    by_cases hqj : qf.val = j.val
    · have hqNat : q = j.val := by
        simpa [qf] using hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.setCol, Matrix.ofFn,
        Vector.getElem_ofFn, hqNat, if_true]
      rw [if_pos (rfl : (⟨j.val, Nat.lt_succ_self j.val⟩ : Fin t) = last)]
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : q ≠ j.val := by
        intro h
        exact hqj (by simpa [qf] using h)
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.setCol, Matrix.ofFn,
        Vector.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      dsimp [M, GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row]
      simp [Vector.getElem_ofFn]
  have hgram :
      Matrix.setCol M last gramCol = M := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    by_cases hq_last : qf = last
    · have hq_lift : GramSchmidt.liftFinLE qf ht = j := by
        exact Fin.ext (by
          have hval := congrArg Fin.val hq_last
          simpa [last] using hval)
      simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Matrix.setCol, Matrix.ofFn,
        Vector.getElem_ofFn]
      rw [if_pos hq_last]
      rw [hq_lift]
    · simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Matrix.setCol, Matrix.ofFn,
        Vector.getElem_ofFn]
      rw [if_neg hq_last]
      simp [Matrix.row]
  calc
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk)
        = Matrix.det (Matrix.setCol M last (fun p => oldCol p + c * gramCol p)) := by
          rw [hnew]
    _ = Matrix.det (Matrix.setCol M last oldCol) +
          Matrix.det (Matrix.setCol M last (fun p => c * gramCol p)) := by
          rw [Matrix.det_setCol_add]
    _ = Matrix.det (Matrix.setCol M last oldCol) +
          c * Matrix.det (Matrix.setCol M last gramCol) := by
          rw [Matrix.det_setCol_smul]
    _ = Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
          rw [← hold, hgram]

/-- When the modified row index `k` lies outside the leading `t`-prefix
(`t ≤ k.val`), the leading Gram matrix of `Matrix.rowAdd b j k c` agrees with
that of `b`. Internal support lemma for the row-add determinant theorem in
`HexGramSchmidtMathlib.Int`. -/
theorem leadingGramMatrixInt_rowAdd_outside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hkt : t ≤ k.val) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      GramSchmidt.leadingGramMatrixInt b t ht := by
  -- Prove the matrices agree row-by-row using a stronger row-level identity:
  -- for all r : Fin n with r.val < t, the rows of `rowAdd b j k c` and `b`
  -- agree.
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  have hp_ne : (GramSchmidt.liftFinLE ⟨p, hp⟩ ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hp hkt)
  have hq_ne : (GramSchmidt.liftFinLE ⟨q, hq⟩ ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hq hkt)
  have hp_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE ⟨p, hp⟩ ht] =
      b[GramSchmidt.liftFinLE ⟨p, hp⟩ ht] :=
    rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE ⟨p, hp⟩ ht) c hp_ne
  have hq_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE ⟨q, hq⟩ ht] =
      b[GramSchmidt.liftFinLE ⟨q, hq⟩ ht] :=
    rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE ⟨q, hq⟩ ht) c hq_ne
  simp only [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
    Vector.getElem_ofFn, hp_eq, hq_eq]

/-- Entry-level structural identity for the leading Gram matrix of
`Matrix.rowAdd b j k c` when the modified row `k` lies inside the leading
`t`-prefix. The four cases (`p = k.val ∨ p ≠ k.val` × `q = k.val ∨ q ≠ k.val`)
are handled separately. -/
private theorem leadingGramMatrixInt_rowAdd_entry_inside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t)
    (p q : Fin t) :
    (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
      (Matrix.colAdd
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
            ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)[p][q] := by
  -- Abbreviations as Fin t.
  let jt : Fin t := ⟨j.val, Nat.lt_trans hjk hkt⟩
  let kt : Fin t := ⟨k.val, hkt⟩
  -- liftFinLE jt ht = j, liftFinLE kt ht = k as Fin n.
  have hjt_lift : GramSchmidt.liftFinLE jt ht = j := Fin.ext rfl
  have hkt_lift : GramSchmidt.liftFinLE kt ht = k := Fin.ext rfl
  -- The Gram matrix entry as a dot product of integer rows.
  have hM_entry : ∀ (a b' : Fin t),
      (GramSchmidt.leadingGramMatrixInt b t ht)[a][b'] =
        Vector.dotProduct (b[GramSchmidt.liftFinLE a ht]) (b[GramSchmidt.liftFinLE b' ht]) := by
    intro a b'
    simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
      Vector.getElem_ofFn]
  -- LHS is a dot product over `Matrix.rowAdd b j k c` rows.
  have hLHS :
      (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
        Vector.dotProduct ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht])
          ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht]) := by
    simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
      Vector.getElem_ofFn]
  -- RHS: the colAdd-rowAdd entry as a conditional.
  have hRHS :
      (Matrix.colAdd
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c) jt kt c)[p][q] =
        if q = kt then
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][q] +
            c * (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][jt]
        else (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][q] := by
    simp [Matrix.colAdd, Matrix.ofFn, Vector.getElem_ofFn]
  rw [hLHS, hRHS]
  -- Case split on `q = kt` and `p = kt`.
  by_cases hqk : q = kt
  · -- q = kt branch
    rw [if_pos hqk]
    rw [rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c q,
        rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c jt]
    -- The `b[·]` rewrites for `liftFinLE jt ht` and `liftFinLE kt ht`
    -- give `b[j]` and `b[k]` respectively. These survive even when direct
    -- `rw` fails on motive: we rewrite the matrix row indexings via
    -- `congrArg b.get` once and reuse.
    have hbjt_lift : b[GramSchmidt.liftFinLE jt ht] = b[j] :=
      congrArg b.get hjt_lift
    have hbkt_lift : b[GramSchmidt.liftFinLE kt ht] = b[k] :=
      congrArg b.get hkt_lift
    by_cases hpk : p = kt
    · -- p = kt, q = kt
      have hpn_k : GramSchmidt.liftFinLE p ht = k :=
        Fin.ext (Fin.val_eq_of_eq hpk : p.val = kt.val)
      have hqn_k : GramSchmidt.liftFinLE q ht = k :=
        Fin.ext (Fin.val_eq_of_eq hqk : q.val = kt.val)
      have hrowAdd_p :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hpn_k
      have hrowAdd_q :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hqn_k
      rw [hrowAdd_p, hrowAdd_q]
      rw [dot_rowAdd_row_at_left b j k c ((Matrix.rowAdd b j k c)[k])]
      have hrec_k :
          Vector.dotProduct b[k] ((Matrix.rowAdd b j k c)[k]) =
            Vector.dotProduct b[k] b[k] + c * Vector.dotProduct b[k] b[j] :=
        dot_rowAdd_row_at_right b j k c b[k]
      have hrec_j :
          Vector.dotProduct b[j] ((Matrix.rowAdd b j k c)[k]) =
            Vector.dotProduct b[j] b[k] + c * Vector.dotProduct b[j] b[j] :=
        dot_rowAdd_row_at_right b j k c b[j]
      rw [hrec_k, hrec_j]
      simp only [if_pos hpk]
      rw [hM_entry kt q, hM_entry jt q, hM_entry kt jt, hM_entry jt jt]
      have hb_q : b[GramSchmidt.liftFinLE q ht] = b[k] :=
        congrArg b.get hqn_k
      rw [hbjt_lift, hbkt_lift, hb_q]
      have hsym : Vector.dotProduct b[j] b[k] = Vector.dotProduct b[k] b[j] := dot_comm_int _ _
      rw [hsym]
    · -- p ≠ kt, q = kt
      have hpn_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val :=
        fun h => hpk (Fin.ext h)
      have hqn_k : GramSchmidt.liftFinLE q ht = k :=
        Fin.ext (Fin.val_eq_of_eq hqk : q.val = kt.val)
      have hrowAdd_q :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hqn_k
      have hb_q : b[GramSchmidt.liftFinLE q ht] = b[k] :=
        congrArg b.get hqn_k
      rw [hrowAdd_q]
      rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hpn_ne]
      rw [dot_rowAdd_row_at_right b j k c (b[GramSchmidt.liftFinLE p ht])]
      simp only [if_neg hpk]
      rw [hM_entry p q, hM_entry p jt]
      rw [hbjt_lift, hb_q]
  · -- q ≠ kt branch
    rw [if_neg hqk]
    have hqn_ne : (GramSchmidt.liftFinLE q ht).val ≠ k.val :=
      fun h => hqk (Fin.ext h)
    rw [rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c q]
    rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE q ht) c hqn_ne]
    have hbjt_lift : b[GramSchmidt.liftFinLE jt ht] = b[j] :=
      congrArg b.get hjt_lift
    have hbkt_lift : b[GramSchmidt.liftFinLE kt ht] = b[k] :=
      congrArg b.get hkt_lift
    by_cases hpk : p = kt
    · -- p = kt, q ≠ kt
      have hpn_k : GramSchmidt.liftFinLE p ht = k :=
        Fin.ext (Fin.val_eq_of_eq hpk : p.val = kt.val)
      have hrowAdd_p :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hpn_k
      rw [hrowAdd_p]
      rw [dot_rowAdd_row_at_left b j k c (b[GramSchmidt.liftFinLE q ht])]
      simp only [if_pos hpk]
      rw [hM_entry kt q, hM_entry jt q]
      rw [hbjt_lift, hbkt_lift]
    · -- p ≠ kt, q ≠ kt
      have hpn_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val :=
        fun h => hpk (Fin.ext h)
      rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hpn_ne]
      simp only [if_neg hpk]
      rw [hM_entry p q]

/-- When the modified row index `k` lies inside the leading `t`-prefix
(`k.val < t`), the leading Gram matrix of `Matrix.rowAdd b j k c` agrees with
the row-and-column-add of the original leading Gram matrix at the lifted
`Fin t` indices `jt`, `kt`. Internal support lemma for the row-add
determinant theorem in `HexGramSchmidtMathlib.Int`. -/
theorem leadingGramMatrixInt_rowAdd_inside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      Matrix.colAdd
        (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
        ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c := by
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  exact leadingGramMatrixInt_rowAdd_entry_inside b j k c t ht hjk hkt
    ⟨p, hp⟩ ⟨q, hq⟩


/-- The executable scaled-coefficient pivot entry changes predictably under
an earlier-row addition. This packages the Cramer/Bareiss pivot identity at
the public `scaledCoeffs` level so update callers need not unfold the
underlying determinant identity directly. -/
theorem scaledCoeffs_rowAdd_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j +
        c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  have hnew := scaledCoeffs_eq_scaledCoeffMatrix_det
    (b := Matrix.rowAdd b j k c) (i := k) (j := j) hjk
  have hold := scaledCoeffs_eq_scaledCoeffMatrix_det (b := b) (i := k) (j := j) hjk
  have hbridge := scaledCoeffMatrix_rowAdd_pivot_det (b := b) (j := j) (k := k) hjk c
  have hlead := leadingGramMatrixInt_det_eq_gramDet_int
    (b := b) (t := j.val + 1) (ht := Nat.succ_le_of_lt j.isLt)
  calc
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
        Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) := hnew
    _ =
        Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1)
              (Nat.succ_le_of_lt j.isLt)) := hbridge
    _ =
        GramSchmidt.entry (scaledCoeffs b) k j +
          c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
      rw [← hold, hlead]


/-- Adding a multiple of an earlier row to a later row leaves the leading
Gram determinant unchanged. The hypothesis `j.val < k.val` makes the source
row earlier than the destination row in the basis. -/
theorem gramDet_rowAdd_earlier
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) :
    gramDet (Matrix.rowAdd b j k c) t ht = gramDet b t ht := by
  unfold gramDet
  -- Reduce to the underlying Bareiss-determinant equality on `Int`.
  congr 1
  by_cases hkt : k.val < t
  · -- Inside case: bareiss = det, then det_rowAdd / det_colAdd preserve.
    rw [leadingGramMatrixInt_rowAdd_inside b j k c t ht hjk hkt]
    -- Identify `bareiss = det` via Mathlib's `Matrix.det ∘ matrixEquiv`,
    -- composing `bareiss_eq_mathlib_det` with `det_eq.symm` to keep the
    -- executable determinant surface visible to `det_colAdd` / `det_rowAdd`.
    have hbareiss_det : ∀ (M : Hex.Matrix Int t t),
        Hex.Matrix.bareiss M = Hex.Matrix.det M := fun M =>
      (HexMatrixMathlib.bareiss_eq_mathlib_det M).trans
        (HexMatrixMathlib.det_eq M).symm
    rw [hbareiss_det, hbareiss_det]
    -- Indices and inequality between `jt` and `kt` in `Fin t`.
    have hjt_ne_kt : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t) ≠ ⟨k.val, hkt⟩ := by
      intro h
      have hval : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t).val =
          (⟨k.val, hkt⟩ : Fin t).val :=
        congrArg Fin.val h
      exact Nat.ne_of_lt hjk hval
    rw [Matrix.det_colAdd _ _ _ _ hjt_ne_kt]
    rw [Matrix.det_rowAdd _ _ _ _ hjt_ne_kt]
  · -- Outside case: leading prefix unchanged.
    have hkt' : t ≤ k.val := Nat.le_of_not_lt hkt
    rw [leadingGramMatrixInt_rowAdd_outside b j k c t ht hkt']


/-! ### `scaledCoeffs` row-by-row updates under earlier-row addition

The three theorems below package the scaled-coefficient update under
`Matrix.rowAdd b j k c` with `j.val < k.val` at each below-diagonal column
position (left of the pivot, the row that is unchanged when not the
destination, and strictly between the source and the pivot column). They
mirror the pattern of `scaledCoeffs_rowAdd_pivot` and let the
`LLLState.sizeReduceColumn` proof-field discharges in `HexLLL/Basic.lean`
work against `rowAdd` directly, without reaching for the Mathlib-side
`scaledCoeffs_sizeReduce_*` wrappers in `HexGramSchmidt/Update.lean`. -/

private theorem intCast_rat_injective_for_rowAdd {a b : Int}
    (h : (a : Rat) = (b : Rat)) : a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

private theorem scaledCoeffs_eq_fin_of_lt (b : Matrix Int n m) (i j : Fin n)
    (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
        GramSchmidt.entry (coeffs b) i j := by
  simpa using scaledCoeffs_eq (b := b) i.val j.val i.isLt hji

/-- Under `Matrix.rowAdd b j k c` with `l.val < j.val < k.val`, the
destination-row scaled coefficient at column `l` updates by the linear
combination `(scaledCoeffs b)[k][l] + c * (scaledCoeffs b)[j][l]`. -/
theorem scaledCoeffs_rowAdd_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l +
        c * GramSchmidt.entry (scaledCoeffs b) j l := by
  apply intCast_rat_injective_for_rowAdd
  have hlk : l.val < k.val := Nat.lt_trans hlj hjk
  have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) k l hlk
  have holdk := scaledCoeffs_eq_fin_of_lt (b := b) k l hlk
  have holdj := scaledCoeffs_eq_fin_of_lt (b := b) j l hlj
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_lower (b := b) l j k hlj hjk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            (GramSchmidt.entry (coeffs b) k l +
              (c : Rat) * GramSchmidt.entry (coeffs b) j l) := by
          rw [hdet, hcoeff]
    _ =
          ((GramSchmidt.entry (scaledCoeffs b) k l +
            c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
          calc
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                (GramSchmidt.entry (coeffs b) k l +
                  (c : Rat) * GramSchmidt.entry (coeffs b) j l)
                =
                  (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                    GramSchmidt.entry (coeffs b) k l +
                    (c : Rat) *
                      ((gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                        GramSchmidt.entry (coeffs b) j l) := by
                  grind
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) +
                    (c : Rat) *
                      ((GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  rw [← holdk, ← holdj]
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l +
                    c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  grind

/-- Under `Matrix.rowAdd b j k c` with `j.val < k.val`, every row of
`scaledCoeffs` other than the destination row `k` is preserved. -/
theorem scaledCoeffs_rowAdd_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (i : Fin n) (hik : i ≠ k) :
    (scaledCoeffs (Matrix.rowAdd b j k c)).row i = (scaledCoeffs b).row i := by
  apply Vector.ext
  intro col hcol
  let l : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l =
    GramSchmidt.entry (scaledCoeffs b) i l
  by_cases hli : l.val < i.val
  · apply intCast_rat_injective_for_rowAdd
    have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) i l hli
    have hold := scaledCoeffs_eq_fin_of_lt (b := b) i l hli
    have hdet :
        gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
          gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
      gramDet_rowAdd_earlier b j k c (l.val + 1)
        (Nat.succ_le_of_lt l.isLt) hjk
    have hrow := coeffs_rowAdd_other_row (b := b) j k c hjk i hik
    have hcoeff :
        GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l =
          GramSchmidt.entry (coeffs b) i l := by
      have hget := congrArg (fun row => row[l]) hrow
      simpa [GramSchmidt.entry] using hget
    calc
      ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l : Int) : Rat)
          =
            (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
                (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l := hnew
      _ =
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs b) i l := by
            rw [hdet, hcoeff]
      _ = ((GramSchmidt.entry (scaledCoeffs b) i l : Int) : Rat) := hold.symm
  · by_cases hil : i = l
    · subst l
      rw [← hil]
      rw [scaledCoeffs_diag, scaledCoeffs_diag]
      exact congrArg Int.ofNat
        (gramDet_rowAdd_earlier b j k c (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) hjk)
    · have hilv : i.val < l.val := by
        have hle : i.val ≤ l.val := Nat.le_of_not_lt hli
        exact Nat.lt_of_le_of_ne hle (fun h => hil (Fin.ext h))
      rw [scaledCoeffs_upper (Matrix.rowAdd b j k c) i.val l.val i.isLt l.isLt hilv,
        scaledCoeffs_upper b i.val l.val i.isLt l.isLt hilv]

/-- Under `Matrix.rowAdd b j k c` with `j.val < l.val < k.val`, the
destination-row scaled coefficient at column `l` between the source column
and the pivot is preserved. -/
theorem scaledCoeffs_rowAdd_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l := by
  apply intCast_rat_injective_for_rowAdd
  have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) k l hlk
  have hold := scaledCoeffs_eq_fin_of_lt (b := b) k l hlk
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_above_pivot (b := b) j l k hjl hlk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs b) k l := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) := hold.symm


/-! ### Determinant-backed independence

These determinant-positivity lemmas for `gramDet` live in
`HexGramSchmidtMathlib` because their proofs identify `gramDet` with the
Leibniz determinant of the leading Gram matrix via the composition of
`HexMatrixMathlib.bareiss_eq_mathlib_det` and `HexMatrixMathlib.det_eq.symm`
(packaged here as `leadingGramMatrixInt_det_eq_gramDet_int`). Callers that
already have a determinant lemma for a special matrix family can produce the
public `independent` predicate stated over Mathlib-free computed data. -/

private theorem gramDet_pos_of_det_positive (b : Matrix Int n m)
    (hdet : ∀ k : Fin n, 0 < Matrix.det (Matrix.leadingSubmatrix (Matrix.gramMatrix b) k))
    (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      let last : Fin n := ⟨r, hrn⟩
      have hsub : 0 < Matrix.det (Matrix.leadingSubmatrix (Matrix.gramMatrix b) last) :=
        hdet last
      have hsub_eq :
          Matrix.leadingSubmatrix (Matrix.gramMatrix b) last =
            GramSchmidt.leadingGramMatrixInt b (r + 1) hk := by
        rw [Matrix.leadingSubmatrix_eq_leadingPrefix]
        rw [GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]
      have hdet_pos :
          0 < Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hk) := by
        simpa [hsub_eq] using hsub
      have hdet_nat :
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hk) =
            Int.ofNat (gramDet b (r + 1) hk) :=
        leadingGramMatrixInt_det_eq_gramDet_int b (r + 1) hk
      have hnat_int : 0 < Int.ofNat (gramDet b (r + 1) hk) := by
        simpa [hdet_nat] using hdet_pos
      exact Int.ofNat_lt.mp hnat_int

/-- A determinant-positive leading-Gram-prefix proof induces the executable
`gramDet` independence predicate. This is useful for callers that already
have determinant lemmas for special matrix families, while keeping the public
predicate stated over Mathlib-free computed data. -/
theorem independent_of_det_positive (b : Matrix Int n m)
    (hdet : ∀ k : Fin n, 0 < Matrix.det (Matrix.leadingSubmatrix (Matrix.gramMatrix b) k)) :
    independent b := by
  intro k
  exact gramDet_pos_of_det_positive b hdet (k.val + 1) (Nat.succ_le_of_lt k.isLt)
    (Nat.succ_pos k.val)

/-- The identity matrix is independent: its Gram matrix is the identity, so
every leading principal minor has determinant `1 > 0`. -/
theorem independent_one {n : Nat} : independent (1 : Matrix Int n n) := by
  exact independent_of_det_positive (1 : Matrix Int n n) (by
    intro k
    rw [Matrix.gramMatrix_one, Matrix.leadingSubmatrix_one, Matrix.det_one]
    decide)


/-! ### Singular-prefix zero propagation for the Gram-Bareiss surface

When the no-pivot Bareiss loop on a Gram matrix records a singular step at
index `s`, the `(s+1)`-leading Gram prefix has zero determinant. By the
multiplicative succession `gramSchmidtNormProduct_succ`, the same vanishing
propagates to every larger prefix. This is the singular branch of the
`gramDetVecEntry_eq_leadingPrefix_bareiss` placeholder. -/


/-- From a partial no-pivot Bareiss pass on `M` recording a singular step at
index `s`, derive that the `s`-fueled prefix is non-singular, has reached
`step = s`, and has zero diagonal at `(s, s)`. This is the structural data
needed to invoke `BareissNoPivotInvariant` at the moment of singularity.

The matrix-entry equality is transferred from the final state to the prefix
state via `Matrix.noPivotLoop_diag_of_le_step`: subsequent no-pivot iterations
do not modify the diagonal at indices `≤ state.step`. -/
private theorem noPivotLoop_prefix_state_at_singular
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).singularStep = none ∧
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s ∧
      (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState M)).matrix[
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] = 0 := by
  set init := Matrix.noPivotInitialState M with hinit_def
  have h_init_sing : init.singularStep = none := rfl
  have h_init_step : init.step = 0 := rfl
  -- First derive `s < fuel` from the singular bound.
  have hsfuel : s < fuel := by
    have := noPivotLoop_singularStep_lt (n := n) fuel init h_init_sing s h_sing
    rw [h_init_step] at this
    omega
  -- Case analysis on whether the s-fueled prefix is already singular.
  rcases noPivotLoop_singular_inv (n := n) s init h_init_sing
    with h_none | ⟨k', h_sing_s, h_step_s, h_zero_s, h_klt⟩
  · -- s-fueled prefix is non-singular: derive .step = s and .matrix[s][s] = 0.
    have hS_step : (Matrix.noPivotLoop s init).step = s := by
      have h_room : init.step + s + 1 ≤ n := by rw [h_init_step]; omega
      have h_step := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        (n := n) s init h_init_sing h_room h_none
      rw [h_step, h_init_step]; omega
    refine ⟨h_none, hS_step, ?_⟩
    -- Apply singular_inv on the full pass to extract the zero diagonal.
    rcases noPivotLoop_singular_inv (n := n) fuel init h_init_sing
      with h_full_none | ⟨k, h_sing_full, h_step_full, h_zero_full, h_klt_full⟩
    · rw [h_full_none] at h_sing; nomatch h_sing
    · -- k.val = s from h_sing.
      have hk_eq : k.val = s := by
        rw [h_sing_full] at h_sing
        exact Option.some.inj h_sing
      -- Transfer the zero diagonal value from the full state back to the prefix state.
      have hsn : s < n := Nat.lt_of_succ_le hs
      have h_full_eq : Matrix.noPivotLoop (s + (fuel - s)) init =
          Matrix.noPivotLoop fuel init := by
        congr 1; omega
      have h_split : Matrix.noPivotLoop fuel init =
          Matrix.noPivotLoop (fuel - s) (Matrix.noPivotLoop s init) := by
        rw [← h_full_eq, Matrix.noPivotLoop_add s (fuel - s) init]
      have h_diag_preserved :
          (Matrix.noPivotLoop (fuel - s) (Matrix.noPivotLoop s init)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s init).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
        Matrix.noPivotLoop_diag_of_le_step (fuel - s)
          (Matrix.noPivotLoop s init) (⟨s, hsn⟩ : Fin n)
          (by rw [hS_step])
      have h_full_diag_eq :
          (Matrix.noPivotLoop fuel init).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s init).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] := by
        rw [h_split]; exact h_diag_preserved
      -- The full state's value at ⟨s, hsn⟩ equals 0 via h_zero_full at k = ⟨s, _⟩.
      have h_fin : k = (⟨s, hsn⟩ : Fin n) := Fin.ext hk_eq
      have h_full_zero :
          (Matrix.noPivotLoop fuel init).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] = 0 :=
        (matrix_diag_at_fin_eq (Matrix.noPivotLoop fuel init).matrix h_fin).symm.trans h_zero_full
      exact h_full_diag_eq.symm.trans h_full_zero
  · -- s-fueled prefix is already singular at some k'.val < s. Contradicts h_sing.
    have h_klt' : k'.val < s := by
      have := noPivotLoop_singularStep_lt (n := n) s init h_init_sing k'.val h_sing_s
      rw [h_init_step] at this
      omega
    -- The singular state persists.
    have h_persist :
        Matrix.noPivotLoop (s + (fuel - s)) init =
          Matrix.noPivotLoop s init :=
      noPivotLoop_extends_singularStep init s (fuel - s) k'
        h_sing_s h_step_s h_zero_s h_klt
    have h_fuel_eq : s + (fuel - s) = fuel := by omega
    rw [h_fuel_eq] at h_persist
    rw [h_persist] at h_sing
    rw [h_sing_s] at h_sing
    have hk'_eq : k'.val = s := Option.some.inj h_sing
    omega

/-- Specialization of `BareissNoPivotInvariant.trailing_eq` to the diagonal
corner: when the no-pivot Bareiss state has `step = k` for a free variable `k`,
its `(k, k)` matrix entry equals the determinant of the `(k + 1)`-leading
prefix of the source matrix. Stated with `k` as a free variable so that
`subst` can replace the let-bound projection with a fresh name. -/
private theorem bareissNoPivotInvariant_diag_eq
    {n : Nat} (M : Matrix Int n n) (state : Matrix.BareissState n) (k : Nat)
    (hinv : HexMatrixMathlib.BareissNoPivotInvariant M state)
    (hsk : k = state.step) (hk : k < n) :
    state.matrix[(⟨k, hk⟩ : Fin n)][(⟨k, hk⟩ : Fin n)] =
      Matrix.det (Matrix.leadingPrefix M (k + 1) (Nat.succ_le_of_lt hk)) := by
  subst hsk
  have h_trail :
      state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
        Matrix.det (Matrix.borderedMinor M state.step hk
          (⟨state.step, hk⟩ : Fin n) (⟨state.step, hk⟩ : Fin n)) :=
    hinv.trailing_eq hk (⟨state.step, hk⟩ : Fin n) (⟨state.step, hk⟩ : Fin n)
      (Nat.le_refl _) (Nat.le_refl _)
  rw [HexMatrixMathlib.borderedMinor_corner_eq_leadingPrefix M state.step hk] at h_trail
  exact h_trail

/-- Identification with the Mathlib leading-prefix determinant: from a partial
no-pivot Bareiss pass that records a singular step at index `s`, the
`(s+1)`-leading prefix of the source matrix has zero determinant (Hex's
`Matrix.det`). -/
private theorem leadingPrefix_det_eq_zero
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    Matrix.det (Matrix.leadingPrefix M (s + 1) hs) = 0 := by
  obtain ⟨h_none, h_step, h_zero⟩ :=
    noPivotLoop_prefix_state_at_singular M fuel s hs h_sing
  -- Apply the noPivotLoop_invariant variant: S satisfies BareissNoPivotInvariant.
  have hinv_init : HexMatrixMathlib.BareissNoPivotInvariant M
      (Matrix.noPivotInitialState M) :=
    HexMatrixMathlib.bareissNoPivotInvariant_initial M
  have hinv_S : HexMatrixMathlib.BareissNoPivotInvariant M
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) :=
    HexMatrixMathlib.noPivotLoop_invariant_of_singularStep_eq_none M s
      (Matrix.noPivotInitialState M) hinv_init h_none
  -- Use Nat.lt_of_succ_le hs as the bound throughout to match the helper's output type.
  -- Specialize the diagonal-corner helper: matrix[⟨s, _⟩][⟨s, _⟩] = det(leadingPrefix M (s+1) _).
  have h_diag_eq_lp :
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[(⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][(⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] =
        Matrix.det (Matrix.leadingPrefix M (s + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hs))) :=
    bareissNoPivotInvariant_diag_eq
      M (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) s hinv_S
      h_step.symm (Nat.lt_of_succ_le hs)
  rw [h_zero] at h_diag_eq_lp
  -- h_diag_eq_lp : 0 = det(leadingPrefix M (s+1) (Nat.succ_le_of_lt ...)). The proof
  -- argument is definitionally equal to `hs`, so the goal matches up to proof irrelevance.
  exact h_diag_eq_lp.symm

/-- Multiplicative zero propagation for `gramSchmidtNormProduct`: if the
norm-product at some index `k₁` vanishes, every larger index's product also
vanishes. Proof is by induction on the gap via `gramSchmidtNormProduct_succ`. -/
private theorem gramSchmidtNormProduct_eq_zero_of_le {n m : Nat}
    (b : Matrix Int n m) (k₁ k₂ : Nat) (hk₂ : k₂ ≤ n) (hkk : k₁ ≤ k₂)
    (h₁ : gramSchmidtNormProduct b k₁ (Nat.le_trans hkk hk₂) = 0) :
    gramSchmidtNormProduct b k₂ hk₂ = 0 := by
  induction k₂ with
  | zero =>
      have : k₁ = 0 := Nat.le_zero.mp hkk
      subst this
      exact h₁
  | succ k₂' ih =>
      by_cases hcase : k₁ = k₂' + 1
      · subst hcase; exact h₁
      · have hkk' : k₁ ≤ k₂' := by omega
        have hk₂' : k₂' ≤ n := Nat.le_of_succ_le hk₂
        have h_prev : gramSchmidtNormProduct b k₂' hk₂' = 0 := by
          have h₁' : gramSchmidtNormProduct b k₁ (Nat.le_trans hkk' hk₂') = 0 := h₁
          exact ih hk₂' hkk' h₁'
        rw [gramSchmidtNormProduct_succ b k₂' hk₂, h_prev, Rat.zero_mul]

/-- Singular-branch zero propagation: if the partial-pass no-pivot Bareiss loop
on the full Gram matrix records a singular step at index `s` strictly before
slot `r + 1`, the public row-pivoted Bareiss determinant of the `(r + 1)`
leading Gram prefix is zero.

This is the supporting lemma needed by the singular branch of the
`gramDetVecEntry_eq_leadingPrefix_bareiss` placeholder: both sides vanish in
this case, and this lemma supplies the right-hand side. The proof composes the
new lemma `HexMatrixMathlib.noPivotLoop_invariant_of_singularStep_eq_none`
(to identify `det(leadingPrefix _ (s+1)) = 0` at the moment of singularity) with
the unconditional `gramDet_eq_prod_normSq_uncond` and the multiplicative
succession `gramSchmidtNormProduct_succ` to propagate zero from `s + 1` to
`r + 1`. -/
theorem leadingPrefix_gram_bareiss_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (r : Nat) (hr : r < n) (s : Nat)
    (h_sing : (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    Matrix.bareiss (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
        (Nat.succ_le_of_lt hr)) = 0 := by
  -- Step A: derive `s < r` from the partial-pass singular bound.
  have hsr : s < r := by
    have h := noPivotLoop_singularStep_lt (n := n) r
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
    change s < 0 + r at h
    omega
  have hs1 : s + 1 ≤ n := Nat.le_trans (Nat.succ_le_of_lt hsr) (Nat.le_of_lt hr)
  -- Step B: derive det(leadingPrefix (gramMatrix b) (s+1)) = 0 via the new lemma.
  have h_det_s1_zero :
      Matrix.det (Matrix.leadingPrefix (Matrix.gramMatrix b) (s + 1) hs1) = 0 :=
    leadingPrefix_det_eq_zero
      (Matrix.gramMatrix b) r s hs1 h_sing
  -- Step C: convert to gramSchmidtNormProduct b (s+1) = 0.
  have h_lead_eq_s :
      GramSchmidt.leadingGramMatrixInt b (s + 1) hs1 =
        Matrix.leadingPrefix (Matrix.gramMatrix b) (s + 1) hs1 :=
    GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram b (s + 1) hs1
  have h_det_lead_s1_zero :
      Matrix.det (GramSchmidt.leadingGramMatrixInt b (s + 1) hs1) = 0 := by
    rw [h_lead_eq_s]; exact h_det_s1_zero
  have h_gd_s1_zero : gramDet b (s + 1) hs1 = 0 := by
    have hnat := leadingGramMatrixInt_det_eq_gramDet_int b (s + 1) hs1
    rw [h_det_lead_s1_zero] at hnat
    have hcast : Int.ofNat (gramDet b (s + 1) hs1) = Int.ofNat 0 := hnat.symm
    exact Int.ofNat.inj hcast
  have h_gd_s1_rat_zero : (gramDet b (s + 1) hs1 : Rat) = 0 := by
    rw [h_gd_s1_zero]; norm_cast
  have h_gsnp_s1_zero : gramSchmidtNormProduct b (s + 1) hs1 = 0 := by
    have := gramDet_eq_prod_normSq_uncond b (s + 1) hs1
    rw [this] at h_gd_s1_rat_zero
    exact h_gd_s1_rat_zero
  -- Step D: propagate to gramSchmidtNormProduct b (r+1) = 0.
  have hr1 : r + 1 ≤ n := Nat.succ_le_of_lt hr
  have hs1r1 : s + 1 ≤ r + 1 := Nat.succ_le_succ (Nat.le_of_lt hsr)
  have h_gsnp_r1_zero : gramSchmidtNormProduct b (r + 1) hr1 = 0 :=
    gramSchmidtNormProduct_eq_zero_of_le b (s + 1) (r + 1) hr1 hs1r1 h_gsnp_s1_zero
  -- Step E: back to gramDet b (r+1) = 0.
  have h_gd_r1_rat_zero : (gramDet b (r + 1) hr1 : Rat) = 0 := by
    rw [gramDet_eq_prod_normSq_uncond b (r + 1) hr1]; exact h_gsnp_r1_zero
  have h_gd_r1_zero : gramDet b (r + 1) hr1 = 0 := by
    have : ((gramDet b (r + 1) hr1 : Nat) : Rat) = (0 : Rat) := h_gd_r1_rat_zero
    exact_mod_cast this
  -- Step F: convert to det(leadingGramMatrixInt b (r+1)) = 0, then to bareiss.
  have h_det_lead_r1_zero :
      Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hr1) = 0 := by
    have hnat := leadingGramMatrixInt_det_eq_gramDet_int b (r + 1) hr1
    rw [h_gd_r1_zero] at hnat
    simpa using hnat
  have h_det_prefix_r1_zero :
      Matrix.det (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1) hr1) = 0 := by
    have h_lead_eq_r :
        GramSchmidt.leadingGramMatrixInt b (r + 1) hr1 =
          Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1) hr1 :=
      GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram b (r + 1) hr1
    rw [← h_lead_eq_r]; exact h_det_lead_r1_zero
  rw [HexMatrixMathlib.bareiss_eq_det]
  exact h_det_prefix_r1_zero

/-- Capstone for the Gram determinant vector: the no-pivot
Bareiss pass over the full Gram matrix records, at slot `r + 1`, the same
leading-prefix determinant as the public row-pivoted Bareiss surface on that
prefix.

This theorem lives in `HexGramSchmidtMathlib` because the proof path for the
singular branch identifies the executable determinant with Mathlib's Leibniz
determinant. Mathlib-free callers should use the executable `gramDet` API
instead of depending on this Bareiss-facing statement. -/
theorem gramDetVecEntry_eq_leadingPrefix_bareiss
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      (Matrix.bareiss
        (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr))).toNat := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let data := Matrix.bareissNoPivotData GM
  let i : Fin n := ⟨r, hr⟩
  by_cases h_prefix :
      (Matrix.noPivotLoop r init).singularStep = none
  · have hdiag :=
      bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
        (b := b) r hr (by simpa [GM, init] using h_prefix)
    have h_step_r : (Matrix.noPivotLoop r init).step = r := by
      have h_room : init.step + r + 1 ≤ n := by
        simp [init, Matrix.noPivotInitialState]
        omega
      have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        r init rfl h_room h_prefix
      simpa [init, Matrix.noPivotInitialState] using h
    have h_entry_diag :
        gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
      have h_split : r + (n - r) = n := by omega
      have h_full :
          Matrix.noPivotLoop n init =
            Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init) := by
        simpa [h_split] using Matrix.noPivotLoop_add r (n - r) init
      rcases noPivotLoop_singular_inv (n := n) (n - r)
          (Matrix.noPivotLoop r init) h_prefix with h_none | h_sing
      · have hdata : data.singularStep = none := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_none
        simp [gramDetVecEntry, data, hdata, i]
        rfl
      · rcases h_sing with ⟨k, h_sing_full, h_step_full, h_zero_full, _hk_bound⟩
        have hdata : data.singularStep = some k.val := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_sing_full
        have hmono := noPivotLoop_step_monotone (n - r) (Matrix.noPivotLoop r init)
        have hr_le_k : r ≤ k.val := by
          rw [h_step_r, h_step_full] at hmono
          exact hmono
        by_cases hkr : k.val = r
        · have hlt : k.val < r + 1 := by omega
          have hdata_matrix :
              data.matrix[i][i] =
                (Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init)).matrix[i][i] := by
            simp [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full]
          have hzero_i : data.matrix[i][i] = 0 := by
            have hi_eq : i = k := Fin.ext hkr.symm
            rw [hdata_matrix]
            simpa [hi_eq] using h_zero_full
          simp [gramDetVecEntry, data, hdata, i, hlt]
          simpa [data, i] using (congrArg Int.toNat hzero_i).symm
        · have hlt : ¬ k.val < r + 1 := by omega
          simp [gramDetVecEntry, data, hdata, i, hlt]
          rfl
    calc
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
          ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
            simpa [data, GM, i] using h_entry_diag
      _ = (Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat := by
            exact congrArg Int.toNat (by simpa [data, GM, i] using hdiag)
  · rcases noPivotLoop_singular_inv (n := n) r init rfl with h_none | h_sing
    · exact False.elim (h_prefix h_none)
    · rcases h_sing with ⟨k, h_sing_r, h_step_r, h_zero_r, h_klt⟩
      have hsr : k.val < r + 1 := by
        have h := noPivotLoop_singularStep_lt (n := n) r init rfl k.val h_sing_r
        simp [init, Matrix.noPivotInitialState] at h
        omega
      have h_full_eq :
          Matrix.noPivotLoop n init = Matrix.noPivotLoop r init := by
        have h_split : n = r + (n - r) := by omega
        have hext :=
          noPivotLoop_extends_singularStep init r (n - r) k
            h_sing_r h_step_r h_zero_r h_klt
        exact (congrArg (fun fuel => Matrix.noPivotLoop fuel init) h_split).trans hext
      have hdata : data.singularStep = some k.val := by
        simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full_eq] using h_sing_r
      have hleft :
          gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
        simp [gramDetVecEntry, data, hdata, hsr]
      have hright :
          Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr)) = 0 :=
        leadingPrefix_gram_bareiss_eq_zero_of_singularStep_lt
          (b := b) r hr k.val (by simpa [GM, init] using h_sing_r)
      rw [hright]
      simpa [data, GM] using hleft


end Int
end GramSchmidt
end Hex
