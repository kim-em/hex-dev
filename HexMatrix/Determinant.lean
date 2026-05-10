import Std
import Init.Grind.Ring.Field
import Batteries.Data.Fin.Fold
import Batteries.Data.List.Lemmas
import Batteries.Data.Vector.Lemmas
import HexMatrix.RowEchelon

/-!
Determinant routines for `hex-matrix`.

This module adds the generic Leibniz-formula determinant for dense square
matrices together with the determinant behavior of the elementary row
operations used by row reduction and Bareiss pivot tracking.
-/

namespace Hex

universe u

namespace Matrix

variable {α : Type u}

/-- Insert an element into a vector at a given position. -/
def insertAt (x : α) (v : Vector α n) (i : Fin (n + 1)) : Vector α (n + 1) :=
  ⟨(v.toList.insertIdx i.val x).toArray, by
    have hi : i.val ≤ v.toList.length := by
      simpa using Nat.lt_succ_iff.mp i.isLt
    simpa using List.length_insertIdx_of_le_length (a := x) (as := v.toList) hi⟩

/-- The unique empty vector. -/
def emptyVec : Vector α 0 :=
  ⟨#[], rfl⟩

/-- Enumerate the permutations of `Fin n` as length-`n` vectors. -/
def permutationVectors : (n : Nat) → List (Vector (Fin n) n)
  | 0 => [emptyVec]
  | n + 1 =>
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n)

/-- Count inversions in a permutation written as a list. -/
def inversionCount : List (Fin n) → Nat
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 + inversionCount xs

private def crossInversionCount {n : Nat} : List (Fin n) → List (Fin n) → Nat
  | [], _ => 0
  | x :: xs, ys =>
      ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        crossInversionCount xs ys

private theorem foldCount_start {α : Type u} (xs : List α) (p : α → Prop)
    [DecidablePred p] (acc : Nat) :
    xs.foldl (fun acc y => acc + if p y then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if p y then 1 else 0), ih (0 + if p y then 1 else 0)]
      omega

private theorem inversionFold_start {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if y < x then 1 else 0), ih (0 + if y < x then 1 else 0)]
      omega

private theorem inversionFold_append {n : Nat} (xs ys : List (Fin n)) (x : Fin n) :
    (xs ++ ys).foldl (fun acc y => acc + if y < x then 1 else 0) 0 =
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  rw [List.foldl_append, inversionFold_start]

private theorem inversionCount_append {n : Nat} (xs ys : List (Fin n)) :
    inversionCount (xs ++ ys) =
      inversionCount xs + inversionCount ys + crossInversionCount xs ys := by
  induction xs with
  | nil =>
      change inversionCount ys =
        inversionCount ([] : List (Fin n)) + inversionCount ys +
          crossInversionCount ([] : List (Fin n)) ys
      simp [inversionCount, crossInversionCount]
  | cons x xs ih =>
      simp only [List.cons_append, inversionCount, crossInversionCount]
      rw [inversionFold_append, ih]
      omega

private theorem crossInversionCount_append_left {n : Nat}
    (xs ys zs : List (Fin n)) :
    crossInversionCount (xs ++ ys) zs =
      crossInversionCount xs zs + crossInversionCount ys zs := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [List.cons_append, crossInversionCount]
      rw [ih]
      omega

private theorem crossInversionCount_append_right {n : Nat}
    (xs ys zs : List (Fin n)) :
    crossInversionCount xs (ys ++ zs) =
      crossInversionCount xs ys + crossInversionCount xs zs := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount]
      rw [inversionFold_append, ih]
      omega

private theorem crossInversionCount_singleton_left {n : Nat}
    (x : Fin n) (ys : List (Fin n)) :
    crossInversionCount [x] ys =
      ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  simp [crossInversionCount]

private theorem crossInversionCount_singleton_right {n : Nat}
    (xs : List (Fin n)) (y : Fin n) :
    crossInversionCount xs [y] =
      xs.foldl (fun acc x => acc + if y < x then 1 else 0) 0 := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount, List.foldl_cons, List.foldl_nil]
      rw [ih]
      exact (foldCount_start xs (fun x => y < x) (0 + if y < x then 1 else 0)).symm

private theorem crossInversionCount_pair_swap_right {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount xs [a, b] =
      crossInversionCount xs [b, a] := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp [crossInversionCount]
      rw [ih]
      omega

private theorem crossInversionCount_pair_swap_left {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount [a, b] xs =
      crossInversionCount [b, a] xs := by
  simp [crossInversionCount]
  omega

private theorem inversionCount_pair {n : Nat} (a b : Fin n) :
    inversionCount [a, b] = if b < a then 1 else 0 := by
  simp [inversionCount]

private theorem inversionCount_adjacent_swap_parity {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (h : a ≠ b) :
    inversionCount (pre ++ a :: b :: post) % 2 =
      (inversionCount (pre ++ b :: a :: post) + 1) % 2 := by
  have horder : a < b ∨ b < a := by
    have hval : a.val ≠ b.val := by
      intro hv
      exact h (Fin.ext hv)
    cases Nat.lt_or_gt_of_ne hval with
    | inl hab => exact Or.inl hab
    | inr hba => exact Or.inr hba
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp]
  rw [show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      crossInversionCount pre ([a, b] ++ post) =
        crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [crossInversionCount_append_right]
    rw [crossInversionCount_pair_swap_right]
  have htail :
      crossInversionCount [a, b] post =
        crossInversionCount [b, a] post := by
    exact crossInversionCount_pair_swap_left post a b
  rw [inversionCount_append pre ([a, b] ++ post)]
  rw [inversionCount_append pre ([b, a] ++ post)]
  rw [hcross]
  rw [inversionCount_append [a, b] post]
  rw [inversionCount_append [b, a] post]
  rw [htail]
  rw [inversionCount_pair a b]
  rw [inversionCount_pair b a]
  cases horder with
  | inl hab =>
      have hba : ¬ b < a := by omega
      simp [hab, hba]
      omega
  | inr hba =>
      have hab : ¬ a < b := by omega
      simp [hab, hba]
      omega

private theorem inversionCount_swap_separated_parity {n : Nat}
    (pre mid post : List (Fin n)) (a b : Fin n)
    (hnodup : (pre ++ a :: mid ++ b :: post).Nodup) :
    inversionCount (pre ++ b :: mid ++ a :: post) % 2 =
      (inversionCount (pre ++ a :: mid ++ b :: post) + 1) % 2 := by
  induction mid generalizing pre with
  | nil =>
      have hne : b ≠ a := by
        intro hba
        subst b
        have hsplit : ((pre ++ [a]) ++ a :: post).Nodup := by
          simpa [List.append_assoc] using hnodup
        exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: post)).mp hsplit).2.2
          a (by simp) a (by simp) rfl
      simpa [Nat.add_comm] using
        (inversionCount_adjacent_swap_parity pre post b a hne)
  | cons x xs ih =>
      have hswap₁ :
          inversionCount (pre ++ b :: x :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: b :: xs ++ a :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ a :: post) b x (by
            intro hbx
            subst b
            have hsplit : ((pre ++ a :: x :: xs) ++ x :: post).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ a :: x :: xs) (l₂ := x :: post)).mp hsplit).2.2
              x (by simp) x (by simp) rfl)
      have hnodup_tail : ((pre ++ [x]) ++ a :: xs ++ b :: post).Nodup := by
        have hp :
            ((pre ++ [x]) ++ a :: xs ++ b :: post).Perm
              (pre ++ a :: x :: xs ++ b :: post) := by
          simpa [List.append_assoc] using
            List.Perm.append_left pre (List.Perm.swap a x (xs ++ b :: post))
        exact hp.nodup_iff.mpr hnodup
      have hmid :
          inversionCount (pre ++ x :: b :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: a :: xs ++ b :: post) + 1) % 2 := by
        simpa only [List.cons_append, List.append_assoc] using
          (ih (pre ++ [x]) hnodup_tail)
      have hswap₂ :
          inversionCount (pre ++ x :: a :: xs ++ b :: post) % 2 =
            (inversionCount (pre ++ a :: x :: xs ++ b :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ b :: post) x a (by
            intro hxa
            subst x
            have hsplit : (pre ++ [a] ++ (a :: xs ++ b :: post)).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: xs ++ b :: post)).mp hsplit).2.2
              a (by simp) a (by simp) rfl)
      omega

/-- The sign of a permutation vector, computed from inversion parity. -/
def detSign {R : Type u} [Lean.Grind.Ring R] {n : Nat} (perm : Vector (Fin n) n) : R :=
  if inversionCount perm.toList % 2 = 0 then 1 else -1

/-- The unsigned product associated to a permutation vector. -/
def detProduct {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * M[i][perm[i]]) 1

/-- The Leibniz summand associated to a permutation vector. -/
def detTerm {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  detSign perm * detProduct M perm

/-- The determinant of a dense square matrix, defined by the Leibniz formula. -/
def det {R : Type u} [Lean.Grind.Ring R] {n : Nat} (M : Matrix R n n) : R :=
  (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0

/-- The determinant of the empty leading prefix is the Bareiss previous-pivot
convention `1`. -/
@[simp] theorem det_leadingPrefix_zero {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R n n) :
    det (leadingPrefix M 0 (Nat.zero_le n)) = (1 : R) := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, emptyVec, inversionCount]
  grind

@[simp] theorem det_one_by_one {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R 1 1) :
    det M = M[0][0] := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, emptyVec, insertAt,
    inversionCount, List.finRange]
  grind

@[simp] theorem det_two_by_two {R : Type u} [Lean.Grind.CommRing R]
    (M : Matrix R 2 2) :
    det M = M[0][0] * M[1][1] - M[1][0] * M[0][1] := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, emptyVec, insertAt,
    inversionCount, List.finRange]
  grind

/-- Congruence for the determinant-style left fold over a finite list. -/
private theorem foldl_det_sum_congr {R : Type u} [Add R] {β : Type v}
    (xs : List β) (f g : β → R) (z : R)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun acc x => acc + f x) z =
      xs.foldl (fun acc x => acc + g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

private theorem foldl_acc_congr {α : Type u} {β : Type v}
    (xs : List β) (f g : α → β → α) (z : α)
    (h : ∀ acc x, x ∈ xs → f acc x = g acc x) :
    xs.foldl f z = xs.foldl g z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h z x (by simp)]
      exact ih (g z x) (fun acc y hy => h acc y (List.mem_cons_of_mem x hy))

private theorem foldl_det_sum_perm {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (f : β → R) {xs ys : List β} (hperm : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc + f x) z =
      ys.foldl (fun acc x => acc + f x) z := by
  induction hperm generalizing z with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldl_cons]
      exact ih (z + _)
  | swap x y xs =>
      simp only [List.foldl_cons]
      congr 1
      grind
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ z).trans (ih₂ z)

private theorem foldl_det_product_congr {R : Type u} [Mul R] {β : Type v}
    (xs : List β) (f g : β → R) (z : R)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun acc x => acc * f x) z =
      xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

private theorem detProduct_congr_matrix {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    {M N : Matrix R n n}
    (h : ∀ (r : Fin n) (c : Fin n), M[r][c] = N[r][c])
    (perm : Vector (Fin n) n) :
    detProduct M perm = detProduct N perm := by
  unfold detProduct
  apply foldl_det_product_congr
  intro r _hr
  exact h r perm[r]

private theorem detTerm_congr_matrix {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    {M N : Matrix R n n}
    (h : ∀ (r : Fin n) (c : Fin n), M[r][c] = N[r][c])
    (perm : Vector (Fin n) n) :
    detTerm M perm = detTerm N perm := by
  unfold detTerm
  rw [detProduct_congr_matrix h perm]

private theorem foldl_det_product_perm {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (f : β → R) {xs ys : List β} (hperm : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc * f x) z =
      ys.foldl (fun acc x => acc * f x) z := by
  induction hperm generalizing z with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldl_cons]
      exact ih (z * _)
  | swap x y xs =>
      simp only [List.foldl_cons]
      congr 1
      grind
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ z).trans (ih₂ z)

private theorem list_nodup_map_of_injective {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} (hinj : Function.Injective f) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hfy⟩
        exact hnodup.1 (hinj hfy.symm ▸ hy)
      · exact list_nodup_map_of_injective hinj hnodup.2

private theorem list_nodup_map_on {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} :
    ∀ {xs : List α}, xs.Nodup →
      (∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) →
      (xs.map f).Nodup
  | [], _hnodup, _hinj => by simp
  | x :: xs, hnodup, hinj => by
      simp only [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
        have hxy := hinj x (by simp) y (List.mem_cons_of_mem x hy) hfy.symm
        subst y
        exact hnodup.1 hy
      · exact list_nodup_map_on hnodup.2 (by
          intro a ha b hb hab
          exact hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab)

/-- Factor a scalar out of a determinant-style finite left fold. -/
private theorem foldl_det_sum_mul_left {R : Type u} [Lean.Grind.CommRing R] {β : Type v}
    (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc + c * f x) (c * z) =
      c * xs.foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z + f x) = c * z + c * f x by grind]
      exact ih (z + f x)

/-- Factor a scalar out of a determinant-style finite left fold from zero. -/
private theorem foldl_det_sum_mul_left_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) :
    xs.foldl (fun acc x => acc + c * f x) 0 =
      c * xs.foldl (fun acc x => acc + f x) 0 := by
  have hzero : c * 0 = 0 := by grind
  simpa [hzero] using (foldl_det_sum_mul_left (R := R) xs c f 0)

private theorem foldl_det_sum_mul_right_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (c : R) :
    xs.foldl (fun acc x => acc + f x * c) 0 =
      xs.foldl (fun acc x => acc + f x) 0 * c := by
  calc
    xs.foldl (fun acc x => acc + f x * c) 0 =
        xs.foldl (fun acc x => acc + c * f x) 0 := by
          apply foldl_det_sum_congr
          intro x _hmem
          grind
    _ = c * xs.foldl (fun acc x => acc + f x) 0 := by
          exact foldl_det_sum_mul_left_zero xs c f
    _ = xs.foldl (fun acc x => acc + f x) 0 * c := by
          grind

private theorem foldl_det_sum_add_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f g : β → R) (a b : R) :
    xs.foldl (fun acc x => acc + (f x + g x)) (a + b) =
      xs.foldl (fun acc x => acc + f x) a +
        xs.foldl (fun acc x => acc + g x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc + (f x + g x)) (a + b + (f x + g x)) =
          xs.foldl (fun acc x => acc + (f x + g x)) ((a + f x) + (b + g x)) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc + f x) (a + f x) +
            xs.foldl (fun acc x => acc + g x) (b + g x) := by
            exact ih (a + f x) (b + g x)

private theorem foldl_det_sum_add_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f g : β → R) :
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
  calc
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + (f x + g x)) ((0 : R) + 0) := by
        congr 1
        grind
    _ =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
        exact foldl_det_sum_add_start xs f g 0 0

private theorem foldl_det_sum_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc + f x) z =
      z + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing z with
  | nil =>
      have hzero : z + (0 : R) = z := by grind
      exact hzero.symm
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (z + f x), ih (0 + f x)]
      grind

private theorem foldl_det_sum_flatMap {R : Type u} [Add R] {β γ : Type v}
    (xs : List β) (f : β → List γ) (g : γ → R) (z : R) :
    (xs.flatMap f).foldl (fun acc x => acc + g x) z =
      xs.foldl (fun acc x => (f x).foldl (fun acc y => acc + g y) acc) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      exact ih ((f x).foldl (fun acc y => acc + g y) z)

private theorem foldl_det_sum_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons]
      have hzero : z + (0 : R) = z := by grind
      simpa [hzero] using ih z

private theorem foldl_det_product_mul_left {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc * f x) (c * z) =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z * f x) = (c * z) * f x by grind]
      exact ih (z * f x)

private theorem foldl_det_product_no_scale_of_not_mem {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R) (hnot : i ∉ xs) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mem_cons, not_or] at hnot
      simp only [List.foldl_cons]
      have hx : x ≠ i := by
        intro hxi
        exact hnot.1 hxi.symm
      rw [if_neg hx]
      exact ih (z * f x) hnot.2

private theorem foldl_det_product_single_scale {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        calc
          xs.foldl (fun acc x => acc * if x = i then c * f x else f x) (z * (c * f i)) =
              xs.foldl (fun acc x => acc * f x) (z * (c * f i)) := by
                exact foldl_det_product_no_scale_of_not_mem xs i c f (z * (c * f i)) hnodup.1
          _ = xs.foldl (fun acc x => acc * f x) (c * (z * f i)) := by
                congr 1
                grind
          _ = c * xs.foldl (fun acc x => acc * f x) (z * f i) := by
                exact foldl_det_product_mul_left xs c f (z * f i)
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) hmemTail hnodup.2

private theorem foldl_det_product_add_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (a b : R) :
    xs.foldl (fun acc x => acc * f x) (a + b) =
      xs.foldl (fun acc x => acc * f x) a +
        xs.foldl (fun acc x => acc * f x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc * f x) ((a + b) * f x) =
          xs.foldl (fun acc x => acc * f x) (a * f x + b * f x) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc * f x) (a * f x) +
            xs.foldl (fun acc x => acc * f x) (b * f x) := by
            exact ih (a * f x) (b * f x)

private theorem foldl_det_product_single_add {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f g : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup)
    (hagree : ∀ x, x ∈ xs → x ≠ i → g x = f x) :
    xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x) z =
      xs.foldl (fun acc x => acc * f x) z +
        c * xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        have hnot : i ∉ xs := hnodup.1
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * (f i + c * g i)) =
            xs.foldl (fun acc x => acc * f x) (z * (f i + c * g i)) := by
              apply foldl_det_product_congr
              intro y hy
              have hyi : y ≠ i := by
                intro h
                exact hnot (h ▸ hy)
              rw [if_neg hyi]
          _ = xs.foldl (fun acc x => acc * f x) (z * f i + c * (z * g i)) := by
              congr 1
              grind
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              xs.foldl (fun acc x => acc * f x) (c * (z * g i)) := by
              exact foldl_det_product_add_start xs f (z * f i) (c * (z * g i))
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * f x) (z * g i) := by
              rw [show
                xs.foldl (fun acc x => acc * f x) (c * (z * g i)) =
                  c * xs.foldl (fun acc x => acc * f x) (z * g i) from
                    foldl_det_product_mul_left xs c f (z * g i)]
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * g x) (z * g i) := by
              congr 2
              apply foldl_det_product_congr
              intro y hy
              exact (hagree y (List.mem_cons.mpr (Or.inr hy)) (by
                intro h
                exact hnot (h ▸ hy))).symm
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        have hgx : g x = f x := hagree x (List.mem_cons.mpr (Or.inl rfl)) hx
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * f x) =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * f x) := by
              exact ih (z * f x) hmemTail hnodup.2
                (fun y hy hyi => hagree y (List.mem_cons.mpr (Or.inr hy)) hyi)
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * g x) := by
              rw [hgx]

private theorem foldl_det_product_zero_start {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} (xs : List β) (f : β → R) :
    xs.foldl (fun acc x => acc * f x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hzero : (0 : R) * f x = 0 := by grind
      simpa [hzero] using ih

private theorem foldl_det_product_zero_of_mem {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hzero : f i = 0) :
    xs.foldl (fun acc x => acc * f x) z = 0 := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [hzero]
        have hz : z * (0 : R) = 0 := by grind
        simpa [hz] using foldl_det_product_zero_start xs f
      · have htail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) htail

private theorem identity_get {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (i j : Fin n) :
    (1 : Matrix R n n)[i][j] = if i = j then 1 else 0 := by
  change Matrix.identity[i][j] = if i = j then 1 else 0
  simp [Matrix.identity, Matrix.ofFn]

private theorem detProduct_identity_zero_of_mismatch {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (perm : Vector (Fin n) n)
    (i : Fin n) (h : perm[i] ≠ i) :
    detProduct (1 : Matrix R n n) perm = 0 := by
  unfold detProduct
  have hsymm : i ≠ perm[i] := by
    intro hi
    exact h hi.symm
  exact foldl_det_product_zero_of_mem
    (List.finRange n) i (fun r => (1 : Matrix R n n)[r][perm[r]]) 1
    (List.mem_finRange i) (by
      change (1 : Matrix R n n)[i][perm[i]] = 0
      rw [identity_get]
      rw [if_neg hsymm])

private theorem insertAt_get_self {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i)[i] = x := by
  unfold insertAt
  simp [List.getElem_insertIdx_self]

private theorem insertAt_last_get_castSucc {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin n) :
    (insertAt x v (Fin.last n))[i.castSucc] = v[i] := by
  unfold insertAt
  simp [List.getElem_insertIdx_of_lt]

private theorem insertAt_get_castSucc_of_lt {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) (i r : Fin (n + 1)) (h : r.val < i.val) :
    (insertAt x v i.castSucc)[r.castSucc.castSucc] = v[r] := by
  unfold insertAt
  simp [List.getElem_insertIdx_of_lt, h]

private theorem insertAt_get_last_of_castSucc_last {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) :
    (insertAt x v (Fin.last n).castSucc)[Fin.last (n + 1)] = v[Fin.last n] := by
  unfold insertAt
  simp [List.getElem_insertIdx_of_gt]

private theorem list_getElem_insertIdx_succ_of_le {α : Type u}
    (xs : List α) (x : α) {i r : Nat} (h : i ≤ r) (hr : r < xs.length) :
    (xs.insertIdx i x)[r + 1]'(by
      have hi : i ≤ xs.length := Nat.le_trans h (Nat.le_of_lt hr)
      rw [List.length_insertIdx_of_le_length hi]
      omega) = xs[r] := by
  induction xs generalizing i r with
  | nil =>
      cases hr
  | cons y ys ih =>
      cases i with
      | zero =>
          cases r with
          | zero =>
              simp
          | succ r =>
              simp
      | succ i =>
          cases r with
          | zero =>
              omega
          | succ r =>
              simp only [List.insertIdx, List.getElem_cons_succ]
              exact ih (Nat.succ_le_succ_iff.mp h) (Nat.succ_lt_succ_iff.mp hr)

private theorem insertAt_prefix_get_self {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) (i : Fin n) :
    (insertAt x v i.castSucc.castSucc)[i.castSucc.castSucc] = x := by
  exact insertAt_get_self x v i.castSucc.castSucc

private theorem insertAt_prefix_get_before {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) (i r : Fin n) (h : r.val < i.val) :
    (insertAt x v i.castSucc.castSucc)[r.castSucc.castSucc] = v[r.castSucc] := by
  exact insertAt_get_castSucc_of_lt x v i.castSucc r.castSucc (by simpa using h)

private theorem insertAt_prefix_get_shifted {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) (i : Fin n) (r : Fin (n + 1))
    (h : i.val ≤ r.val) :
    (insertAt x v i.castSucc.castSucc)[(⟨r.val + 1, by omega⟩ : Fin (n + 2))] =
      v[r] := by
  unfold insertAt
  simpa [Vector.toList] using
    list_getElem_insertIdx_succ_of_le v.toList x h (by simp [Vector.length_toList])

private theorem insertAt_prefix_get_last {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) (i : Fin n) :
    (insertAt x v i.castSucc.castSucc)[Fin.last (n + 1)] = v[Fin.last n] := by
  have hle : i.val ≤ (Fin.last n).val := by
    simp [Nat.le_of_lt i.isLt]
  simpa using insertAt_prefix_get_shifted x v i (Fin.last n) hle

private theorem insertAt_castSucc_last_get_boundary {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) :
    (insertAt x v (Fin.last n).castSucc)[(Fin.last n).castSucc] = x := by
  exact insertAt_get_self x v (Fin.last n).castSucc

private theorem insertAt_castSucc_last_get_last {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) :
    (insertAt x v (Fin.last n).castSucc)[Fin.last (n + 1)] = v[Fin.last n] := by
  exact insertAt_get_last_of_castSucc_last x v

private theorem insertAt_castSucc_last_get_prefix {α : Type u} {n : Nat}
    (x : α) (v : Vector α (n + 1)) (i : Fin n) :
    (insertAt x v (Fin.last n).castSucc)[i.castSucc.castSucc] = v[i.castSucc] := by
  exact insertAt_get_castSucc_of_lt x v (Fin.last n) i.castSucc (by simp)

private theorem detProduct_identity_insertAt_not_last_zero {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (h : i ≠ Fin.last n) :
    detProduct (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  apply detProduct_identity_zero_of_mismatch
  exact by
    rw [insertAt_get_self]
    exact h.symm

private theorem detProduct_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detProduct (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detProduct (1 : Matrix R n n) v := by
  unfold detProduct
  rw [← Fin.foldl_eq_foldl_finRange, ← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              (1 : Matrix R (n + 1) (n + 1))[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
      Fin.foldl n (fun acc i => acc * (1 : Matrix R n n)[i][v[i]]) 1 := by
    congr
    funext acc i
    rw [identity_get, identity_get]
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    rw [hget]
    simp [Fin.ext_iff]
  have hlast :
      (1 : Matrix R (n + 1) (n + 1))[Fin.last n][
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n]] = 1 := by
    rw [identity_get]
    have hself :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
          Fin.last n := by
      exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
    simp [hself]
  rw [hfold, hlast]
  have hmul_one : ∀ x : R, x * (1 : R) = x := by
    intro x
    exact Lean.Grind.Semiring.mul_one x
  exact hmul_one _

private theorem inversionFold_map_castSucc {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if y.castSucc < x.castSucc then 1 else 0) =
            (if y < x then 1 else 0) := by
        simp [Fin.lt_def]
      rw [hhead]
      exact ih _

private theorem inversionCount_map_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount (xs.map Fin.castSucc) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_castSucc]

private theorem inversionCount_insert_last_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount ((xs.map Fin.castSucc) ++ [Fin.last n]) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.cons_append, inversionCount]
      rw [ih]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [inversionFold_map_castSucc]
      simp [Fin.lt_def]

private theorem foldl_insertIdx_last_castSucc_not_lt {n : Nat} (xs : List (Fin n))
    (x : Fin n) (p acc : Nat) :
    ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
      (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc := by
  induction xs generalizing p acc with
  | nil =>
      cases p <;> simp [List.insertIdx, Fin.lt_def]
  | cons y ys ih =>
      cases p with
      | zero =>
          have hnlt : ¬ n < x.val := by omega
          simp [List.insertIdx, Fin.lt_def, hnlt]
      | succ p =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [List.foldl_cons]
          change
            ((ys.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0) =
              (ys.map Fin.castSucc).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0)
          rw [ih p (acc + if y.castSucc < x.castSucc then 1 else 0)]

private theorem foldl_all_lt_last_castSucc {n : Nat} (xs : List (Fin n)) (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < Fin.last n then 1 else 0) acc =
      acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, List.length_cons]
      rw [ih (acc + if x.castSucc < Fin.last n then 1 else 0)]
      simp [Fin.lt_def]
      omega

private theorem inversionCount_insertIdx_castSucc_last_eq {n : Nat}
    (xs : List (Fin n)) (p : Nat) (hp : p ≤ xs.length) :
    inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
      inversionCount xs + (xs.length - p) := by
  induction xs generalizing p with
  | nil =>
      cases p with
      | zero => rfl
      | succ p => cases hp
  | cons x xs ih =>
      cases p with
      | zero =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_zero]
          simp only [inversionCount, List.foldl_cons]
          rw [foldl_all_lt_last_castSucc xs
            (0 + if x.castSucc < Fin.last n then 1 else 0)]
          rw [inversionFold_map_castSucc]
          rw [inversionCount_map_castSucc]
          simp [Fin.lt_def]
          omega
      | succ p =>
          have hp' : p ≤ xs.length := Nat.succ_le_succ_iff.mp hp
          have hlen : (x :: xs).length - (p + 1) = xs.length - p := by
            simp
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [inversionCount]
          change
            ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0) 0 +
                inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
              xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
                inversionCount xs + ((x :: xs).length - (p + 1))
          rw [foldl_insertIdx_last_castSucc_not_lt xs x p]
          rw [inversionFold_map_castSucc]
          rw [ih p hp']
          rw [hlen]
          grind

private theorem list_insertIdx_length {α : Type u} (xs : List α) (x : α) :
    xs.insertIdx xs.length x = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp [ih]

private theorem vector_toList_map {α β : Type u} {n : Nat} (v : Vector α n)
    (f : α → β) :
    (v.map f).toList = v.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

private theorem insertAt_last_toList {α : Type u} {n : Nat} (x : α) (v : Vector α n) :
    (insertAt x v (Fin.last n)).toList = v.toList ++ [x] := by
  unfold insertAt
  simp only [Vector.toList]
  have hidx : (Fin.last n).val = v.toArray.toList.length := by
    simp
  simpa [hidx] using list_insertIdx_length v.toArray.toList x

private theorem insertAt_toList {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i).toList = v.toList.insertIdx i.val x := by
  unfold insertAt
  simp [Vector.toList]

private theorem list_nodup_map_castSucc {n : Nat} (xs : List (Fin n)) :
    xs.Nodup → (xs.map Fin.castSucc).Nodup := by
  induction xs with
  | nil =>
      intro _h
      simp
  | cons x xs ih =>
      intro hnodup
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hxy⟩
        have hval : x.val = y.val := by
          simpa using (congrArg Fin.val hxy).symm
        exact hnodup.1 (Fin.ext hval ▸ hy)
      · exact ih hnodup.2

private theorem finLast_not_mem_map_castSucc {n : Nat} (xs : List (Fin n)) :
    Fin.last n ∉ xs.map Fin.castSucc := by
  intro hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨x, _hxmem, hxlast⟩
  have hval : x.val = n := by
    simpa using congrArg Fin.val hxlast
  exact Nat.ne_of_lt x.isLt hval

private theorem insertAt_last_castSucc_nodup {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1))
    (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup := by
  rw [insertAt_toList]
  have hmap : (v.map Fin.castSucc).toList.Nodup := by
    rw [vector_toList_map]
    exact list_nodup_map_castSucc v.toList hnodup
  have hlast : Fin.last n ∉ (v.map Fin.castSucc).toList := by
    rw [vector_toList_map]
    exact finLast_not_mem_map_castSucc v.toList
  have hcons : (Fin.last n :: (v.map Fin.castSucc).toList).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hlast, hmap⟩
  have hidx : i.val ≤ (v.map Fin.castSucc).toList.length := by
    simpa using Nat.lt_succ_iff.mp i.isLt
  exact (List.perm_insertIdx (Fin.last n) (v.map Fin.castSucc).toList hidx).symm.nodup hcons

private theorem finList_length_le_card {n : Nat} {xs : List (Fin n)}
    (hnodup : xs.Nodup) :
    xs.length ≤ n := by
  have hsub : List.Subperm xs (List.finRange n) := by
    exact List.subperm_of_subset hnodup (fun x _hx => List.mem_finRange x)
  simpa [List.length_finRange] using List.Subperm.length_le hsub

private theorem finLast_mem_of_full_nodup {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    Fin.last n ∈ xs := by
  by_cases hmem : Fin.last n ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange (n + 1)).erase (Fin.last n)) := by
      apply List.subperm_of_subset hnodup
      intro x hx
      exact (List.mem_erase_of_ne (by
        intro hxlast
        exact hmem (hxlast ▸ hx))).2 (List.mem_finRange x)
    have hle : xs.length ≤ ((List.finRange (n + 1)).erase (Fin.last n)).length :=
      List.Subperm.length_le hsub
    have herase :
        ((List.finRange (n + 1)).erase (Fin.last n)).length = n := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    omega

private def lowerFinLast {n : Nat} (x : Fin (n + 1)) (h : x ≠ Fin.last n) :
    Fin n :=
  ⟨x.val, by
    have hxlt : x.val < n + 1 := x.isLt
    have hxne : x.val ≠ n := by
      intro hx
      exact h (Fin.ext hx)
    omega⟩

private def raiseFinAbove {n : Nat} (i : Fin (n + 1)) (r : Fin n) :
    Fin (n + 1) :=
  if h : r.val < i.val then
    ⟨r.val, by omega⟩
  else
    ⟨r.val + 1, by omega⟩

private theorem insertAt_get_raiseFinAbove {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) (r : Fin n) :
    (insertAt x v i)[raiseFinAbove i r] = v[r] := by
  unfold insertAt raiseFinAbove
  split
  · simpa [Vector.getElem_toList] using
      List.getElem_insertIdx_of_lt (l := v.toList) (x := x) (i := i.val)
        (j := r.val) ‹r.val < i.val› (by
          have hi : i.val ≤ v.toList.length := by
            simpa [Vector.length_toList] using Nat.lt_succ_iff.mp i.isLt
          rw [List.length_insertIdx_of_le_length hi]
          simpa [Vector.length_toList] using Nat.lt_succ_of_lt r.isLt)
  · simpa using
      list_getElem_insertIdx_succ_of_le v.toList x (Nat.le_of_not_gt ‹¬r.val < i.val›)
        (by simp [Vector.length_toList])

private theorem raiseFinAbove_lt_iff {n : Nat} (i : Fin (n + 1)) (a b : Fin n) :
    raiseFinAbove i a < raiseFinAbove i b ↔ a < b := by
  by_cases hai : a.val < i.val
  · by_cases hbi : b.val < i.val
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
      omega
  · by_cases hbi : b.val < i.val
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
      omega
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]

private theorem inversionFold_map_raiseFinAbove {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (x : Fin n) (acc : Nat) :
    (xs.map (raiseFinAbove i)).foldl
        (fun acc y => acc + if y < raiseFinAbove i x then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if raiseFinAbove i y < raiseFinAbove i x then 1 else 0) =
            (if y < x then 1 else 0) := by
        by_cases hyx : y < x
        · have hraise : raiseFinAbove i y < raiseFinAbove i x :=
            (raiseFinAbove_lt_iff i y x).2 hyx
          simp [hyx, hraise]
        · have hraise : ¬ raiseFinAbove i y < raiseFinAbove i x := by
            intro h
            exact hyx ((raiseFinAbove_lt_iff i y x).1 h)
          simp [hyx, hraise]
      rw [hhead]
      exact ih _

private theorem inversionCount_map_raiseFinAbove {n : Nat}
    (i : Fin (n + 1)) (xs : List (Fin n)) :
    inversionCount (xs.map (raiseFinAbove i)) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_raiseFinAbove]

private theorem inversionFold_map_raiseFinAbove_self {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (acc : Nat) :
    (xs.map (raiseFinAbove i)).foldl
        (fun acc y => acc + if i < y then 1 else 0) acc =
    acc + xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if i < raiseFinAbove i x then 1 else 0) =
            (if i.val ≤ x.val then 1 else 0) := by
        by_cases hxi : x.val < i.val
        · have hnle : ¬ i.val ≤ x.val := by omega
          have hnlt : ¬ i < raiseFinAbove i x := by
            simp [raiseFinAbove, hxi, Fin.lt_def]
            omega
          simp [hnle, hnlt]
        · have hle : i.val ≤ x.val := Nat.le_of_not_gt hxi
          have hlt : i < raiseFinAbove i x := by
            change i.val < (raiseFinAbove i x).val
            simp [raiseFinAbove, hxi]
            omega
          simp [hle, hlt]
      rw [hhead]
      rw [ih (acc + if i.val ≤ x.val then 1 else 0)]
      rw [foldCount_start xs (fun y : Fin n => i.val ≤ y.val)
        (0 + if i.val ≤ x.val then 1 else 0)]
      omega

private theorem inversionCount_map_raiseFinAbove_append_self {n : Nat}
    (i : Fin (n + 1)) (xs : List (Fin n)) :
    inversionCount ((xs.map (raiseFinAbove i)) ++ [i]) =
      inversionCount xs +
        xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 := by
  rw [inversionCount_append]
  rw [inversionCount_map_raiseFinAbove]
  have hsingle : inversionCount ([i] : List (Fin (n + 1))) = 0 := by
    simp [inversionCount]
  rw [hsingle]
  rw [crossInversionCount_singleton_right]
  rw [inversionFold_map_raiseFinAbove_self i xs 0]
  omega

private theorem foldCount_map_castSucc_ge {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if i.val ≤ y.val then 1 else 0) acc =
      xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih _

private theorem foldl_ignore {α : Type u} (xs : List α) (acc : Nat) :
    xs.foldl (fun acc _x => acc) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons]
      exact ih acc

private theorem foldCount_finRange_ge {n : Nat} (i : Fin (n + 1)) :
    (List.finRange n).foldl
        (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
      n - i.val := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases htop : i.val = n + 1
      · have hfalse :
            ∀ acc y, y ∈ List.finRange (n + 1) →
              (fun (acc : Nat) (y : Fin (n + 1)) =>
                acc + if i.val ≤ y.val then 1 else 0) acc y =
                (fun (acc : Nat) (_y : Fin (n + 1)) => acc) acc y := by
          intro acc y _hy
          have hnle : ¬ i.val ≤ y.val := by omega
          simp [hnle]
        calc
          (List.finRange (n + 1)).foldl
              (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
              (List.finRange (n + 1)).foldl
                (fun (acc : Nat) (_y : Fin (n + 1)) => acc) 0 := by
                exact foldl_acc_congr (List.finRange (n + 1))
                  (fun (acc : Nat) (y : Fin (n + 1)) =>
                    acc + if i.val ≤ y.val then 1 else 0)
                  (fun (acc : Nat) (_y : Fin (n + 1)) => acc) 0 hfalse
          _ = 0 := foldl_ignore (List.finRange (n + 1)) 0
          _ = n + 1 - i.val := by omega
      · have hiLt : i.val < n + 1 := by omega
        let i' : Fin (n + 1) := ⟨i.val, hiLt⟩
        rw [List.finRange_succ_last]
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [foldCount_map_castSucc_ge i' (List.finRange n) 0]
        rw [ih i']
        have hleLast : i.val ≤ n := by omega
        simp [i', hleLast]
        omega

private theorem foldCount_perm {α : Type u} (p : α → Prop) [DecidablePred p]
    {xs ys : List α} (hperm : xs.Perm ys) :
    xs.foldl (fun acc y => acc + if p y then 1 else 0) 0 =
      ys.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
  induction hperm with
  | nil => rfl
  | cons x hperm ih =>
      rename_i l₁ l₂
      simp only [List.foldl_cons]
      let a := 0 + if p x then 1 else 0
      calc
        l₁.foldl (fun acc y => acc + if p y then 1 else 0) a =
            a + l₁.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
              exact foldCount_start l₁ p a
        _ = a + l₂.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
              rw [ih]
        _ = l₂.foldl (fun acc y => acc + if p y then 1 else 0) a := by
              exact (foldCount_start l₂ p a).symm
  | swap x y xs =>
      simp only [List.foldl_cons]
      rw [foldCount_start xs p ((0 + if p y then 1 else 0) + if p x then 1 else 0)]
      rw [foldCount_start xs p ((0 + if p x then 1 else 0) + if p y then 1 else 0)]
      omega
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem fin_mem_of_full_nodup_for_count {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    x ∈ xs := by
  by_cases hmem : x ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange n).erase x) := by
      apply List.subperm_of_subset hnodup
      intro y hy
      exact (List.mem_erase_of_ne (by
        intro hyx
        exact hmem (hyx ▸ hy))).2 (List.mem_finRange y)
    have hle : xs.length ≤ ((List.finRange n).erase x).length :=
      List.Subperm.length_le hsub
    have herase : ((List.finRange n).erase x).length = n - 1 := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    rw [hlen, herase] at hle
    cases n with
    | zero => exact Fin.elim0 x
    | succ n => omega

private theorem list_perm_finRange_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.Perm (List.finRange n) := by
  rw [List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)]
  intro x
  constructor
  · intro _hx
    exact List.mem_finRange x
  · intro _hx
    exact fin_mem_of_full_nodup_for_count x hlen hnodup

private theorem foldCount_full_nodup_ge {n : Nat} (i : Fin (n + 1))
    {xs : List (Fin n)} (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
      n - i.val := by
  rw [foldCount_perm (fun y : Fin n => i.val ≤ y.val)
    (list_perm_finRange_of_full_nodup hlen hnodup)]
  exact foldCount_finRange_ge i

private theorem lowerFinLast_castSucc {n : Nat} (x : Fin (n + 1))
    (h : x ≠ Fin.last n) :
    (lowerFinLast x h).castSucc = x := by
  exact Fin.ext rfl

private theorem finLast_idxOf_lt_of_full_nodup {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    xs.idxOf (Fin.last n) < xs.length := by
  exact List.idxOf_lt_length_of_mem (finLast_mem_of_full_nodup hlen hnodup)

private def peelLastVector {n : Nat} (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (_hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) : Vector (Fin n) n :=
  Vector.ofFn fun r =>
    let j := if r.val < k then r.val else r.val + 1
    have hj : j < n + 1 := by
      dsimp [j]
      split
      · omega
      · have hr : r.val < n := r.isLt
        omega
    let y := perm[(⟨j, hj⟩ : Fin (n + 1))]
    lowerFinLast y (by
      intro hy
      have hjlen : j < perm.toList.length := by
        simpa [Vector.length_toList] using hj
      have hjidx :
          perm.toList.idxOf (perm.toList[j]'hjlen) = j := by
        exact hnodup.idxOf_getElem j hjlen
      have hylist : perm.toList[j]'hjlen = Fin.last n := by
        simpa [Vector.getElem_toList] using hy
      have hkj : k = j := by
        rw [← hidx, ← hylist, hjidx]
      dsimp [j] at hkj
      split at hkj
      · omega
      · omega)

private theorem peelLastVector_castSucc_toList {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc).toList =
      perm.toList.eraseIdx k := by
  apply List.ext_getElem
  · have hklist : k < perm.toList.length := by
      simpa [Vector.length_toList] using hk
    rw [List.length_eraseIdx_of_lt hklist]
    simp [Vector.length_toList]
  · intro i hi₁ hi₂
    by_cases hik : i < k
    · simp [peelLastVector, hik, lowerFinLast_castSucc, List.getElem_eraseIdx]
    · have hikle : k ≤ i := Nat.le_of_not_gt hik
      have hklist : k < perm.toList.length := by
        simpa [Vector.length_toList] using hk
      have heraseLen : (perm.toList.eraseIdx k).length = n := by
        rw [List.length_eraseIdx_of_lt hklist]
        simp [Vector.length_toList]
      have hi : i < n := by
        simpa [heraseLen] using hi₂
      simp [peelLastVector, hik, lowerFinLast_castSucc, List.getElem_eraseIdx]

private theorem list_nodup_of_map_injective {α β : Type u} {f : α → β}
    (hinj : Function.Injective f) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hxmem
        exact hnodup.1 (List.mem_map.mpr ⟨x, hxmem, rfl⟩)
      · exact list_nodup_of_map_injective hinj hnodup.2

private theorem peelLastVector_nodup {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    (peelLastVector perm k hk hidx hnodup).toList.Nodup := by
  apply list_nodup_of_map_injective (f := Fin.castSucc)
  · intro x y hxy
    exact Fin.ext (by simpa using congrArg Fin.val hxy)
  · rw [← vector_toList_map]
    rw [peelLastVector_castSucc_toList perm k hk hidx hnodup]
    exact hnodup.eraseIdx k

private theorem list_insertIdx_eraseIdx_getElem {α : Type u} {xs : List α} {i : Nat}
    (hi : i < xs.length) :
    (xs.eraseIdx i).insertIdx i (xs[i]'hi) = xs := by
  induction xs generalizing i with
  | nil =>
      cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simp [ih hi]

private theorem insertAt_peelLastVector {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    insertAt (Fin.last n)
        ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩ =
      perm := by
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  change (insertAt (Fin.last n)
        ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩).toList =
      perm.toList
  rw [insertAt_toList]
  rw [peelLastVector_castSucc_toList perm k hk hidx hnodup]
  have hklist : k < perm.toList.length := by
    simpa [Vector.length_toList] using hk
  have hget : perm.toList[k]'hklist = Fin.last n := by
    have hidxLt : perm.toList.idxOf (Fin.last n) < perm.toList.length := by
      simpa [hidx] using hklist
    simpa [hidx] using
      (List.getElem_idxOf (x := Fin.last n) (xs := perm.toList) hidxLt)
  simpa [hget] using
    (list_insertIdx_eraseIdx_getElem (xs := perm.toList) (i := k) hklist)

theorem permutationVectors_complete {n : Nat} {perm : Vector (Fin n) n}
    (hnodup : perm.toList.Nodup) :
    perm ∈ permutationVectors n := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hperm : perm = emptyVec := by
        apply Vector.ext
        intro i hi
        omega
      simp [permutationVectors, hperm]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt_of_full_nodup (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled : peeled ∈ permutationVectors n := by
        exact ih (peelLastVector_nodup perm k hk hidx hnodup)
      change perm ∈
        List.flatMap
          (fun v =>
            (List.finRange (n + 1)).map fun i =>
              insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (permutationVectors n)
      rw [List.mem_flatMap]
      refine ⟨peeled, hpeeled, ?_⟩
      rw [List.mem_map]
      refine ⟨(⟨k, hk⟩ : Fin (n + 1)), List.mem_finRange (⟨k, hk⟩ : Fin (n + 1)), ?_⟩
      exact insertAt_peelLastVector perm k hk hidx hnodup

theorem permutationVectors_nodup {n : Nat} {perm : Vector (Fin n) n}
    (hmem : perm ∈ permutationVectors n) :
    perm.toList.Nodup := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      rw [hnil]
      simp
  | succ n ih =>
      simp [permutationVectors, List.mem_flatMap, List.mem_map] at hmem
      rcases hmem with ⟨v, hv, i, _hi, rfl⟩
      exact insertAt_last_castSucc_nodup v i (ih hv)

private theorem insertAt_last_castSucc_idxOf {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf (Fin.last n) =
      i.val := by
  have hins :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup :=
    insertAt_last_castSucc_nodup v i hnodup
  have hlen :
      i.val < (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.length := by
    simp [Vector.length_toList]
  have hget :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList[i.val] =
        Fin.last n := by
    change (insertAt (Fin.last n) (v.map Fin.castSucc) i)[i] = Fin.last n
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) i
  simpa [hget] using hins.idxOf_getElem i.val hlen

private theorem insertAt_last_castSucc_injective {n : Nat}
    {v w : Vector (Fin n) n} {i j : Fin (n + 1)}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup)
    (h :
      insertAt (Fin.last n) (v.map Fin.castSucc) i =
        insertAt (Fin.last n) (w.map Fin.castSucc) j) :
    i = j ∧ v = w := by
  have hidx :
      i.val = j.val := by
    rw [← insertAt_last_castSucc_idxOf v i hv]
    rw [h]
    exact insertAt_last_castSucc_idxOf w j hw
  have hij : i = j := Fin.ext hidx
  subst j
  have hlist := congrArg
    (fun x : Vector (Fin (n + 1)) (n + 1) => x.toList.eraseIdx i.val) h
  change
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.eraseIdx i.val =
      (insertAt (Fin.last n) (w.map Fin.castSucc) i).toList.eraseIdx i.val at hlist
  rw [insertAt_toList, insertAt_toList] at hlist
  repeat rw [List.eraseIdx_insertIdx_self] at hlist
  have hmap : v.toList.map Fin.castSucc = w.toList.map Fin.castSucc := by
    simpa [vector_toList_map] using hlist
  have hvwList : v.toList = w.toList := by
    exact (List.map_inj_right
      (fun x y hxy => Fin.ext (by simpa using congrArg Fin.val hxy))).mp hmap
  refine ⟨rfl, ?_⟩
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  simpa [Vector.toList] using hvwList

private theorem permutationVectorInsertions_nodup {n : Nat}
    (v : Vector (Fin n) n) (hnodup : v.toList.Nodup) :
    ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  exact list_nodup_map_of_injective
    (fun i j h => (insertAt_last_castSucc_injective hnodup hnodup h).1)
    (List.nodup_finRange (n + 1))

private theorem permutationVectorInsertions_disjoint {n : Nat}
    {v w : Vector (Fin n) n}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup) (hvw : v ≠ w) :
    ∀ a, a ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i) →
      ∀ b, b ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (w.map Fin.castSucc) i) →
        a ≠ b := by
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  rcases ha with ⟨i, _hi, rfl⟩
  rcases hb with ⟨j, _hj, hb⟩
  exact hvw (insertAt_last_castSucc_injective hv hw (hab.trans hb.symm)).2

private theorem permutationVectors_flatMap_nodup {n : Nat}
    (vs : List (Vector (Fin n) n))
    (hvs : vs.Nodup) (hperm : ∀ v, v ∈ vs → v.toList.Nodup) :
    (vs.flatMap fun v =>
        (List.finRange (n + 1)).map fun i =>
          insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  induction vs with
  | nil =>
      simp
  | cons v vs ih =>
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      simp only [List.nodup_cons] at hvs
      refine ⟨?_, ?_, ?_⟩
      · exact permutationVectorInsertions_nodup v (hperm v (by simp))
      · exact ih hvs.2 (fun w hw => hperm w (List.mem_cons_of_mem v hw))
      · intro a ha b hb hab
        simp only [List.mem_flatMap, List.mem_map] at hb
        rcases hb with ⟨w, hw, j, _hj, rfl⟩
        exact permutationVectorInsertions_disjoint
          (hperm v (by simp)) (hperm w (List.mem_cons_of_mem v hw))
          (by
            intro hvw
            exact hvs.1 (hvw ▸ hw))
          a ha _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) hab

theorem permutationVectors_nodup_list {n : Nat} :
    (permutationVectors n).Nodup := by
  induction n with
  | zero =>
      simp [permutationVectors]
  | succ n ih =>
      simp only [permutationVectors]
      exact permutationVectors_flatMap_nodup
        (permutationVectors n) ih
        (fun v hv => permutationVectors_nodup hv)

theorem detSign_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (v : Vector (Fin n) n) :
    detSign (R := R)
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detSign (R := R) v := by
  unfold detSign
  rw [insertAt_last_toList, vector_toList_map, inversionCount_insert_last_castSucc]

private theorem detSignParity_add {R : Type u} [Lean.Grind.Ring R] (a m : Nat) :
    (if (a + m) % 2 = 0 then (1 : R) else -1) =
      (-1 : R) ^ m * if a % 2 = 0 then (1 : R) else -1 := by
  induction m with
  | zero =>
      simp [Nat.add_zero]
      grind
  | succ m ih =>
      rw [Nat.add_succ]
      rw [Lean.Grind.Semiring.pow_succ]
      rw [show (-1 : R) ^ m * -1 * (if a % 2 = 0 then (1 : R) else -1) =
          -1 * ((-1 : R) ^ m * if a % 2 = 0 then (1 : R) else -1) by
        grind]
      rw [← ih]
      have hsucc : (a + m).succ = a + (m + 1) := by omega
      rw [hsucc]
      by_cases hm : (a + m) % 2 = 0
      · have hmnot' : ¬(a + (m + 1)) % 2 = 0 := by omega
        rw [if_pos hm, if_neg hmnot']
        grind
      · have hmnext' : (a + (m + 1)) % 2 = 0 := by omega
        rw [if_neg hm, if_pos hmnext']
        grind

private theorem detSign_of_inversionCount_add {R : Type u} [Lean.Grind.Ring R]
    {n n' : Nat} (perm : Vector (Fin n) n) (perm' : Vector (Fin n') n') (m : Nat)
    (h :
      inversionCount perm'.toList =
        inversionCount perm.toList + m) :
    detSign (R := R) perm' = (-1 : R) ^ m * detSign (R := R) perm := by
  unfold detSign
  rw [h]
  exact detSignParity_add (R := R) (inversionCount perm.toList) m

private theorem detSign_insertAt_prefix {R : Type u} [Lean.Grind.Ring R] {k : Nat}
    (v : Vector (Fin (k + 1)) (k + 1)) (r : Fin k) :
    detSign (R := R)
      (insertAt (Fin.last (k + 1)) (v.map Fin.castSucc) r.castSucc.castSucc) =
      (-1 : R) ^ (k + 1 - r.val) * detSign (R := R) v := by
  apply detSign_of_inversionCount_add
  rw [insertAt_toList, vector_toList_map]
  change inversionCount ((v.toList.map Fin.castSucc).insertIdx r.val (Fin.last (k + 1))) =
    inversionCount v.toList + (k + 1 - r.val)
  simpa [Vector.length_toList] using
    inversionCount_insertIdx_castSucc_last_eq v.toList r.val (by
      simp [Vector.length_toList]
      omega)

theorem detSign_identity {R : Type u} [Lean.Grind.Ring R] (n : Nat) :
    detSign (R := R) (Vector.ofFn fun i : Fin n => i) = 1 := by
  induction n with
  | zero =>
      have hvec : (Vector.ofFn fun i : Fin 0 => i) = emptyVec := by
        apply Vector.ext
        intro i hi
        omega
      simp [hvec, detSign, emptyVec, inversionCount]
  | succ n ih =>
      have hvec :
          (Vector.ofFn fun i : Fin (n + 1) => i) =
            insertAt (Fin.last n)
              ((Vector.ofFn fun i : Fin n => i).map Fin.castSucc) (Fin.last n) := by
        apply Vector.ext
        intro k hk
        by_cases hlast : k = n
        · subst k
          simp [insertAt, List.getElem_insertIdx_self]
          exact Fin.ext rfl
        · have hklt : k < n := by omega
          simp [insertAt, List.getElem_insertIdx_of_lt, hklt]
      rw [hvec, detSign_insertAt_last]
      exact ih

/-- Product reindexing for a permutation that fixes the final column. The
Leibniz product splits into the product on the leading prefix times the final
row/column entry. -/
theorem detProduct_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n] := by
  unfold detProduct
  rw [← Fin.foldl_eq_foldl_finRange, ← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              M[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
        Fin.foldl n
          (fun acc i => acc * (leadingPrefix M n (Nat.le_succ n))[i][v[i]]) 1 := by
    congr
    funext acc i
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    simp [leadingPrefix, ofFn, hget]
  have hlast :
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
        Fin.last n := by
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
  rw [hfold]
  simp [hlast]

/-- Leibniz-term reindexing for a permutation that fixes the final column. This
packages the sign and product split used by last-row/last-column expansions. -/
theorem detTerm_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detSign (R := R) v *
        (detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_insertAt_last]

private theorem detTerm_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detTerm (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detTerm (1 : Matrix R n n) v := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_identity_insertAt_last]

private theorem foldl_detTerm_identity_insertions {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) (z : R) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm (1 : Matrix R (n + 1) (n + 1))
            (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detTerm (1 : Matrix R n n) v := by
  rw [← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_foldl_finRange]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply foldl_det_sum_congr
          intro i _hmem
          unfold detTerm
          rw [detProduct_identity_insertAt_not_last_zero (R := R) v i.castSucc (by
            intro hlast
            have hval := congrArg Fin.val hlast
            simp at hval
            exact (Nat.ne_of_lt i.isLt) hval)]
          grind
      _ = z := by
          exact foldl_det_sum_zero (List.finRange n) z
  rw [hprefix]
  rw [detTerm_identity_insertAt_last]

private theorem rowScale_get {R : Type u} [Mul R] {n m : Nat}
    (M : Matrix R n m) (i r : Fin n) (c : R) (k : Fin m) :
    (rowScale M i c)[r][k] = if r = i then c * M[i][k] else M[r][k] := by
  by_cases h : r = i
  · subst r
    simp [rowScale]
  · simp [rowScale, h]
    have hval : i.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set i (Vector.ofFn fun k => c * M[i][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne (xs := M) (x := Vector.ofFn fun k => c * M[i][k])
          i.isLt r.isLt hval)
    simpa [rowScale] using congrArg (fun row => row[k]) hrow

private theorem detProduct_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowScale M i c) perm = c * detProduct M perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowScale M i c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * if r = i then c * M[r][perm[r]] else M[r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        by_cases h : r = i
        · subst r
          simpa using (rowScale_get M i i c perm[i])
        · simpa [h] using (rowScale_get M i r c perm[r])
    _ = c * (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 := by
        exact foldl_det_product_single_scale
          (List.finRange n) i c (fun r => M[r][perm[r]]) 1
          (List.mem_finRange i) (List.nodup_finRange n)

private def finTranspose {n : Nat} (i j : Fin n) (r : Fin n) : Fin n :=
  if r = i then j else if r = j then i else r

private theorem finTranspose_left {n : Nat} (i j : Fin n) :
    finTranspose i j i = j := by
  simp [finTranspose]

private theorem finTranspose_right {n : Nat} (i j : Fin n) :
    finTranspose i j j = i := by
  by_cases h : j = i
  · subst j
    simp [finTranspose]
  · simp [finTranspose, h]

private theorem finTranspose_of_ne {n : Nat} (i j r : Fin n)
    (hi : r ≠ i) (hj : r ≠ j) :
    finTranspose i j r = r := by
  simp [finTranspose, hi, hj]

private theorem finTranspose_involutive {n : Nat} (i j r : Fin n) :
    finTranspose i j (finTranspose i j r) = r := by
  by_cases hi : r = i
  · subst r
    rw [finTranspose_left, finTranspose_right]
  · by_cases hj : r = j
    · subst r
      rw [finTranspose_right, finTranspose_left]
    · rw [finTranspose_of_ne i j r hi hj]
      exact finTranspose_of_ne i j r hi hj

private theorem finTranspose_injective {n : Nat} (i j : Fin n) :
    Function.Injective (finTranspose i j) := by
  intro a b h
  have h' := congrArg (finTranspose i j) h
  simpa [finTranspose_involutive] using h'

private theorem finTranspose_ne_iff {n : Nat} (i j a b : Fin n) :
    finTranspose i j a ≠ finTranspose i j b ↔ a ≠ b := by
  constructor
  · intro h hab
    exact h (hab ▸ rfl)
  · intro h hab
    exact h (finTranspose_injective i j hab)

private theorem finRange_map_finTranspose_perm {n : Nat} (i j : Fin n) :
    ((List.finRange n).map (finTranspose i j)).Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup
    (list_nodup_map_of_injective (finTranspose_injective i j) (List.nodup_finRange n))
    (List.nodup_finRange n)).mpr
  intro r
  constructor
  · intro _h
    exact List.mem_finRange r
  · intro _h
    simp only [List.mem_map]
    exact ⟨finTranspose i j r, List.mem_finRange _, by
      rw [finTranspose_involutive]⟩

private def transposePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  Vector.ofFn fun r => perm[finTranspose i j r]

private theorem rowSwap_get {R : Type u} {n m : Nat}
    (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  by_cases hrj : r = j
  · subst r
    simp [rowSwap]
  · by_cases hri : r = i
    · subst r
      simp [rowSwap, hrj]
      have hval : j.val ≠ i.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow : ((M.set i M[j]).set j M[i])[i] = (M.set i M[j])[i] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i]) j.isLt i.isLt hval
      simpa using congrArg (fun row => row[k]) hrow
    · simp [rowSwap, hrj, hri]
      have hir : i.val ≠ r.val := by
        intro hval
        exact hri (Fin.ext hval.symm)
      have hjr : j.val ≠ r.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow₁ : (M.set i M[j])[r] = M[r] := by
        exact Vector.getElem_set_ne (xs := M) (x := M[j]) i.isLt r.isLt hir
      have hrow₂ : ((M.set i M[j]).set j M[i])[r] = (M.set i M[j])[r] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i]) j.isLt r.isLt hjr
      exact (congrArg (fun row => row[k]) hrow₂).trans (congrArg (fun row => row[k]) hrow₁)

private theorem rowSwap_get_finTranspose {R : Type u} {n m : Nat}
    (M : Matrix R n m) (i j r : Fin n) (h : i ≠ j) (k : Fin m) :
    (rowSwap M i j)[r][k] = M[finTranspose i j r][k] := by
  rw [rowSwap_get]
  by_cases hrj : r = j
  · subst r
    simp [finTranspose, h.symm]
  · by_cases hri : r = i
    · subst r
      simp [finTranspose, hrj]
    · rw [if_neg hrj, if_neg hri]
      exact congrArg (fun row => M[row][k]) (finTranspose_of_ne i j r hri hrj).symm

private theorem transposePermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (transposePermutationValues perm i j)[r] = perm[finTranspose i j r] := by
  simp [transposePermutationValues]

private theorem transposePermutationValues_insertAt_last_boundary {n : Nat}
    (v : Vector (Fin (n + 1)) (n + 1)) :
    transposePermutationValues
        (insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last (n + 1)))
        (Fin.last n).castSucc (Fin.last (n + 1)) =
      insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last n).castSucc := by
  apply Vector.ext
  intro r hr
  let row : Fin (n + 2) := ⟨r, hr⟩
  let old : Fin (n + 2) := (Fin.last n).castSucc
  let last : Fin (n + 2) := Fin.last (n + 1)
  let finalPerm :=
    insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last (n + 1))
  let boundaryPerm :=
    insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last n).castSucc
  change (transposePermutationValues finalPerm old last)[row] = boundaryPerm[row]
  rw [transposePermutationValues_get]
  by_cases hrowOld : row = old
  · have hft : finTranspose old last row = last := by
      rw [hrowOld]
      exact finTranspose_left old last
    calc
      finalPerm[finTranspose old last row] = finalPerm[last] := by
        exact congrArg (fun c => finalPerm[c]) hft
      _ = Fin.last (n + 1) := by
        exact insertAt_get_self (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last (n + 1))
      _ = boundaryPerm[old] := by
        exact (insertAt_castSucc_last_get_boundary
          (Fin.last (n + 1)) (v.map Fin.castSucc)).symm
      _ = boundaryPerm[row] := by
        exact (congrArg (fun c => boundaryPerm[c]) hrowOld).symm
  · by_cases hrowLast : row = last
    · have hft : finTranspose old last row = old := by
        rw [hrowLast]
        exact finTranspose_right old last
      have hfinal :
          finalPerm[old] = (v[Fin.last n]).castSucc := by
        change
          (insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last (n + 1)))[
              (Fin.last n).castSucc] =
            (v[Fin.last n]).castSucc
        simpa using
          insertAt_last_get_castSucc (Fin.last (n + 1)) (v.map Fin.castSucc)
            (Fin.last n)
      have hboundary :
          boundaryPerm[last] = (v[Fin.last n]).castSucc := by
        change
          (insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last n).castSucc)[
              Fin.last (n + 1)] =
            (v[Fin.last n]).castSucc
        simpa using
          insertAt_castSucc_last_get_last (Fin.last (n + 1)) (v.map Fin.castSucc)
      calc
        finalPerm[finTranspose old last row] = finalPerm[old] := by
          exact congrArg (fun c => finalPerm[c]) hft
        _ = (v[Fin.last n]).castSucc := hfinal
        _ = boundaryPerm[last] := hboundary.symm
        _ = boundaryPerm[row] := by
          exact (congrArg (fun c => boundaryPerm[c]) hrowLast).symm
    · have hrowLt : row.val < n := by
        have hneOldVal : row.val ≠ n := by
          intro hval
          exact hrowOld (Fin.ext hval)
        have hneLastVal : row.val ≠ n + 1 := by
          intro hval
          exact hrowLast (Fin.ext hval)
        omega
      let i : Fin n := ⟨row.val, hrowLt⟩
      have hrow : row = i.castSucc.castSucc := Fin.ext rfl
      have hfinal :
          finalPerm[i.castSucc.castSucc] = (v[i.castSucc]).castSucc := by
        change
          (insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last (n + 1)))[
              i.castSucc.castSucc] =
            (v[i.castSucc]).castSucc
        simpa using
          insertAt_last_get_castSucc (Fin.last (n + 1)) (v.map Fin.castSucc)
            i.castSucc
      have hboundary :
          boundaryPerm[i.castSucc.castSucc] = (v[i.castSucc]).castSucc := by
        change
          (insertAt (Fin.last (n + 1)) (v.map Fin.castSucc) (Fin.last n).castSucc)[
              i.castSucc.castSucc] =
            (v[i.castSucc]).castSucc
        simpa using
          insertAt_castSucc_last_get_prefix (Fin.last (n + 1)) (v.map Fin.castSucc) i
      calc
        finalPerm[finTranspose old last row] = finalPerm[row] := by
          exact congrArg (fun c => finalPerm[c])
            (finTranspose_of_ne old last row hrowOld hrowLast)
        _ = finalPerm[i.castSucc.castSucc] := by
          exact congrArg (fun c => finalPerm[c]) hrow
        _ = (v[i.castSucc]).castSucc := hfinal
        _ = boundaryPerm[i.castSucc.castSucc] := hboundary.symm
        _ = boundaryPerm[row] := by
          exact (congrArg (fun c => boundaryPerm[c]) hrow).symm

private theorem vector_toList_eq_finRange_map_get {α : Type u} {n : Nat}
    (v : Vector α n) :
    v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp

private theorem transposePermutationValues_toList_perm {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    (transposePermutationValues perm i j).toList.Perm perm.toList := by
  rw [vector_toList_eq_finRange_map_get (transposePermutationValues perm i j)]
  rw [vector_toList_eq_finRange_map_get perm]
  have hleft :
      (List.finRange n).map (fun r => (transposePermutationValues perm i j)[r]) =
        (List.finRange n).map ((fun r => perm[r]) ∘ finTranspose i j) := by
    apply List.map_congr_left
    intro r _hr
    exact transposePermutationValues_get perm i j r
  rw [hleft]
  simpa [List.map_map] using
    (finRange_map_finTranspose_perm i j).map fun r => perm[r]

private theorem transposePermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    transposePermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact (transposePermutationValues_toList_perm perm i j).symm.nodup
    (permutationVectors_nodup hmem)

private theorem vector_get_fin_congr {α : Type u} {n : Nat} (v : Vector α n)
    {a b : Fin n} (h : a = b) : v[a] = v[b] := by
  subst b
  rfl

private theorem vector_toList_split_two {α : Type u} {n : Nat}
    (v : Vector α n) {i j : Fin n} (hij : i.val < j.val) :
    v.toList =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
  have hi : i.val < v.toList.length := by
    simp [Vector.length_toList]
  have hjdrop : j.val - i.val - 1 < (v.toList.drop (i.val + 1)).length := by
    simp only [List.length_drop, Vector.length_toList]
    omega
  calc
    v.toList = v.toList.take i.val ++ v.toList.drop i.val := by
      exact (List.take_append_drop i.val v.toList).symm
    _ = v.toList.take i.val ++ v[i] :: v.toList.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      simp [Vector.getElem_toList]
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          (v.toList.drop (i.val + 1)).drop (j.val - i.val - 1) := by
      rw [List.append_assoc]
      congr 1
      congr 1
      exact (List.take_append_drop (j.val - i.val - 1)
        (v.toList.drop (i.val + 1))).symm
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
      have hmid : i.val + 1 + (j.val - i.val - 1) = j.val := by
        omega
      have hdrop : i.val + 1 + ((j.val - i.val - 1) + 1) = j.val + 1 := by
        omega
      rw [List.drop_eq_getElem_cons hjdrop]
      simp [List.drop_drop, Vector.getElem_toList, List.getElem_drop, hmid, hdrop]

private theorem transposePermutationValues_take_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.take i.val =
      perm.toList.take i.val := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hk : k < n := by omega
    have hki : (⟨k, hk⟩ : Fin n) ≠ i := by
      intro h
      have : k = i.val := by simpa using congrArg Fin.val h
      omega
    have hkj : (⟨k, hk⟩ : Fin n) ≠ j := by
      intro h
      have : k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take i.val (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[k]'hk := by
        simp [Vector.getElem_toList]
      _ = perm[k]'hk := by
        change (transposePermutationValues perm i j)[(⟨k, hk⟩ : Fin n)] =
          perm[(⟨k, hk⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm (finTranspose_of_ne i j ⟨k, hk⟩ hki hkj)
      _ = (List.take i.val perm.toList)[k] := by
        simp [Vector.getElem_toList]

private theorem transposePermutationValues_middle_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    ((transposePermutationValues perm i j).toList.drop (i.val + 1)).take
        (j.val - i.val - 1) =
      (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : i.val + 1 + k < n := by
      omega
    have hri : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : i.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : i.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take (j.val - i.val - 1)
          (List.drop (i.val + 1) (transposePermutationValues perm i j).toList))[k] =
          (transposePermutationValues perm i j)[i.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[i.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨i.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨i.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨i.val + 1 + k, hrlt⟩ hri hrj)
      _ =
          (List.take (j.val - i.val - 1) (List.drop (i.val + 1) perm.toList))[k] := by
        simp [Vector.getElem_toList]

private theorem transposePermutationValues_drop_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.drop (j.val + 1) =
      perm.toList.drop (j.val + 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : j.val + 1 + k < n := by
      omega
    have hri : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : j.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : j.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.drop (j.val + 1) (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[j.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[j.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨j.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨j.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨j.val + 1 + k, hrlt⟩ hri hrj)
      _ = (List.drop (j.val + 1) perm.toList)[k] := by
        simp [Vector.getElem_toList]

private theorem transposePermutationValues_toList_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take i.val ++ perm[j] ::
        (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          perm[i] :: perm.toList.drop (j.val + 1) := by
  rw [vector_toList_split_two (transposePermutationValues perm i j) hij]
  rw [transposePermutationValues_take_of_lt perm hij]
  rw [transposePermutationValues_middle_of_lt perm hij]
  rw [transposePermutationValues_drop_of_lt perm hij]
  have hi : (transposePermutationValues perm i j)[i] = perm[j] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_left i j)
  have hj : (transposePermutationValues perm i j)[j] = perm[i] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_right i j)
  rw [hi, hj]

private theorem transposePermutationValues_toList_of_gt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hji : j.val < i.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take j.val ++ perm[i] ::
        (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
          perm[j] :: perm.toList.drop (i.val + 1) := by
  have hcomm : transposePermutationValues perm i j = transposePermutationValues perm j i := by
    apply Vector.ext
    intro r hr
    change (transposePermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (transposePermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [transposePermutationValues_get]
    by_cases hri : (⟨r, hr⟩ : Fin n) = i
    · subst i
      exact vector_get_fin_congr perm
        ((finTranspose_left ⟨r, hr⟩ j).trans
          (finTranspose_right j ⟨r, hr⟩).symm)
    · by_cases hrj : (⟨r, hr⟩ : Fin n) = j
      · subst j
        exact vector_get_fin_congr perm
          ((finTranspose_right i ⟨r, hr⟩).trans
            (finTranspose_left ⟨r, hr⟩ i).symm)
      · exact vector_get_fin_congr perm
          ((finTranspose_of_ne i j ⟨r, hr⟩ hri hrj).trans
            (finTranspose_of_ne j i ⟨r, hr⟩ hrj hri).symm)
  rw [hcomm]
  exact
    (transposePermutationValues_toList_of_lt perm (i := j) (j := i) hji)

private theorem transposePermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    transposePermutationValues (transposePermutationValues perm i j) i j = perm := by
  apply Vector.ext
  intro r hr
  simp [transposePermutationValues, finTranspose_involutive]

private theorem transposePermutationValues_map_permutationVectors_perm {n : Nat}
    (i j : Fin n) :
    ((permutationVectors n).map fun perm => transposePermutationValues perm i j).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map fun perm => transposePermutationValues perm i j).Nodup := by
    exact list_nodup_map_of_injective
      (f := fun perm => transposePermutationValues perm i j)
      (fun a b h => by
        have h' := congrArg (fun perm => transposePermutationValues perm i j) h
        change
          transposePermutationValues (transposePermutationValues a i j) i j =
            transposePermutationValues (transposePermutationValues b i j) i j at h'
        rw [transposePermutationValues_involutive] at h'
        rw [transposePermutationValues_involutive] at h'
        exact h')
      permutationVectors_nodup_list
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    simp only [List.mem_map] at hmem
    rcases hmem with ⟨pre, hpre, rfl⟩
    exact transposePermutationValues_mem_permutationVectors i j hpre
  · intro hmem
    simp only [List.mem_map]
    refine ⟨transposePermutationValues perm i j,
      transposePermutationValues_mem_permutationVectors i j hmem, ?_⟩
    exact transposePermutationValues_involutive perm i j

def swapPermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  perm.map (finTranspose i j)

private theorem swapPermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] = finTranspose i j perm[r] := by
  simp [swapPermutationValues]

theorem swapPermutationValues_get_if {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] =
      if perm[r] = i then j else if perm[r] = j then i else perm[r] := by
  rw [swapPermutationValues_get]
  rfl

private theorem swapPermutationValues_toList_nodup {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.Nodup := by
  change (perm.map (finTranspose i j)).toList.Nodup
  rw [vector_toList_map]
  exact list_nodup_map_of_injective (finTranspose_injective i j) hnodup

private theorem swapPermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    swapPermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact swapPermutationValues_toList_nodup perm i j (permutationVectors_nodup hmem)

private theorem swapPermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    swapPermutationValues (swapPermutationValues perm i j) i j = perm := by
  apply Vector.ext
  intro r hr
  simp [swapPermutationValues, finTranspose_involutive]

private theorem swapPermutationValues_map_permutationVectors_perm {n : Nat}
    (i j : Fin n) :
    ((permutationVectors n).map fun perm => swapPermutationValues perm i j).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map fun perm => swapPermutationValues perm i j).Nodup := by
    exact list_nodup_map_of_injective
      (f := fun perm => swapPermutationValues perm i j)
      (fun a b h => by
        have h' := congrArg (fun perm => swapPermutationValues perm i j) h
        change
          swapPermutationValues (swapPermutationValues a i j) i j =
            swapPermutationValues (swapPermutationValues b i j) i j at h'
        rw [swapPermutationValues_involutive] at h'
        rw [swapPermutationValues_involutive] at h'
        exact h')
      permutationVectors_nodup_list
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    simp only [List.mem_map] at hmem
    rcases hmem with ⟨pre, hpre, rfl⟩
    exact swapPermutationValues_mem_permutationVectors i j hpre
  · intro hmem
    simp only [List.mem_map]
    refine ⟨swapPermutationValues perm i j,
      swapPermutationValues_mem_permutationVectors i j hmem, ?_⟩
    exact swapPermutationValues_involutive perm i j

private theorem fin_mem_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    x ∈ xs := by
  by_cases hmem : x ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange n).erase x) := by
      apply List.subperm_of_subset hnodup
      intro y hy
      exact (List.mem_erase_of_ne (by
        intro hyx
        exact hmem (hyx ▸ hy))).2 (List.mem_finRange y)
    have hle : xs.length ≤ ((List.finRange n).erase x).length :=
      List.Subperm.length_le hsub
    have herase : ((List.finRange n).erase x).length = n - 1 := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    rw [hlen, herase] at hle
    cases n with
    | zero => exact Fin.elim0 x
    | succ n => omega

private theorem fin_idxOf_lt_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.idxOf x < xs.length := by
  exact List.idxOf_lt_length_of_mem (fin_mem_of_full_nodup x hlen hnodup)

/-- The inverse permutation vector: at value `c`, return the position where
`c` occurs in `perm`. -/
private def inversePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    Vector (Fin n) n :=
  Vector.ofFn fun c =>
    ⟨perm.toList.idxOf c,
      by
        simpa [Vector.length_toList] using
          fin_idxOf_lt_of_full_nodup c (by simp [Vector.length_toList]) hnodup⟩

private theorem inversePermutationValues_get_value {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (c : Fin n) :
    perm[(inversePermutationValues perm hnodup)[c]] = c := by
  change
    perm.toList[(inversePermutationValues perm hnodup)[c].val]'(by
      simp [Vector.length_toList]) = c
  simp [inversePermutationValues]

private theorem inversePermutationValues_get_index {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (i : Fin n) :
    (inversePermutationValues perm hnodup)[perm[i]] = i := by
  apply Fin.ext
  simp [inversePermutationValues]
  exact hnodup.idxOf_getElem i.val (by simp [Vector.length_toList])

private theorem inversePermutationValues_nodup {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    (inversePermutationValues perm hnodup).toList.Nodup := by
  rw [vector_toList_eq_finRange_map_get]
  apply list_nodup_map_of_injective
  · intro a b h
    have hval :
        perm[(inversePermutationValues perm hnodup)[a]] =
          perm[(inversePermutationValues perm hnodup)[b]] :=
      congrArg (fun k => perm[k]) h
    rw [inversePermutationValues_get_value perm hnodup a] at hval
    rw [inversePermutationValues_get_value perm hnodup b] at hval
    exact hval
  · exact List.nodup_finRange n

private theorem inversePermutationValues_insertAt_last_castSucc {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    inversePermutationValues
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (insertAt_last_castSucc_nodup v i hnodup) =
      insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
        (Fin.last n) := by
  apply Vector.ext
  intro k hk
  let c : Fin (n + 1) := ⟨k, hk⟩
  by_cases hlast : k = n
  · subst k
    have hleft :
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup))[Fin.last n] = i := by
      apply Fin.ext
      simp [inversePermutationValues]
      exact insertAt_last_castSucc_idxOf v i hnodup
    have hright :
        (insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
          (Fin.last n))[Fin.last n] = i := by
      exact insertAt_get_self i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
        (Fin.last n)
    exact hleft.trans hright.symm
  · have hklt : k < n := by omega
    let old : Fin n := ⟨k, hklt⟩
    have hc : c = old.castSucc := Fin.ext rfl
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)[
            raiseFinAbove i ((inversePermutationValues v hnodup)[old])] =
          old.castSucc := by
      rw [insertAt_get_raiseFinAbove]
      simpa using congrArg Fin.castSucc (inversePermutationValues_get_value v hnodup old)
    have hleft :
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup))[old.castSucc] =
          raiseFinAbove i ((inversePermutationValues v hnodup)[old]) := by
      apply Fin.ext
      have hgetList :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList[
              (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val] =
            old.castSucc := by
        simpa [Vector.getElem_toList] using hget
      have hidxOf :=
        (insertAt_last_castSucc_nodup v i hnodup).idxOf_getElem
          (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val
          (by simp [Vector.length_toList])
      have hidx :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf old.castSucc =
            (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val := by
        exact hgetList ▸ hidxOf
      have hidx' :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf
              (⟨old.val, by omega⟩ : Fin (n + 1)) =
            (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val := by
        simpa using hidx
      simpa [inversePermutationValues] using hidx'
    have hright :
        (insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
          (Fin.last n))[old.castSucc] =
          raiseFinAbove i ((inversePermutationValues v hnodup)[old]) := by
      simpa using
        insertAt_last_get_castSucc i
          ((inversePermutationValues v hnodup).map (raiseFinAbove i)) old
    simpa [c, hc] using hleft.trans hright.symm

private theorem inversionCount_inversePermutationValues_insertAt_last_castSucc {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    inversionCount
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup)).toList =
      inversionCount (inversePermutationValues v hnodup).toList + (n - i.val) := by
  rw [inversePermutationValues_insertAt_last_castSucc v i hnodup]
  rw [insertAt_last_toList]
  rw [vector_toList_map]
  rw [inversionCount_map_raiseFinAbove_append_self]
  rw [foldCount_full_nodup_ge i]
  · simp [Vector.length_toList]
  · exact inversePermutationValues_nodup v hnodup

private theorem inversionCount_inversePermutationValues_mod_two {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversionCount (inversePermutationValues perm hnodup).toList % 2 =
      inversionCount perm.toList % 2 := by
  induction n with
  | zero =>
      have hperm_nil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hinv_nil : (inversePermutationValues perm hnodup).toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      simp [hperm_nil, hinv_nil, inversionCount]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt_of_full_nodup (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        peelLastVector_nodup perm k hk hidx hnodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          insertAt_peelLastVector perm k hk hidx hnodup
      have hinv_count :
          inversionCount (inversePermutationValues perm hnodup).toList =
            inversionCount (inversePermutationValues peeled hpeeled_nodup).toList +
              (n - pos.val) := by
        have hnodup_insert :
            (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos).toList.Nodup :=
          insertAt_last_castSucc_nodup peeled pos hpeeled_nodup
        have hinv_eq :
            inversePermutationValues perm hnodup =
              inversePermutationValues
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)
                hnodup_insert := by
          apply Vector.ext
          intro c hc
          simp [inversePermutationValues, hinsert]
        rw [hinv_eq]
        simpa [peeled, pos] using
          inversionCount_inversePermutationValues_insertAt_last_castSucc
            peeled pos hpeeled_nodup
      have hperm_count :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert]
        rw [insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          inversionCount_insertIdx_castSucc_last_eq peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      rw [hinv_count, hperm_count]
      have hih := ih peeled hpeeled_nodup
      omega

private theorem detSign_inversePermutationValues {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detSign (R := R) (inversePermutationValues perm hnodup) = detSign (R := R) perm := by
  unfold detSign
  rw [inversionCount_inversePermutationValues_mod_two perm hnodup]

private theorem inversePermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationValues perm (permutationVectors_nodup hmem) ∈ permutationVectors n := by
  exact permutationVectors_complete
    (inversePermutationValues_nodup perm (permutationVectors_nodup hmem))

private theorem inversePermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationValues
        (inversePermutationValues perm hnodup)
        (inversePermutationValues_nodup perm hnodup) = perm := by
  apply Vector.ext
  intro k hk
  let i : Fin n := ⟨k, hk⟩
  have h :=
    inversePermutationValues_get_index
      (inversePermutationValues perm hnodup)
      (inversePermutationValues_nodup perm hnodup) (perm[i])
  have hi := inversePermutationValues_get_index perm hnodup i
  have hleft :
      (inversePermutationValues
        (inversePermutationValues perm hnodup)
        (inversePermutationValues_nodup perm hnodup))[i] =
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (inversePermutationValues_nodup perm hnodup))[
            (inversePermutationValues perm hnodup)[perm[i]]] :=
    congrArg
      (fun x =>
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (inversePermutationValues_nodup perm hnodup))[x])
      hi.symm
  exact hleft.trans h

private def inversePermutationVector {n : Nat}
    (perm : Vector (Fin n) n) : Vector (Fin n) n :=
  if hnodup : perm.toList.Nodup then
    inversePermutationValues perm hnodup
  else
    perm

private theorem inversePermutationVector_eq {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationVector perm = inversePermutationValues perm hnodup := by
  simp [inversePermutationVector, hnodup]

private theorem inversePermutationVector_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector perm ∈ permutationVectors n := by
  rw [inversePermutationVector_eq perm (permutationVectors_nodup hmem)]
  exact inversePermutationValues_mem_permutationVectors hmem

private theorem inversePermutationVector_involutive_of_mem {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector (inversePermutationVector perm) = perm := by
  rw [inversePermutationVector_eq perm (permutationVectors_nodup hmem)]
  rw [inversePermutationVector_eq
    (inversePermutationValues perm (permutationVectors_nodup hmem))
    (inversePermutationValues_nodup perm (permutationVectors_nodup hmem))]
  exact inversePermutationValues_involutive perm (permutationVectors_nodup hmem)

private theorem inversePermutationVector_map_permutationVectors_perm {n : Nat} :
    ((permutationVectors n).map inversePermutationVector).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map inversePermutationVector).Nodup := by
    exact list_nodup_map_on permutationVectors_nodup_list (by
      intro a ha b hb hab
      have h' := congrArg inversePermutationVector hab
      rw [inversePermutationVector_involutive_of_mem ha] at h'
      rw [inversePermutationVector_involutive_of_mem hb] at h'
      exact h')
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pre, hpre, rfl⟩
    exact inversePermutationVector_mem_permutationVectors hpre
  · intro hmem
    exact List.mem_map.mpr ⟨inversePermutationVector perm,
      inversePermutationVector_mem_permutationVectors hmem,
      inversePermutationVector_involutive_of_mem hmem⟩

private theorem permutationVectors_inverseVector_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (f : Vector (Fin n) n → R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + f (inversePermutationVector perm)) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + f (inversePermutationVector perm)) 0 =
      ((permutationVectors n).map inversePermutationVector).foldl
        (fun acc perm => acc + f perm) 0 := by
        simp [List.foldl_map]
    _ = (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
        exact foldl_det_sum_perm f inversePermutationVector_map_permutationVectors_perm 0

private theorem finRange_map_perm_get_perm {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    ((List.finRange n).map fun i => perm[i]).Perm (List.finRange n) := by
  rw [← vector_toList_eq_finRange_map_get perm]
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).mpr
  intro x
  constructor
  · intro _h
    exact List.mem_finRange x
  · intro _h
    exact fin_mem_of_full_nodup x (by simp [Vector.length_toList]) hnodup

private theorem detProduct_transpose_inversePermutationValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct M.transpose perm =
      detProduct M (inversePermutationValues perm hnodup) := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * M.transpose[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * M[perm[r]][r]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        simp [Matrix.transpose, Matrix.col]
    _ =
      ((List.finRange n).map fun r => perm[r]).foldl
        (fun acc c => acc * M[c][(inversePermutationValues perm hnodup)[c]]) 1 := by
        simp only [List.foldl_map]
        apply foldl_det_product_congr
        intro r _hmem
        exact congrArg (fun c => M[perm[r]][c])
          (inversePermutationValues_get_index perm hnodup r).symm
    _ =
      (List.finRange n).foldl
        (fun acc c => acc * M[c][(inversePermutationValues perm hnodup)[c]]) 1 := by
        exact foldl_det_product_perm
          (fun c => M[c][(inversePermutationValues perm hnodup)[c]])
          (finRange_map_perm_get_perm perm hnodup) 1

private theorem swapPermutationValues_eq_transposePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    let pi : Fin n := ⟨perm.toList.idxOf i,
      by simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
    let pj : Fin n := ⟨perm.toList.idxOf j,
      by simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
    swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
  dsimp
  apply Vector.ext
  intro r hr
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
      List.getElem_idxOf (x := i) (xs := perm.toList) hlt
    exact hget
  have hpj_get : perm[pj] = j := by
    have hlt : perm.toList.idxOf j < perm.toList.length := by
      simpa [pj, Vector.length_toList] using pj.isLt
    have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
      List.getElem_idxOf (x := j) (xs := perm.toList) hlt
    exact hget
  change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
    (transposePermutationValues perm pi pj)[(⟨r, hr⟩ : Fin n)]
  rw [swapPermutationValues_get, transposePermutationValues_get]
  by_cases hri : (⟨r, hr⟩ : Fin n) = pi
  · rw [hri]
    calc
      finTranspose i j perm[pi] = finTranspose i j i := by rw [hpi_get]
      _ = j := finTranspose_left i j
      _ = perm[pj] := hpj_get.symm
      _ = perm[finTranspose pi pj pi] := by
          exact congrArg (fun x => perm[x]) (finTranspose_left pi pj).symm
  · by_cases hrj : (⟨r, hr⟩ : Fin n) = pj
    · rw [hrj]
      calc
        finTranspose i j perm[pj] = finTranspose i j j := by rw [hpj_get]
        _ = i := finTranspose_right i j
        _ = perm[pi] := hpi_get.symm
        _ = perm[finTranspose pi pj pj] := by
            exact congrArg (fun x => perm[x]) (finTranspose_right pi pj).symm
    · have hnot_i : perm[(⟨r, hr⟩ : Fin n)] ≠ i := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pi.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf i := by rw [hv]
            _ = pi.val := rfl
        exact hri (Fin.ext hval)
      have hnot_j : perm[(⟨r, hr⟩ : Fin n)] ≠ j := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pj.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf j := by rw [hv]
            _ = pj.val := rfl
        exact hrj (Fin.ext hval)
      rw [finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hnot_i hnot_j]
      exact vector_get_fin_congr perm (finTranspose_of_ne pi pj ⟨r, hr⟩ hri hrj).symm

private theorem detSign_transposePermutationValues_involutive {R : Type u}
    [Lean.Grind.Ring R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    detSign (R := R) (transposePermutationValues (transposePermutationValues perm i j) i j) =
      detSign (R := R) perm := by
  rw [transposePermutationValues_involutive]

private theorem inversionCount_transposePermutationValues_parity {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    inversionCount (transposePermutationValues perm i j).toList % 2 =
      (inversionCount perm.toList + 1) % 2 := by
  have hval : i.val ≠ j.val := by
    intro hv
    exact h (Fin.ext hv)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hnodup_split :
          (perm.toList.take i.val ++ perm[i] ::
              (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                perm[j] :: perm.toList.drop (j.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hij]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take i.val ++ perm[j] ::
                (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                  perm[i] :: perm.toList.drop (j.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take i.val)
            ((perm.toList.drop (i.val + 1)).take (j.val - i.val - 1))
            (perm.toList.drop (j.val + 1)) perm[i] perm[j] hnodup_split
        rw [← vector_toList_split_two perm hij] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_lt perm hij]
      exact hpar
  | inr hji =>
      have hnodup_split :
          (perm.toList.take j.val ++ perm[j] ::
              (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                perm[i] :: perm.toList.drop (i.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hji]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take j.val ++ perm[i] ::
                (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                  perm[j] :: perm.toList.drop (i.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take j.val)
            ((perm.toList.drop (j.val + 1)).take (i.val - j.val - 1))
            (perm.toList.drop (i.val + 1)) perm[j] perm[i] hnodup_split
        rw [← vector_toList_split_two perm hji] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_gt perm hji]
      exact hpar

private theorem detProduct_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) (perm : Vector (Fin n) n) :
    detProduct (rowSwap M i j) perm =
      detProduct M (transposePermutationValues perm i j) := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowSwap M i j)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * M[finTranspose i j r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        exact rowSwap_get_finTranspose M i j r h perm[r]
    _ =
      ((List.finRange n).map (finTranspose i j)).foldl
        (fun acc r => acc * M[r][perm[finTranspose i j r]]) 1 := by
        simp only [List.foldl_map]
        apply foldl_det_product_congr
        intro r _hmem
        exact congrArg (fun k => M[finTranspose i j r][k])
          (vector_get_fin_congr perm (finTranspose_involutive i j r).symm)
    _ =
      (List.finRange n).foldl
        (fun acc r => acc * M[r][perm[finTranspose i j r]]) 1 := by
        exact foldl_det_product_perm
          (fun r => M[r][perm[finTranspose i j r]])
          (finRange_map_finTranspose_perm i j) 1
    _ =
      (List.finRange n).foldl
        (fun acc r => acc * M[r][(transposePermutationValues perm i j)[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        exact congrArg (fun k => M[r][k])
          (transposePermutationValues_get perm i j r).symm

private theorem detSign_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (transposePermutationValues perm i j) := by
  unfold detSign
  have hpar :=
    inversionCount_transposePermutationValues_parity perm i j hnodup h
  by_cases hp : inversionCount perm.toList % 2 = 0
  · have ht : inversionCount (transposePermutationValues perm i j).toList % 2 ≠ 0 := by
      omega
    simp [hp, ht]
    grind
  · have hpone : inversionCount perm.toList % 2 = 1 := by
      have hlt : inversionCount perm.toList % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have ht : inversionCount (transposePermutationValues perm i j).toList % 2 = 0 := by
      omega
    simp [hp, ht]

theorem detSign_swapPermutationValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (swapPermutationValues perm i j) := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
  have hpij : pi ≠ pj := by
    intro hp
    have hpi_get : perm[pi] = i := by
      have hlt : perm.toList.idxOf i < perm.toList.length := by
        simpa [pi, Vector.length_toList] using pi.isLt
      have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
        List.getElem_idxOf (x := i) (xs := perm.toList) hlt
      exact hget
    have hpj_get : perm[pj] = j := by
      have hlt : perm.toList.idxOf j < perm.toList.length := by
        simpa [pj, Vector.length_toList] using pj.isLt
      have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
        List.getElem_idxOf (x := j) (xs := perm.toList) hlt
      exact hget
    exact h (by rw [← hpi_get, ← hpj_get, hp])
  have hswap :
      swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
    simpa [pi, pj] using swapPermutationValues_eq_transposePermutationValues perm i j hnodup
  rw [hswap]
  exact detSign_transposeValues (R := R) perm pi pj hnodup hpij

private theorem swapPermutationValues_idxOf_left {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf i = perm.toList.idxOf j := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    exact List.getElem_idxOf (x := i) (xs := perm.toList) hlt
  have hswap :
      swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
    simpa [pi, pj] using swapPermutationValues_eq_transposePermutationValues perm i j hnodup
  have hpj_swap : (swapPermutationValues perm i j)[pj] = i := by
    rw [hswap, transposePermutationValues_get]
    calc
      perm[finTranspose pi pj pj] = perm[pi] := by
        exact congrArg (fun x => perm[x]) (finTranspose_right pi pj)
      _ = i := hpi_get
  have hnodupSwap := swapPermutationValues_toList_nodup perm i j hnodup
  have hpjLen : pj.val < (swapPermutationValues perm i j).toList.length := by
    simp [Vector.length_toList]
  have hidx :
      (swapPermutationValues perm i j).toList.idxOf
          ((swapPermutationValues perm i j).toList[pj.val]'hpjLen) = pj.val := by
    exact hnodupSwap.idxOf_getElem pj.val hpjLen
  have hget :
      (swapPermutationValues perm i j).toList[pj.val]'hpjLen = i := by
    exact hpj_swap
  rw [hget] at hidx
  exact hidx

private theorem swapPermutationValues_idxOf_right {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf j = perm.toList.idxOf i := by
  have hcomm : swapPermutationValues perm i j = swapPermutationValues perm j i := by
    apply Vector.ext
    intro r hr
    change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (swapPermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [swapPermutationValues_get]
    by_cases hpi : perm[(⟨r, hr⟩ : Fin n)] = i
    · rw [hpi]
      exact (finTranspose_left i j).trans (finTranspose_right j i).symm
    · by_cases hpj : perm[(⟨r, hr⟩ : Fin n)] = j
      · rw [hpj]
        exact (finTranspose_right i j).trans (finTranspose_left j i).symm
      · exact
          (finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hpi hpj).trans
            (finTranspose_of_ne j i perm[(⟨r, hr⟩ : Fin n)] hpj hpi).symm
  rw [hcomm]
  exact swapPermutationValues_idxOf_left perm j i hnodup

private theorem permutation_idxOf_ne_of_ne {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    perm.toList.idxOf i ≠ perm.toList.idxOf j := by
  intro hidx
  have hiLt : perm.toList.idxOf i < perm.toList.length :=
    fin_idxOf_lt_of_full_nodup i (by simp [Vector.length_toList]) hnodup
  have hjLt : perm.toList.idxOf j < perm.toList.length :=
    fin_idxOf_lt_of_full_nodup j (by simp [Vector.length_toList]) hnodup
  have hiGet : perm.toList[perm.toList.idxOf i]'hiLt = i :=
    List.getElem_idxOf (x := i) (xs := perm.toList) hiLt
  have hjGet : perm.toList[perm.toList.idxOf j]'hjLt = j :=
    List.getElem_idxOf (x := j) (xs := perm.toList) hjLt
  apply h
  have hfin :
      (⟨perm.toList.idxOf i, hiLt⟩ : Fin perm.toList.length) =
        ⟨perm.toList.idxOf j, hjLt⟩ := Fin.ext hidx
  have hgeteq := congrArg (fun k : Fin perm.toList.length => perm.toList[k]) hfin
  exact hiGet.symm.trans (hgeteq.trans hjGet)

private theorem detProduct_colDuplicate_swapValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) :
    detProduct M perm = detProduct M (swapPermutationValues perm src dst) := by
  unfold detProduct
  apply foldl_det_product_congr
  intro r _hmem
  by_cases hsrc : perm[r] = src
  · have hswap : (swapPermutationValues perm src dst)[r] = dst := by
      rw [swapPermutationValues_get]
      exact hsrc ▸ finTranspose_left src dst
    calc
      M[r][perm[r]] = M[r][src] := congrArg (fun c => M[r][c]) hsrc
      _ = M[r][dst] := hcol r
      _ = M[r][(swapPermutationValues perm src dst)[r]] :=
          (congrArg (fun c => M[r][c]) hswap).symm
  · by_cases hdst : perm[r] = dst
    · have hswap : (swapPermutationValues perm src dst)[r] = src := by
        rw [swapPermutationValues_get]
        exact hdst ▸ finTranspose_right src dst
      calc
        M[r][perm[r]] = M[r][dst] := congrArg (fun c => M[r][c]) hdst
        _ = M[r][src] := (hcol r).symm
        _ = M[r][(swapPermutationValues perm src dst)[r]] :=
            (congrArg (fun c => M[r][c]) hswap).symm
    · have hswap : (swapPermutationValues perm src dst)[r] = perm[r] := by
        rw [swapPermutationValues_get]
        exact finTranspose_of_ne src dst perm[r] hsrc hdst
      exact (congrArg (fun c => M[r][c]) hswap).symm

private theorem detTerm_colDuplicate_swapValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm M perm = -detTerm M (swapPermutationValues perm src dst) := by
  unfold detTerm
  rw [detProduct_colDuplicate_swapValues M src dst hcol perm]
  rw [detSign_swapPermutationValues (R := R) perm src dst hnodup h]
  grind

private def colAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  Matrix.ofFn fun r c => if c = dst then M[r][src] else M[r][c]

private theorem colAddDuplicate_get {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst r c : Fin n) :
    (colAddDuplicate M src dst)[r][c] = if c = dst then M[r][src] else M[r][c] := by
  simp [colAddDuplicate, Matrix.ofFn]

private theorem colAdd_get {R : Type u} [Mul R] [Add R] {n : Nat}
    (M : Matrix R n n) (src dst r cidx : Fin n) (c : R) :
    (colAdd M src dst c)[r][cidx] =
      if cidx = dst then M[r][cidx] + c * M[r][src] else M[r][cidx] := by
  simp [colAdd, Matrix.ofFn]

private theorem detProduct_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colAdd M src dst c) perm =
      detProduct M perm + c * detProduct (colAddDuplicate M src dst) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colAdd M src dst c)[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            M[x][perm[x]] + c * (colAddDuplicate M src dst)[x][perm[x]]
          else
            M[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colAdd_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos rfl, colAddDuplicate_get, if_pos hpivot]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          rw [if_neg hperm_ne]
    _ =
      (List.finRange n).foldl (fun acc x => acc * M[x][perm[x]]) 1 +
        c * (List.finRange n).foldl
          (fun acc x => acc * (colAddDuplicate M src dst)[x][perm[x]]) 1 := by
      exact
        foldl_det_product_single_add (R := R) (β := Fin n)
          (List.finRange n) pivot c
          (fun x => M[x][perm[x]])
          (fun x => (colAddDuplicate M src dst)[x][perm[x]])
          1 (List.mem_finRange pivot) (List.nodup_finRange n)
          (by
            intro x _hx hxp
            change (colAddDuplicate M src dst)[x][perm[x]] = M[x][perm[x]]
            rw [colAddDuplicate_get]
            have hperm_ne : perm[x] ≠ dst := by
              intro hperm
              have hxidx : perm.toList.idxOf perm[x] = x.val := by
                simpa [Vector.getElem_toList, Vector.length_toList] using
                  hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
              have hpidx : perm.toList.idxOf dst = pivot.val := rfl
              have hval : x.val = pivot.val := by
                rw [← hxidx, hperm, hpidx]
              exact hxp (Fin.ext hval)
            rw [if_neg hperm_ne])

private theorem detTerm_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colAdd M src dst c) perm =
      detTerm M perm + c * detTerm (colAddDuplicate M src dst) perm := by
  unfold detTerm
  rw [detProduct_colAdd M src dst c perm hnodup]
  grind

private theorem detTerm_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (rowSwap M i j) perm =
      -detTerm M (transposePermutationValues perm i j) := by
  unfold detTerm
  rw [detProduct_rowSwap_transposeValues M i j h perm]
  rw [detSign_transposeValues (R := R) perm i j hnodup h]
  grind

private theorem permutationVectors_transposeValues_neg_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (_h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 =
      ((permutationVectors n).map fun perm => transposePermutationValues perm i j).foldl
        (fun acc perm => acc + -detTerm M perm) 0 := by
        simp [List.foldl_map]
    _ =
      (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M perm) 0 := by
        exact foldl_det_sum_perm
          (fun perm => -detTerm M perm)
          (transposePermutationValues_map_permutationVectors_perm i j) 0
    _ =
      (permutationVectors n).foldl
        (fun acc perm => acc + (-1 : R) * detTerm M perm) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        grind
    _ =
      (-1 : R) *
        ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact foldl_det_sum_mul_left_zero (permutationVectors n) (-1 : R) (detTerm M)
    _ = -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        grind

/-- The permutation-vector enumeration contributes `1` on the identity
matrix: all non-identity terms vanish and the identity vector appears once. -/
private theorem permutationVectors_identity_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (1 : Matrix R n n) perm) 0 = 1 := by
  induction n with
  | zero =>
      simp [permutationVectors, emptyVec, detTerm, detSign, detProduct, inversionCount]
      grind
  | succ n ih =>
      simp only [permutationVectors]
      rw [foldl_det_sum_flatMap]
      simp only [List.foldl_map, foldl_detTerm_identity_insertions]
      exact ih

/-- Row swapping pairs the permutation-vector Leibniz terms with opposite sign. -/
private theorem permutationVectors_rowSwap_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_rowSwap_transposeValues M i j h perm (permutationVectors_nodup hmem)
    _ = -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact permutationVectors_transposeValues_neg_sum M i j h

/-- Scaling one matrix row scales each Leibniz term by the same scalar. -/
private theorem detTerm_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowScale M i c) perm = c * detTerm M perm := by
  unfold detTerm
  rw [detProduct_rowScale]
  grind

private def rowAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  M.set dst M[src]

private theorem rowAdd_get {R : Type u} [Mul R] [Add R] {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (c : R) (k : Fin n) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAdd]
  · simp [rowAdd, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne
          (xs := M) (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
          dst.isLt r.isLt hval)
    simpa [rowAdd] using congrArg (fun row => row[k]) hrow

private theorem rowAddDuplicate_get {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (k : Fin n) :
    (rowAddDuplicate M src dst)[r][k] =
      if r = dst then M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAddDuplicate]
  · simp [rowAddDuplicate, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow : (M.set dst M[src])[r] = M[r] := by
      exact (Vector.getElem_set_ne (xs := M) (x := M[src]) dst.isLt r.isLt hval)
    simpa [rowAddDuplicate] using congrArg (fun row => row[k]) hrow

private theorem detProduct_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowAdd M src dst c) perm =
      detProduct M perm + c * detProduct (rowAddDuplicate M src dst) perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowAdd M src dst c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r =>
          acc * if r = dst then
            M[r][perm[r]] + c * (rowAddDuplicate M src dst)[r][perm[r]]
          else
            M[r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        by_cases h : r = dst
        · subst r
          rw [rowAdd_get M src dst dst c perm[dst]]
          rw [rowAddDuplicate_get M src dst dst perm[dst]]
          simp
        · rw [rowAdd_get, rowAddDuplicate_get]
          simp [h]
    _ =
      (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 +
        c * (List.finRange n).foldl
          (fun acc r => acc * (rowAddDuplicate M src dst)[r][perm[r]]) 1 := by
        exact foldl_det_product_single_add
          (List.finRange n) dst c
          (fun r => M[r][perm[r]])
          (fun r => (rowAddDuplicate M src dst)[r][perm[r]]) 1
          (List.mem_finRange dst) (List.nodup_finRange n)
          (fun r _hmem hne => by
            change (rowAddDuplicate M src dst)[r][perm[r]] = M[r][perm[r]]
            rw [rowAddDuplicate_get]
            simp [hne])

private theorem detTerm_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowAdd M src dst c) perm =
      detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm := by
  unfold detTerm
  rw [detProduct_rowAdd]
  grind

private theorem foldl_det_sum_filter_split_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    ∀ a b : R,
      xs.foldl (fun acc x => acc + f x) (a + b) =
        (xs.filter p).foldl (fun acc x => acc + f x) a +
          (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) b := by
  induction xs with
  | nil =>
      intro a b
      rfl
  | cons x xs ih =>
      intro a b
      simp only [List.foldl_cons]
      by_cases hp : p x
      · simp [hp]
        have hstart : a + b + f x = a + f x + b := by grind
        rw [hstart]
        exact ih (a + f x) b
      · simp [hp]
        have hstart : a + b + f x = a + (b + f x) := by grind
        rw [hstart]
        exact ih a (b + f x)

private theorem foldl_det_sum_filter_split {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    xs.foldl (fun acc x => acc + f x) 0 =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
  calc
    xs.foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f x) ((0 : R) + 0) := by
        have hzero : (0 : R) + 0 = 0 := by grind
        rw [hzero]
    _ =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
      exact foldl_det_sum_filter_split_start xs p f 0 0

private theorem foldl_det_sum_map {R : Type u} [Zero R] [Add R]
    {β : Type v} {γ : Type w} (xs : List β) (map : β → γ) (f : γ → R) :
    (xs.map map).foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f (map x)) 0 := by
  simp [List.foldl_map]

private theorem rowSwap_rowAddDuplicate_eq {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (_h : src ≠ dst) :
    rowSwap (rowAddDuplicate M src dst) src dst = rowAddDuplicate M src dst := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro k hk
  change
    (rowSwap (rowAddDuplicate M src dst) src dst)[(⟨r, hr⟩ : Fin n)][(⟨k, hk⟩ : Fin n)] =
      (rowAddDuplicate M src dst)[(⟨r, hr⟩ : Fin n)][(⟨k, hk⟩ : Fin n)]
  rw [rowSwap_get]
  let fr : Fin n := ⟨r, hr⟩
  let fk : Fin n := ⟨k, hk⟩
  change
    (if fr = dst then (rowAddDuplicate M src dst)[src][fk]
      else if fr = src then (rowAddDuplicate M src dst)[dst][fk]
      else (rowAddDuplicate M src dst)[fr][fk]) =
      (rowAddDuplicate M src dst)[fr][fk]
  by_cases hrd : fr = dst
  · rw [if_pos hrd]
    rw [rowAddDuplicate_get M src dst src fk, rowAddDuplicate_get M src dst fr fk]
    simp [hrd]
  · by_cases hrs : fr = src
    · rw [if_neg hrd, if_pos hrs]
      rw [rowAddDuplicate_get M src dst dst fk, rowAddDuplicate_get M src dst fr fk]
      simp [hrs]
    · simp [hrd, hrs]

private theorem detProduct_rowAddDuplicate_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (perm : Vector (Fin n) n) :
    detProduct (rowAddDuplicate M src dst) perm =
      detProduct (rowAddDuplicate M src dst)
        (transposePermutationValues perm src dst) := by
  have hswap :=
    detProduct_rowSwap_transposeValues
      (rowAddDuplicate M src dst) src dst h perm
  rw [rowSwap_rowAddDuplicate_eq M src dst h] at hswap
  exact hswap

private theorem detTerm_rowAddDuplicate_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (rowAddDuplicate M src dst) perm =
      -detTerm (rowAddDuplicate M src dst)
        (transposePermutationValues perm src dst) := by
  unfold detTerm
  rw [detProduct_rowAddDuplicate_transposeValues M src dst h perm]
  rw [detSign_transposeValues (R := R) perm src dst hnodup h]
  grind

private theorem permutationVectors_duplicateRow_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 = 0 := by
  let p : Vector (Fin n) n → Bool := fun perm => perm[src] < perm[dst]
  let term : Vector (Fin n) n → R := detTerm (rowAddDuplicate M src dst)
  have hsplit :=
    foldl_det_sum_filter_split (R := R) (permutationVectors n) p term
  rw [hsplit]
  have hright :
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + term (transposePermutationValues perm src dst)) 0 := by
    have hperm :
        (((permutationVectors n).filter p).map
            fun perm => transposePermutationValues perm src dst).Perm
          ((permutationVectors n).filter fun perm => !p perm) := by
      have hleftNodup :
          (((permutationVectors n).filter p).map
              fun perm => transposePermutationValues perm src dst).Nodup := by
        exact list_nodup_map_of_injective
          (f := fun perm => transposePermutationValues perm src dst)
          (fun a b hab => by
            have h' := congrArg (fun perm => transposePermutationValues perm src dst) hab
            change
              transposePermutationValues (transposePermutationValues a src dst) src dst =
                transposePermutationValues (transposePermutationValues b src dst) src dst at h'
            rw [transposePermutationValues_involutive] at h'
            rw [transposePermutationValues_involutive] at h'
            exact h')
          (permutationVectors_nodup_list.filter p)
      have hrightNodup :
          ((permutationVectors n).filter fun perm => !p perm).Nodup :=
        permutationVectors_nodup_list.filter _
      apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
      intro perm
      constructor
      · intro hmem
        simp only [List.mem_map, List.mem_filter] at hmem ⊢
        rcases hmem with ⟨pre, ⟨hpreMem, hpreP⟩, rfl⟩
        constructor
        · exact transposePermutationValues_mem_permutationVectors src dst hpreMem
        · have hsrc : (transposePermutationValues pre src dst)[src] = pre[dst] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr pre (finTranspose_left src dst)
          have hdst : (transposePermutationValues pre src dst)[dst] = pre[src] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr pre (finTranspose_right src dst)
          simp [p] at hpreP ⊢
          calc
            (transposePermutationValues pre src dst)[dst] = pre[src] := hdst
            _ ≤ pre[dst] := by
              change pre[src].val ≤ pre[dst].val
              have hpreP' : pre[src].val < pre[dst].val := hpreP
              omega
            _ = (transposePermutationValues pre src dst)[src] := hsrc.symm
      · intro hmem
        simp only [List.mem_filter] at hmem
        rcases hmem with ⟨hpermMem, hpfalse⟩
        simp only [List.mem_map, List.mem_filter]
        refine ⟨transposePermutationValues perm src dst,
          ⟨transposePermutationValues_mem_permutationVectors src dst hpermMem, ?_⟩, ?_⟩
        · have hsrc : (transposePermutationValues perm src dst)[src] = perm[dst] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr perm (finTranspose_left src dst)
          have hdst : (transposePermutationValues perm src dst)[dst] = perm[src] := by
            rw [transposePermutationValues_get]
            exact vector_get_fin_congr perm (finTranspose_right src dst)
          simp [p] at hpfalse
          have hne_values : perm[src] ≠ perm[dst] := by
            intro hvals
            have hnodup := permutationVectors_nodup hpermMem
            have hsrcidx : perm.toList.idxOf perm[src] = src.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem src.val (by simp [Vector.length_toList])
            have hdstidx : perm.toList.idxOf perm[dst] = dst.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem dst.val (by simp [Vector.length_toList])
            have hvals_idx : perm.toList.idxOf perm[src] = perm.toList.idxOf perm[dst] := by
              rw [hvals]
            have hvaleq : src.val = dst.val := by
              rw [← hsrcidx, ← hdstidx]
              exact hvals_idx
            exact h (Fin.ext hvaleq)
          rw [show p (transposePermutationValues perm src dst) =
              decide ((transposePermutationValues perm src dst)[src] <
                (transposePermutationValues perm src dst)[dst]) by rfl]
          exact decide_eq_true (by
            rw [hsrc, hdst]
            change perm[dst].val < perm[src].val
            have hle : perm[dst].val ≤ perm[src].val := hpfalse
            have hneVal : perm[dst].val ≠ perm[src].val := by
              intro hval
              exact hne_values.symm (Fin.ext hval)
            omega)
        · exact transposePermutationValues_involutive perm src dst
    calc
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        (((permutationVectors n).filter p).map
            fun perm => transposePermutationValues perm src dst).foldl
          (fun acc perm => acc + term perm) 0 := by
          exact (foldl_det_sum_perm term hperm 0).symm
      _ =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (transposePermutationValues perm src dst)) 0 := by
          exact foldl_det_sum_map ((permutationVectors n).filter p)
            (fun perm => transposePermutationValues perm src dst) term
  rw [hright]
  calc
    ((permutationVectors n).filter p).foldl (fun acc perm => acc + term perm) 0 +
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (transposePermutationValues perm src dst)) 0 =
      ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + (term perm + term (transposePermutationValues perm src dst))) 0 := by
        exact (foldl_det_sum_add_zero
          ((permutationVectors n).filter p) term
          (fun perm => term (transposePermutationValues perm src dst))).symm
    _ = ((permutationVectors n).filter p).foldl (fun acc _ => acc + 0) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        simp only [term]
        rw [detTerm_rowAddDuplicate_transposeValues M src dst h perm]
        · grind
        · exact permutationVectors_nodup (List.mem_filter.mp hmem).1
    _ = 0 := by
        exact foldl_det_sum_zero ((permutationVectors n).filter p) 0

private theorem permutationVectors_duplicateCol_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 = 0 := by
  let p : Vector (Fin n) n → Bool :=
    fun perm => perm.toList.idxOf src < perm.toList.idxOf dst
  let term : Vector (Fin n) n → R := detTerm M
  have hsplit :=
    foldl_det_sum_filter_split (R := R) (permutationVectors n) p term
  rw [hsplit]
  have hright :
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
    have hperm :
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).Perm
          ((permutationVectors n).filter fun perm => !p perm) := by
      have hleftNodup :
          (((permutationVectors n).filter p).map
              fun perm => swapPermutationValues perm src dst).Nodup := by
        exact list_nodup_map_of_injective
          (f := fun perm => swapPermutationValues perm src dst)
          (fun a b hab => by
            have h' := congrArg (fun perm => swapPermutationValues perm src dst) hab
            change
              swapPermutationValues (swapPermutationValues a src dst) src dst =
                swapPermutationValues (swapPermutationValues b src dst) src dst at h'
            rw [swapPermutationValues_involutive] at h'
            rw [swapPermutationValues_involutive] at h'
            exact h')
          (permutationVectors_nodup_list.filter p)
      have hrightNodup :
          ((permutationVectors n).filter fun perm => !p perm).Nodup :=
        permutationVectors_nodup_list.filter _
      apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
      intro perm
      constructor
      · intro hmem
        simp only [List.mem_map, List.mem_filter] at hmem ⊢
        rcases hmem with ⟨pre, ⟨hpreMem, hpreP⟩, rfl⟩
        constructor
        · exact swapPermutationValues_mem_permutationVectors src dst hpreMem
        · have hpreNodup := permutationVectors_nodup hpreMem
          simp [p] at hpreP ⊢
          rw [swapPermutationValues_idxOf_left pre src dst hpreNodup]
          rw [swapPermutationValues_idxOf_right pre src dst hpreNodup]
          omega
      · intro hmem
        simp only [List.mem_filter] at hmem
        rcases hmem with ⟨hpermMem, hpfalse⟩
        simp only [List.mem_map, List.mem_filter]
        refine ⟨swapPermutationValues perm src dst,
          ⟨swapPermutationValues_mem_permutationVectors src dst hpermMem, ?_⟩, ?_⟩
        · have hpermNodup := permutationVectors_nodup hpermMem
          simp [p] at hpfalse ⊢
          rw [swapPermutationValues_idxOf_left perm src dst hpermNodup]
          rw [swapPermutationValues_idxOf_right perm src dst hpermNodup]
          have hneIdx := permutation_idxOf_ne_of_ne perm src dst hpermNodup h
          omega
        · exact swapPermutationValues_involutive perm src dst
    calc
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).foldl
          (fun acc perm => acc + term perm) 0 := by
          exact (foldl_det_sum_perm term hperm 0).symm
      _ =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
          exact foldl_det_sum_map ((permutationVectors n).filter p)
            (fun perm => swapPermutationValues perm src dst) term
  rw [hright]
  calc
    ((permutationVectors n).filter p).foldl (fun acc perm => acc + term perm) 0 +
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 =
      ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + (term perm + term (swapPermutationValues perm src dst))) 0 := by
        exact (foldl_det_sum_add_zero
          ((permutationVectors n).filter p) term
          (fun perm => term (swapPermutationValues perm src dst))).symm
    _ = ((permutationVectors n).filter p).foldl (fun acc _ => acc + 0) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        simp only [term]
        rw [detTerm_colDuplicate_swapValues M src dst h hcol perm]
        · grind
        · exact permutationVectors_nodup (List.mem_filter.mp hmem).1
    _ = 0 := by
        exact foldl_det_sum_zero ((permutationVectors n).filter p) 0

/-- The multilinear expansion of a column addition has zero total
duplicate-column contribution, so the Leibniz sum is unchanged. -/
private theorem permutationVectors_colAdd_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm M perm + c * detTerm (colAddDuplicate M src dst) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colAdd M src dst c perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + c * detTerm (colAddDuplicate M src dst) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n) (detTerm M)
          (fun perm => c * detTerm (colAddDuplicate M src dst) perm)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colAddDuplicate M src dst) perm) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        rw [permutationVectors_duplicateCol_sum (colAddDuplicate M src dst) src dst h]
        · grind
        · intro r
          rw [colAddDuplicate_get, colAddDuplicate_get]
          simp

/-- The multilinear expansion of a row addition has zero total duplicate-row
contribution, so the Leibniz sum is unchanged. -/
private theorem permutationVectors_rowAdd_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        exact detTerm_rowAdd M src dst c perm
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + c * detTerm (rowAddDuplicate M src dst) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n) (detTerm M) (fun perm => c * detTerm (rowAddDuplicate M src dst) perm)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        rw [permutationVectors_duplicateRow_sum M src dst h]
        grind

/-- The Leibniz sum for the identity matrix has exactly the identity
permutation as its nonzero contribution. -/
private theorem det_identity_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (1 : Matrix R n n) perm) 0 = 1 := by
  exact permutationVectors_identity_sum

/-- Swapping two rows pairs each Leibniz summand with the corresponding
transposed permutation and flips the computed inversion parity. -/
private theorem det_rowSwap_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  exact permutationVectors_rowSwap_sum M i j h

/-- Scaling one row factors the scalar out of every nonzero Leibniz summand. -/
private theorem det_rowScale_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm M perm) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        exact detTerm_rowScale M i c perm
    _ = c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact foldl_det_sum_mul_left_zero (permutationVectors n) c (detTerm M)

/-- Adding a multiple of one row to a distinct row leaves the Leibniz sum
unchanged; the extra multilinear contribution has two equal rows. -/
private theorem det_rowAdd_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  exact permutationVectors_rowAdd_sum M src dst c h

theorem det_one {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    det (1 : Matrix R n n) = 1 := by
  simpa [det] using (det_identity_leibniz (R := R) (n := n))

theorem det_rowSwap {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (rowSwap M i j) = -det M := by
  simpa [det] using det_rowSwap_leibniz M i j h

theorem det_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    det (rowScale M i c) = c * det M := by
  simpa [det] using det_rowScale_leibniz M i c

theorem det_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (rowAdd M src dst c) = det M := by
  simpa [det] using det_rowAdd_leibniz M src dst c h

/-- The determinant is invariant under matrix transpose. -/
theorem det_transpose {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) :
    det M.transpose = det M := by
  unfold det
  calc
    (permutationVectors n).foldl (fun acc perm => acc + detTerm M.transpose perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + detTerm M (inversePermutationVector perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        have hnodup := permutationVectors_nodup hmem
        rw [inversePermutationVector_eq perm hnodup]
        unfold detTerm
        rw [detProduct_transpose_inversePermutationValues M perm hnodup]
        rw [← detSign_inversePermutationValues (R := R) perm hnodup]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        exact permutationVectors_inverseVector_sum (R := R) (n := n) (fun perm => detTerm M perm)

/-- Adding a multiple of one column to a distinct column preserves determinant. -/
theorem det_colAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (colAdd M src dst c) = det M := by
  simpa [det] using permutationVectors_colAdd_sum M src dst c h

/-- Replace one column of a square matrix by the supplied column function. -/
def colReplace {R : Type u} {n : Nat} (M : Matrix R n n) (dst : Fin n)
    (v : Fin n → R) : Matrix R n n :=
  Matrix.ofFn fun r c => if c = dst then v r else M[r][c]

theorem colReplace_get {R : Type u} {n : Nat} (M : Matrix R n n) (dst r c : Fin n)
    (v : Fin n → R) :
    (colReplace M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  simp [colReplace, Matrix.ofFn]

private theorem detProduct_colReplace_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colReplace M dst (fun r => v r + w r)) perm =
      detProduct (colReplace M dst v) perm +
        detProduct (colReplace M dst w) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colReplace M dst (fun r => v r + w r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (colReplace M dst v)[x][perm[x]] + (colReplace M dst w)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colReplace_get, colReplace_get, colReplace_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then v x + w x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (colReplace M dst v)[x][perm[x]] + (1 : R) * (colReplace M dst w)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        by_cases hxp : x = pivot
        · rw [if_pos hxp]
          grind
        · simp [hxp]
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 +
        (1 : R) * (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst w)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_add (R := R) (β := Fin n)
            (List.finRange n) pivot (1 : R)
            (fun x => (colReplace M dst v)[x][perm[x]])
            (fun x => (colReplace M dst w)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)
            (by
              intro x _hx hxp
              have hperm_ne : perm[x] ≠ dst := by
                intro hperm
                have hxidx : perm.toList.idxOf perm[x] = x.val := by
                  simpa [Vector.getElem_toList, Vector.length_toList] using
                    hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
                have hpidx : perm.toList.idxOf dst = pivot.val := rfl
                have hval : x.val = pivot.val := by
                  rw [← hxidx, hperm, hpidx]
                exact hxp (Fin.ext hval)
              change (colReplace M dst w)[x][perm[x]] =
                (colReplace M dst v)[x][perm[x]]
              rw [colReplace_get, colReplace_get]
              change (if perm[x] = dst then w x else M[x][perm[x]]) =
                (if perm[x] = dst then v x else M[x][perm[x]])
              rw [if_neg hperm_ne, if_neg hperm_ne])
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 +
        (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst w)[x][perm[x]]) 1 := by
        grind

private theorem detProduct_colReplace_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (colReplace M dst (fun r => c * v r)) perm =
      c * detProduct (colReplace M dst v) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      fin_idxOf_lt_of_full_nodup dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (colReplace M dst (fun r => c * v r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            c * (colReplace M dst v)[x][perm[x]]
          else
            (colReplace M dst v)[x][perm[x]]) 1 := by
        apply foldl_det_product_congr
        intro x _hx
        rw [colReplace_get, colReplace_get]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then c * v x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      c * (List.finRange n).foldl
          (fun acc x => acc * (colReplace M dst v)[x][perm[x]]) 1 := by
        exact
          foldl_det_product_single_scale (R := R) (β := Fin n)
            (List.finRange n) pivot c
            (fun x => (colReplace M dst v)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)

private theorem detTerm_colReplace_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colReplace M dst (fun r => v r + w r)) perm =
      detTerm (colReplace M dst v) perm + detTerm (colReplace M dst w) perm := by
  unfold detTerm
  rw [detProduct_colReplace_add M dst v w perm hnodup]
  grind

private theorem detTerm_colReplace_smul {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (colReplace M dst (fun r => c * v r)) perm =
      c * detTerm (colReplace M dst v) perm := by
  unfold detTerm
  rw [detProduct_colReplace_smul M dst c v perm hnodup]
  grind

/-- Determinant linearity in one replaced column, additive form. -/
theorem det_colReplace_add {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (colReplace M dst (fun r => v r + w r)) =
      det (colReplace M dst v) + det (colReplace M dst w) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colReplace M dst (fun r => v r + w r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm (colReplace M dst v) perm +
            detTerm (colReplace M dst w) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colReplace_add M dst v w perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst v) perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst w) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n)
          (detTerm (colReplace M dst v))
          (detTerm (colReplace M dst w))

/-- Determinant linearity in one replaced column, scalar form. -/
theorem det_colReplace_smul {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R) :
    det (colReplace M dst (fun r => c * v r)) =
      c * det (colReplace M dst v) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (colReplace M dst (fun r => c * v r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm (colReplace M dst v) perm) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_colReplace_smul M dst c v perm (permutationVectors_nodup hmem)
    _ =
      c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (colReplace M dst v) perm) 0 := by
        exact foldl_det_sum_mul_left_zero
          (permutationVectors n) c (detTerm (colReplace M dst v))

private theorem det_colReplace_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    det (colReplace M dst (fun _ => (0 : R))) = 0 := by
  have h := det_colReplace_smul M dst (0 : R) (fun _ => (1 : R))
  have hcol : (fun r : Fin n => (0 : R) * (1 : R)) = fun _ => (0 : R) := by
    funext r
    grind
  rw [hcol] at h
  grind

private theorem det_colReplace_sum_list {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) {β : Type v} (xs : List β)
    (coeff : β → R) (source : β → Fin n → R) :
    det (colReplace M dst
        (fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0)) =
      xs.foldl
        (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
  induction xs with
  | nil =>
      exact det_colReplace_zero M dst
  | cons x xs ih =>
      simp only [List.foldl_cons]
      let tail : Fin n → R :=
        fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0
      have hcol :
          (fun r : Fin n =>
              xs.foldl (fun acc x => acc + coeff x * source x r)
                (0 + coeff x * source x r)) =
            fun r => coeff x * source x r + tail r := by
        funext r
        rw [foldl_det_sum_start]
        simp [tail]
        grind
      calc
        det (colReplace M dst
            (fun r => xs.foldl (fun acc x => acc + coeff x * source x r)
              (0 + coeff x * source x r))) =
          det (colReplace M dst (fun r => coeff x * source x r + tail r)) := by
            rw [hcol]
        _ =
          det (colReplace M dst (fun r => coeff x * source x r)) +
            det (colReplace M dst tail) := by
            exact det_colReplace_add M dst (fun r => coeff x * source x r) tail
        _ =
          coeff x * det (colReplace M dst (source x)) +
            xs.foldl (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
            rw [det_colReplace_smul]
            simp [tail]
            rw [ih]
        _ =
          xs.foldl (fun acc x => acc + coeff x * det (colReplace M dst (source x)))
            (0 + coeff x * det (colReplace M dst (source x))) := by
            have hstart :=
              (foldl_det_sum_start (R := R) xs
                (fun x => coeff x * det (colReplace M dst (source x)))
                (0 + coeff x * det (colReplace M dst (source x)))).symm
            calc
              coeff x * det (colReplace M dst (source x)) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 =
                (0 + coeff x * det (colReplace M dst (source x))) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (colReplace M dst (source x))) 0 := by
                  grind
              _ =
                xs.foldl
                  (fun acc x => acc + coeff x * det (colReplace M dst (source x)))
                  (0 + coeff x * det (colReplace M dst (source x))) := hstart

/-- Square matrix whose `j`-th column is the finite linear combination of the
columns of `source` with coefficients from row `j` of `coeff`. -/
private def columnSumMatrix {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) : Matrix R n n :=
  ofFn fun r j =>
    (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0

@[simp] private theorem columnSumMatrix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (r j : Fin n) :
    (columnSumMatrix source coeff)[r][j] =
      (List.finRange m).foldl (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrix, ofFn]

private theorem colReplace_columnSumMatrix_self
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (dst : Fin n) :
    colReplace (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
      columnSumMatrix source coeff := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (colReplace (columnSumMatrix source coeff) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0))[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [colReplace_get]
  by_cases hcol : (⟨c, hc⟩ : Fin n) = dst
  · subst dst
    rw [if_pos rfl]
    exact (columnSumMatrix_entry source coeff (⟨r, hr⟩ : Fin n) (⟨c, hc⟩ : Fin n)).symm
  · simp [hcol]

private theorem det_columnSumMatrix_expand_column
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (dst : Fin n) :
    det (columnSumMatrix source coeff) =
      (List.finRange m).foldl
        (fun acc k =>
          acc + coeff[dst][k] *
            det (colReplace (columnSumMatrix source coeff) dst (fun r => source[r][k]))) 0 := by
  have hsum :=
    det_colReplace_sum_list
    (columnSumMatrix source coeff) dst (List.finRange m)
    (fun k => coeff[dst][k]) (fun k r => source[r][k])
  have hself := colReplace_columnSumMatrix_self source coeff dst
  rw [hself] at hsum
  exact hsum

/-- Matrix obtained during the ordered column expansion: columns with
`choices c = some k` have already been specialized to source column `k`, while
unassigned columns remain the finite coefficient-weighted column sum. -/
private def columnChoiceMatrix {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) : Matrix R n n :=
  ofFn fun r c =>
    match choices c with
    | some k => source[r][k]
    | none => (List.finRange m).foldl (fun acc k => acc + coeff[c][k] * source[r][k]) 0

private def setColumnChoice {n m : Nat} (choices : Fin n → Option (Fin m))
    (dst : Fin n) (k : Fin m) : Fin n → Option (Fin m) :=
  fun c => if c = dst then some k else choices c

@[simp] private theorem columnChoiceMatrix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) (r c : Fin n) :
    (columnChoiceMatrix source coeff choices)[r][c] =
      match choices c with
      | some k => source[r][k]
      | none => (List.finRange m).foldl (fun acc k => acc + coeff[c][k] * source[r][k]) 0 := by
  simp [columnChoiceMatrix, ofFn]

private theorem columnChoiceMatrix_none
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    columnChoiceMatrix source coeff (fun _ => none) = columnSumMatrix source coeff := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (columnChoiceMatrix source coeff (fun _ => none))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnChoiceMatrix_entry, columnSumMatrix_entry]

private theorem colReplace_columnChoiceMatrix_none_self
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) (dst : Fin n)
    (hchoice : choices dst = none) :
    colReplace (columnChoiceMatrix source coeff choices) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
      columnChoiceMatrix source coeff choices := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (colReplace (columnChoiceMatrix source coeff choices) dst
        (fun r => (List.finRange m).foldl
          (fun acc k => acc + coeff[dst][k] * source[r][k]) 0))[
          (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnChoiceMatrix source coeff choices)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [colReplace_get]
  by_cases hcol : (⟨c, hc⟩ : Fin n) = dst
  · subst dst
    rw [if_pos rfl]
    rw [columnChoiceMatrix_entry]
    rw [hchoice]
  · simp [hcol]

private theorem colReplace_columnChoiceMatrix_set_some
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) (dst : Fin n)
    (k : Fin m) :
    colReplace (columnChoiceMatrix source coeff choices) dst (fun r => source[r][k]) =
      columnChoiceMatrix source coeff (setColumnChoice choices dst k) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (colReplace (columnChoiceMatrix source coeff choices) dst (fun r => source[r][k]))[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnChoiceMatrix source coeff (setColumnChoice choices dst k))[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [colReplace_get]
  by_cases hcol : (⟨c, hc⟩ : Fin n) = dst
  · subst dst
    rw [if_pos rfl]
    rw [columnChoiceMatrix_entry]
    simp [setColumnChoice]
  · rw [if_neg hcol]
    rw [columnChoiceMatrix_entry, columnChoiceMatrix_entry]
    have hset : setColumnChoice choices dst k (⟨c, hc⟩ : Fin n) = choices (⟨c, hc⟩ : Fin n) := by
      unfold setColumnChoice
      rw [if_neg hcol]
    rw [hset]

private theorem det_columnChoiceMatrix_expand_column
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (choices : Fin n → Option (Fin m)) (dst : Fin n)
    (hchoice : choices dst = none) :
    det (columnChoiceMatrix source coeff choices) =
      (List.finRange m).foldl
        (fun acc k =>
          acc + coeff[dst][k] *
            det (columnChoiceMatrix source coeff (setColumnChoice choices dst k))) 0 := by
  have hsum :=
    det_colReplace_sum_list
      (columnChoiceMatrix source coeff choices) dst (List.finRange m)
      (fun k => coeff[dst][k]) (fun k r => source[r][k])
  have hself := colReplace_columnChoiceMatrix_none_self source coeff choices dst hchoice
  rw [hself] at hsum
  have hreplace :
      (List.finRange m).foldl
          (fun acc k =>
            acc + coeff[dst][k] *
              det (colReplace (columnChoiceMatrix source coeff choices) dst
                (fun r => source[r][k]))) 0 =
        (List.finRange m).foldl
          (fun acc k =>
            acc + coeff[dst][k] *
              det (columnChoiceMatrix source coeff (setColumnChoice choices dst k))) 0 := by
    apply foldl_det_sum_congr
    intro k _hmem
    rw [colReplace_columnChoiceMatrix_set_some source coeff choices dst k]
  rw [hreplace] at hsum
  exact hsum

/-- A determinant with two equal rows is zero. -/
theorem det_eq_zero_of_row_eq {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hrow : M[src] = M[dst]) :
    det M = 0 := by
  have hdup : rowAddDuplicate M src dst = M := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (rowAddDuplicate M src dst)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      M[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [rowAddDuplicate_get]
    by_cases hdst : (⟨r, hr⟩ : Fin n) = dst
    · subst hdst
      simpa using congrArg (fun row => row[(⟨c, hc⟩ : Fin n)]) hrow
    · simp [hdst]
  have hsum := permutationVectors_duplicateRow_sum M src dst h
  rw [hdup] at hsum
  simpa [det] using hsum

/-- A determinant with two equal columns is zero. -/
theorem det_eq_zero_of_col_eq {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    det M = 0 := by
  simpa [det] using permutationVectors_duplicateCol_sum M src dst h hcol

/-- Square submatrix obtained by selecting an ordered tuple of columns. -/
def columnTupleMatrix {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) : Matrix R n n :=
  ofFn fun r c => A[r][cols c]

@[simp] theorem columnTupleMatrix_entry {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) (r c : Fin n) :
    (columnTupleMatrix A cols)[r][c] = A[r][cols c] := by
  simp [columnTupleMatrix, ofFn]

private theorem columnChoiceMatrix_some
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (cols : Fin n → Fin m) :
    columnChoiceMatrix source coeff (fun c => some (cols c)) = columnTupleMatrix source cols := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change
    (columnChoiceMatrix source coeff (fun c => some (cols c)))[(⟨r, hr⟩ : Fin n)][
        (⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix source cols)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnChoiceMatrix_entry, columnTupleMatrix_entry]

/-- Interpret an ordered column tuple vector as its column-selection function. -/
def columnTupleVectorFn {n m : Nat} (cols : Vector (Fin m) n) : Fin n → Fin m :=
  fun i => cols[i]

@[simp] theorem columnTupleVectorFn_apply {n m : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    columnTupleVectorFn cols i = cols[i] := rfl

/-- Enumerate all ordered `n`-tuples of columns from `Fin m`. -/
def columnTupleVectors : (n m : Nat) → List (Vector (Fin m) n)
  | 0, _ => [emptyVec]
  | n + 1, m =>
      (columnTupleVectors n m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last n)

private theorem columnTupleVectors_ofFn_succ
    {n m : Nat} (cols : Fin (n + 1) → Fin m) :
    Vector.ofFn cols =
      insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
        (Fin.last n) := by
  apply Vector.ext
  intro i hi
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
      simp [columnTupleVectors, emptyVec]
  | succ n ih =>
      rw [columnTupleVectors_ofFn_succ cols]
      rw [columnTupleVectors, List.mem_flatMap]
      refine ⟨Vector.ofFn fun i : Fin n => cols i.castSucc, ih (fun i => cols i.castSucc), ?_⟩
      rw [List.mem_map]
      exact ⟨cols (Fin.last n), List.mem_finRange (cols (Fin.last n)), rfl⟩

/-- Product coefficient attached to an ordered column tuple in the Gram expansion. -/
def columnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * A[i][cols[i]]) 1

/-- The determinant summand associated to an ordered column tuple. -/
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

/-! ### All-column ordered tuple expansion

Iterates `det_columnSumMatrix_expand_column` over every column to express
`det (columnSumMatrix source coeff)` as a sum over ordered column tuples.
Uses a list-based "left prefix" partial assignment, with a Fubini-style
sum-swap to align the iteration order with `columnTupleVectors`.
-/

/-- Sum-swap (Fubini) for the standard determinant-style nested folds. -/
private theorem foldl_det_sum_swap {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
      simp only [List.foldl_nil]
      exact (foldl_det_sum_zero ys 0).symm
  | cons x xs ih =>
      have hLHS :
          (x :: xs).foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
            ys.foldl (fun acc' y => acc' + f x y) 0 +
              xs.foldl
                (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
        simp only [List.foldl_cons]
        rw [foldl_det_sum_start xs
              (fun x' => ys.foldl (fun acc' y => acc' + f x' y) 0)
              (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
        grind
      have hRHS :
          ys.foldl
              (fun acc y => acc + (x :: xs).foldl
                (fun acc' x' => acc' + f x' y) 0) 0 =
            ys.foldl (fun acc' y => acc' + f x y) 0 +
              ys.foldl
                (fun acc y => acc + xs.foldl
                  (fun acc' x' => acc' + f x' y) 0) 0 := by
        have hfun :
            (fun (acc : R) y =>
                acc + (x :: xs).foldl (fun acc' x' => acc' + f x' y) 0) =
              (fun (acc : R) y =>
                acc + (f x y + xs.foldl (fun acc' x' => acc' + f x' y) 0)) := by
          funext acc y
          congr 1
          simp only [List.foldl_cons]
          rw [foldl_det_sum_start xs (fun x' => f x' y) (0 + f x y)]
          grind
        rw [hfun]
        exact foldl_det_sum_add_zero ys (fun y => f x y)
          (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
      rw [hLHS, hRHS, ih]

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

@[simp] private theorem columnSumMatrixWithPrefix_entry
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (columnSumMatrixWithPrefix source coeff chosen)[r][j] =
      if h : j.val < chosen.length then
        source[r][chosen[j.val]'h]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  simp [columnSumMatrixWithPrefix, ofFn]

private theorem columnSumMatrixWithPrefix_nil
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    columnSumMatrixWithPrefix source coeff [] = columnSumMatrix source coeff := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (columnSumMatrixWithPrefix source coeff [])[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithPrefix_entry, columnSumMatrix_entry]
  rw [dif_neg (by simp : ¬ c < ([] : List (Fin m)).length)]

private theorem columnSumMatrixWithPrefix_eq_columnTupleMatrix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hfull : chosen.length = n) :
    columnSumMatrixWithPrefix source coeff chosen =
      columnTupleMatrix source (fun j => chosen[j.val]'(by omega)) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (columnSumMatrixWithPrefix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix source (fun j => chosen[j.val]'(by omega)))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithPrefix_entry, dif_pos (by omega : c < chosen.length)]
  simp [columnTupleMatrix, ofFn]

/-- Replacing the column at index `chosen.length` of the partial-prefix matrix
with a fixed `source` column extends the prefix by that selection. -/
private theorem colReplace_columnSumMatrixWithPrefix_extend
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) (c : Fin m) :
    colReplace (columnSumMatrixWithPrefix source coeff chosen)
        (⟨chosen.length, hk⟩ : Fin n) (fun r => source[r][c]) =
      columnSumMatrixWithPrefix source coeff (chosen ++ [c]) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro k hk2
  change (colReplace (columnSumMatrixWithPrefix source coeff chosen)
      (⟨chosen.length, hk⟩ : Fin n) (fun r => source[r][c]))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)] =
    (columnSumMatrixWithPrefix source coeff (chosen ++ [c]))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)]
  rw [colReplace_get]
  simp only [columnSumMatrixWithPrefix_entry]
  have happ_len : (chosen ++ [c]).length = chosen.length + 1 := by
    simp [List.length_append]
  by_cases hkd : (⟨k, hk2⟩ : Fin n) = (⟨chosen.length, hk⟩ : Fin n)
  · have hkeq : k = chosen.length := by
      have := congrArg Fin.val hkd; simpa using this
    subst hkeq
    rw [if_pos hkd]
    rw [dif_pos (show chosen.length < (chosen ++ [c]).length by omega)]
    congr 1
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp
  · rw [if_neg hkd]
    have hkne : k ≠ chosen.length := fun h => hkd (Fin.ext h)
    by_cases hk_lt : k < chosen.length
    · rw [dif_pos hk_lt]
      rw [dif_pos (show k < (chosen ++ [c]).length by omega)]
      congr 1
      exact (List.getElem_append_left hk_lt).symm
    · rw [dif_neg hk_lt]
      rw [dif_neg (show ¬ k < (chosen ++ [c]).length by omega)]

/-- One-step expansion of the partial column-sum matrix: when not all columns
are fixed, peel off the next column as a sum over `Fin m`. -/
private theorem det_columnSumMatrixWithPrefix_expand
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    det (columnSumMatrixWithPrefix source coeff chosen) =
      (List.finRange m).foldl
        (fun acc c => acc + coeff[(⟨chosen.length, hk⟩ : Fin n)][c] *
          det (columnSumMatrixWithPrefix source coeff (chosen ++ [c]))) 0 := by
  let dst : Fin n := ⟨chosen.length, hk⟩
  have hself :
      colReplace (columnSumMatrixWithPrefix source coeff chosen) dst
          (fun r => (List.finRange m).foldl
            (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
        columnSumMatrixWithPrefix source coeff chosen := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (colReplace (columnSumMatrixWithPrefix source coeff chosen) dst _)[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrixWithPrefix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [colReplace_get, columnSumMatrixWithPrefix_entry]
    by_cases hcd : (⟨c, hc⟩ : Fin n) = dst
    · rw [if_pos hcd, hcd]
      rw [dif_neg (show ¬ dst.val < chosen.length by simp [dst])]
    · rw [if_neg hcd]
  have hsum := det_colReplace_sum_list
      (columnSumMatrixWithPrefix source coeff chosen) dst
      (List.finRange m) (fun k => coeff[dst][k]) (fun k r => source[r][k])
  rw [hself] at hsum
  rw [hsum]
  apply foldl_det_sum_congr
  intro c _hc
  congr 2
  exact colReplace_columnSumMatrixWithPrefix_extend source coeff chosen hk c

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

@[simp] private theorem columnSumMatrixWithSuffix_entry
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
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  change (columnSumMatrixWithSuffix source coeff [])[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [columnSumMatrixWithSuffix_entry, columnSumMatrix_entry]
  rw [dif_neg (show ¬ n - ([] : List (Fin m)).length ≤ c by simp; omega)]

/-- Replacing the rightmost sum column of the suffix-partial matrix with a fixed
`source` column extends the suffix by prepending that selection. -/
private theorem colReplace_columnSumMatrixWithSuffix_extend
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) (c : Fin m) :
    colReplace (columnSumMatrixWithSuffix source coeff chosen)
        (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]) =
      columnSumMatrixWithSuffix source coeff (c :: chosen) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro k hk2
  change (colReplace (columnSumMatrixWithSuffix source coeff chosen)
      (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)] =
    (columnSumMatrixWithSuffix source coeff (c :: chosen))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)]
  rw [colReplace_get]
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
      colReplace (columnSumMatrixWithSuffix source coeff chosen) dst
          (fun r => (List.finRange m).foldl
            (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
        columnSumMatrixWithSuffix source coeff chosen := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    change (colReplace (columnSumMatrixWithSuffix source coeff chosen) dst _)[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [colReplace_get, columnSumMatrixWithSuffix_entry]
    by_cases hcd : (⟨c, hc⟩ : Fin n) = dst
    · rw [if_pos hcd, hcd]
      rw [dif_neg (show ¬ n - chosen.length ≤ dst.val by simp [dst]; omega)]
    · rw [if_neg hcd]
  have hsum := det_colReplace_sum_list
      (columnSumMatrixWithSuffix source coeff chosen) dst
      (List.finRange m) (fun k => coeff[dst][k]) (fun k r => source[r][k])
  rw [hself] at hsum
  rw [hsum]
  apply foldl_det_sum_congr
  intro c _hc
  congr 2
  exact colReplace_columnSumMatrixWithSuffix_extend source coeff chosen hk c

end Matrix
end Hex
