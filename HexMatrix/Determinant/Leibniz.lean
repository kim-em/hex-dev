module

public import Std
public import Init.Grind.Ring.Field
public import Batteries.Data.Fin.Fold
public import Batteries.Data.List.Lemmas
public import Batteries.Data.Vector.Lemmas
public import HexMatrix.Determinant.Enumeration
public import HexMatrix.RowEchelon
public import HexMatrix.Submatrix

public section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- The sign of a permutation vector, computed from inversion parity. -/
@[expose]
def detSign {R : Type u} [Lean.Grind.Ring R] {n : Nat} (perm : Vector (Fin n) n) : R :=
  if inversionCount perm.toList % 2 = 0 then 1 else -1

/-- The unsigned product associated to a permutation vector. -/
@[expose]
def detProduct {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * M[i][perm[i]]) 1

/-- The Leibniz summand associated to a permutation vector. -/
@[expose]
def detTerm {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  detSign perm * detProduct M perm

/-- The determinant of a dense square matrix, defined by the Leibniz formula. -/
@[expose]
def det {R : Type u} [Lean.Grind.Ring R] {n : Nat} (M : Matrix R n n) : R :=
  (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0

/-- The determinant of the empty leading prefix is the Bareiss previous-pivot
convention `1`. -/
@[simp, grind =] theorem det_leadingPrefix_zero {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R n n) :
    det (leadingPrefix M 0 (Nat.zero_le n)) = (1 : R) := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, inversionCount]
  grind

/-- The determinant of a `1 × 1` matrix is its only entry.
This is the smallest non-empty determinant base case. -/
@[simp, grind =] theorem det_one_by_one {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R 1 1) :
    det M = M[0][0] := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, insertAt,
    inversionCount, List.finRange]
  grind

/-- The determinant of a `2 × 2` matrix has the usual diagonal-minus-off-diagonal
closed form used by small cofactor expansions. -/
@[simp, grind =] theorem det_two_by_two {R : Type u} [Lean.Grind.CommRing R]
    (M : Matrix R 2 2) :
    det M = M[0][0] * M[1][1] - M[1][0] * M[0][1] := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, insertAt,
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

/-- Two left folds agree when their step functions agree on every list
element. -/
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

/-- A summing left fold is invariant under permuting the list. -/
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

/-- A product left fold is unchanged when its factor function is replaced by one
agreeing on every list element. -/
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

/-- A product left fold is invariant under permuting the list. -/
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

/-- Mapping a duplicate-free list by an injective function preserves
duplicate-freeness. -/
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

/-- Mapping a duplicate-free list preserves duplicate-freeness when the function
is injective on that list's elements. -/
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

/-- Factor a right multiplier out of a summing left fold started from zero. -/
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

/-- A summing left fold of a sum of two functions splits into the two folds,
distributing the starting accumulator. -/
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

/-- A summing left fold of the pointwise sum `f x + g x` from `0` splits into the
sum of the separate folds of `f` and of `g`, each from `0`. -/
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

/-- A summing left fold from a starting accumulator `z` equals `z` plus the same
fold from `0`. -/
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

/-- A summing left fold over `xs.flatMap f` equals the fold over `xs` whose body
folds each sublist `f x` into the accumulator. -/
private theorem foldl_det_sum_flatMap {R : Type u} [Add R] {β γ : Type v}
    (xs : List β) (f : β → List γ) (g : γ → R) (z : R) :
    (xs.flatMap f).foldl (fun acc x => acc + g x) z =
      xs.foldl (fun acc x => (f x).foldl (fun acc y => acc + g y) acc) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      exact ih ((f x).foldl (fun acc y => acc + g y) z)

/-- A summing left fold whose body adds `0` returns the starting accumulator `z`
unchanged. -/
private theorem foldl_det_sum_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons]
      have hzero : z + (0 : R) = z := by grind
      simpa [hzero] using ih z

/-- If `a - b + c = 0` and `f x - g x + h x = 0` for every `x ∈ xs`, then the same
combination of the three summing folds from `a`, `b`, `c` is `0`. -/
private theorem foldl_det_sum_sub_add_zero
    {R : Type u} [Lean.Grind.CommRing R] {β : Type v}
    (xs : List β) (f g h : β → R) (a b c : R)
    (hacc : a - b + c = 0)
    (hall : ∀ x, x ∈ xs → f x - g x + h x = 0) :
    xs.foldl (fun acc x => acc + f x) a -
      xs.foldl (fun acc x => acc + g x) b +
      xs.foldl (fun acc x => acc + h x) c = 0 := by
  induction xs generalizing a b c with
  | nil => exact hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · have hx : f x - g x + h x = 0 := hall x List.mem_cons_self
        grind
      · intro y hy
        exact hall y (List.mem_cons_of_mem x hy)

/-- A multiplying left fold from `c * z` equals `c` times the same fold from `z`,
factoring the scalar out to the left. -/
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

/-- When `i ∉ xs`, scaling the factor at index `i` by `c` leaves the multiplying
fold unchanged, since no element of `xs` equals `i`. -/
private theorem foldl_det_product_no_scale {R : Type u}
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

/-- For a `Nodup` list `xs` containing `i`, scaling only the factor at `i` by `c`
multiplies the entire multiplying fold by `c`. -/
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
                exact foldl_det_product_no_scale xs i c f (z * (c * f i)) hnodup.1
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

/-- A multiplying left fold from a sum `a + b` of starting accumulators equals the
sum of the folds from `a` and from `b`. -/
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

/-- For a `Nodup` list containing `i` with `g` agreeing with `f` away from `i`,
replacing the factor at `i` by `f i + c * g i` splits the fold into the `f`-product
plus `c` times the `g`-product. -/
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

/-- A multiplying left fold from starting accumulator `0` is `0`. -/
private theorem foldl_det_product_zero_start {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} (xs : List β) (f : β → R) :
    xs.foldl (fun acc x => acc * f x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hzero : (0 : R) * f x = 0 := by grind
      simpa [hzero] using ih

/-- A multiplying left fold is `0` whenever some factor vanishes, that is `i ∈ xs`
and `f i = 0`. -/
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

/-- Entry `(i, j)` of the identity matrix `(1 : Matrix R n n)` is `1` when `i = j`
and `0` otherwise. -/
private theorem identity_get {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (i j : Fin n) :
    (1 : Matrix R n n)[i][j] = if i = j then 1 else 0 := by
  change Matrix.identity[i][j] = if i = j then 1 else 0
  simp [Matrix.identity, Matrix.ofFn]

/-- `detProduct` of the identity matrix along `perm` is `0` whenever `perm` moves
some index, that is `perm[i] ≠ i`. -/
private theorem detProduct_identity_zero {R : Type u}
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

/-- For `i ≤ r < xs.length`, element `r + 1` of `xs.insertIdx i x` is the original
`xs[r]`, since the insertion shifts later entries up by one. -/
private theorem list_getElem_insertIdx_succ {α : Type u}
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

/-- `detProduct` of the identity matrix along `insertAt (Fin.last n) (v.map
Fin.castSucc) i` is `0` when `i ≠ Fin.last n`, since the inserted index is then
moved. -/
private theorem detProduct_identity_insertAt_not_last_zero {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (h : i ≠ Fin.last n) :
    detProduct (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  apply detProduct_identity_zero
  exact by
    rw [insertAt_get_self]
    exact h.symm

/-- Inserting `Fin.last n` at the last position equates `detProduct` of the
`(n + 1)`-identity along the extended permutation with `detProduct` of the
`n`-identity along `v`. -/
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

/-- Folding the inversion count against a pivot is unchanged when both the list
`xs` and the pivot `x` are mapped through `Fin.castSucc`. -/
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

/-- `inversionCount` is invariant under mapping the permutation list through
`Fin.castSucc`. -/
private theorem inversionCount_map_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount (xs.map Fin.castSucc) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_castSucc]

/-- Appending `Fin.last n` after the `castSucc`-embedded list adds no inversions,
so the count equals `inversionCount xs`. -/
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

/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded list leaves
the inversion fold against `x.castSucc` unchanged, since the new last element is
never below `x.castSucc`. -/
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

/-- Every `castSucc`-embedded element is below `Fin.last n`, so folding the
`< Fin.last n` count over the embedded list adds exactly its length. -/
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

/-- Inserting `Fin.last n` at position `p ≤ xs.length` into the `castSucc`-embedded
list raises the inversion count by the `xs.length - p` elements it jumps over. -/
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

/-- Mapping a `Nodup` list through the injective `Fin.castSucc` keeps it `Nodup`. -/
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

/-- `Fin.last n` never lies in the image of a list under `Fin.castSucc`. -/
private theorem finLast_not_mem_map_castSucc {n : Nat} (xs : List (Fin n)) :
    Fin.last n ∉ xs.map Fin.castSucc := by
  intro hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨x, _hxmem, hxlast⟩
  have hval : x.val = n := by
    simpa using congrArg Fin.val hxlast
  exact Nat.ne_of_lt x.isLt hval

/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded nodup vector
keeps the resulting list `Nodup`, since `Fin.last n` is new and the embedding
stays injective. -/
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

/-- A `Nodup` list of `Fin (n + 1)` with full length `n + 1` must contain
`Fin.last n`. -/
private theorem finLast_mem {n : Nat} {xs : List (Fin (n + 1))}
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


end Matrix
end Hex
