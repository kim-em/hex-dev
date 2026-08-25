/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Defs
public meta import Batteries.Tactic.Lint.Misc

public section

/-!
The executable commutative-ring structure on fixed-precision truncated series.

Multiplication is the schoolbook truncated convolution.  `mulUpTo` shares that
definition while zeroing coefficients at and above a requested work bound, so
Newton iterations can double their useful precision geometrically.  Natural
powers use square-and-multiply rather than linear iteration.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

/-- The coefficient of degree `i` in the product of two coefficient
functions. -/
@[expose]
def convCoeff [Zero R] [Add R] [Mul R] (f g : Nat → R) (i : Nat) : R :=
  (List.range (i + 1)).foldl (fun acc j => acc + f j * g (i - j)) 0

/-- The zero truncated series. -/
@[expose] def zero [Zero R] : TSeries R n := ofFn fun _ => 0
/-- The constant-one truncated series. -/
@[expose] def one [Zero R] [One R] : TSeries R n :=
  ofFn fun i => if i = 0 then 1 else 0
/-- Coefficientwise addition of truncated series. -/
@[expose] def add [Zero R] [Add R] (a b : TSeries R n) : TSeries R n :=
  ofFn fun i => a.coeff i + b.coeff i
/-- Coefficientwise negation of a truncated series. -/
@[expose] def neg [Zero R] [Neg R] (a : TSeries R n) : TSeries R n :=
  ofFn fun i => -a.coeff i
/-- Coefficientwise subtraction of truncated series. -/
@[expose] def sub [Zero R] [Sub R] (a b : TSeries R n) : TSeries R n :=
  ofFn fun i => a.coeff i - b.coeff i
/-- Schoolbook truncated convolution. -/
@[expose] def mul [Zero R] [Add R] [Mul R]
    (a b : TSeries R n) : TSeries R n :=
  ofFn fun i => convCoeff a.coeff b.coeff i

instance [Zero R] : Zero (TSeries R n) := ⟨zero⟩
instance [Zero R] [One R] : One (TSeries R n) := ⟨one⟩
instance [Zero R] [Add R] : Add (TSeries R n) := ⟨add⟩
instance [Zero R] [Neg R] : Neg (TSeries R n) := ⟨neg⟩
instance [Zero R] [Sub R] : Sub (TSeries R n) := ⟨sub⟩
instance [Zero R] [Add R] [Mul R] : Mul (TSeries R n) := ⟨mul⟩

/-- The constant truncated series. -/
@[expose]
def C [Zero R] (c : R) : TSeries R n :=
  ofFn fun i => if i = 0 then c else 0

/-- The indeterminate `x`, which is zero at precisions zero and one. -/
@[expose]
def X [Zero R] [One R] : TSeries R n :=
  ofFn fun i => if i = 1 then 1 else 0

/-- Truncated-series exponentiation by square-and-multiply. -/
@[expose]
def pow [Zero R] [One R] [Add R] [Mul R]
    (a : TSeries R n) (k : Nat) : TSeries R n :=
  let rec go (acc base : TSeries R n) (e : Nat) : TSeries R n :=
    if he : e = 0 then
      acc
    else
      let acc' := if e % 2 = 1 then acc * base else acc
      go acc' (base * base) (e / 2)
  termination_by e
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)
  go 1 a k

attribute [nolint docBlame] pow.go

instance [Zero R] [One R] [Add R] [Mul R] : Pow (TSeries R n) Nat := ⟨pow⟩

/-- Multiply only through degree `m - 1`, zeroing the remaining stored
coefficients. -/
@[expose]
def mulUpTo [Zero R] [Add R] [Mul R] (m : Nat)
    (a b : TSeries R n) : TSeries R n :=
  ofFn fun i => if i < m then convCoeff a.coeff b.coeff i else 0

/-- Allocation-conscious implementation of `mulUpTo`.  It writes only the
requested prefix into one uniquely owned zero buffer. -/
@[expose]
def mulUpToImpl [Zero R] [Add R] [Mul R] (m : Nat)
    (a b : TSeries R n) : TSeries R n :=
  let init := (zero (R := R) (n := n)).coeffs
  let coeffs := (List.range (min m n)).foldl
    (fun out i => out.modify i fun _ => convCoeff a.coeff b.coeff i) init
  ⟨coeffs⟩

/-- Reading a represented coefficient after an in-place vector update sees
the replacement exactly at the updated index. -/
theorem coeff_modify [Zero R] (a : TSeries R n) (k i : Nat)
    (c : R) (hi : i < n) :
    (⟨a.coeffs.modify k fun _ => c⟩ : TSeries R n).coeff i =
      if k = i then c else a.coeff i := by
  unfold coeff
  rw [dif_pos hi, Vector.getElem_modify hi, dif_pos hi]

private theorem getFoldNotMem {α : Type u} {N : Nat}
    (g : Nat → α → α) {r : Nat} (hr : r < N) :
    ∀ (xs : List Nat) (v0 : Vector α N), r ∉ xs →
      (xs.foldl (fun v i => v.modify i (g i)) v0)[r]'hr = v0[r]'hr := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons x xs ih =>
      intro v0 hnm
      rw [List.foldl_cons, ih _ (fun h => hnm (List.mem_cons_of_mem _ h)),
        Vector.getElem_modify_of_ne hr (fun h => hnm (h ▸ List.mem_cons_self))]

private theorem getFoldMem {α : Type u} {N : Nat}
    (g : Nat → α → α) :
    ∀ (xs : List Nat), xs.Nodup → ∀ (v0 : Vector α N) (r : Nat) (hr : r < N), r ∈ xs →
      (xs.foldl (fun v i => v.modify i (g i)) v0)[r]'hr = g r (v0[r]'hr) := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ hr; simp at hr
  | cons x xs ih =>
      intro hnd v0 r hr hmem
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [getFoldNotMem g hr xs _ (fun h => (List.nodup_cons.mp hnd).1 h),
          Vector.getElem_modify_self hr]
      · have hxr : x ≠ r := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hmem)
        rw [ih (List.nodup_cons.mp hnd).2 _ r hr hmem,
          Vector.getElem_modify_of_ne hr hxr]

/-- Compiled bounded multiplication uses the single-buffer implementation. -/
@[csimp]
theorem mulUpTo_eq_impl : @mulUpTo = @mulUpToImpl := by
  funext R n instZero instAdd instMul m a b
  apply ext
  intro i hi
  unfold mulUpTo
  rw [coeff_ofFn _ i hi]
  unfold mulUpToImpl
  unfold coeff
  rw [dif_pos hi]
  change (if i < m then convCoeff a.coeff b.coeff i else 0) =
    ((List.range (min m n)).foldl
      (fun out j => out.modify j fun _ => convCoeff a.coeff b.coeff j)
      (zero (R := R) (n := n)).coeffs)[i]'hi
  by_cases him : i < m
  · have hmin : i < min m n := by omega
    rw [if_pos him]
    exact (getFoldMem
      (g := fun j (_ : R) => convCoeff a.coeff b.coeff j)
      (List.range (min m n)) List.nodup_range _ i hi
      (List.mem_range.mpr hmin)).symm
  · rw [if_neg him]
    have hnot : i ∉ List.range (min m n) := by
      intro hmem
      have := List.mem_range.mp hmem
      omega
    calc
      0 = (zero (R := R) (n := n)).coeffs[i]'hi := by
        have hz : (zero (R := R) (n := n)).coeff i = 0 := by
          change (ofFn (n := n) (fun _ => (0 : R))).coeff i = 0
          rw [coeff_ofFn _ i hi]
        unfold coeff at hz
        rw [dif_pos hi] at hz
        exact hz.symm
      _ = _ := (getFoldNotMem
        (g := fun j (_ : R) => convCoeff a.coeff b.coeff j)
        hi _ _ hnot).symm

/-- Every coefficient of the zero series is zero. -/
@[simp, grind =] theorem coeff_zero [Lean.Grind.CommRing R] (i : Nat) :
    (0 : TSeries R n).coeff i = 0 := by
  change (ofFn (n := n) (fun _ => (0 : R))).coeff i = 0
  by_cases hi : i < n
  · exact coeff_ofFn _ i hi
  · simp [coeff, hi]

/-- The constant and higher coefficients of the one series. -/
@[simp, grind =] theorem coeff_one [Lean.Grind.CommRing R]
    (i : Nat) (hi : i < n) :
    (1 : TSeries R n).coeff i = if i = 0 then 1 else 0 := by
  change (ofFn (n := n) (fun i => if i = 0 then (1 : R) else 0)).coeff i = _
  rw [coeff_ofFn _ i hi]

/-- Coefficient extraction commutes with addition. -/
@[simp, grind =] theorem coeff_add [Lean.Grind.CommRing R]
    (a b : TSeries R n) (i : Nat) (hi : i < n) :
    (a + b).coeff i = a.coeff i + b.coeff i := by
  change (ofFn (n := n) (fun i => a.coeff i + b.coeff i)).coeff i = _
  rw [coeff_ofFn _ i hi]

/-- Coefficient extraction commutes with a left fold of series addition. -/
theorem coeff_foldl_add [Lean.Grind.CommRing R] {α : Type}
    (xs : List α) (f : α → TSeries R n) (z : TSeries R n)
    (i : Nat) (hi : i < n) :
    (xs.foldl (fun acc k => acc + f k) z).coeff i =
      xs.foldl (fun acc k => acc + (f k).coeff i) (z.coeff i) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, coeff_add z (f x) i hi]

/-- Coefficient extraction commutes with negation. -/
@[simp, grind =] theorem coeff_neg [Lean.Grind.CommRing R]
    (a : TSeries R n) (i : Nat) (hi : i < n) :
    (-a).coeff i = -a.coeff i := by
  change (ofFn (n := n) (fun i => -a.coeff i)).coeff i = _
  rw [coeff_ofFn _ i hi]

/-- Coefficient extraction commutes with subtraction. -/
@[simp, grind =] theorem coeff_sub [Lean.Grind.CommRing R]
    (a b : TSeries R n) (i : Nat) (hi : i < n) :
    (a - b).coeff i = a.coeff i - b.coeff i := by
  change (ofFn (n := n) (fun i => a.coeff i - b.coeff i)).coeff i = _
  rw [coeff_ofFn _ i hi]

/-- Product coefficients are the truncated convolution of the operands. -/
@[grind =] theorem coeff_mul [Lean.Grind.CommRing R]
    (a b : TSeries R n) (i : Nat) (hi : i < n) :
    (a * b).coeff i = convCoeff a.coeff b.coeff i := by
  change (ofFn (n := n) (fun i => convCoeff a.coeff b.coeff i)).coeff i = _
  rw [coeff_ofFn _ i hi]

/-- The constant coefficient of a product is the product of the constants. -/
@[simp, grind =] theorem coeff_mul_zero [Lean.Grind.CommRing R]
    (a b : TSeries R n) (h : 0 < n) :
    (a * b).coeff 0 = a.coeff 0 * b.coeff 0 := by
  rw [coeff_mul a b 0 h]
  unfold convCoeff
  change 0 + a.coeff 0 * b.coeff 0 = a.coeff 0 * b.coeff 0
  grind

/-- Coefficients of a constant series. -/
@[simp, grind =] theorem coeff_C [Lean.Grind.CommRing R]
    (c : R) (i : Nat) (hi : i < n) :
    (C c : TSeries R n).coeff i = if i = 0 then c else 0 := by
  exact coeff_ofFn _ i hi

/-- Coefficients of the indeterminate. -/
@[simp, grind =] theorem coeff_X [Lean.Grind.CommRing R]
    (i : Nat) (hi : i < n) :
    (X : TSeries R n).coeff i = if i = 1 then 1 else 0 := by
  exact coeff_ofFn _ i hi

/-- The indeterminate has zero constant coefficient at every precision. -/
@[simp, grind =]
theorem X_coeff_zero [Lean.Grind.CommRing R] :
    (X : TSeries R n).coeff 0 = 0 := by
  by_cases hn : 0 < n
  · rw [coeff_X 0 hn]
    simp
  · unfold coeff
    rw [dif_neg hn]

/-- Embedding one as a constant series agrees with the series one. -/
@[simp] theorem C_one [Lean.Grind.CommRing R] :
    (C 1 : TSeries R n) = 1 := by
  apply ext
  intro i hi
  rw [coeff_C 1 i hi, coeff_one i hi]

/-- Embedding zero as a constant series agrees with the series zero. -/
@[simp] theorem C_zero [Lean.Grind.CommRing R] :
    (C 0 : TSeries R n) = 0 := by
  apply ext
  intro i hi
  rw [coeff_C 0 i hi, coeff_zero]
  split <;> rfl

/-- Constant-series embedding preserves addition. -/
@[simp] theorem C_add [Lean.Grind.CommRing R] (a b : R) :
    (C (a + b) : TSeries R n) = C a + C b := by
  apply ext
  intro i hi
  rw [coeff_C (a + b) i hi, coeff_add (C a) (C b) i hi,
    coeff_C a i hi, coeff_C b i hi]
  split <;> grind

/-- Constant-series embedding preserves multiplication. -/
@[simp] theorem C_mul [Lean.Grind.CommRing R] (a b : R) :
    (C (a * b) : TSeries R n) = C a * C b := by
  apply ext
  intro i hi
  rw [coeff_C (a * b) i hi, coeff_mul (C a) (C b) i hi]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    unfold convCoeff
    change a * b = 0 + (C a : TSeries R n).coeff 0 * (C b).coeff 0
    rw [coeff_C a 0 hi, coeff_C b 0 hi]
    grind
  · rw [if_neg hi0]
    unfold convCoeff
    apply (List.foldl_add_eq_self _ _ 0 ?_).symm
    intro j hj
    have hj' : j ≤ i := by
      have := List.mem_range.mp hj
      omega
    by_cases hj0 : j = 0
    · rw [coeff_C b (i - j) (by omega)]
      simp [hj0, hi0]
      grind
    · rw [coeff_C a j (by omega)]
      simp [hj0]
      grind

/-- Left multiplication by a constant series scales every coefficient. -/
@[simp] theorem coeff_C_mul [Lean.Grind.CommRing R]
    (c : R) (a : TSeries R n) (i : Nat) (hi : i < n) :
    (C c * a).coeff i = c * a.coeff i := by
  rw [coeff_mul (C c) a i hi]
  unfold convCoeff
  calc
    (List.range (i + 1)).foldl
        (fun acc j => acc + (C c).coeff j * a.coeff (i - j)) 0 =
      (List.range (i + 1)).foldl
        (fun acc j => acc + if j = 0 then c * a.coeff (i - j) else 0) 0 := by
          apply List.foldl_add_congr
          intro j hj
          rw [coeff_C c j (by
            have := List.mem_range.mp hj
            omega)]
          split <;> grind
    _ = 0 + c * a.coeff (i - 0) :=
      List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega)) List.nodup_range
    _ = c * a.coeff i := by grind

/-- Bounded multiplication agrees with multiplication below its work bound
and is zero above it. -/
@[simp, grind =] theorem coeff_mulUpTo [Lean.Grind.CommRing R]
    (m : Nat) (a b : TSeries R n) (i : Nat) (hi : i < n) :
    (mulUpTo m a b).coeff i = if i < m then (a * b).coeff i else 0 := by
  rw [show (mulUpTo m a b).coeff i =
      (if i < m then convCoeff a.coeff b.coeff i else 0) from coeff_ofFn _ i hi,
    coeff_mul a b i hi]

/-! The following finite reindexing lemmas keep the ring proof Mathlib-free.
They identify the two enumerations of a diagonal (for commutativity) and of a
three-dimensional diagonal (for associativity). -/

namespace ConvComm

private def left (i : Nat) : List (Nat × Nat) :=
  (List.range (i + 1)).map fun j => (j, i - j)

private def right (i : Nat) : List (Nat × Nat) :=
  (List.range (i + 1)).map fun j => (i - j, j)

private theorem left_nodup (i : Nat) : (left i).Nodup := by
  unfold left
  apply List.nodup_map_on List.nodup_range
  intro a _ b _ hab
  exact Prod.ext_iff.mp hab |>.1

private theorem right_nodup (i : Nat) : (right i).Nodup := by
  unfold right
  apply List.nodup_map_on List.nodup_range
  intro a _ b _ hab
  exact Prod.ext_iff.mp hab |>.2

private theorem mem_left (i : Nat) (ab : Nat × Nat) :
    ab ∈ left i ↔ ab.1 + ab.2 = i := by
  rcases ab with ⟨a, b⟩
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j, hj, heq⟩
    have hj' : j < i + 1 := List.mem_range.mp hj
    injection heq with ha hb
    omega
  · intro h
    apply List.mem_map.mpr
    refine ⟨a, List.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext <;> simp <;> omega

private theorem mem_right (i : Nat) (ab : Nat × Nat) :
    ab ∈ right i ↔ ab.1 + ab.2 = i := by
  rcases ab with ⟨a, b⟩
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j, hj, heq⟩
    have hj' : j < i + 1 := List.mem_range.mp hj
    injection heq with ha hb
    omega
  · intro h
    apply List.mem_map.mpr
    refine ⟨b, List.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext <;> simp <;> omega

private theorem perm (i : Nat) : (left i).Perm (right i) := by
  rw [List.perm_iff_count]
  intro ab
  rw [(left_nodup i).count, (right_nodup i).count]
  simp [mem_left, mem_right]

private theorem reindex [Lean.Grind.CommRing R] (f g : Nat → R) (i : Nat) :
    (List.range (i + 1)).foldl (fun acc j => acc + f j * g (i - j)) 0 =
      (List.range (i + 1)).foldl (fun acc j => acc + g j * f (i - j)) 0 := by
  have hp := List.foldl_add_perm
    (fun ab : Nat × Nat => f ab.1 * g ab.2) (perm i) 0
  simp only [left, right, List.foldl_map] at hp
  calc
    _ = (List.range (i + 1)).foldl
        (fun acc j => acc + f (i - j) * g j) 0 := hp
    _ = _ := by
      apply List.foldl_add_congr
      intro j _
      grind

end ConvComm

namespace ConvAssoc

private def left (i : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (i + 1)).flatMap fun j =>
    (List.range (j + 1)).map fun k => ((k, j - k), i - j)

private def right (i : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (i + 1)).flatMap fun j =>
    (List.range (i - j + 1)).map fun k => ((j, k), i - j - k)

private theorem left_nodup (i : Nat) : (left i).Nodup := by
  unfold left
  apply List.nodup_flatMap_of_disjoint List.nodup_range
  · intro j _
    apply List.nodup_map_on List.nodup_range
    intro a _ b _ hab
    injection hab with hp _
    exact Prod.ext_iff.mp hp |>.1
  · intro j hj k hk hjk z hzj hzk
    rcases List.mem_map.mp hzj with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, heq⟩
    injection heq with hp hlast
    injection hp with hfirst hsecond
    have hj' : j < i + 1 := List.mem_range.mp hj
    have hk' : k < i + 1 := List.mem_range.mp hk
    omega

private theorem right_nodup (i : Nat) : (right i).Nodup := by
  unfold right
  apply List.nodup_flatMap_of_disjoint List.nodup_range
  · intro j _
    apply List.nodup_map_on List.nodup_range
    intro a _ b _ hab
    injection hab with hp _
    exact Prod.ext_iff.mp hp |>.2
  · intro j _ k _ hjk z hzj hzk
    rcases List.mem_map.mp hzj with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, heq⟩
    injection heq with hp _
    exact hjk (Prod.ext_iff.mp hp |>.1).symm

private theorem mem_left (i : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ left i ↔ abc.1.1 + abc.1.2 + abc.2 = i := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [left]
  constructor
  · intro h; omega
  · intro h
    refine ⟨a + b, ?_, a, ?_, ?_⟩ <;> omega

private theorem mem_right (i : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ right i ↔ abc.1.1 + abc.1.2 + abc.2 = i := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [right]
  constructor
  · intro h; omega
  · intro h
    refine ⟨a, ?_, b, ?_, ?_⟩ <;> omega

private theorem perm (i : Nat) : (left i).Perm (right i) := by
  rw [List.perm_iff_count]
  intro abc
  rw [(left_nodup i).count, (right_nodup i).count]
  simp [mem_left, mem_right]

private theorem reindex [Lean.Grind.CommRing R]
    (f g h : Nat → R) (i : Nat) :
    (List.range (i + 1)).foldl
        (fun acc j => acc +
          (List.range (j + 1)).foldl
            (fun acc k => acc + (f k * g (j - k)) * h (i - j)) 0) 0 =
      (List.range (i + 1)).foldl
        (fun acc j => acc +
          (List.range (i - j + 1)).foldl
            (fun acc k => acc + f j * (g k * h (i - j - k))) 0) 0 := by
  have hp := List.foldl_add_perm
    (fun abc : (Nat × Nat) × Nat => (f abc.1.1 * g abc.1.2) * h abc.2)
    (perm i) 0
  simp only [left, right] at hp
  rw [List.foldl_add_flatMap, List.foldl_add_flatMap] at hp
  simp only [List.foldl_map] at hp
  have hleft :
      (fun (acc : R) j =>
        (List.range (j + 1)).foldl
          (fun acc k => acc + (f k * g (j - k)) * h (i - j)) acc) =
        (fun acc j => acc +
          (List.range (j + 1)).foldl
            (fun acc k => acc + (f k * g (j - k)) * h (i - j)) 0) := by
    funext acc j
    exact List.foldl_add_eq_add_foldl _ _ _
  have hright :
      (fun (acc : R) j =>
        (List.range (i - j + 1)).foldl
          (fun acc k => acc + (f j * g k) * h (i - j - k)) acc) =
        (fun acc j => acc +
          (List.range (i - j + 1)).foldl
            (fun acc k => acc + (f j * g k) * h (i - j - k)) 0) := by
    funext acc j
    exact List.foldl_add_eq_add_foldl _ _ _
  rw [hleft, hright] at hp
  calc
    _ = (List.range (i + 1)).foldl
        (fun acc j => acc +
          (List.range (i - j + 1)).foldl
            (fun acc k => acc + (f j * g k) * h (i - j - k)) 0) 0 := hp
    _ = _ := by
      apply List.foldl_add_congr
      intro j _
      apply List.foldl_add_congr
      intro k _
      grind

end ConvAssoc

private theorem convCoeff_comm [Lean.Grind.CommRing R]
    (f g : Nat → R) (i : Nat) : convCoeff f g i = convCoeff g f i := by
  exact ConvComm.reindex f g i

private theorem convCoeff_assoc [Lean.Grind.CommRing R]
    (f g h : Nat → R) (i : Nat) :
    convCoeff (convCoeff f g) h i = convCoeff f (convCoeff g h) i := by
  unfold convCoeff
  calc
    (List.range (i + 1)).foldl
        (fun acc j => acc +
          (List.range (j + 1)).foldl (fun acc k => acc + f k * g (j - k)) 0 *
            h (i - j)) 0 =
      (List.range (i + 1)).foldl
        (fun acc j => acc +
          (List.range (j + 1)).foldl
            (fun acc k => acc + (f k * g (j - k)) * h (i - j)) 0) 0 := by
          apply List.foldl_add_congr
          intro j _
          exact (List.foldl_add_mul_right_zero (R := R) (List.range (j + 1))
            (fun k => f k * g (j - k)) (h (i - j))).symm
    _ = (List.range (i + 1)).foldl
        (fun acc j => acc +
          (List.range (i - j + 1)).foldl
            (fun acc k => acc + f j * (g k * h (i - j - k))) 0) 0 :=
          ConvAssoc.reindex f g h i
    _ = (List.range (i + 1)).foldl
        (fun acc j => acc + f j *
          (List.range (i - j + 1)).foldl
            (fun acc k => acc + g k * h (i - j - k)) 0) 0 := by
          apply List.foldl_add_congr
          intro j _
          exact List.foldl_add_mul_left_zero (R := R) (List.range (i - j + 1))
            (f j) (fun k => g k * h (i - j - k))

private theorem convCoeff_congr [Lean.Grind.CommRing R]
    (f f' g g' : Nat → R) (i : Nat)
    (hf : ∀ j, j ≤ i → f j = f' j)
    (hg : ∀ j, j ≤ i → g j = g' j) :
    convCoeff f g i = convCoeff f' g' i := by
  unfold convCoeff
  apply List.foldl_add_congr
  intro j hj
  have hj' : j ≤ i := by
    have := List.mem_range.mp hj
    omega
  rw [hf j hj', hg (i - j) (by omega)]

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- Natural casts are constant series. -/
instance instNatCast [Lean.Grind.CommRing R] : NatCast (TSeries R n) :=
  ⟨fun k =>
    match k with
    | 0 => 0
    | 1 => 1
    | k + 2 => C (Nat.cast (k + 2))⟩

/-- Natural numerals are constant series. -/
instance instOfNat [Lean.Grind.CommRing R] (k : Nat) : OfNat (TSeries R n) k :=
  ⟨match k with
   | 0 => 0
   | 1 => 1
   | k + 2 => C (OfNat.ofNat (k + 2))⟩

/-- Natural scalar multiplication is multiplication by a constant series. -/
instance instNSMul [Lean.Grind.CommRing R] : SMul Nat (TSeries R n) :=
  ⟨fun k a => (Nat.cast k : TSeries R n) * a⟩

/-- Integer casts are constant series. -/
instance instIntCast [Lean.Grind.CommRing R] : IntCast (TSeries R n) :=
  ⟨fun i =>
    match i with
    | .ofNat k => (Nat.cast k : TSeries R n)
    | .negSucc k => -(Nat.cast (k + 1) : TSeries R n)⟩

/-- Integer scalar multiplication uses the standard signed natural action. -/
instance instZSMul [Lean.Grind.CommRing R] : SMul Int (TSeries R n) :=
  ⟨fun i a =>
    match i with
    | .ofNat k => k • a
    | .negSucc k => -((k + 1) • a)⟩

/-- Zero is a right identity for truncated-series addition. -/
theorem add_zero [Lean.Grind.CommRing R] (a : TSeries R n) : a + 0 = a := by
  apply ext
  intro i hi
  rw [coeff_add a 0 i hi, coeff_zero]
  grind

/-- Truncated-series addition is commutative. -/
theorem add_comm [Lean.Grind.CommRing R] (a b : TSeries R n) : a + b = b + a := by
  apply ext
  intro i hi
  rw [coeff_add a b i hi, coeff_add b a i hi]
  grind

/-- Truncated-series addition is associative. -/
theorem add_assoc [Lean.Grind.CommRing R] (a b c : TSeries R n) :
    a + b + c = a + (b + c) := by
  apply ext
  intro i hi
  rw [coeff_add (a + b) c i hi, coeff_add a b i hi,
    coeff_add a (b + c) i hi, coeff_add b c i hi]
  grind
/-- Truncated-series multiplication is associative. -/
theorem mul_assoc [Lean.Grind.CommRing R] (a b c : TSeries R n) :
    a * b * c = a * (b * c) := by
  apply ext
  intro i hi
  rw [coeff_mul (a * b) c i hi, coeff_mul a (b * c) i hi]
  calc
    convCoeff (a * b).coeff c.coeff i =
        convCoeff (convCoeff a.coeff b.coeff) c.coeff i := by
      apply convCoeff_congr
      · intro j hj
        exact coeff_mul a b j (by omega)
      · intro _ _; rfl
    _ = convCoeff a.coeff (convCoeff b.coeff c.coeff) i :=
      convCoeff_assoc a.coeff b.coeff c.coeff i
    _ = convCoeff a.coeff (b * c).coeff i := by
      apply convCoeff_congr
      · intro _ _; rfl
      · intro j hj
        exact (coeff_mul b c j (by omega)).symm

/-- One is a right identity for truncated-series multiplication. -/
theorem mul_one [Lean.Grind.CommRing R] (a : TSeries R n) : a * 1 = a := by
  apply ext
  intro i hi
  rw [coeff_mul a 1 i hi]
  unfold convCoeff
  calc
    (List.range (i + 1)).foldl
        (fun acc j => acc + a.coeff j * (1 : TSeries R n).coeff (i - j)) 0 =
      (List.range (i + 1)).foldl
        (fun acc j => acc + if j = i then a.coeff j else 0) 0 := by
          apply List.foldl_add_congr
          intro j hj
          have hj' : j ≤ i := by
            have := List.mem_range.mp hj
            omega
          rw [coeff_one (i - j) (by omega)]
          by_cases hji : j = i
          · simp [hji]
            grind
          · have : i - j ≠ 0 := by omega
            simp [hji, this]
            grind
    _ = 0 + a.coeff i :=
      List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega)) List.nodup_range
    _ = a.coeff i := by grind

/-- One is a left identity for truncated-series multiplication. -/
theorem one_mul [Lean.Grind.CommRing R] (a : TSeries R n) : 1 * a = a := by
  apply ext
  intro i hi
  rw [coeff_mul 1 a i hi]
  unfold convCoeff
  calc
    (List.range (i + 1)).foldl
        (fun acc j => acc + (1 : TSeries R n).coeff j * a.coeff (i - j)) 0 =
      (List.range (i + 1)).foldl
        (fun acc j => acc + if j = 0 then a.coeff (i - j) else 0) 0 := by
          apply List.foldl_add_congr
          intro j hj
          rw [coeff_one j (by
            have := List.mem_range.mp hj
            omega)]
          by_cases hj0 : j = 0 <;> simp [hj0] <;> grind
    _ = 0 + a.coeff (i - 0) :=
      List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega)) List.nodup_range
    _ = a.coeff i := by grind

/-- Multiplication distributes over addition on the left. -/
theorem left_distrib [Lean.Grind.CommRing R] (a b c : TSeries R n) :
    a * (b + c) = a * b + a * c := by
  apply ext
  intro i hi
  rw [coeff_mul a (b + c) i hi, coeff_add (a * b) (a * c) i hi,
    coeff_mul a b i hi, coeff_mul a c i hi]
  unfold convCoeff
  rw [← List.foldl_add_add]
  apply List.foldl_add_congr
  intro j hj
  rw [coeff_add b c (i - j) (by
    have := List.mem_range.mp hj
    omega)]
  grind

/-- Multiplication distributes over addition on the right. -/
theorem right_distrib [Lean.Grind.CommRing R] (a b c : TSeries R n) :
    (a + b) * c = a * c + b * c := by
  apply ext
  intro i hi
  rw [coeff_mul (a + b) c i hi, coeff_add (a * c) (b * c) i hi,
    coeff_mul a c i hi, coeff_mul b c i hi]
  unfold convCoeff
  rw [← List.foldl_add_add]
  apply List.foldl_add_congr
  intro j hj
  rw [coeff_add a b j (by
    have := List.mem_range.mp hj
    omega)]
  grind
/-- Zero annihilates truncated-series multiplication on the left. -/
theorem zero_mul [Lean.Grind.CommRing R] (a : TSeries R n) : 0 * a = 0 := by
  apply ext
  intro i hi
  rw [coeff_mul 0 a i hi, coeff_zero]
  unfold convCoeff
  apply List.foldl_add_eq_self
  intro j _hj
  rw [coeff_zero]
  grind

/-- Zero annihilates truncated-series multiplication on the right. -/
theorem mul_zero [Lean.Grind.CommRing R] (a : TSeries R n) : a * 0 = 0 := by
  apply ext
  intro i hi
  rw [coeff_mul a 0 i hi, coeff_zero]
  unfold convCoeff
  apply List.foldl_add_eq_self
  intro j _hj
  rw [coeff_zero]
  grind

private theorem mul_comm_raw [Lean.Grind.CommRing R]
    (a b : TSeries R n) : a * b = b * a := by
  apply ext
  intro i hi
  rw [coeff_mul a b i hi, coeff_mul b a i hi]
  exact convCoeff_comm a.coeff b.coeff i

private def linearPow [Lean.Grind.CommRing R] (a : TSeries R n) : Nat → TSeries R n
  | 0 => 1
  | k + 1 => linearPow a k * a

private theorem linearPow_add [Lean.Grind.CommRing R]
    (a : TSeries R n) (j k : Nat) :
    linearPow a (j + k) = linearPow a j * linearPow a k := by
  induction k with
  | zero => simp [linearPow, mul_one]
  | succ k ih =>
      rw [Nat.add_succ, linearPow, ih, linearPow]
      exact mul_assoc _ _ _

private theorem linearPow_double [Lean.Grind.CommRing R]
    (a : TSeries R n) (k : Nat) :
    linearPow a (2 * k) = linearPow (a * a) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have htwo : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [htwo]
      change linearPow a ((2 * k + 1) + 1) = linearPow (a * a) k * (a * a)
      rw [linearPow, linearPow, ih]
      exact mul_assoc _ _ _

private theorem linearPow_odd [Lean.Grind.CommRing R]
    (a : TSeries R n) (k : Nat) :
    linearPow a (2 * k + 1) = a * linearPow (a * a) k := by
  rw [linearPow, linearPow_double, mul_comm_raw]

private theorem powGo_eq [Lean.Grind.CommRing R]
    (acc base : TSeries R n) (k : Nat) :
    pow.go acc base k = acc * linearPow base k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | ind k ih =>
      rw [pow.go.eq_def]
      by_cases hk : k = 0
      · simp [hk, linearPow, mul_one]
      · rw [dif_neg hk]
        have hlt : k / 2 < k :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
        cases Nat.mod_two_eq_zero_or_one k with
        | inl hmod0 =>
            have hk_eq : k = 2 * (k / 2) := by
              have h := Nat.mod_add_div k 2
              omega
            have hnot : ¬ k % 2 = 1 := by omega
            have hdiv : 2 * (k / 2) / 2 = k / 2 :=
              Nat.mul_div_right (k / 2) (by decide)
            rw [if_neg hnot]
            calc
              pow.go acc (base * base) (k / 2) =
                  acc * linearPow (base * base) (k / 2) := ih _ hlt _ _
              _ = acc * linearPow base k := by rw [hk_eq, hdiv, linearPow_double]
        | inr hmod1 =>
            have hk_eq : k = 2 * (k / 2) + 1 := by
              have h := Nat.mod_add_div k 2
              omega
            rw [if_pos hmod1]
            calc
              pow.go (acc * base) (base * base) (k / 2) =
                  (acc * base) * linearPow (base * base) (k / 2) := ih _ hlt _ _
              _ = acc * (base * linearPow (base * base) (k / 2)) := mul_assoc _ _ _
              _ = acc * linearPow base (2 * (k / 2) + 1) := by rw [linearPow_odd]
              _ = acc * linearPow base k := by rw [← hk_eq]

private theorem pow_eq_linearPow [Lean.Grind.CommRing R]
    (a : TSeries R n) (k : Nat) : pow a k = linearPow a k := by
  unfold pow
  rw [powGo_eq, one_mul]

/-- The zeroth power of a truncated series is one. -/
theorem pow_zero [Lean.Grind.CommRing R] (a : TSeries R n) : a ^ 0 = 1 := by
  rw [show a ^ 0 = pow a 0 from rfl, pow_eq_linearPow]
  rfl

/-- Successor powers multiply the preceding power by the base. -/
theorem pow_succ [Lean.Grind.CommRing R] (a : TSeries R n) (k : Nat) :
    a ^ (k + 1) = a ^ k * a := by
  change pow a (k + 1) = pow a k * a
  rw [pow_eq_linearPow, pow_eq_linearPow]
  rfl

/-- Direct-definition form of `pow_zero`, for bridges that also install a
second lawful power operation. -/
theorem pow_zero' [Lean.Grind.CommRing R] (a : TSeries R n) : pow a 0 = 1 := by
  exact pow_zero a

/-- Direct-definition form of `pow_succ`, for bridges that also install a
second lawful power operation. -/
theorem pow_succ' [Lean.Grind.CommRing R] (a : TSeries R n) (k : Nat) :
    pow a (k + 1) = pow a k * a := by
  exact pow_succ a k

/-- The first power of a truncated series is the series itself. -/
@[simp]
theorem pow_one [Lean.Grind.CommRing R] (a : TSeries R n) : a ^ 1 = a := by
  rw [show 1 = 0 + 1 by decide, pow_succ, pow_zero]
  exact one_mul a

/-- Powers at a sum of exponents split as a product. -/
theorem pow_add [Lean.Grind.CommRing R] (a : TSeries R n) (j k : Nat) :
    a ^ (j + k) = a ^ j * a ^ k := by
  change pow a (j + k) = pow a j * pow a k
  rw [pow_eq_linearPow, pow_eq_linearPow, pow_eq_linearPow]
  exact linearPow_add a j k

/-- Iterated powers multiply their exponents. -/
theorem pow_mul [Lean.Grind.CommRing R] (a : TSeries R n) (j k : Nat) :
    (a ^ j) ^ k = a ^ (j * k) := by
  induction k with
  | zero => rw [pow_zero, Nat.mul_zero, pow_zero]
  | succ k ih =>
      rw [pow_succ, ih, Nat.mul_succ, pow_add]
/-- Successor numerals in truncated series agree with addition by one. -/
theorem ofNat_succ [Lean.Grind.CommRing R] (k : Nat) :
    (OfNat.ofNat (α := TSeries R n) (k + 1)) =
      OfNat.ofNat (α := TSeries R n) k + 1 := by
  apply ext
  intro i hi
  rw [coeff_add _ _ i hi, coeff_one i hi]
  cases k with
  | zero =>
      change (1 : TSeries R n).coeff i = (0 : TSeries R n).coeff i + _
      rw [coeff_one i hi, coeff_zero]
      split <;> grind
  | succ k =>
      cases k with
      | zero =>
          change (C (OfNat.ofNat 2) : TSeries R n).coeff i =
            (1 : TSeries R n).coeff i + _
          rw [coeff_C _ i hi, coeff_one i hi]
          split <;> grind
      | succ k =>
          change (C (OfNat.ofNat (k + 3)) : TSeries R n).coeff i =
            (C (OfNat.ofNat (k + 2)) : TSeries R n).coeff i + _
          rw [coeff_C _ i hi, coeff_C _ i hi]
          split
          · simpa only [show k + 2 + 1 = k + 3 by omega] using
              (Lean.Grind.Semiring.ofNat_succ (α := R) (k + 2))
          · grind
/-- Natural numerals agree with the natural-cast operation. -/
theorem ofNat_eq_natCast [Lean.Grind.CommRing R] (k : Nat) :
    (OfNat.ofNat (α := TSeries R n) k) = (Nat.cast k : TSeries R n) := by
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
          change (C (OfNat.ofNat (k + 2)) : TSeries R n) = C (Nat.cast (k + 2))
          apply ext
          intro i hi
          rw [coeff_C _ i hi, coeff_C _ i hi]
          split
          · exact Lean.Grind.Semiring.ofNat_eq_natCast (α := R) (k + 2)
          · rfl
/-- Natural scalar multiplication is multiplication by the corresponding
constant series. -/
theorem nsmul_eq_natCast_mul [Lean.Grind.CommRing R] (k : Nat) (a : TSeries R n) :
    k • a = (Nat.cast k : TSeries R n) * a := rfl
/-- Additive negation cancels a truncated series. -/
theorem neg_add_cancel [Lean.Grind.CommRing R] (a : TSeries R n) : -a + a = 0 := by
  apply ext
  intro i hi
  rw [coeff_add (-a) a i hi, coeff_neg a i hi, coeff_zero]
  grind

/-- Subtraction agrees with addition of the negation. -/
theorem sub_eq_add_neg [Lean.Grind.CommRing R] (a b : TSeries R n) :
    a - b = a + -b := by
  apply ext
  intro i hi
  rw [coeff_sub a b i hi, coeff_add a (-b) i hi, coeff_neg b i hi]
  grind
/-- Negating an integer scalar negates its scalar action. -/
theorem neg_zsmul [Lean.Grind.CommRing R] (i : Int) (a : TSeries R n) :
    (-i) • a = -(i • a) := by
  have neg_zero : -(0 : TSeries R n) = 0 := by
    apply ext
    intro j hj
    rw [coeff_neg 0 j hj, coeff_zero]
    grind
  have neg_neg (x : TSeries R n) : -(-x) = x := by
    apply ext
    intro j hj
    rw [coeff_neg (-x) j hj, coeff_neg x j hj]
    grind
  cases i with
  | ofNat k =>
      cases k with
      | zero =>
          change (0 : TSeries R n) * a = -((0 : TSeries R n) * a)
          rw [zero_mul, neg_zero]
      | succ k => rfl
  | negSucc k => exact (neg_neg ((k + 1) • a)).symm
/-- Integer casts commute with negation. -/
theorem intCast_neg [Lean.Grind.CommRing R] (i : Int) :
    ((-i : Int) : TSeries R n) = -((i : Int) : TSeries R n) := by
  have neg_zero : -(0 : TSeries R n) = 0 := by
    apply ext
    intro j hj
    rw [coeff_neg 0 j hj, coeff_zero]
    grind
  have neg_neg (x : TSeries R n) : -(-x) = x := by
    apply ext
    intro j hj
    rw [coeff_neg (-x) j hj, coeff_neg x j hj]
    grind
  cases i with
  | ofNat k =>
      cases k with
      | zero =>
          change (0 : TSeries R n) = -(0 : TSeries R n)
          exact neg_zero.symm
      | succ k => rfl
  | negSucc k => exact (neg_neg (Nat.cast (k + 1) : TSeries R n)).symm
/-- Truncated-series multiplication is commutative. -/
theorem mul_comm [Lean.Grind.CommRing R] (a b : TSeries R n) : a * b = b * a := by
  exact mul_comm_raw a b

/-- Multiplication by `X` shifts coefficients upward by one. -/
@[simp] theorem coeff_mul_X [Lean.Grind.CommRing R]
    (a : TSeries R n) (i : Nat) (hi : i < n) :
    (a * X).coeff i = if i = 0 then 0 else a.coeff (i - 1) := by
  rw [mul_comm a X, coeff_mul X a i hi]
  unfold convCoeff
  by_cases hi0 : i = 0
  · subst i
    change 0 + (X : TSeries R n).coeff 0 * a.coeff 0 = _
    rw [coeff_X 0 hi]
    rw [if_neg (by decide), if_pos rfl]
    grind
  · rw [if_neg hi0]
    calc
      (List.range (i + 1)).foldl
          (fun acc j => acc + (X : TSeries R n).coeff j * a.coeff (i - j)) 0 =
        (List.range (i + 1)).foldl
          (fun acc j => acc + if j = 1 then a.coeff (i - j) else 0) 0 := by
            apply List.foldl_add_congr
            intro j hj
            rw [coeff_X j (by
              have := List.mem_range.mp hj
              omega)]
            split <;> grind
      _ = 0 + a.coeff (i - 1) :=
        List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega)) List.nodup_range
      _ = a.coeff (i - 1) := by grind

/-- The coefficient of `X ^ k` is one in degree `k` and zero elsewhere. -/
@[simp] theorem coeff_X_pow [Lean.Grind.CommRing R]
    (k i : Nat) (hi : i < n) :
    ((X : TSeries R n) ^ k).coeff i = if i = k then 1 else 0 := by
  induction k generalizing i with
  | zero =>
      rw [pow_zero, coeff_one i hi]
  | succ k ih =>
      rw [pow_succ, coeff_mul_X (X ^ k) i hi]
      by_cases hi0 : i = 0
      · subst i
        simp
      · rw [if_neg hi0, ih (i - 1) (by omega)]
        by_cases hik : i = k + 1
        · simp [hik]
        · have : i - 1 ≠ k := by omega
          simp [hik, this]

/-- Multiplication by `X ^ k` shifts coefficients upward by `k`, with
coefficients below that degree equal to zero. -/
@[simp] theorem coeff_X_pow_mul [Lean.Grind.CommRing R]
    (a : TSeries R n) (k i : Nat) (hi : i < n) :
    (((X : TSeries R n) ^ k) * a).coeff i =
      if k ≤ i then a.coeff (i - k) else 0 := by
  induction k generalizing i with
  | zero =>
      rw [pow_zero, one_mul]
      simp
  | succ k ih =>
      have hmul :
          (X : TSeries R n) ^ (k + 1) * a =
            ((X : TSeries R n) ^ k * a) * X := by
        rw [pow_succ]
        rw [mul_assoc, mul_comm X a, ← mul_assoc]
      rw [hmul, coeff_mul_X ((X : TSeries R n) ^ k * a) i hi]
      by_cases hi0 : i = 0
      · subst i
        simp
      · rw [if_neg hi0, ih (i - 1) (by omega)]
        by_cases hki : k + 1 ≤ i
        · rw [if_pos hki, if_pos (by omega)]
          rw [show (i - 1) - k = i - (k + 1) by omega]
        · rw [if_neg hki, if_neg (by omega)]

/-- A scalar monomial has its scalar coefficient in exactly one degree. -/
theorem coeff_C_mul_X_pow [Lean.Grind.CommRing R]
    (c : R) (k i : Nat) (hi : i < n) :
    (C c * (X : TSeries R n) ^ k).coeff i = if i = k then c else 0 := by
  rw [coeff_C_mul c (X ^ k) i hi, coeff_X_pow k i hi]
  split <;> grind

/-- Fixed-precision truncated series form a lightweight commutative ring. -/
instance [Lean.Grind.CommRing R] : Lean.Grind.Semiring (TSeries R n) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact add_zero
  · exact add_comm
  · exact add_assoc
  · exact mul_assoc
  · exact mul_one
  · exact one_mul
  · exact left_distrib
  · exact right_distrib
  · exact zero_mul
  · exact mul_zero
  · exact pow_zero
  · exact pow_succ
  · exact ofNat_succ
  · exact ofNat_eq_natCast
  · exact nsmul_eq_natCast_mul

instance [Lean.Grind.CommRing R] : Lean.Grind.Ring (TSeries R n) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · exact neg_add_cancel
  · exact sub_eq_add_neg
  · exact neg_zsmul
  · intro k a; rfl
  · intro k; exact (ofNat_eq_natCast k).symm
  · exact intCast_neg

instance [Lean.Grind.CommRing R] : Lean.Grind.CommRing (TSeries R n) := by
  refine Lean.Grind.CommRing.mk ?_
  exact mul_comm

end Hex.TSeries
