import HexPoly.Dense
import Init.Data.Array.Lemmas

/-!
Executable arithmetic operations for dense array-backed polynomials.

This module implements executable `DensePoly` operations: addition,
subtraction, schoolbook multiplication, Horner evaluation, composition,
and derivative. All constructors route through `ofCoeffs`, so results are
re-normalized automatically.
-/
namespace Hex

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Multiply every coefficient by `c`. -/
def scale [Mul R] (c : R) (p : DensePoly R) : DensePoly R :=
  ofCoeffs <| p.toArray.toList.map (fun a => c * a) |>.toArray

/-- Multiply by `x^n`. -/
def shift (n : Nat) (p : DensePoly R) : DensePoly R :=
  if p.isZero then 0 else
    ofCoeffs <| ((List.replicate n (Zero.zero : R)) ++ p.toArray.toList).toArray

omit [DecidableEq R] in
private theorem list_getD_map_mul_zero [Mul R] (c : R) (coeffs : List R) (n : Nat)
    (hzero : c * (Zero.zero : R) = (Zero.zero : R)) :
    (coeffs.map fun a => c * a).getD n (Zero.zero : R) =
      c * coeffs.getD n (Zero.zero : R) := by
  induction coeffs generalizing n with
  | nil =>
      simp [hzero]
  | cons a as ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simpa using ih n

omit [DecidableEq R] in
private theorem list_getD_replicate_append_zero (n k : Nat) (coeffs : List R) :
    (List.replicate n (Zero.zero : R) ++ coeffs).getD k (Zero.zero : R) =
      if k < n then (Zero.zero : R) else coeffs.getD (k - n) (Zero.zero : R) := by
  induction n generalizing k with
  | zero =>
      simp
  | succ n ih =>
      cases k with
      | zero =>
          simp [List.replicate]
      | succ k =>
          simpa [Nat.succ_sub_succ_eq_sub] using ih k

omit [DecidableEq R] in
private theorem list_getD_map_range (size n : Nat) (f : Nat → R) :
    ((List.range size).map f).getD n (Zero.zero : R) =
      if n < size then f n else (Zero.zero : R) := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

/-- Coefficient law for scalar multiplication. The explicit zero law records the fact that
scaling a missing coefficient still gives the default coefficient `0`. -/
theorem coeff_scale [Mul R] (c : R) (p : DensePoly R) (n : Nat)
    (hzero : c * (Zero.zero : R) = (Zero.zero : R)) :
    (scale c p).coeff n = c * p.coeff n := by
  unfold scale
  rw [coeff_ofCoeffs_list]
  simpa [coeff] using list_getD_map_mul_zero (R := R) c p.toArray.toList n hzero

@[simp, grind =] theorem scale_zero_right [Mul R] (c : R) :
    scale c (0 : DensePoly R) = 0 := by
  unfold scale toArray
  rfl

/-- Semiring-specialized coefficient law for scalar multiplication, registered as a normalizing
rewrite because the required `c * 0 = 0` law is available from the semiring structure. -/
@[simp, grind =] theorem coeff_scale_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (c : S) (p : DensePoly S) (n : Nat) :
    (scale c p).coeff n = c * p.coeff n :=
  coeff_scale c p n (Lean.Grind.Semiring.mul_zero c)

/-- Semiring-specialized left zero law for scalar multiplication. -/
@[simp, grind =] theorem scale_zero_left_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (p : DensePoly S) :
    scale (0 : S) p = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_scale_semiring]
  rw [show (0 : DensePoly S).coeff n = (0 : S) by
    exact coeff_eq_zero_of_size_le (0 : DensePoly S) (by simp)]
  exact Lean.Grind.Semiring.zero_mul (p.coeff n)

/-- Coefficient law for shifting by `x^n`: coefficients below `n` are zero and later
coefficients are read from the original polynomial with the index shifted down. -/
@[simp, grind =] theorem coeff_shift (n : Nat) (p : DensePoly R) (k : Nat) :
    (shift n p).coeff k =
      if k < n then (Zero.zero : R) else p.coeff (k - n) := by
  unfold shift
  by_cases hp : p.isZero
  · have hsize : p.size = 0 := by
      simp [isZero] at hp
      simpa [size] using hp
    by_cases hk : k < n
    · simp [hp, hk]
      change (0 : DensePoly R).coeff k = (Zero.zero : R)
      exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)
    · have hzero : p.coeff (k - n) = (Zero.zero : R) := by
        exact coeff_eq_zero_of_size_le p (by omega)
      simp [hp, hk, hzero]
      change (0 : DensePoly R).coeff k = (Zero.zero : R)
      exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)
  · rw [if_neg hp]
    rw [coeff_ofCoeffs_list]
    simpa [coeff] using list_getD_replicate_append_zero (R := R) n k p.toArray.toList

@[simp, grind =] theorem shift_zero_right (n : Nat) :
    shift n (0 : DensePoly R) = 0 := by
  unfold shift isZero
  rfl

@[simp, grind =] theorem shift_zero_left (p : DensePoly R) :
    shift 0 p = p := by
  apply ext_coeff
  intro k
  simp

/-- Combined coefficient law for a scaled shift. The zero-law hypothesis is the only algebraic
fact needed to normalize coefficients that are outside the support. -/
theorem coeff_shift_scale [Mul R] (i : Nat) (c : R) (p : DensePoly R) (k : Nat)
    (hzero : c * (Zero.zero : R) = (Zero.zero : R)) :
    (shift i (scale c p)).coeff k =
      if k < i then (Zero.zero : R) else c * p.coeff (k - i) := by
  rw [coeff_shift]
  by_cases hk : k < i
  · simp [hk]
  · simp [hk, coeff_scale, hzero]

/-- Semiring-specialized coefficient law for a scaled shift, registered as a normalizing rewrite
for the common algebraic setting. -/
@[simp, grind =] theorem coeff_shift_scale_semiring
    {S : Type u} [Lean.Grind.Semiring S] [DecidableEq S]
    (i : Nat) (c : S) (p : DensePoly S) (k : Nat) :
    (shift i (scale c p)).coeff k =
      if k < i then (Zero.zero : S) else c * p.coeff (k - i) :=
  coeff_shift_scale i c p k (Lean.Grind.Semiring.mul_zero c)

/-- Add two dense polynomials coefficientwise. -/
def add [Add R] (p q : DensePoly R) : DensePoly R :=
  let size := max p.size q.size
  ofCoeffs <| (List.range size).map (fun i => p.coeff i + q.coeff i) |>.toArray

instance [Add R] : Add (DensePoly R) where
  add := add

/-- Subtract two dense polynomials coefficientwise. -/
def sub [Sub R] (p q : DensePoly R) : DensePoly R :=
  let size := max p.size q.size
  ofCoeffs <| (List.range size).map (fun i => p.coeff i - q.coeff i) |>.toArray

instance [Sub R] : Sub (DensePoly R) where
  sub := sub

/-- Coefficientwise additive inverse, expressed through executable subtraction. -/
def neg [Sub R] (p : DensePoly R) : DensePoly R :=
  0 - p

instance [Sub R] : Neg (DensePoly R) where
  neg := neg

/-- Compatibility law for caller-facing `Zero`/`Add` instances used by semiring wrappers. -/
class AddZeroLaw (S : Type u) [Zero S] [Add S] : Prop where
  add_zero_zero : (Zero.zero : S) + (Zero.zero : S) = (Zero.zero : S)

/-- Semiring structures provide the zero-addition compatibility law used by coefficient lemmas. -/
instance addZeroLaw_of_semiring {S : Type u} [Lean.Grind.Semiring S] :
    AddZeroLaw S where
  add_zero_zero := by grind

/-- Compatibility law for caller-facing `Zero`/`Sub` instances used by ring wrappers. -/
class SubZeroLaw (S : Type u) [Zero S] [Sub S] : Prop where
  sub_zero_zero : (Zero.zero : S) - (Zero.zero : S) = (Zero.zero : S)

/-- Ring structures provide the zero-subtraction compatibility law used by coefficient lemmas. -/
instance subZeroLaw_of_ring {S : Type u} [Lean.Grind.Ring S] :
    SubZeroLaw S where
  sub_zero_zero := by grind

/-- Compatibility law for caller-facing `Zero`/`Sub`/`Neg` instances used by negation wrappers. -/
class ZeroSubNegLaw (S : Type u) [Zero S] [Sub S] [Neg S] : Prop where
  zero_sub_eq_neg : ∀ a : S, (Zero.zero : S) - a = -a

/-- Ring structures provide the zero-subtraction negation law used by coefficient lemmas. -/
instance zeroSubNegLaw_of_ring {S : Type u} [Lean.Grind.Ring S] : ZeroSubNegLaw S where
  zero_sub_eq_neg := by
    intro a
    grind

/-- Schoolbook dense polynomial multiplication by direct coefficient convolution. -/
def mul [Add R] [Mul R] (p q : DensePoly R) : DensePoly R :=
  if p.isZero || q.isZero then 0 else
    let size := p.size + q.size - 1
    let coeffs :=
      (List.range p.size).foldl
        (fun acc i =>
          (List.range q.size).foldl
            (fun acc j =>
              let k := i + j
              acc.set! k ((acc[k]?).getD (Zero.zero : R) + p.coeff i * q.coeff j))
            acc)
        (Array.replicate size (Zero.zero : R))
    ofCoeffs coeffs

instance [Add R] [Mul R] : Mul (DensePoly R) where
  mul := mul

/-- One inner schoolbook multiplication step, projected to coefficient `n`. -/
def mulCoeffStep [Add R] [Mul R] (p q : DensePoly R) (n i : Nat) (acc : R) (j : Nat) : R :=
  if i + j = n then acc + p.coeff i * q.coeff j else acc

/-- The schoolbook coefficient fold matching the executable multiplication loop order. -/
def mulCoeffSum [Add R] [Mul R] (p q : DensePoly R) (n : Nat) : R :=
  (List.range p.size).foldl
    (fun acc i => (List.range q.size).foldl (mulCoeffStep p q n i) acc)
    (Zero.zero : R)

omit [DecidableEq R] in
private theorem array_getD_set!_schoolbook [Add R] [Mul R]
    (acc : Array R) (n k : Nat) (term : R) (hk : k < acc.size) :
    (acc.set! k (acc[k]?.getD (Zero.zero : R) + term)).getD n (Zero.zero : R) =
      if k = n then acc.getD n (Zero.zero : R) + term else acc.getD n (Zero.zero : R) := by
  by_cases hkn : k = n
  · subst n
    simp [Array.getD, hk]
  ·
    by_cases hn : n < acc.size
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hk, hn, hkn]
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hk, hn, hkn]

private theorem mul_inner_array_coeff_fold [Add R] [Mul R]
    (p q : DensePoly R) (n i : Nat) (xs : List Nat) (acc : Array R)
    (hbound : ∀ j, j ∈ xs → i + j < acc.size) :
    (xs.foldl
        (fun acc j =>
          let k := i + j
          acc.set! k ((acc[k]?).getD (Zero.zero : R) + p.coeff i * q.coeff j))
        acc).getD n (Zero.zero : R) =
      xs.foldl (mulCoeffStep p q n i) (acc.getD n (Zero.zero : R)) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      have hj : i + j < acc.size := hbound j (by simp)
      rw [ih]
      · rw [array_getD_set!_schoolbook (R := R) acc n (i + j) (p.coeff i * q.coeff j) hj]
        unfold mulCoeffStep
        by_cases h : i + j = n
        · simp [h]
        · simp [h]
      · intro j' hj'
        simpa [Array.size_setIfInBounds] using hbound j' (by simp [hj'])

private theorem mul_inner_array_size [Add R] [Mul R]
    (p q : DensePoly R) (i : Nat) (xs : List Nat) (acc : Array R) :
    (xs.foldl
        (fun acc j =>
          let k := i + j
          acc.set! k ((acc[k]?).getD (Zero.zero : R) + p.coeff i * q.coeff j))
        acc).size = acc.size := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Array.size_setIfInBounds]

private theorem mul_array_coeff_fold [Add R] [Mul R]
    (p q : DensePoly R) (n : Nat) (xs : List Nat) (acc : Array R) (size : Nat)
    (hacc : acc.size = size)
    (hbound : ∀ i, i ∈ xs → ∀ j, j < q.size → i + j < size) :
    (xs.foldl
        (fun acc i =>
          (List.range q.size).foldl
            (fun acc j =>
              let k := i + j
              acc.set! k ((acc[k]?).getD (Zero.zero : R) + p.coeff i * q.coeff j))
            acc)
        acc).getD n (Zero.zero : R) =
      xs.foldl (fun coeff i => (List.range q.size).foldl (mulCoeffStep p q n i) coeff)
        (acc.getD n (Zero.zero : R)) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hinner :
          ((List.range q.size).foldl
              (fun acc j =>
                let k := i + j
                acc.set! k ((acc[k]?).getD (Zero.zero : R) + p.coeff i * q.coeff j))
              acc).getD n (Zero.zero : R) =
            (List.range q.size).foldl (mulCoeffStep p q n i)
              (acc.getD n (Zero.zero : R)) := by
        apply mul_inner_array_coeff_fold
        intro j hj
        have hjlt : j < q.size := by simpa using List.mem_range.mp hj
        simpa [hacc] using hbound i (by simp) j hjlt
      rw [ih]
      · rw [hinner]
      · rw [mul_inner_array_size]
        exact hacc
      · intro i' hi' j hj
        exact hbound i' (by simp [hi']) j hj

omit [Zero R] [DecidableEq R] in
private theorem list_foldl_ignore (xs : List Nat) (init : R) :
    xs.foldl (fun acc _ => acc) init = init := by
  induction xs generalizing init with
  | nil =>
      rfl
  | cons _ xs ih =>
      simpa using ih init

/-- Characterising coefficient law for multiplication: each coefficient of `p * q` is computed by
the same nested schoolbook fold as the executable multiplication loop. -/
theorem coeff_mul [Add R] [Mul R] (p q : DensePoly R) (n : Nat) :
    (p * q).coeff n = mulCoeffSum p q n := by
  change (mul p q).coeff n = mulCoeffSum p q n
  unfold mul
  by_cases hzero : p.isZero || q.isZero
  · rw [if_pos hzero]
    by_cases hp : p.isZero
    · have hpsize : p.size = 0 := (DensePoly.isZero_eq_true_iff p).1 (by simpa using hp)
      rw [show (0 : DensePoly R).coeff n = (Zero.zero : R) by
        exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)]
      simp [mulCoeffSum, hpsize]
    · have hq : q.isZero = true := by
        cases hq' : q.isZero <;> simp [hp, hq'] at hzero ⊢
      have hqsize : q.size = 0 := (DensePoly.isZero_eq_true_iff q).1 hq
      rw [show (0 : DensePoly R).coeff n = (Zero.zero : R) by
        exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)]
      simp [mulCoeffSum, hqsize, list_foldl_ignore]
  · rw [if_neg hzero]
    rw [coeff_ofCoeffs]
    have hp_not : p.isZero = false := by
      cases hp : p.isZero <;> cases hq : q.isZero <;> simp [hp, hq] at hzero ⊢
    have hq_not : q.isZero = false := by
      cases hp : p.isZero <;> cases hq : q.isZero <;> simp [hp, hq] at hzero ⊢
    have hp_pos : 0 < p.size := (DensePoly.isZero_eq_false_iff p).1 hp_not
    have hq_pos : 0 < q.size := (DensePoly.isZero_eq_false_iff q).1 hq_not
    let size := p.size + q.size - 1
    have hfold :=
      mul_array_coeff_fold p q n (List.range p.size)
        (Array.replicate size (Zero.zero : R)) size (by simp)
        (by
          intro i hi j hj
          have hi' : i < p.size := by simpa using List.mem_range.mp hi
          omega)
    simpa [mulCoeffSum, size, Array.getD] using hfold

/-- Evaluate a polynomial using Horner's method. -/
def eval [Add R] [Mul R] (p : DensePoly R) (x : R) : R :=
  p.toArray.toList.reverse.foldl (fun acc coeff => acc * x + coeff) (Zero.zero : R)

/-- Compose polynomials using Horner's method. -/
def compose [Add R] [Mul R] (p q : DensePoly R) : DensePoly R :=
  p.toArray.toList.reverse.foldl (fun acc coeff => acc * q + C coeff) (0 : DensePoly R)

/-- Left-composition by the zero polynomial is zero. -/
@[simp, grind =] theorem compose_zero_left [Add R] [Mul R] (q : DensePoly R) :
    compose (0 : DensePoly R) q = 0 := by
  rfl

/-- Composition of a constant polynomial. The explicit zero-addition law is needed because
the generic `Add`/`Mul`/`Zero` interfaces do not provide algebraic simplification rules. -/
theorem compose_C [Add R] [Mul R] (c : R) (q : DensePoly R)
    (hzero_add : (Zero.zero : R) + c = c) :
    compose (C c) q = C c := by
  by_cases hc : c = (0 : R)
  · rw [hc]
    change compose (C (Zero.zero : R)) q = (C (Zero.zero : R))
    unfold compose toArray
    rw [show (C (Zero.zero : R)).coeffs = #[] by
      change (C (0 : R)).coeffs = #[]
      exact coeffs_C_zero]
    change (0 : DensePoly R) = C (Zero.zero : R)
    apply ext_coeff
    intro n
    rw [show (0 : DensePoly R).coeff n = (Zero.zero : R) by
      exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)]
    rw [coeff_C]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  · change c ≠ Zero.zero at hc
    unfold compose toArray
    rw [coeffs_C_of_ne_zero hc]
    change (0 : DensePoly R) * q + C c = C c
    rw [show (0 : DensePoly R) * q = 0 by rfl]
    apply ext_coeff
    intro n
    change (add (0 : DensePoly R) (C c)).coeff n = (C c).coeff n
    unfold add
    rw [coeff_ofCoeffs_list]
    have hzero_coeff : ∀ i, (0 : DensePoly R).coeff i = (Zero.zero : R) := by
      intro i
      exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)
    cases n with
    | zero =>
        simp [size_C_of_ne_zero hc, hzero_coeff, hzero_add]
    | succ n =>
        simp [size_C_of_ne_zero hc, hzero_coeff]

/-- Semiring-specialized composition law for constants. This packages the zero-addition
law needed by the generic `compose_C`. -/
@[simp, grind =] theorem compose_C_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (c : S) (q : DensePoly S) :
    compose (C c) q = C c :=
  compose_C c q (by grind)

/-- Formal derivative. The coefficient of `x^i` becomes `(i + 1) * a_(i+1)`. -/
def derivative [NatCast R] [Mul R] (p : DensePoly R) : DensePoly R :=
  ofCoeffs <|
    (List.range (p.size - 1)).map (fun i => ((i + 1 : Nat) : R) * p.coeff (i + 1)) |>.toArray

/-- Coefficient law for addition. The explicit zero law is needed because the generic
`Add`/`Zero` interface does not imply `0 + 0 = 0`. -/
theorem coeff_add [Add R] (p q : DensePoly R) (n : Nat)
    (hzero : (Zero.zero : R) + (Zero.zero : R) = (Zero.zero : R)) :
    (p + q).coeff n = (p.coeff n + q.coeff n) := by
  change (add p q).coeff n = (p.coeff n + q.coeff n)
  unfold add
  rw [coeff_ofCoeffs_list]
  rw [list_getD_map_range]
  by_cases hn : n < max p.size q.size
  · simp [hn]
  · have hmax : max p.size q.size ≤ n := Nat.le_of_not_gt hn
    have hp : p.size ≤ n := Nat.le_trans (Nat.le_max_left p.size q.size) hmax
    have hq : q.size ≤ n := Nat.le_trans (Nat.le_max_right p.size q.size) hmax
    simp [hn, coeff_eq_zero_of_size_le p hp, coeff_eq_zero_of_size_le q hq, hzero]

/-- Semiring-specialized coefficient law for addition. -/
@[simp, grind =] theorem coeff_add_semiring {S : Type u}
    [Zero S] [Add S] [Lean.Grind.Semiring S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat)
    (hzero : AddZeroLaw S := by infer_instance) :
    (p + q).coeff n = p.coeff n + q.coeff n :=
  coeff_add p q n hzero.add_zero_zero

/-- Coefficient law for subtraction. The explicit zero law is needed because the generic
`Sub`/`Zero` interface does not imply `0 - 0 = 0`. -/
theorem coeff_sub [Sub R] (p q : DensePoly R) (n : Nat)
    (hzero : (Zero.zero : R) - (Zero.zero : R) = (Zero.zero : R)) :
    (p - q).coeff n = (p.coeff n - q.coeff n) := by
  change (sub p q).coeff n = (p.coeff n - q.coeff n)
  unfold sub
  rw [coeff_ofCoeffs_list]
  rw [list_getD_map_range]
  by_cases hn : n < max p.size q.size
  · simp [hn]
  · have hmax : max p.size q.size ≤ n := Nat.le_of_not_gt hn
    have hp : p.size ≤ n := Nat.le_trans (Nat.le_max_left p.size q.size) hmax
    have hq : q.size ≤ n := Nat.le_trans (Nat.le_max_right p.size q.size) hmax
    simp [hn, coeff_eq_zero_of_size_le p hp, coeff_eq_zero_of_size_le q hq, hzero]

/-- Ring-specialized coefficient law for subtraction. -/
@[simp, grind =] theorem coeff_sub_ring {S : Type u}
    [Zero S] [Sub S] [Lean.Grind.Ring S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat)
    (hzero : SubZeroLaw S := by infer_instance) :
    (p - q).coeff n = p.coeff n - q.coeff n :=
  coeff_sub p q n hzero.sub_zero_zero

/-- The zero polynomial has coefficient `0` at every index. -/
@[simp, grind =] theorem coeff_zero (n : Nat) :
    (0 : DensePoly R).coeff n = (0 : R) := by
  exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)

/-- Coefficient law for negation, expressed through subtraction from zero. The explicit zero law
is inherited from the generic subtraction coefficient theorem. -/
theorem coeff_neg [Sub R] (p : DensePoly R) (n : Nat)
    (hzero : (Zero.zero : R) - (Zero.zero : R) = (Zero.zero : R)) :
    (-p).coeff n = ((0 : R) - p.coeff n) := by
  change (neg p).coeff n = ((0 : R) - p.coeff n)
  simp [neg, coeff_sub, hzero]

/-- Ring-specialized coefficient law for negation. -/
@[simp, grind =] theorem coeff_neg_ring {S : Type u}
    [Zero S] [Sub S] [Neg S] [Lean.Grind.Ring S] [DecidableEq S]
    (p : DensePoly S) (n : Nat)
    (hsub : SubZeroLaw S := by infer_instance)
    (hneg : ZeroSubNegLaw S := by infer_instance) :
    (-p).coeff n = -(p.coeff n) := by
  have h := coeff_neg p n hsub.sub_zero_zero
  rw [h]
  exact hneg.zero_sub_eq_neg (p.coeff n)

/-- Semiring-specialized right zero law for dense polynomial addition. -/
@[simp, grind =] theorem add_zero_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (p : DensePoly S) :
    p + 0 = p := by
  apply ext_coeff
  intro n
  rw [coeff_add_semiring, coeff_zero]
  grind

/-- Semiring-specialized left zero law for dense polynomial addition. -/
@[simp, grind =] theorem zero_add_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (p : DensePoly S) :
    0 + p = p := by
  apply ext_coeff
  intro n
  rw [coeff_add_semiring, coeff_zero]
  grind

/-- Ring-specialized right zero law for dense polynomial subtraction. -/
@[simp, grind =] theorem sub_zero_ring {S : Type u}
    [Lean.Grind.Ring S] [DecidableEq S]
    (p : DensePoly S) :
    p - 0 = p := by
  apply ext_coeff
  intro n
  rw [coeff_sub_ring, coeff_zero]
  grind

/-- Ring-specialized left zero law for dense polynomial subtraction. -/
@[simp, grind =] theorem zero_sub_ring {S : Type u}
    [Lean.Grind.Ring S] [DecidableEq S]
    (p : DensePoly S) :
    0 - p = -p := by
  apply ext_coeff
  intro n
  rw [coeff_sub_ring, coeff_zero, coeff_neg_ring]
  grind

/-- Ring-specialized negation of the zero dense polynomial. -/
@[simp, grind =] theorem neg_zero_ring {S : Type u}
    [Lean.Grind.Ring S] [DecidableEq S] :
    -(0 : DensePoly S) = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_neg_ring, coeff_zero]
  grind

/-- Horner evaluation sends the zero dense polynomial to `0`. -/
@[simp, grind =] theorem eval_zero [Add R] [Mul R] (x : R) :
    eval (0 : DensePoly R) x = 0 := by
  rfl

/-- Evaluation of a constant polynomial. The explicit zero laws are needed because the
generic `Add`/`Mul`/`Zero` interfaces do not provide algebraic simplification rules. -/
theorem eval_C [Add R] [Mul R] (c x : R)
    (hzero_mul : (Zero.zero : R) * x = (Zero.zero : R))
    (hzero_add : (Zero.zero : R) + c = c) :
    eval (C c) x = c := by
  by_cases hc : c = (0 : R)
  · rw [hc]
    change eval (C (Zero.zero : R)) x = (Zero.zero : R)
    unfold eval toArray
    rw [show (C (Zero.zero : R)).coeffs = #[] by
      change (C (0 : R)).coeffs = #[]
      exact coeffs_C_zero]
    rfl
  · change c ≠ Zero.zero at hc
    simp [eval, toArray, coeffs_C_of_ne_zero hc, hzero_mul, hzero_add]

/-- Semiring-specialized evaluation law for constants. This packages the
zero-multiplication and zero-addition laws needed by the generic `eval_C`. -/
@[simp, grind =] theorem eval_C_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (c x : S) :
    eval (C c) x = c :=
  eval_C c x (Lean.Grind.Semiring.zero_mul x) (by grind)

private theorem semiring_mul_pow_left {S : Type u} [Lean.Grind.Semiring S]
    (x : S) (n : Nat) :
    x * x ^ n = x ^ (n + 1) := by
  induction n with
  | zero =>
      rw [Lean.Grind.Semiring.pow_succ x 0, Lean.Grind.Semiring.pow_zero,
        Lean.Grind.Semiring.one_mul]
      exact Lean.Grind.Semiring.mul_one x
  | succ n ih =>
      calc
        x * x ^ (n + 1) = x * (x ^ n * x) := by rw [Lean.Grind.Semiring.pow_succ]
        _ = (x * x ^ n) * x := by rw [Lean.Grind.Semiring.mul_assoc]
        _ = x ^ (n + 1) * x := by rw [ih]
        _ = x ^ (n + 1 + 1) := by
          exact (Lean.Grind.Semiring.pow_succ x (n + 1)).symm

private theorem eval_replicate_zero_semiring {S : Type u} [Lean.Grind.Semiring S]
    (n : Nat) (c x : S) :
    (List.replicate n (0 : S)).foldl (fun acc coeff => acc * x + coeff) c =
      c * x ^ n := by
  induction n generalizing c with
  | zero =>
      simp [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.mul_one]
  | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      simp [Lean.Grind.Semiring.add_zero, Lean.Grind.Semiring.mul_assoc,
        semiring_mul_pow_left]

/-- Semiring-specialized evaluation law for monomials. -/
@[simp, grind =] theorem eval_monomial_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (n : Nat) (c x : S) :
    eval (monomial n c) x = c * x ^ n := by
  by_cases hc : c = (0 : S)
  · rw [hc, monomial_zero, eval_zero]
    simp [Lean.Grind.Semiring.zero_mul]
  · unfold eval toArray monomial
    change c ≠ Zero.zero at hc
    rw [dif_neg hc]
    simp [Array.toList_push]
    have hinit : (Zero.zero : S) * x + c = c := by
      change (0 : S) * x + c = c
      rw [Lean.Grind.Semiring.zero_mul]
      grind
    rw [hinit]
    exact eval_replicate_zero_semiring n c x

/-- The formal derivative of the zero polynomial is zero. -/
@[simp, grind =] theorem derivative_zero [NatCast R] [Mul R] :
    derivative (0 : DensePoly R) = 0 := by
  rfl

/-- Characterising coefficient law for the formal derivative: the coefficient of
`x^n` in `derivative p` is `(n + 1) * p.coeff (n + 1)`. The explicit zero law
`((n + 1 : Nat) : R) * 0 = 0` is needed because the generic `NatCast`/`Mul`/`Zero`
interface does not guarantee it, mirroring the hypothesis on `coeff_scale`. -/
theorem coeff_derivative [NatCast R] [Mul R] (p : DensePoly R) (n : Nat)
    (hzero : ((n + 1 : Nat) : R) * (Zero.zero : R) = (Zero.zero : R)) :
    (derivative p).coeff n = ((n + 1 : Nat) : R) * p.coeff (n + 1) := by
  unfold derivative
  rw [coeff_ofCoeffs_list, list_getD_map_range]
  by_cases hn : n < p.size - 1
  · simp [hn]
  · have hp : p.size ≤ n + 1 := by omega
    rw [coeff_eq_zero_of_size_le p hp, if_neg hn, hzero]

attribute [local instance 1100] Lean.Grind.Semiring.natCast

/-- Semiring-specialized coefficient law for the formal derivative, registered
as a normalizing rewrite because semirings provide the required `a * 0 = 0`
law. -/
@[simp, grind =] theorem coeff_derivative_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S] (p : DensePoly S) (n : Nat) :
    (derivative p).coeff n = ((n + 1 : Nat) : S) * p.coeff (n + 1) := by
  exact coeff_derivative p n (Lean.Grind.Semiring.mul_zero _)

/-- The formal derivative of a constant polynomial is zero over a semiring. -/
@[simp, grind =] theorem derivative_C_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S] (c : S) :
    derivative (C c : DensePoly S) = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_derivative_semiring, coeff_zero, coeff_C]
  simp only [Nat.succ_ne_zero, if_false]
  change ((n + 1 : Nat) : S) * (0 : S) = 0
  exact Lean.Grind.Semiring.mul_zero _

/-- The formal derivative of a degree-zero monomial is zero over a semiring. -/
@[simp, grind =] theorem derivative_monomial_zero_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S] (c : S) :
    derivative (monomial 0 c : DensePoly S) = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_derivative_semiring, coeff_zero, coeff_monomial]
  simp only [Nat.succ_ne_zero, if_false]
  change ((n + 1 : Nat) : S) * (0 : S) = 0
  exact Lean.Grind.Semiring.mul_zero _

/-- The formal derivative of `c * x^(n + 1)` is `(n + 1) * c * x^n` over a semiring. -/
theorem derivative_monomial_succ_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S] (n : Nat) (c : S) :
    derivative (monomial (n + 1) c : DensePoly S) =
      monomial n (((n + 1 : Nat) : S) * c) := by
  apply ext_coeff
  intro i
  rw [coeff_derivative_semiring, coeff_monomial, coeff_monomial]
  by_cases hi : i = n
  · subst i
    simp
  · have hsucc : i + 1 ≠ n + 1 := by omega
    simp only [hsucc, hi, if_false]
    change ((i + 1 : Nat) : S) * (0 : S) = 0
    exact Lean.Grind.Semiring.mul_zero _

end DensePoly
end Hex
