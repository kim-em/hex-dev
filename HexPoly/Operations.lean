/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Dense
public import Init.Data.Array.Lemmas

public section

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
@[expose]
def scale [Mul R] (c : R) (p : DensePoly R) : DensePoly R :=
  ofCoeffs <| p.toArray.toList.map (fun a => c * a) |>.toArray

/-- Multiply by `x^n`. -/
@[expose]
def shift (n : Nat) (p : DensePoly R) : DensePoly R :=
  if p.isZero then 0 else
    ofCoeffs <| ((List.replicate n (Zero.zero : R)) ++ p.toArray.toList).toArray

omit [DecidableEq R] in
/-- Scaling a list by `c` commutes with default-indexed reads: the `n`-th `getD` of
`coeffs.map (c * ·)` is `c` times the `n`-th `getD` of `coeffs`. Used by `coeff_scale`
to derive the scalar-multiplication coefficient law. -/
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
/-- Default-indexed read of a list prefixed by `n` zeros: indices below `n` read the
default `0`, and index `k ≥ n` reads `coeffs` at the shifted position `k - n`. Used by the
`shift` coefficient law to relate `shift n p` back to `p`. -/
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
          simpa [Nat.succ_sub_succ_eq_sub, List.replicate_succ, List.cons_append,
            List.getElem?_cons_succ] using ih k

omit [DecidableEq R] in
/-- Default-indexed read of `(List.range size).map f`: index `n` reads `f n` when
`n < size` and the default `0` otherwise. The workhorse indexing fact for the coefficient-
list extensionality proofs (e.g. `toList_eq_coeff_range`). -/
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
  simpa [coeff, toArray] using list_getD_map_mul_zero (R := R) c p.toArray.toList n hzero

/-- Scaling the zero polynomial yields the zero polynomial: `scale c 0 = 0`.
A `simp`/`grind` normal form, so callers need no `c * 0 = 0` hypothesis to
discharge the scaled-zero case. -/
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
    simpa [coeff, toArray] using list_getD_replicate_append_zero (R := R) n k p.toArray.toList

/-- Shifting the zero polynomial by any power leaves it zero: `shift n 0 = 0`.
A `simp`/`grind` normal form for the degenerate input to `shift`. -/
@[simp, grind =] theorem shift_zero_right (n : Nat) :
    shift n (0 : DensePoly R) = 0 := by
  unfold shift isZero
  rfl

/-- Shifting by `x^0` is the identity: `shift 0 p = p`. A `simp`/`grind` normal
form so a trivial shift drops out of multiplication and division proofs. -/
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

omit [DecidableEq R] in
/-- Default-indexed reads agree across `List.toArray`. -/
private theorem toArray_getD_eq_getD (l : List R) (n : Nat) :
    l.toArray.getD n (Zero.zero : R) = l.getD n (Zero.zero : R) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rfl

/-- Reading the spec-level coefficient list with default zero agrees with
`DensePoly.coeff`. -/
theorem toList_getD_eq_coeff (p : DensePoly R) (n : Nat) :
    p.toList.getD n (Zero.zero : R) = p.coeff n := by
  unfold toList toArray coeff
  rw [Array.getD_eq_getD_getElem?]
  change p.coeffs.toList[n]?.getD (Zero.zero : R) =
    p.coeffs[n]?.getD (Zero.zero : R)
  rw [Array.getElem?_toList]

/-- The zero polynomial has coefficient `0` at every index. -/
@[simp, grind =] theorem coeff_zero (n : Nat) :
    (0 : DensePoly R).coeff n = (0 : R) := by
  exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)

/-- Zip two coefficient lists with `f`, padding the shorter list with literal
`Zero.zero` arguments: overhang entries become `f p Zero.zero` / `f Zero.zero q`
rather than being passed through, so every output entry is literally
`f (xs.getD i) (ys.getD i)` — the value the `Array.ofFn` runtime impls
reproduce with no algebraic laws on `R`. -/
@[expose]
def zipPad (f : R → R → R) : List R → List R → List R
  | [], [] => []
  | [], q :: qs => f (Zero.zero : R) q :: zipPad f [] qs
  | p :: ps, [] => f p (Zero.zero : R) :: zipPad f ps []
  | p :: ps, q :: qs => f p q :: zipPad f ps qs

/-- Default-indexed read of a padded zip: inside the padded range the entry is
`f` of the two default-indexed reads, outside it is the default. -/
private theorem zipPad_getD (f : R → R → R) (xs ys : List R) (n : Nat) :
    (zipPad f xs ys).getD n (Zero.zero : R) =
      if n < max xs.length ys.length
      then f (xs.getD n (Zero.zero : R)) (ys.getD n (Zero.zero : R))
      else (Zero.zero : R) := by
  induction xs generalizing ys n with
  | nil =>
      induction ys generalizing n with
      | nil => simp [zipPad]
      | cons q qs ihq =>
          cases n with
          | zero => simp [zipPad]
          | succ m => simpa [zipPad] using ihq m
  | cons p ps ihp =>
      cases ys with
      | nil =>
          cases n with
          | zero => simp [zipPad]
          | succ m => simpa [zipPad] using ihp [] m
      | cons q qs =>
          cases n with
          | zero => simp [zipPad]
          | succ m => simpa [zipPad] using ihp qs m

/-- Default-indexed read of `Array.ofFn`: the generator inside the range,
the default outside. -/
private theorem array_ofFn_getD {n : Nat} (f : Fin n → R) (i : Nat) :
    (Array.ofFn f).getD i (Zero.zero : R) =
      if h : i < n then f ⟨i, h⟩ else (Zero.zero : R) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : i < n
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

/-- Default-indexed read of `Array.map`: `g` of the entry inside the range,
the default outside. -/
private theorem array_map_getD (g : R → R) (a : Array R) (i : Nat) :
    (a.map g).getD i (Zero.zero : R) =
      if h : i < a.size then g a[i] else (Zero.zero : R) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  by_cases h : i < a.size
  · rw [Array.getElem?_eq_getElem h, dif_pos h]
    rfl
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt h), dif_neg h]
    rfl

/-- Add two dense polynomials coefficientwise.

Kernel-facing specification: a single padded walk of the two coefficient
lists. Compiled code runs the one-allocation `Array.ofFn` loop `addImpl`
via the `@[csimp]` proof `add_eq_impl`. -/
@[expose]
noncomputable def add [Add R] (p q : DensePoly R) : DensePoly R :=
  ofCoeffs (zipPad (· + ·) p.toList q.toList).toArray

/-- Runtime implementation of `add`: one `Array.ofFn` allocation over the
padded index range (value-equal to `add` by `add_eq_impl`, registered
`@[csimp]`). -/
@[expose]
def addImpl [Add R] (p q : DensePoly R) : DensePoly R :=
  ofCoeffs (Array.ofFn (n := max p.size q.size) fun i => p.coeff i + q.coeff i)

/-- The spec `add` and the `Array.ofFn` runtime loop compute the same
polynomial: each output coefficient is literally `p.coeff i + q.coeff i` on
both sides, so no algebraic laws on `R` are needed. -/
theorem add_eq_addImpl [Add R] (p q : DensePoly R) : add p q = addImpl p q := by
  apply ext_coeff
  intro n
  unfold add addImpl
  rw [coeff_ofCoeffs, coeff_ofCoeffs, toArray_getD_eq_getD, zipPad_getD, array_ofFn_getD]
  simp only [length_toList, toList_getD_eq_coeff]
  by_cases hn : n < max p.size q.size
  · rw [if_pos hn, dif_pos hn]
  · rw [if_neg hn, dif_neg hn]

/-- Register the `Array.ofFn` loop as the compiled implementation of `add`. -/
@[csimp]
theorem add_eq_impl : @add = @addImpl := by
  funext R _ _ _ p q
  exact add_eq_addImpl p q

instance [Add R] : Add (DensePoly R) where
  add := add

/-- Subtract two dense polynomials coefficientwise.

Kernel-facing specification; compiled code runs the `Array.ofFn` loop
`subImpl` via the `@[csimp]` proof `sub_eq_impl`. -/
@[expose]
noncomputable def sub [Sub R] (p q : DensePoly R) : DensePoly R :=
  ofCoeffs (zipPad (· - ·) p.toList q.toList).toArray

/-- Runtime implementation of `sub` (value-equal to `sub` by `sub_eq_impl`,
registered `@[csimp]`). -/
@[expose]
def subImpl [Sub R] (p q : DensePoly R) : DensePoly R :=
  ofCoeffs (Array.ofFn (n := max p.size q.size) fun i => p.coeff i - q.coeff i)

/-- The spec `sub` and the `Array.ofFn` runtime loop compute the same
polynomial. -/
theorem sub_eq_subImpl [Sub R] (p q : DensePoly R) : sub p q = subImpl p q := by
  apply ext_coeff
  intro n
  unfold sub subImpl
  rw [coeff_ofCoeffs, coeff_ofCoeffs, toArray_getD_eq_getD, zipPad_getD, array_ofFn_getD]
  simp only [length_toList, toList_getD_eq_coeff]
  by_cases hn : n < max p.size q.size
  · rw [if_pos hn, dif_pos hn]
  · rw [if_neg hn, dif_neg hn]

/-- Register the `Array.ofFn` loop as the compiled implementation of `sub`. -/
@[csimp]
theorem sub_eq_impl : @sub = @subImpl := by
  funext R _ _ _ p q
  exact sub_eq_subImpl p q

instance [Sub R] : Sub (DensePoly R) where
  sub := sub

/-- Coefficientwise additive inverse, expressed through executable subtraction.

Kernel-facing specification (one `sub` against the zero polynomial); compiled
code runs the single `Array.map` pass `negImpl` via the `@[csimp]` proof
`neg_eq_impl`. -/
@[expose]
noncomputable def neg [Sub R] (p : DensePoly R) : DensePoly R :=
  0 - p

/-- Runtime implementation of `neg`: one `Array.map` pass over the stored
coefficients (value-equal to `neg` by `neg_eq_impl`, registered `@[csimp]`). -/
@[expose]
def negImpl [Sub R] (p : DensePoly R) : DensePoly R :=
  ofCoeffs (p.toArray.map (fun a => (Zero.zero : R) - a))

/-- The spec `neg` and the `Array.map` runtime pass compute the same
polynomial: each coefficient is literally `Zero.zero - p.coeff i` on both
sides. -/
theorem neg_eq_negImpl [Sub R] (p : DensePoly R) : neg p = negImpl p := by
  apply ext_coeff
  intro n
  show (sub 0 p).coeff n = (negImpl p).coeff n
  rw [sub_eq_subImpl]
  unfold subImpl negImpl
  rw [coeff_ofCoeffs, coeff_ofCoeffs, array_ofFn_getD, array_map_getD]
  simp only [size_zero, Nat.zero_max, toArray_size, coeff_zero]
  by_cases hn : n < p.size
  · rw [dif_pos hn, dif_pos hn,
      show p.toArray[n] = p.coeff n by
        rw [Array.getElem_eq_getD (Zero.zero : R), toArray_getD]]
    rfl
  · rw [dif_neg hn, dif_neg hn]

/-- Register the `Array.map` pass as the compiled implementation of `neg`. -/
@[csimp]
theorem neg_eq_impl : @neg = @negImpl := by
  funext R _ _ _ p
  exact neg_eq_negImpl p

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

omit [Zero R] [DecidableEq R] in
/-- One row of the schoolbook convolution: add `c` times each entry of `qs`
into the corresponding entry of `acc`, dropping contributions past the end of
`acc` (matching the dropped out-of-bounds `Array.set!` writes of `mulImpl`). -/
@[expose]
def mulRow [Add R] [Mul R] (c : R) : List R → List R → List R
  | acc, [] => acc
  | [], _ :: _ => []
  | a :: acc, q :: qs => (a + c * q) :: mulRow c acc qs

omit [Zero R] [DecidableEq R] in
/-- All rows of the schoolbook convolution: for each coefficient of `ps` in
ascending-degree order, add its scaled copy of `qs` into the accumulator at the
matching offset. The accumulator entry at the current offset is final once its
row is applied, so each step emits one finished coefficient and recurses on the
tail. Additions reach each accumulator entry in exactly the order of the
`Array`-based `mulImpl` loop, which is what makes `mul_eq_impl` provable
without any algebraic laws on `R`. -/
@[expose]
def mulRows [Add R] [Mul R] (qs : List R) : List R → List R → List R
  | [], acc => acc
  | _ :: _, [] => []
  | c :: ps, a :: acc =>
      match qs with
      | [] => a :: mulRows qs ps acc
      | q :: qs' => (a + c * q) :: mulRows qs ps (mulRow c acc qs')

/-- Schoolbook dense polynomial multiplication by direct coefficient convolution.

This definition is the kernel-reduction-friendly specification: the accumulator
is a plain list walked head-first, so reducing a concrete product costs one
cons-step per `(i, j)` coefficient pair instead of an O(size) list traversal
per `Array` access. Compiled code instead runs the in-place `Array` loop
`mulImpl`, registered by the `@[csimp]` proof `mul_eq_impl`. -/
@[expose]
noncomputable def mul [Add R] [Mul R] (p q : DensePoly R) : DensePoly R :=
  if p.isZero || q.isZero then 0 else
    let size := p.size + q.size - 1
    ofCoeffs (mulRows q.toList p.toList
      (List.replicate size (Zero.zero : R))).toArray

/-- Runtime implementation of `mul`: the same schoolbook convolution computed
by in-place `Array` writes (value-equal to `mul` by `mul_eq_impl`, registered
`@[csimp]`).

The inner `j`-loop reads the loop-invariant coefficient `p.coeff i` from a single
`let`-bound value (`pi`) instead of re-projecting it on every `(i, j)` step, so
the compiled inner loop performs one bounds-checked coefficient read per `i`
rather than per `(i, j)`. The `let` is a zeta reduction away from the bare
convolution, so it does not change the value, the `coeff_mul` spec, or any
proof. -/
@[expose]
def mulImpl [Add R] [Mul R] (p q : DensePoly R) : DensePoly R :=
  if p.isZero || q.isZero then 0 else
    let size := p.size + q.size - 1
    let coeffs :=
      (List.range p.size).foldl
        (fun acc i =>
          let pi := p.coeff i
          (List.range q.size).foldl
            (fun acc j =>
              let k := i + j
              acc.set! k ((acc[k]?).getD (Zero.zero : R) + pi * q.coeff j))
            acc)
        (Array.replicate size (Zero.zero : R))
    ofCoeffs coeffs

/-- One inner schoolbook multiplication step, projected to coefficient `n`. -/
@[expose]
def mulCoeffStep [Add R] [Mul R] (p q : DensePoly R) (n i : Nat) (acc : R) (j : Nat) : R :=
  if i + j = n then acc + p.coeff i * q.coeff j else acc

/-- The schoolbook coefficient fold matching the executable multiplication loop order. -/
@[expose]
def mulCoeffSum [Add R] [Mul R] (p q : DensePoly R) (n : Nat) : R :=
  (List.range p.size).foldl
    (fun acc i => (List.range q.size).foldl (mulCoeffStep p q n i) acc)
    (Zero.zero : R)

omit [DecidableEq R] in
/-- Default-indexed read after one schoolbook accumulation step: `set!`-adding `term` at
in-bounds index `k` changes only the `k`-th coefficient, leaving every other `getD` read
unchanged. Used by `mul_inner_array_coeff_fold` to unfold the inner multiplication fold. -/
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
/-- Folding with a step that discards each element returns the initial value unchanged.
Used in the zero-polynomial branch of `coeff_mul`, where the inner multiplication step
contributes nothing. -/
private theorem list_foldl_ignore (xs : List Nat) (init : R) :
    xs.foldl (fun acc _ => acc) init = init := by
  induction xs generalizing init with
  | nil =>
      rfl
  | cons _ xs ih =>
      simpa using ih init

/-- The array-loop `mulImpl` computes each coefficient by the schoolbook fold
`mulCoeffSum`; the workhorse behind `coeff_mul` and `mul_eq_impl`. -/
private theorem coeff_mulImpl [Add R] [Mul R] (p q : DensePoly R) (n : Nat) :
    (mulImpl p q).coeff n = mulCoeffSum p q n := by
  unfold mulImpl
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

omit [Zero R] [DecidableEq R] in
/-- A row scaled from the empty coefficient list adds nothing, so `mulRows`
with no `q`-coefficients returns the accumulator unchanged. -/
private theorem mulRows_nil [Add R] [Mul R] (ps acc : List R) :
    mulRows ([] : List R) ps acc = acc := by
  induction ps generalizing acc with
  | nil => rfl
  | cons x ps ih =>
      cases acc with
      | nil => rfl
      | cons a acc =>
          show a :: mulRows [] ps acc = a :: acc
          rw [ih]

omit [Zero R] [DecidableEq R] in
/-- `mulRow` writes into existing accumulator entries only, so it preserves
the accumulator length. -/
private theorem mulRow_length [Add R] [Mul R] (c : R) (acc qs : List R) :
    (mulRow c acc qs).length = acc.length := by
  induction acc generalizing qs with
  | nil => cases qs <;> rfl
  | cons a acc ih =>
      cases qs with
      | nil => rfl
      | cons q qs => simpa [mulRow] using ih qs

omit [Zero R] [DecidableEq R] in
/-- `mulRows` freezes or rewrites accumulator entries but never appends, so it
preserves the accumulator length. -/
private theorem mulRows_length [Add R] [Mul R] (qs ps acc : List R) :
    (mulRows qs ps acc).length = acc.length := by
  induction ps generalizing acc with
  | nil => rfl
  | cons x ps ih =>
      cases acc with
      | nil => cases qs <;> rfl
      | cons a acc =>
          cases qs with
          | nil => simpa [mulRows] using ih acc
          | cons q qs' => simp [mulRows, ih, mulRow_length]

omit [DecidableEq R] in
/-- Default-indexed read after one `mulRow`: index `n` gains the term
`c * qs.getD n` exactly when both the accumulator and the row still have an
entry there. -/
private theorem mulRow_getD [Add R] [Mul R] (c : R) (acc qs : List R) (n : Nat) :
    (mulRow c acc qs).getD n (Zero.zero : R) =
      if n < acc.length ∧ n < qs.length
      then acc.getD n (Zero.zero : R) + c * qs.getD n (Zero.zero : R)
      else acc.getD n (Zero.zero : R) := by
  induction acc generalizing qs n with
  | nil =>
      cases qs with
      | nil => simp [mulRow]
      | cons q qs => simp [mulRow]
  | cons a acc ih =>
      cases qs with
      | nil => simp [mulRow]
      | cons q qs =>
          cases n with
          | zero => simp [mulRow]
          | succ m => simpa [mulRow] using ih qs m

/-- The inner schoolbook fold over `j < m` at row `i` adds exactly the single
matching term `p.coeff i * q.coeff (n - i)` when the target index `n` is
reachable from row `i` within `m` columns, and nothing otherwise. -/
private theorem foldl_mulCoeffStep_range [Add R] [Mul R]
    (p q : DensePoly R) (n i : Nat) (c : R) (m : Nat) :
    (List.range m).foldl (mulCoeffStep p q n i) c =
      if i ≤ n ∧ n - i < m then c + p.coeff i * q.coeff (n - i) else c := by
  induction m with
  | zero =>
      rw [List.range_zero, List.foldl_nil, if_neg (by omega)]
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      unfold mulCoeffStep
      by_cases hlast : i + m = n
      · rw [if_neg (by omega : ¬(i ≤ n ∧ n - i < m)), if_pos hlast,
          if_pos (by omega : i ≤ n ∧ n - i < m + 1),
          show m = n - i by omega]
      · rw [if_neg hlast]
        by_cases h : i ≤ n ∧ n - i < m
        · rw [if_pos h, if_pos (by omega : i ≤ n ∧ n - i < m + 1)]
        · rw [if_neg h, if_neg (by omega : ¬(i ≤ n ∧ n - i < m + 1))]

omit [Zero R] [DecidableEq R] in
/-- Folds over the same list with pointwise-equal step functions agree. -/
private theorem list_foldl_congr {α : Type}
    (f g : R → α → R) (xs : List α) (init : R)
    (h : ∀ acc a, a ∈ xs → f acc a = g acc a) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons a xs ih =>
      rw [List.foldl_cons, List.foldl_cons, h init a (by simp)]
      exact ih _ fun acc b hb => h acc b (by simp [hb])

omit [DecidableEq R] in
/-- Reading a replicated zero list with default zero gives zero at every index. -/
private theorem list_getD_replicate (k n : Nat) :
    (List.replicate k (Zero.zero : R)).getD n (Zero.zero : R) = (Zero.zero : R) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      cases n with
      | zero => rfl
      | succ m => simpa [List.replicate_succ] using ih m

/-- `mulCoeffSum` collapsed to a single fold over the row index, with each
row's inner fold replaced by its closed form from `foldl_mulCoeffStep_range`. -/
private theorem mulCoeffSum_eq_singleFold [Add R] [Mul R]
    (p q : DensePoly R) (n : Nat) :
    mulCoeffSum p q n =
      (List.range p.size).foldl
        (fun c i =>
          if i ≤ n ∧ n - i < q.size
          then c + p.coeff i * q.coeff (n - i)
          else c)
        (Zero.zero : R) := by
  unfold mulCoeffSum
  exact list_foldl_congr _ _ _ _
    fun acc i _ => foldl_mulCoeffStep_range p q n i acc q.size

omit [DecidableEq R] in
/-- Default-indexed read of the full `mulRows` accumulator: index `n` collects
the terms `ps.getD i * qs.getD (n - i)` for each reachable row `i`, in
ascending row order, exactly as the `Array` loop of `mulImpl` does. The bound
hypothesis mirrors the in-bounds invariant of the `Array` accumulator. -/
private theorem mulRows_getD [Add R] [Mul R] (qs ps acc : List R) (n : Nat)
    (hbound : ∀ i, i < ps.length → ∀ j, j < qs.length → i + j < acc.length) :
    (mulRows qs ps acc).getD n (Zero.zero : R) =
      (List.range ps.length).foldl
        (fun c i =>
          if i ≤ n ∧ n - i < qs.length
          then c + ps.getD i (Zero.zero : R) * qs.getD (n - i) (Zero.zero : R)
          else c)
        (acc.getD n (Zero.zero : R)) := by
  induction ps generalizing acc n with
  | nil => rfl
  | cons x ps ih =>
      cases acc with
      | nil =>
          cases qs with
          | nil =>
              show (List.getD [] n (Zero.zero : R)) = _
              rw [list_foldl_congr _ (fun (c : R) (_ : Nat) => c) _ _
                  (fun c i _ => if_neg (by simp)),
                list_foldl_ignore]
          | cons q qs' =>
              exact absurd (hbound 0 (by simp) 0 (by simp)) (by simp)
      | cons a acc =>
          cases qs with
          | nil =>
              rw [mulRows_nil,
                list_foldl_congr _ (fun (c : R) (_ : Nat) => c) _ _
                  (fun c i _ => if_neg (by simp)),
                list_foldl_ignore]
          | cons q qs' =>
              show ((a + x * q) :: mulRows (q :: qs') ps (mulRow x acc qs')).getD n
                  (Zero.zero : R) = _
              simp only [List.length_cons]
              rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
              cases n with
              | zero =>
                  rw [List.getD_cons_zero,
                    if_pos ⟨Nat.le_refl 0, by simp⟩,
                    list_foldl_congr _ (fun (c : R) (_ : Nat) => c) _ _
                      (fun c i _ => if_neg (by omega)),
                    list_foldl_ignore,
                    List.getD_cons_zero, List.getD_cons_zero, List.getD_cons_zero]
              | succ m =>
                  rw [List.getD_cons_succ]
                  have hlen : m < qs'.length → m < acc.length := by
                    intro hm
                    have := hbound 0 (by simp) (m + 1) (by simpa using Nat.succ_lt_succ hm)
                    simpa using this
                  have hbound' : ∀ i, i < ps.length →
                      ∀ j, j < (q :: qs').length → i + j < (mulRow x acc qs').length := by
                    intro i hi j hj
                    rw [mulRow_length]
                    have := hbound (i + 1) (by simpa using Nat.succ_lt_succ hi) j hj
                    simp only [List.length_cons] at this
                    omega
                  rw [ih (mulRow x acc qs') m hbound']
                  have hinit : (mulRow x acc qs').getD m (Zero.zero : R) =
                      if 0 ≤ m + 1 ∧ m + 1 - 0 < (q :: qs').length
                      then (a :: acc).getD (m + 1) (Zero.zero : R) +
                        (x :: ps).getD 0 (Zero.zero : R) *
                          (q :: qs').getD (m + 1 - 0) (Zero.zero : R)
                      else (a :: acc).getD (m + 1) (Zero.zero : R) := by
                    rw [mulRow_getD]
                    by_cases hq : m < qs'.length
                    · rw [if_pos ⟨hlen hq, hq⟩, if_pos ⟨Nat.zero_le _, by simpa using Nat.succ_lt_succ hq⟩]
                      rw [List.getD_cons_succ, List.getD_cons_zero, Nat.sub_zero,
                        List.getD_cons_succ]
                    · rw [if_neg (fun h => hq h.2),
                        if_neg (by simpa [Nat.succ_lt_succ_iff] using hq),
                        List.getD_cons_succ]
                  rw [hinit]
                  exact list_foldl_congr _ _ _ _ fun c i _ => by
                    simp only [Nat.succ_eq_add_one, List.getD_cons_succ,
                      Nat.add_sub_add_right, Nat.add_le_add_iff_right,
                      List.length_cons]

/-- The list-walking specification `mul` satisfies the same coefficient law as
the `Array` loop: both fold the schoolbook terms into each output coefficient
in the identical order captured by `mulCoeffSum`. -/
private theorem coeff_mul_spec [Add R] [Mul R] (p q : DensePoly R) (n : Nat) :
    (mul p q).coeff n = mulCoeffSum p q n := by
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
    have hp_not : p.isZero = false := by
      cases hp : p.isZero <;> cases hq : q.isZero <;> simp [hp, hq] at hzero ⊢
    have hq_not : q.isZero = false := by
      cases hp : p.isZero <;> cases hq : q.isZero <;> simp [hp, hq] at hzero ⊢
    have hp_pos : 0 < p.size := (DensePoly.isZero_eq_false_iff p).1 hp_not
    have hq_pos : 0 < q.size := (DensePoly.isZero_eq_false_iff q).1 hq_not
    rw [coeff_ofCoeffs, toArray_getD_eq_getD, mulRows_getD, mulCoeffSum_eq_singleFold]
    · simp only [toList_getD_eq_coeff, length_toList, list_getD_replicate]
    · intro i hi j hj
      simp only [length_toList] at hi hj
      simp only [List.length_replicate]
      omega

/-- The specification `mul` and the `Array`-loop `mulImpl` compute the same
polynomial: both sides perform the same coefficient additions in the same
order, so no algebraic laws on `R` are needed. -/
theorem mul_eq_mulImpl [Add R] [Mul R] (p q : DensePoly R) :
    mul p q = mulImpl p q := by
  apply ext_coeff
  intro n
  rw [coeff_mul_spec, coeff_mulImpl]

/-- Register the `Array`-loop `mulImpl` as the compiled implementation of
`mul`. As with `trimTrailingZeros_eq_impl`, the `@[csimp]` swap is backed by a
proof, so the runtime loop is verified equal to the kernel-facing
specification. -/
@[csimp]
theorem mul_eq_impl : @mul = @mulImpl := by
  funext R _ _ _ _ p q
  exact mul_eq_mulImpl p q

instance [Add R] [Mul R] : Mul (DensePoly R) where
  mul := mul

/-- Characterising coefficient law for multiplication: each coefficient of `p * q` is computed by
the same nested schoolbook fold as the executable multiplication loop. -/
theorem coeff_mul [Add R] [Mul R] (p q : DensePoly R) (n : Nat) :
    (p * q).coeff n = mulCoeffSum p q n := by
  change (mul p q).coeff n = mulCoeffSum p q n
  exact coeff_mul_spec p q n

/-- A product stores at most `p.size + q.size - 1` coefficients. -/
theorem size_mul_le [Add R] [Mul R] (p q : DensePoly R) :
    (p * q).size ≤ p.size + q.size - 1 := by
  change (mul p q).size ≤ p.size + q.size - 1
  unfold mul
  by_cases hzero : p.isZero || q.isZero
  · rw [if_pos hzero, size_zero]
    exact Nat.zero_le _
  · rw [if_neg hzero]
    refine Nat.le_trans (size_ofCoeffs_le _) ?_
    simp [mulRows_length]

/-- Evaluate a polynomial using Horner's method. -/
@[expose]
def eval [Add R] [Mul R] (p : DensePoly R) (x : R) : R :=
  p.toArray.toList.reverse.foldl (fun acc coeff => acc * x + coeff) (Zero.zero : R)

omit [DecidableEq R] in
/-- List-level Horner evaluation, reading coefficients from low to high degree. -/
private def evalCoeffList [Add R] [Mul R] :
    List R → R → R
  | [], _ => Zero.zero
  | c :: cs, x => evalCoeffList cs x * x + c

omit [DecidableEq R] in
private theorem reverse_foldl_evalCoeffList [Add R] [Mul R] (coeffs : List R) (x : R) :
    coeffs.reverse.foldl (fun acc coeff => acc * x + coeff) (Zero.zero : R) =
      evalCoeffList coeffs x := by
  induction coeffs with
  | nil =>
      rfl
  | cons c cs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, evalCoeffList]
      rw [ih]

/-- Horner evaluation agrees with the list-level Horner form over stored coefficients. -/
private theorem eval_eq_evalCoeffList [Add R] [Mul R] (p : DensePoly R) (x : R) :
    eval p x = evalCoeffList p.toArray.toList x := by
  unfold eval
  exact reverse_foldl_evalCoeffList p.toArray.toList x

private theorem evalCoeffList_trimTrailingZerosList [Add R] [Mul R] (coeffs : List R) (x : R)
    (hzero : (Zero.zero : R) * x + (Zero.zero : R) = (Zero.zero : R)) :
    evalCoeffList (trimTrailingZerosList coeffs) x = evalCoeffList coeffs x := by
  induction coeffs with
  | nil =>
      rfl
  | cons c cs ih =>
      by_cases htrim : trimTrailingZerosList cs = [] ∧ c = (Zero.zero : R)
      · have htail : evalCoeffList cs x = (Zero.zero : R) := by
          rw [← ih, htrim.1]
          rfl
        rw [show trimTrailingZerosList (c :: cs) = [] by
          simp [trimTrailingZerosList, htrim.1, htrim.2]]
        change (Zero.zero : R) = evalCoeffList cs x * x + c
        rw [htail, htrim.2]
        exact hzero.symm
      · rw [show trimTrailingZerosList (c :: cs) = c :: trimTrailingZerosList cs by
          simp [trimTrailingZerosList, htrim]]
        change evalCoeffList (trimTrailingZerosList cs) x * x + c = evalCoeffList cs x * x + c
        rw [ih]

private theorem eval_ofList_eq_evalCoeffList [Add R] [Mul R] (coeffs : List R) (x : R)
    (hzero : (Zero.zero : R) * x + (Zero.zero : R) = (Zero.zero : R)) :
    eval (ofList coeffs : DensePoly R) x = evalCoeffList coeffs x := by
  rw [eval_eq_evalCoeffList]
  unfold ofList toArray ofCoeffs trimTrailingZeros
  simpa using evalCoeffList_trimTrailingZerosList (R := R) coeffs x hzero

private theorem ofList_coeff_range_eq (p : DensePoly R) {n : Nat} (hn : p.size ≤ n) :
    (ofList ((List.range n).map (fun i => p.coeff i)) : DensePoly R) = p := by
  apply ext_coeff
  intro i
  rw [coeff_ofList, list_getD_map_range]
  by_cases hi : i < n
  · simp [hi]
  · have hp : p.size ≤ i := Nat.le_trans hn (Nat.le_of_not_gt hi)
    simp [hi, coeff_eq_zero_of_size_le p hp]

omit [DecidableEq R] in
/-- Horner evaluation distributes over the padded coefficientwise sum, given
the zero-preservation and one-step distributivity laws. -/
private theorem evalCoeffList_zipPad_add [Add R] [Mul R] (xs ys : List R) (x : R)
    (hzero_add : (Zero.zero : R) + (Zero.zero : R) = (Zero.zero : R))
    (hzero_horner : (Zero.zero : R) * x + (Zero.zero : R) = (Zero.zero : R))
    (hstep : ∀ a b c d : R, (a + b) * x + (c + d) = (a * x + c) + (b * x + d)) :
    evalCoeffList (zipPad (· + ·) xs ys) x =
      evalCoeffList xs x + evalCoeffList ys x := by
  induction xs generalizing ys with
  | nil =>
      induction ys with
      | nil => simpa [zipPad, evalCoeffList] using hzero_add.symm
      | cons q qs ihq =>
          simp only [zipPad, evalCoeffList] at ihq ⊢
          rw [ihq, hstep, hzero_horner]
  | cons c cs ihp =>
      cases ys with
      | nil =>
          simp only [zipPad, evalCoeffList] at ihp ⊢
          rw [ihp [], hstep]
          simp only [evalCoeffList, hzero_horner]
      | cons q qs =>
          simp only [zipPad, evalCoeffList]
          rw [ihp qs, hstep]

omit [DecidableEq R] in
/-- Horner evaluation distributes over the padded coefficientwise difference. -/
private theorem evalCoeffList_zipPad_sub [Sub R] [Add R] [Mul R] (xs ys : List R) (x : R)
    (hzero_sub : (Zero.zero : R) - (Zero.zero : R) = (Zero.zero : R))
    (hzero_horner : (Zero.zero : R) * x + (Zero.zero : R) = (Zero.zero : R))
    (hstep : ∀ a b c d : R, (a - b) * x + (c - d) = (a * x + c) - (b * x + d)) :
    evalCoeffList (zipPad (· - ·) xs ys) x =
      evalCoeffList xs x - evalCoeffList ys x := by
  induction xs generalizing ys with
  | nil =>
      induction ys with
      | nil => simpa [zipPad, evalCoeffList] using hzero_sub.symm
      | cons q qs ihq =>
          simp only [zipPad, evalCoeffList] at ihq ⊢
          rw [ihq, hstep, hzero_horner]
  | cons c cs ihp =>
      cases ys with
      | nil =>
          simp only [zipPad, evalCoeffList] at ihp ⊢
          rw [ihp [], hstep]
          simp only [evalCoeffList, hzero_horner]
      | cons q qs =>
          simp only [zipPad, evalCoeffList]
          rw [ihp qs, hstep]

/-- Compose polynomials using Horner's method. -/
@[expose]
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
    rw [coeff_ofCoeffs, toArray_getD_eq_getD, zipPad_getD]
    simp only [length_toList, toList_getD_eq_coeff, size_zero, Nat.zero_max, coeff_zero]
    by_cases hn : n < (C c).size
    · rw [if_pos hn]
      have hn0 : n = 0 := by
        have h1 := size_C_of_ne_zero (c := c) hc
        omega
      subst hn0
      rw [coeff_C, if_pos rfl]
      exact hzero_add
    · rw [if_neg hn,
        coeff_eq_zero_of_size_le (C c) (Nat.le_of_not_gt hn)]

/-- Semiring-specialized composition law for constants. This packages the zero-addition
law needed by the generic `compose_C`. -/
@[simp, grind =] theorem compose_C_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (c : S) (q : DensePoly S) :
    compose (C c) q = C c :=
  compose_C c q (by grind)

/-- List-level Horner form for composition, reading coefficients from low to high degree. -/
@[expose]
def composeScalarCoeffList [Add R] [Mul R] :
    List R → DensePoly R → DensePoly R
  | [], _ => 0
  | c :: cs, q => C c + q * composeScalarCoeffList cs q

/-- `DensePoly.compose` agrees with the list-level Horner form over the stored coefficients
when the caller supplies the algebraic step that commutes a Horner tail past `q`. -/
theorem compose_eq_composeScalarCoeffList_of_step [Add R] [Mul R] (p q : DensePoly R)
    (hstep : ∀ acc c, acc * q + C c = C c + q * acc) :
    compose p q = composeScalarCoeffList p.toList q := by
  unfold compose toList
  induction p.toArray.toList with
  | nil => rfl
  | cons c cs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      exact hstep (composeScalarCoeffList cs q) c

/-- Iterated polynomial power used by the compose power-sum characterisation. -/
@[expose]
def composePower [One R] [Add R] [Mul R] (q : DensePoly R) : Nat → DensePoly R
  | 0 => C (1 : R)
  | n + 1 => q * composePower q n

/-- List-backed power-sum form for composition, starting at a coefficient base index. -/
@[expose]
def composeCoeffPowerSumFrom [One R] [Add R] [Mul R] :
    List R → Nat → DensePoly R → DensePoly R
  | [], _, _ => 0
  | c :: cs, base, q =>
      C c * composePower q base + composeCoeffPowerSumFrom cs (base + 1) q

/-- Coefficient-indexed bounded power-sum form for composition. -/
@[expose]
def composeCoeffPowerSumUpTo [One R] [Add R] [Mul R]
    (coeff : Nat → R) :
    Nat → Nat → DensePoly R → DensePoly R
  | 0, _, _ => 0
  | n + 1, base, q =>
      C (coeff base) * composePower q base +
        composeCoeffPowerSumUpTo coeff n (base + 1) q

/-- `composeCoeffPowerSumFrom` over a consecutive range is the bounded coefficient-indexed
power sum. -/
theorem composeCoeffPowerSumFrom_range_eq_upTo [One R] [Add R] [Mul R]
    (coeff : Nat → R) (q : DensePoly R) :
    ∀ n base,
      composeCoeffPowerSumFrom ((List.range n).map (fun i => coeff (base + i))) base q =
        composeCoeffPowerSumUpTo coeff n base q
  | 0, base => by
      simp [composeCoeffPowerSumFrom, composeCoeffPowerSumUpTo]
  | n + 1, base => by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      simp only [composeCoeffPowerSumFrom, composeCoeffPowerSumUpTo]
      congr 1
      simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using composeCoeffPowerSumFrom_range_eq_upTo coeff q n (base + 1)

omit [DecidableEq R] in
/-- List extensionality through default-indexed reads: two lists of equal length that agree
under `getD` at every in-bounds index are equal. Used by `toList_eq_coeff_range` to
identify the stored coefficient list with the range of coefficient reads. -/
private theorem list_eq_of_length_eq_of_getD_eq
    {xs ys : List R}
    (hlen : xs.length = ys.length)
    (hget : ∀ i, i < xs.length → xs.getD i (Zero.zero : R) = ys.getD i (Zero.zero : R)) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
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

/-- The spec-level coefficient list is the range of coefficient reads over `p.size`. -/
theorem toList_eq_coeff_range (p : DensePoly R) :
    p.toList = (List.range p.size).map (fun i => p.coeff i) := by
  apply list_eq_of_length_eq_of_getD_eq
  · simp [toList, toArray, size]
  · intro i hi
    have hi_size : i < p.size := by
      simpa [toList, toArray, size] using hi
    rw [toList_getD_eq_coeff, list_getD_map_range]
    simp [hi_size]

/-- Index-carrying derivative walk: entry `j` of `derivList i cs` is
`((i + j + 1 : Nat) : R) * cs[j]`. Applied at `i = 0` to the coefficient
tail, it produces the formal-derivative coefficients in one cons walk. -/
@[expose]
def derivList [NatCast R] [Mul R] : Nat → List R → List R
  | _, [] => []
  | i, c :: cs => ((i + 1 : Nat) : R) * c :: derivList (i + 1) cs

/-- Default-indexed read of the derivative walk. -/
private theorem derivList_getD [NatCast R] [Mul R] (i : Nat) (cs : List R) (n : Nat) :
    (derivList i cs).getD n (Zero.zero : R) =
      if n < cs.length
      then ((i + n + 1 : Nat) : R) * cs.getD n (Zero.zero : R)
      else (Zero.zero : R) := by
  induction cs generalizing i n with
  | nil => simp [derivList]
  | cons c cs ih =>
      cases n with
      | zero => simp [derivList]
      | succ m =>
          simp only [derivList, List.getD_cons_succ, List.length_cons,
            Nat.add_lt_add_iff_right]
          rw [ih]
          have harith : i + 1 + m + 1 = i + (m + 1) + 1 := by omega
          rw [harith]

/-- Formal derivative. The coefficient of `x^i` becomes `(i + 1) * a_(i+1)`.

Kernel-facing specification: one cons walk of the coefficient tail. Compiled
code runs the `Array.ofFn` loop `derivativeImpl` via the `@[csimp]` proof
`derivative_eq_impl`. -/
@[expose]
noncomputable def derivative [NatCast R] [Mul R] (p : DensePoly R) : DensePoly R :=
  ofCoeffs (derivList 0 (p.toList.drop 1)).toArray

/-- Runtime implementation of `derivative`: one `Array.ofFn` allocation
(value-equal to `derivative` by `derivative_eq_impl`, registered `@[csimp]`). -/
@[expose]
def derivativeImpl [NatCast R] [Mul R] (p : DensePoly R) : DensePoly R :=
  ofCoeffs (Array.ofFn (n := p.size - 1) fun i => ((i.1 + 1 : Nat) : R) * p.coeff (i.1 + 1))

/-- Default-indexed read of the spec derivative coefficients. -/
private theorem derivative_coeffs_getD [NatCast R] [Mul R] (p : DensePoly R) (n : Nat) :
    (derivList 0 (p.toList.drop 1)).getD n (Zero.zero : R) =
      if n < p.size - 1
      then ((n + 1 : Nat) : R) * p.coeff (n + 1)
      else (Zero.zero : R) := by
  rw [derivList_getD]
  simp only [List.length_drop, length_toList, Nat.zero_add]
  by_cases hn : n < p.size - 1
  · rw [if_pos hn, if_pos hn]
    have hdrop : (p.toList.drop 1).getD n (Zero.zero : R) =
        p.toList.getD (1 + n) (Zero.zero : R) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
    rw [hdrop, Nat.add_comm 1 n, toList_getD_eq_coeff]
  · rw [if_neg hn, if_neg hn]

/-- The spec `derivative` and the `Array.ofFn` runtime loop compute the same
polynomial. -/
theorem derivative_eq_derivativeImpl [NatCast R] [Mul R] (p : DensePoly R) :
    derivative p = derivativeImpl p := by
  apply ext_coeff
  intro n
  unfold derivative derivativeImpl
  rw [coeff_ofCoeffs, coeff_ofCoeffs, toArray_getD_eq_getD,
    derivative_coeffs_getD, array_ofFn_getD]
  by_cases hn : n < p.size - 1
  · rw [if_pos hn, dif_pos hn]
  · rw [if_neg hn, dif_neg hn]

/-- Register the `Array.ofFn` loop as the compiled implementation of
`derivative`. -/
@[csimp]
theorem derivative_eq_impl : @derivative = @derivativeImpl := by
  funext R _ _ _ _ p
  exact derivative_eq_derivativeImpl p

/-- The derivative walk preserves list length. -/
private theorem derivList_length [NatCast R] [Mul R] (i : Nat) (cs : List R) :
    (derivList i cs).length = cs.length := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs ih => simpa [derivList] using ih (i + 1)

/-- The derivative stores at most one fewer coefficient than its input. -/
theorem size_derivative_le [NatCast R] [Mul R] (p : DensePoly R) :
    (derivative p).size ≤ p.size - 1 := by
  unfold derivative
  refine Nat.le_trans (size_ofCoeffs_le _) ?_
  simp [derivList_length]

/-- Coefficient law for addition. The explicit zero law is needed because the generic
`Add`/`Zero` interface does not imply `0 + 0 = 0`. -/
theorem coeff_add [Add R] (p q : DensePoly R) (n : Nat)
    (hzero : (Zero.zero : R) + (Zero.zero : R) = (Zero.zero : R)) :
    (p + q).coeff n = (p.coeff n + q.coeff n) := by
  change (add p q).coeff n = (p.coeff n + q.coeff n)
  unfold add
  rw [coeff_ofCoeffs, toArray_getD_eq_getD, zipPad_getD]
  simp only [length_toList, toList_getD_eq_coeff]
  by_cases hn : n < max p.size q.size
  · rw [if_pos hn]
  · have hmax : max p.size q.size ≤ n := Nat.le_of_not_gt hn
    have hp : p.size ≤ n := Nat.le_trans (Nat.le_max_left p.size q.size) hmax
    have hq : q.size ≤ n := Nat.le_trans (Nat.le_max_right p.size q.size) hmax
    rw [if_neg hn, coeff_eq_zero_of_size_le p hp, coeff_eq_zero_of_size_le q hq, hzero]

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
  rw [coeff_ofCoeffs, toArray_getD_eq_getD, zipPad_getD]
  simp only [length_toList, toList_getD_eq_coeff]
  by_cases hn : n < max p.size q.size
  · rw [if_pos hn]
  · have hmax : max p.size q.size ≤ n := Nat.le_of_not_gt hn
    have hp : p.size ≤ n := Nat.le_trans (Nat.le_max_left p.size q.size) hmax
    have hq : q.size ≤ n := Nat.le_trans (Nat.le_max_right p.size q.size) hmax
    rw [if_neg hn, coeff_eq_zero_of_size_le p hp, coeff_eq_zero_of_size_le q hq, hzero]

/-- Ring-specialized coefficient law for subtraction. -/
@[simp, grind =] theorem coeff_sub_ring {S : Type u}
    [Zero S] [Sub S] [Lean.Grind.Ring S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat)
    (hzero : SubZeroLaw S := by infer_instance) :
    (p - q).coeff n = p.coeff n - q.coeff n :=
  coeff_sub p q n hzero.sub_zero_zero

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

/-- Evaluation law for addition. The explicit laws package the zero-preservation and
one-step Horner distributivity needed by the generic `Add`/`Mul` interface. -/
theorem eval_add [Add R] [Mul R] (p q : DensePoly R) (x : R)
    (hzero_add : (Zero.zero : R) + (Zero.zero : R) = (Zero.zero : R))
    (hzero_horner : (Zero.zero : R) * x + (Zero.zero : R) = (Zero.zero : R))
    (hstep : ∀ a b c d : R, (a + b) * x + (c + d) = (a * x + c) + (b * x + d)) :
    eval (p + q) x = eval p x + eval q x := by
  have hadd : eval (p + q) x =
      evalCoeffList (zipPad (· + ·) p.toList q.toList) x := by
    change eval (add p q) x = _
    unfold add
    exact eval_ofList_eq_evalCoeffList _ x hzero_horner
  rw [hadd, eval_eq_evalCoeffList, eval_eq_evalCoeffList]
  exact evalCoeffList_zipPad_add p.toList q.toList x hzero_add hzero_horner hstep

/-- Semiring-specialized evaluation law for addition. -/
@[simp, grind =] theorem eval_add_semiring {S : Type u}
    [Lean.Grind.Semiring S] [DecidableEq S]
    (p q : DensePoly S) (x : S) :
    eval (p + q) x = eval p x + eval q x :=
  eval_add p q x (by grind)
    (by
      change (0 : S) * x + (0 : S) = (0 : S)
      rw [Lean.Grind.Semiring.zero_mul]
      exact Lean.Grind.Semiring.add_zero 0)
    (by grind)

/-- Evaluation law for subtraction. The explicit laws package the zero-preservation and
one-step Horner distributivity needed by the generic `Sub`/`Mul` interface. -/
theorem eval_sub [Sub R] [Add R] [Mul R] (p q : DensePoly R) (x : R)
    (hzero_sub : (Zero.zero : R) - (Zero.zero : R) = (Zero.zero : R))
    (hzero_horner : (Zero.zero : R) * x + (Zero.zero : R) = (Zero.zero : R))
    (hstep : ∀ a b c d : R, (a - b) * x + (c - d) = (a * x + c) - (b * x + d)) :
    eval (p - q) x = eval p x - eval q x := by
  have hsub : eval (p - q) x =
      evalCoeffList (zipPad (· - ·) p.toList q.toList) x := by
    change eval (sub p q) x = _
    unfold sub
    exact eval_ofList_eq_evalCoeffList _ x hzero_horner
  rw [hsub, eval_eq_evalCoeffList, eval_eq_evalCoeffList]
  exact evalCoeffList_zipPad_sub p.toList q.toList x hzero_sub hzero_horner hstep

/-- Ring-specialized evaluation law for subtraction. -/
@[simp, grind =] theorem eval_sub_ring {S : Type u}
    [Lean.Grind.Ring S] [DecidableEq S]
    (p q : DensePoly S) (x : S) :
    eval (p - q) x = eval p x - eval q x :=
  eval_sub p q x (by grind)
    (by
      change (0 : S) * x + (0 : S) = (0 : S)
      rw [Lean.Grind.Semiring.zero_mul]
      exact Lean.Grind.Semiring.add_zero 0)
    (by grind)

/-- Evaluation law for negation, expressed through subtraction from zero. -/
theorem eval_neg [Sub R] [Add R] [Mul R] (p : DensePoly R) (x : R)
    (hzero_sub : (Zero.zero : R) - (Zero.zero : R) = (Zero.zero : R))
    (hzero_horner : (Zero.zero : R) * x + (Zero.zero : R) = (Zero.zero : R))
    (hstep : ∀ a b c d : R, (a - b) * x + (c - d) = (a * x + c) - (b * x + d)) :
    eval (-p) x = (Zero.zero : R) - eval p x := by
  change eval (sub (0 : DensePoly R) p) x = (Zero.zero : R) - eval p x
  have h := eval_sub (0 : DensePoly R) p x hzero_sub hzero_horner hstep
  exact h

/-- Ring-specialized evaluation law for negation. -/
@[simp, grind =] theorem eval_neg_ring {S : Type u}
    [Lean.Grind.Ring S] [DecidableEq S]
    (p : DensePoly S) (x : S)
    (hneg : ZeroSubNegLaw S := by infer_instance) :
    eval (-p) x = -(eval p x) := by
  have h := eval_neg p x (by grind)
    (by
      change (0 : S) * x + (0 : S) = (0 : S)
      rw [Lean.Grind.Semiring.zero_mul]
      exact Lean.Grind.Semiring.add_zero 0)
    (by grind)
  rw [h]
  exact hneg.zero_sub_eq_neg (eval p x)

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
  rw [coeff_ofCoeffs, toArray_getD_eq_getD, derivative_coeffs_getD]
  by_cases hn : n < p.size - 1
  · rw [if_pos hn]
  · have hp : p.size ≤ n + 1 := by omega
    rw [if_neg hn, coeff_eq_zero_of_size_le p hp, hzero]

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
