/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
import HexBasic.List
public import HexBasic.ArrayDecEq
public import HexBasic.ExtTreeMap
public import HexBasic.OfFn

@[expose] public section

/-!
Exponent vectors, their arithmetic, and the explicit monomial-order
interface used by `Hex.MvPoly`.
-/

namespace Hex

open scoped Hex

/-- An exponent vector for `n` ordered variables. -/
abbrev Mono (n : Nat) := Vector Nat n

namespace Mono

/-- The constant monomial. -/
def zero : Mono n :=
  Hex.Vector.ofFn' fun _ => 0

instance : Inhabited (Mono n) :=
  ⟨zero⟩

/-- The monomial consisting of one copy of variable `i`. -/
def unit (i : Fin n) : Mono n :=
  Hex.Vector.ofFn' fun j => if j = i then 1 else 0

/-- Monomial multiplication, represented by pointwise exponent addition. -/
def mul (a b : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => a[i] + b[i]

/-- Multiply every exponent by `k`. -/
def scale (k : Nat) (m : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => k * m[i]

/-- Whether `a` divides `b`, i.e. whether every exponent of `a` is at
most the corresponding exponent of `b`. -/
def dvd (a b : Mono n) : Bool :=
  decide (∀ i : Fin n, a[i] ≤ b[i])

/-- The exact quotient `b / a`, returning `none` when `a` does not
divide `b`. -/
def div (a b : Mono n) : Option (Mono n) :=
  if h : ∀ i : Fin n, a[i] ≤ b[i] then
    some <| Hex.Vector.ofFn' fun i => b[i] - a[i]
  else
    none

/-- Pointwise maximum of two monomials. -/
def lcm (a b : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => max a[i] b[i]

/-- Pointwise minimum of two monomials. -/
def gcd (a b : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => min a[i] b[i]

/-- Total degree of a monomial. -/
def degree (m : Mono n) : Nat :=
  (List.finRange n).foldl (fun acc i => acc + m[i]) 0

/-- Exponent of variable `i` in a monomial. -/
def degreeOf (i : Fin n) (m : Mono n) : Nat :=
  m[i]

/-- Variables occurring with positive exponent, in increasing index order. -/
def support (m : Mono n) : List (Fin n) :=
  (List.finRange n).filter fun i => m[i] != 0

/-- Rename variables, adding exponents when several source variables map
to the same target variable. -/
def rename {k : Nat} (f : Fin n → Fin k) (m : Mono n) : Mono k :=
  Hex.Vector.ofFn' fun j =>
    (List.finRange n).foldl
      (fun acc i => acc + if f i = j then m[i] else 0) 0

/-- Increase the exponent of variable `i` by one. -/
def succAt (i : Fin n) (m : Mono n) : Mono n :=
  mul m (unit i)

/-- Remove the first exponent from a nonempty monomial. -/
def dropHead (m : Mono (n + 1)) : Mono n :=
  Hex.Vector.ofFn' fun i => m[i.succ]

/-- Add an exponent at the front of a monomial. -/
def prepend (e : Nat) (m : Mono n) : Mono (n + 1) :=
  Hex.Vector.ofFn' fun i =>
    if h : i.val = 0 then e else m[i.val - 1]'(by omega)

/-- All decompositions `a * b = m`. Each exponent is split independently,
so the list has `∏ i, (m[i] + 1)` entries. -/
def splits : {n : Nat} → Mono n → List (Mono n × Mono n)
  | 0, _ => [(zero, zero)]
  | _ + 1, m =>
      (List.range (m.head + 1)).flatMap fun k =>
        (splits (dropHead m)).map fun (a, b) =>
          (prepend k a, prepend (m.head - k) b)

/-- Exponentiation by repeated squaring, used here so monomial evaluation
does not depend on a coefficient type's choice of `Pow` implementation. -/
def powBySq [One R] [Mul R] (a : R) : Nat → R
  | 0 => 1
  | k + 1 =>
      let q := powBySq a ((k + 1) / 2)
      let q2 := q * q
      if (k + 1) % 2 = 0 then q2 else q2 * a
termination_by k => k
decreasing_by omega

/-- Repeated-squaring exponentiation agrees with the semiring power. -/
theorem powBySq_eq_pow [Lean.Grind.Semiring R] (a : R) (k : Nat) :
    powBySq a k = a ^ k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero =>
          rw [powBySq, Lean.Grind.Semiring.pow_zero]
      | succ k =>
          have hlt : (k + 1) / 2 < k + 1 :=
            Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
          rw [powBySq, ih ((k + 1) / 2) hlt]
          by_cases heven : (k + 1) % 2 = 0
          · rw [ite_eq_left heven, ← Lean.Grind.Semiring.pow_add]
            have hdecomp := Nat.mod_add_div (k + 1) 2
            congr 1
            omega
          · rw [ite_eq_right heven, ← Lean.Grind.Semiring.pow_add,
              ← Lean.Grind.Semiring.pow_succ]
            have hdecomp := Nat.mod_add_div (k + 1) 2
            have hmod := Nat.mod_two_eq_zero_or_one (k + 1)
            congr 1
            omega

/-- Evaluate a monomial at `x`, using logarithmic exponentiation for each
variable. -/
def prod [One R] [Mul R] (x : Fin n → R) (m : Mono n) : R :=
  (List.finRange n).foldl (fun acc i => acc * powBySq (x i) m[i]) 1

/-- Plain lexicographic comparison, with the first variable most
significant. -/
def lex (a b : Mono n) : Ordering :=
  List.compareLex compare a.toList b.toList

/-- Graded lexicographic comparison: total degree first, then `lex`. -/
def grlex (a b : Mono n) : Ordering :=
  compareLex (fun x y => compare (degree x) (degree y)) lex a b

/-- Reverse-lexicographic tie breaker used by `grevlex`. -/
def revlex (a b : Mono n) : Ordering :=
  List.compareLex (fun x y => compare y x) a.toList.reverse b.toList.reverse

/-- Graded reverse lexicographic comparison: total degree first; among
equal-degree monomials, the monomial with the larger exponent in the last
differing variable compares smaller. -/
def grevlex (a b : Mono n) : Ordering :=
  compareLex (fun x y => compare (degree x) (degree y)) revlex a b

instance instLexTransCmp : Std.TransCmp (@lex n) where
  eq_swap {a b} := by
    unfold lex
    exact Std.OrientedCmp.eq_swap
      (cmp := List.compareLex (compare (α := Nat)))
  isLE_trans {a b c} := by
    unfold lex
    exact Std.TransCmp.isLE_trans
      (cmp := List.compareLex (compare (α := Nat)))

instance instLexLawfulEqCmp : Std.LawfulEqCmp (@lex n) where
  compare_self {a} := by
    unfold lex
    exact Std.ReflCmp.compare_self
      (cmp := List.compareLex (compare (α := Nat)))
  eq_of_compare {a b} h := by
    have hlist : a.toList = b.toList :=
      Std.LawfulEqCmp.eq_of_compare
        (cmp := List.compareLex (compare (α := Nat))) h
    exact Vector.toList_inj.mp hlist

instance instRevlexTransCmp : Std.TransCmp (@revlex n) where
  eq_swap {a b} := by
    unfold revlex
    exact Std.OrientedCmp.eq_swap
      (cmp := List.compareLex (fun x y : Nat => compare y x))
  isLE_trans {a b c} := by
    unfold revlex
    exact Std.TransCmp.isLE_trans
      (cmp := List.compareLex (fun x y : Nat => compare y x))

instance instRevlexLawfulEqCmp : Std.LawfulEqCmp (@revlex n) where
  compare_self {a} := by
    unfold revlex
    exact Std.ReflCmp.compare_self
      (cmp := List.compareLex (fun x y : Nat => compare y x))
  eq_of_compare {a b} h := by
    have hrev : a.toList.reverse = b.toList.reverse :=
      Std.LawfulEqCmp.eq_of_compare
        (cmp := List.compareLex (fun x y : Nat => compare y x)) h
    exact Vector.toList_inj.mp (List.reverse_inj.mp hrev)

private instance instDegreeTransCmp :
    Std.TransCmp (fun a b : Mono n => compare (degree a) (degree b)) := by
  change Std.TransCmp (compareOn degree)
  infer_instance

instance instGrlexTransCmp : Std.TransCmp (@grlex n) := by
  unfold grlex
  infer_instance

instance instGrlexLawfulEqCmp : Std.LawfulEqCmp (@grlex n) where
  compare_self {a} := by
    simp [grlex, Std.ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    have hp : degree a = degree b ∧ a = b := by
      simpa [grlex, compareLex, Ordering.then_eq_eq] using h
    exact hp.2

instance instGrevlexTransCmp : Std.TransCmp (@grevlex n) := by
  unfold grevlex
  infer_instance

instance instGrevlexLawfulEqCmp : Std.LawfulEqCmp (@grevlex n) where
  compare_self {a} := by
    simp [grevlex, Std.ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    have hp : degree a = degree b ∧ a = b := by
      simpa [grevlex, compareLex, Ordering.then_eq_eq] using h
    exact hp.2

end Mono

/-- Laws needed of a comparator by leading-term and reduction algorithms.
Storage itself uses the inherited `TransCmp` and `LawfulEqCmp` laws. -/
class IsMonomialOrder {n : Nat} (cmp : Mono n → Mono n → Ordering) : Prop
    extends Std.TransCmp cmp, Std.LawfulEqCmp cmp where
  /-- The constant monomial is least. -/
  zero_le : ∀ m, cmp Mono.zero m ≠ .gt
  /-- Multiplying both sides by the same monomial preserves comparison. -/
  mul_mono : ∀ a b c, cmp a b = cmp (Mono.mul a c) (Mono.mul b c)
  /-- Strict comparison is well founded. -/
  wf : WellFounded fun a b => cmp a b = .lt

namespace Mono

/-- Every exponent of the zero monomial is zero. -/
@[simp] theorem getElem_zero (i : Fin n) : (zero : Mono n)[i] = 0 := by
  simp [zero]

/-- A unit monomial has exponent one at its selected variable and zero
elsewhere. -/
@[simp] theorem getElem_unit (i j : Fin n) :
    (unit i : Mono n)[j] = if j = i then 1 else 0 := by
  simp [unit]

/-- Monomial multiplication adds exponents pointwise. -/
@[simp] theorem getElem_mul (a b : Mono n) (i : Fin n) :
    (mul a b)[i] = a[i] + b[i] := by
  simp [mul]

/-- The zero monomial is a left identity for monomial multiplication. -/
@[simp] theorem zero_mul (m : Mono n) : mul zero m = m := by
  apply Vector.ext
  intro i hi
  simp [mul, zero]

/-- The zero monomial is a right identity for monomial multiplication. -/
@[simp] theorem mul_zero (m : Mono n) : mul m zero = m := by
  apply Vector.ext
  intro i hi
  simp [mul, zero]

/-- Monomial multiplication is associative. -/
theorem mul_assoc (a b c : Mono n) :
    mul (mul a b) c = mul a (mul b c) := by
  apply Vector.ext
  intro i hi
  simp [mul, Nat.add_assoc]

/-- Monomial multiplication is commutative. -/
theorem mul_comm (a b : Mono n) : mul a b = mul b a := by
  apply Vector.ext
  intro i hi
  simp [mul, Nat.add_comm]

/-- Scaling a monomial multiplies every exponent by the scale. -/
@[simp] theorem getElem_scale (k : Nat) (m : Mono n) (i : Fin n) :
    (scale k m)[i] = k * m[i] := by
  simp [scale]

/-- Scaling by zero yields the zero monomial. -/
@[simp] theorem zero_scale (m : Mono n) : scale 0 m = zero := by
  apply Vector.ext
  intro i hi
  simp [scale, zero]

/-- Every scaling of the zero monomial is zero. -/
@[simp] theorem scale_zero (k : Nat) : scale k (zero : Mono n) = zero := by
  apply Vector.ext
  intro i hi
  simp [scale, zero]

/-- Scaling by one leaves a monomial unchanged. -/
@[simp] theorem one_scale (m : Mono n) : scale 1 m = m := by
  apply Vector.ext
  intro i hi
  simp [scale]

/-- Scaling by a sum is multiplication of the separately scaled monomials. -/
theorem add_scale (a b : Nat) (m : Mono n) :
    scale (a + b) m = mul (scale a m) (scale b m) := by
  apply Vector.ext
  intro i hi
  simp [scale, mul, Nat.add_mul]

/-- Every monomial is the product of its scaled unit monomials. -/
theorem mul_units (m : Mono n) :
    (List.finRange n).foldl
        (fun acc i => mul acc (scale m[i] (unit i)))
        zero =
      m := by
  apply Vector.ext
  intro j hj
  let r : Fin n := ⟨j, hj⟩
  have get_fold : ∀ (xs : List (Fin n)) (acc : Mono n),
      (xs.foldl
        (fun acc i => mul acc (scale m[i] (unit i))) acc)[r] =
      xs.foldl
        (fun acc i => acc + (scale m[i] (unit i))[r])
        acc[r] := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih, getElem_mul]
  change
    ((List.finRange n).foldl
      (fun acc i => mul acc (scale m[i] (unit i))) zero)[r] = m[r]
  rw [get_fold, getElem_zero]
  calc
    (List.finRange n).foldl
        (fun acc i => acc + (scale m[i] (unit i))[r]) 0 =
        (List.finRange n).foldl
          (fun acc i => acc + if i = r then m[i] else 0) 0 := by
            apply List.foldl_congr
            intro acc i _
            rw [getElem_scale, getElem_unit]
            by_cases hir : i = r
            · subst i
              simp
            · simp [hir, Ne.symm hir]
    _ = 0 + m[r] :=
      List.foldl_add_single _ _ _ _
        (List.mem_finRange r) (List.nodup_finRange n)
    _ = m[r] := by omega

/-- The monomial least common multiple takes pointwise maximum exponents. -/
@[simp] theorem getElem_lcm (a b : Mono n) (i : Fin n) :
    (lcm a b)[i] = max a[i] b[i] := by
  simp [lcm]

/-- The monomial greatest common divisor takes pointwise minimum exponents. -/
@[simp] theorem getElem_gcd (a b : Mono n) (i : Fin n) :
    (gcd a b)[i] = min a[i] b[i] := by
  simp [gcd]

/-- Dropping the head shifts every remaining exponent down one coordinate. -/
@[simp] theorem getElem_dropHead (m : Mono (n + 1)) (i : Fin n) :
    (dropHead m)[i] = m[i.succ] := by
  simp [dropHead]

/-- The head of a prepended monomial is the supplied exponent. -/
@[simp] theorem getElem_prepend_zero (e : Nat) (m : Mono n) :
    (prepend e m)[0] = e := by
  simp [prepend]

/-- The tail of a prepended monomial contains the original exponents. -/
@[simp] theorem getElem_prepend_succ (e : Nat) (m : Mono n) (i : Fin n) :
    (prepend e m)[i.succ] = m[i] := by
  simp [prepend]

/-- Dropping a freshly prepended exponent recovers the original monomial. -/
@[simp] theorem dropHead_prepend (e : Nat) (m : Mono n) :
    dropHead (prepend e m) = m := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  change (dropHead (prepend e m))[j] = m[j]
  rw [getElem_dropHead, getElem_prepend_succ]

/-- Prepending a monomial's head to its tail reconstructs it. -/
theorem prepend_head_dropHead (m : Mono (n + 1)) :
    prepend m.head (dropHead m) = m := by
  apply Vector.ext
  intro i hi
  by_cases hzero : i = 0
  · subst i
    unfold prepend
    rw [Hex.Vector.getElem_ofFn' _ 0 (by omega)]
    simp only [↓reduceDIte]
    change m[0] = m[0]
    rfl
  · unfold prepend
    rw [Hex.Vector.getElem_ofFn' _ i hi]
    split
    · contradiction
    · unfold dropHead
      rw [Hex.Vector.getElem_ofFn' _ (i - 1) (by omega)]
      change m[(i - 1) + 1] = m[i]
      exact getElem_congr_idx (c := m) (by omega)

/-- Multiplication distributes across prepended exponent vectors. -/
theorem mul_prepend (ea eb : Nat) (a b : Mono n) :
    mul (prepend ea a) (prepend eb b) =
      prepend (ea + eb) (mul a b) := by
  have get_ofFn {r : Nat} (g : Fin r → Nat) (j : Fin r) :
      (Hex.Vector.ofFn' g).get j = g j := by
    change (Hex.Vector.ofFn' g)[j.val] = g j
    rw [Hex.Vector.getElem_ofFn' g j.val j.isLt]
  have get_mul {r : Nat} (x y : Mono r) (j : Fin r) :
      (mul x y).get j = x.get j + y.get j := by
    unfold mul
    rw [get_ofFn]
    change x.get j + y.get j = x.get j + y.get j
    rfl
  apply Vector.ext
  intro i hi
  let t : Fin (n + 1) := ⟨i, hi⟩
  change (mul (prepend ea a) (prepend eb b)).get t =
    (prepend (ea + eb) (mul a b)).get t
  rw [get_mul]
  by_cases hzero : t.val = 0
  · have hi0 : i = 0 := by simpa [t] using hzero
    subst i
    unfold prepend
    rw [get_ofFn, get_ofFn, get_ofFn]
    have ht : t = 0 := Fin.ext hzero
    simp [ht]
  · unfold prepend
    rw [get_ofFn, get_ofFn, get_ofFn]
    simp only [hzero, ↓reduceDIte]
    let j : Fin n := ⟨t.val - 1, by omega⟩
    change a.get j + b.get j = (mul a b).get j
    exact (get_mul a b j).symm

/-- Dropping the head commutes with monomial multiplication. -/
theorem dropHead_mul (a b : Mono (n + 1)) :
    dropHead (mul a b) = mul (dropHead a) (dropHead b) := by
  have get_ofFn {r : Nat} (g : Fin r → Nat) (j : Fin r) :
      (Hex.Vector.ofFn' g).get j = g j := by
    change (Hex.Vector.ofFn' g)[j.val] = g j
    rw [Hex.Vector.getElem_ofFn' g j.val j.isLt]
  have get_mul {r : Nat} (x y : Mono r) (j : Fin r) :
      (mul x y).get j = x.get j + y.get j := by
    unfold mul
    rw [get_ofFn]
    change x.get j + y.get j = x.get j + y.get j
    rfl
  have get_drop (x : Mono (n + 1)) (j : Fin n) :
      (dropHead x).get j = x.get j.succ := by
    unfold dropHead
    rw [get_ofFn]
    rfl
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  change (dropHead (mul a b)).get j =
    (mul (dropHead a) (dropHead b)).get j
  rw [get_drop, get_mul, get_mul, get_drop, get_drop]

/-- Boolean monomial divisibility is pointwise exponent comparison. -/
theorem dvd_eq_true_iff (a b : Mono n) :
    dvd a b = true ↔ ∀ i : Fin n, a[i] ≤ b[i] := by
  simp [dvd]

/-- Exact monomial division returns a quotient exactly when multiplying it
back recovers the dividend. -/
theorem div_eq_some_iff (a b q : Mono n) :
    div a b = some q ↔ Mono.mul a q = b := by
  have get_ofFn (f : Fin n → Nat) (j : Fin n) :
      (Hex.Vector.ofFn' f).get j = f j := by
    change (Hex.Vector.ofFn' f)[j.val] = f j
    rw [Hex.Vector.getElem_ofFn' f j.val j.isLt]
  constructor
  · intro hdiv
    unfold div at hdiv
    split at hdiv
    next hle =>
      simp only [Option.some.injEq] at hdiv
      subst q
      apply Vector.ext
      intro i hi
      unfold mul
      rw [Hex.Vector.getElem_ofFn' _ i hi]
      let j : Fin n := ⟨i, hi⟩
      change a.get j + (Hex.Vector.ofFn' fun i => b[i] - a[i]).get j = b.get j
      rw [get_ofFn]
      change a.get j + (b.get j - a.get j) = b.get j
      have hj := hle j
      change a.get j ≤ b.get j at hj
      omega
    next =>
      contradiction
  · intro hmul
    have hle : ∀ i : Fin n, a[i] ≤ b[i] := by
      intro i
      have hi := congrArg (fun m : Mono n => m[i]) hmul
      rw [getElem_mul] at hi
      omega
    rw [div, dite_eq_left hle]
    congr 1
    apply Vector.ext
    intro i hi
    let j : Fin n := ⟨i, hi⟩
    have hi' := congrArg (fun m : Mono n => m.get j) hmul
    unfold mul at hi'
    rw [get_ofFn] at hi'
    change a.get j + q.get j = b.get j at hi'
    change (Hex.Vector.ofFn' fun i => b[i] - a[i]).get j = q.get j
    rw [get_ofFn]
    change b.get j - a.get j = q.get j
    omega

/-- Exact monomial division fails exactly when the divisor does not divide. -/
theorem div_eq_none_iff (a b : Mono n) :
    div a b = none ↔ ¬ ∀ i : Fin n, a[i] ≤ b[i] := by
  simp [div]

/-- Total degree is additive under monomial multiplication. -/
theorem degree_mul (a b : Mono n) :
    degree (mul a b) = degree a + degree b := by
  have fold_start (f : Fin n → Nat) :
      ∀ (is : List (Fin n)) (init : Nat),
        is.foldl (fun acc i => acc + f i) init =
          init + is.foldl (fun acc i => acc + f i) 0 := by
    intro is
    induction is with
    | nil =>
      intro init
      simp only [List.foldl_nil, Nat.add_zero]
    | cons i is ih =>
      intro init
      rw [List.foldl_cons, ih (init + f i), List.foldl_cons,
        ih (0 + f i)]
      omega
  have fold_add : ∀ is : List (Fin n),
      is.foldl (fun acc i => acc + (a[i] + b[i])) 0 =
        is.foldl (fun acc i => acc + a[i]) 0 +
          is.foldl (fun acc i => acc + b[i]) 0 := by
    intro is
    induction is with
    | nil => simp only [List.foldl_nil, Nat.add_zero]
    | cons i is ih =>
      simp only [List.foldl_cons]
      rw [fold_start (fun j => a[j] + b[j]),
        fold_start (fun j => a[j]), fold_start (fun j => b[j]), ih]
      omega
  unfold degree
  simp only [getElem_mul]
  exact fold_add (List.finRange n)

/-- Converting a prepended monomial to a list prepends the exponent. -/
@[simp] theorem toList_prepend (e : Nat) (m : Mono n) :
    (prepend e m).toList = e :: m.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    cases i with
    | zero =>
        simp
    | succ i =>
        have hi' : i < n := by simpa using hi
        let j : Fin n := ⟨i, hi'⟩
        change (prepend e m)[i + 1] = m[i]
        exact getElem_prepend_succ e m j

/-- The exponent list of a product is the pointwise sum of exponent lists. -/
theorem toList_mul (a b : Mono n) :
    (mul a b).toList = List.zipWith (· + ·) a.toList b.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_zipWith]
    simp [mul]

/-- Lexicographic comparison of prepended monomials first compares their
heads. -/
theorem lex_prepend (ea eb : Nat) (a b : Mono n) :
    lex (prepend ea a) (prepend eb b) =
      (compare ea eb).then (lex a b) := by
  simp [lex, List.compareLex_cons_cons]

/-- The zero monomial is zero prepended to the smaller zero monomial. -/
private theorem zero_eq_prepend :
    (zero : Mono (n + 1)) = prepend 0 (zero : Mono n) := by
  apply Vector.ext
  intro i hi
  simp [zero, prepend]

/-- Adding a common natural number preserves comparison. -/
private theorem compare_add_right (a b c : Nat) :
    compare a b = compare (a + c) (b + c) := by
  cases h : compare a b with
  | lt =>
      rw [Nat.compare_eq_lt] at h
      apply Eq.symm
      rw [Nat.compare_eq_lt]
      omega
  | eq =>
      rw [Nat.compare_eq_eq] at h
      apply Eq.symm
      rw [Nat.compare_eq_eq]
      omega
  | gt =>
      rw [Nat.compare_eq_gt] at h
      apply Eq.symm
      rw [Nat.compare_eq_gt]
      omega

/-- The zero monomial is least in lexicographic order. -/
private theorem lex_zero_le : ∀ {n} (m : Mono n), lex zero m ≠ .gt
  | 0, m => by
      have hm : m = zero := by
        apply Vector.ext
        intro i hi
        omega
      subst m
      intro h
      have hself : lex (zero : Mono 0) zero = .eq :=
        Std.ReflCmp.compare_self
      rw [hself] at h
      contradiction
  | n + 1, m => by
      rw [zero_eq_prepend, ← prepend_head_dropHead m, lex_prepend]
      cases h : compare 0 m.head with
      | lt => simp
      | eq =>
          simp only [Ordering.eq_then]
          exact lex_zero_le (dropHead m)
      | gt =>
          rw [Nat.compare_eq_gt] at h
          omega

/-- Lexicographic comparison is invariant under a common monomial factor. -/
private theorem lex_mul_mono : ∀ {n} (a b c : Mono n),
    lex a b = lex (mul a c) (mul b c)
  | 0, a, b, c => by
      have hz (m : Mono 0) : m = zero := by
        apply Vector.ext
        intro i hi
        omega
      simp [hz a, hz b, hz c]
  | n + 1, a, b, c => by
      rw [← prepend_head_dropHead a, ← prepend_head_dropHead b,
        ← prepend_head_dropHead c, mul_prepend, mul_prepend,
        lex_prepend, lex_prepend, ← compare_add_right,
        lex_mul_mono (dropHead a) (dropHead b) (dropHead c)]

/-- Strict lexicographic order on fixed-arity natural exponent vectors is
well-founded. -/
private theorem lex_wf : ∀ n, WellFounded fun a b : Mono n => lex a b = .lt
  | 0 => by
      apply WellFounded.intro
      intro a
      apply Acc.intro
      intro b h
      have hz (m : Mono 0) : m = zero := by
        apply Vector.ext
        intro i hi
        omega
      have hself : lex (zero : Mono 0) zero = .eq :=
        Std.ReflCmp.compare_self
      rw [hz a, hz b, hself] at h
      contradiction
  | n + 1 => by
      let tailOrder : WellFoundedRelation (Mono n) :=
        ⟨fun a b => lex a b = .lt, lex_wf n⟩
      apply Subrelation.wf
        (r := InvImage
          (Prod.Lex Nat.lt tailOrder.rel)
          (fun m : Mono (n + 1) => (m.head, dropHead m)))
      · intro a b h
        rw [← prepend_head_dropHead a, ← prepend_head_dropHead b,
          lex_prepend] at h
        simp only [Ordering.then_eq_lt] at h
        rcases h with hhead | ⟨hhead, htail⟩
        · exact Prod.Lex.left _ _ (Nat.compare_eq_lt.mp hhead)
        · exact Prod.lex_def.mpr
            (Or.inr ⟨Nat.compare_eq_eq.mp hhead, htail⟩)
      · exact InvImage.wf _
          (Prod.lex Nat.lt_wfRel tailOrder).wf

instance instLexOrder : IsMonomialOrder (@lex n) where
  zero_le := lex_zero_le
  mul_mono := lex_mul_mono
  wf := lex_wf n

/-- The zero monomial has total degree zero. -/
@[simp] theorem degree_zero : degree (zero : Mono n) = 0 := by
  unfold degree
  apply List.foldl_add_eq_self
  intro i _
  exact getElem_zero i

/-- The zero monomial is least in graded lexicographic order. -/
private theorem grlex_zero_le (m : Mono n) : grlex zero m ≠ .gt := by
  unfold grlex compareLex
  change
    (compare (degree zero) (degree m)).then (lex zero m) ≠ .gt
  rw [degree_zero]
  cases h : compare 0 (degree m) with
  | lt => simp
  | eq =>
      simp only [Ordering.eq_then]
      exact lex_zero_le m
  | gt =>
      rw [Nat.compare_eq_gt] at h
      omega

/-- Graded lexicographic comparison is invariant under a common monomial
factor. -/
private theorem grlex_mul_mono (a b c : Mono n) :
    grlex a b = grlex (mul a c) (mul b c) := by
  unfold grlex compareLex
  change
    (compare (degree a) (degree b)).then (lex a b) =
      (compare (degree (mul a c)) (degree (mul b c))).then
        (lex (mul a c) (mul b c))
  rw [degree_mul, degree_mul, ← compare_add_right,
    lex_mul_mono a b c]

/-- Strict graded lexicographic order is well-founded. -/
private theorem grlex_wf :
    WellFounded fun a b : Mono n => grlex a b = .lt := by
  let lexOrder : WellFoundedRelation (Mono n) :=
    ⟨fun a b => lex a b = .lt, lex_wf n⟩
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex Nat.lt lexOrder.rel)
      (fun m : Mono n => (degree m, m)))
  · intro a b h
    unfold grlex compareLex at h
    simp only [Ordering.then_eq_lt] at h
    rcases h with hdegree | ⟨hdegree, hlex⟩
    · exact Prod.Lex.left _ _ (Nat.compare_eq_lt.mp hdegree)
    · exact Prod.lex_def.mpr
        (Or.inr ⟨Nat.compare_eq_eq.mp hdegree, hlex⟩)
  · exact InvImage.wf _
      (Prod.lex Nat.lt_wfRel lexOrder).wf

instance instGrlexOrder :
    IsMonomialOrder (@grlex n) where
  zero_le := grlex_zero_le
  mul_mono := grlex_mul_mono
  wf := grlex_wf

/-- Reverse lexicographic comparison is invariant under a common monomial
factor. -/
private theorem revlex_mul_mono (a b c : Mono n) :
    revlex a b = revlex (mul a c) (mul b c) := by
  have hac : a.toList.length = c.toList.length := by simp
  have hbc : b.toList.length = c.toList.length := by simp
  unfold revlex
  rw [toList_mul, toList_mul,
    List.reverse_zipWith (f := (· + ·)) hac,
    List.reverse_zipWith (f := (· + ·)) hbc]
  apply List.compareLex_zipWith
  · intro x y z
    exact compare_add_right y x z
  · simp
  · simp

/-- Every individual exponent is bounded by total degree. -/
theorem degreeOf_le_degree (i : Fin n) (m : Mono n) :
    degreeOf i m ≤ degree m := by
  unfold degreeOf degree
  exact List.le_foldl_add_of_mem
    (List.finRange n) (fun j => m[j]) (List.mem_finRange i)

/-- Lexicographic key for the reverse-lexicographic tie breaker at one
fixed total degree. Its coordinate subtractions are exact because every
exponent is bounded by the total degree. -/
private def revDegreeKey (m : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => degree m - m[i.rev]

/-- The reverse-degree key lists complementary exponents in reverse order. -/
private theorem toList_revDegreeKey (m : Mono n) :
    (revDegreeKey m).toList =
      m.toList.reverse.map (fun e => degree m - e) := by
  apply List.ext_getElem
  · simp [revDegreeKey]
  · intro i hi hj
    simp [revDegreeKey, Fin.rev]
    congr 2 <;> omega

/-- Comparing complements reverses comparison of bounded naturals. -/
private theorem compare_sub (d x y : Nat) (hx : x ≤ d) (hy : y ≤ d) :
    compare y x = compare (d - x) (d - y) := by
  cases h : compare y x with
  | lt =>
      rw [Nat.compare_eq_lt] at h
      apply Eq.symm
      rw [Nat.compare_eq_lt]
      omega
  | eq =>
      rw [Nat.compare_eq_eq] at h
      apply Eq.symm
      rw [Nat.compare_eq_eq]
      omega
  | gt =>
      rw [Nat.compare_eq_gt] at h
      apply Eq.symm
      rw [Nat.compare_eq_gt]
      omega

/-- Lexicographic comparison of complement lists reverses the original
comparison. -/
private theorem compareLex_complement (d : Nat) :
    ∀ (xs ys : List Nat),
      (∀ x, x ∈ xs → x ≤ d) →
      (∀ y, y ∈ ys → y ≤ d) →
      List.compareLex (fun x y => compare y x) xs ys =
        List.compareLex compare
          (xs.map (fun x => d - x))
          (ys.map (fun y => d - y))
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | x :: xs, y :: ys, hxs, hys => by
      simp only [List.map, List.compareLex_cons_cons]
      rw [compare_sub d x y (hxs x (by simp)) (hys y (by simp)),
        compareLex_complement d xs ys
          (fun z hz => hxs z (by simp [hz]))
          (fun z hz => hys z (by simp [hz]))]

/-- At equal total degree, reverse lexicographic comparison is ordinary
lexicographic comparison of the reversed degree-complement keys. -/
private theorem revlex_eq_key_lex {a b : Mono n}
    (hdegree : degree a = degree b) :
    revlex a b = lex (revDegreeKey a) (revDegreeKey b) := by
  unfold revlex lex
  rw [toList_revDegreeKey, toList_revDegreeKey, ← hdegree]
  apply compareLex_complement
  · intro x hx
    rw [List.mem_reverse] at hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    let j : Fin n := ⟨i, by simpa using hi⟩
    exact degreeOf_le_degree j a
  · intro x hx
    rw [List.mem_reverse] at hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    let j : Fin n := ⟨i, by simpa using hi⟩
    rw [hdegree]
    exact degreeOf_le_degree j b

/-- The zero monomial is least in graded reverse lexicographic order. -/
private theorem grevlex_zero_le (m : Mono n) : grevlex zero m ≠ .gt := by
  unfold grevlex compareLex
  change
    (compare (degree zero) (degree m)).then (revlex zero m) ≠ .gt
  rw [degree_zero]
  cases h : compare 0 (degree m) with
  | lt => simp
  | eq =>
      have hdegree : degree m = 0 := Nat.compare_eq_eq.mp h |>.symm
      have hm : m = zero := by
        apply Vector.ext
        intro i hi
        let j : Fin n := ⟨i, hi⟩
        have hj := degreeOf_le_degree j m
        change m[j] ≤ degree m at hj
        have : m[j] = 0 := by omega
        change m[j] = (zero : Mono n)[j]
        rw [getElem_zero]
        exact this
      subst m
      intro hgt
      simp [Std.ReflCmp.compare_self] at hgt
  | gt =>
      rw [Nat.compare_eq_gt] at h
      omega

/-- Graded reverse lexicographic comparison is invariant under a common
monomial factor. -/
private theorem grevlex_mul_mono (a b c : Mono n) :
    grevlex a b = grevlex (mul a c) (mul b c) := by
  unfold grevlex compareLex
  change
    (compare (degree a) (degree b)).then (revlex a b) =
      (compare (degree (mul a c)) (degree (mul b c))).then
        (revlex (mul a c) (mul b c))
  rw [degree_mul, degree_mul, ← compare_add_right,
    revlex_mul_mono a b c]

/-- Strict graded reverse lexicographic order is well-founded. -/
private theorem grevlex_wf :
    WellFounded fun a b : Mono n => grevlex a b = .lt := by
  let lexOrder : WellFoundedRelation (Mono n) :=
    ⟨fun a b => lex a b = .lt, lex_wf n⟩
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex Nat.lt lexOrder.rel)
      (fun m : Mono n => (degree m, revDegreeKey m)))
  · intro a b h
    unfold grevlex compareLex at h
    simp only [Ordering.then_eq_lt] at h
    rcases h with hdegree | ⟨hdegree, hrevlex⟩
    · exact Prod.Lex.left _ _ (Nat.compare_eq_lt.mp hdegree)
    · have heq := Nat.compare_eq_eq.mp hdegree
      have hlex : lex (revDegreeKey a) (revDegreeKey b) = .lt := by
        rw [← revlex_eq_key_lex heq]
        exact hrevlex
      apply Prod.lex_def.mpr
      exact Or.inr ⟨heq, hlex⟩
  · exact InvImage.wf _
      (Prod.lex Nat.lt_wfRel lexOrder).wf

instance instGrevlexOrder :
    IsMonomialOrder (@grevlex n) where
  zero_le := grevlex_zero_le
  mul_mono := grevlex_mul_mono
  wf := grevlex_wf

/-- Renaming variables commutes with monomial multiplication. -/
theorem rename_mul {k : Nat} (f : Fin n → Fin k) (a b : Mono n) :
    rename f (mul a b) = mul (rename f a) (rename f b) := by
  have get_ofFn {r : Nat} (g : Fin r → Nat) (j : Fin r) :
      (Hex.Vector.ofFn' g).get j = g j := by
    change (Hex.Vector.ofFn' g)[j.val] = g j
    rw [Hex.Vector.getElem_ofFn' g j.val j.isLt]
  have fold_start (g : Fin n → Nat) :
      ∀ (is : List (Fin n)) (init : Nat),
        is.foldl (fun acc i => acc + g i) init =
          init + is.foldl (fun acc i => acc + g i) 0 := by
    intro is
    induction is with
    | nil =>
      intro init
      simp only [List.foldl_nil, Nat.add_zero]
    | cons i is ih =>
      intro init
      rw [List.foldl_cons, ih (init + g i), List.foldl_cons,
        ih (0 + g i)]
      omega
  have fold_add (u v : Fin n → Nat) : ∀ is : List (Fin n),
      is.foldl (fun acc i => acc + (u i + v i)) 0 =
        is.foldl (fun acc i => acc + u i) 0 +
          is.foldl (fun acc i => acc + v i) 0 := by
    intro is
    induction is with
    | nil => simp only [List.foldl_nil, Nat.add_zero]
    | cons i is ih =>
      simp only [List.foldl_cons]
      rw [fold_start (fun j => u j + v j),
        fold_start u, fold_start v, ih]
      omega
  apply Vector.ext
  intro idx hidx
  let j : Fin k := ⟨idx, hidx⟩
  have get_mul {r : Nat} (x y : Mono r) (t : Fin r) :
      (mul x y).get t = x.get t + y.get t := by
    unfold mul
    rw [get_ofFn]
    change x.get t + y.get t = x.get t + y.get t
    rfl
  have get_rename (x : Mono n) :
      (rename f x).get j =
        (List.finRange n).foldl
          (fun acc i => acc + if f i = j then x[i] else 0) 0 := by
    unfold rename
    rw [get_ofFn]
  change (rename f (mul a b)).get j =
    (mul (rename f a) (rename f b)).get j
  rw [get_rename, get_mul, get_rename, get_rename]
  simp only [getElem_mul]
  have hterm (i : Fin n) :
      (if f i = j then a[i] + b[i] else 0) =
        (if f i = j then a[i] else 0) +
          (if f i = j then b[i] else 0) := by
    by_cases h : f i = j <;> simp [h]
  simp only [hterm]
  exact fold_add
    (fun i => if f i = j then a[i] else 0)
    (fun i => if f i = j then b[i] else 0)
    (List.finRange n)

/-- A pair occurs in `splits m` exactly when its monomial product is `m`. -/
theorem splits_mem_iff (m a b : Mono n) :
    (a, b) ∈ splits m ↔ mul a b = m := by
  induction n with
  | zero =>
    have hzero (x : Mono 0) : x = zero := by
      apply Vector.ext
      intro i hi
      omega
    rw [hzero a, hzero b, hzero m]
    have hm : mul (zero : Mono 0) zero = zero :=
      hzero (mul zero zero)
    simp [splits, hm]
  | succ n ih =>
    constructor
    · intro hmem
      rcases List.mem_flatMap.mp hmem with ⟨e, he, hpairs⟩
      rcases List.mem_map.mp hpairs with
        ⟨⟨a', b'⟩, hab, hpairs⟩
      cases hpairs
      have htail : mul a' b' = dropHead m :=
        (ih (dropHead m) a' b').mp hab
      rw [mul_prepend, htail]
      have he' := List.mem_range.mp he
      have hsum : e + (m.head - e) = m.head := by omega
      rw [hsum, prepend_head_dropHead]
    · intro hmul
      have hhead :=
        congrArg (fun x : Mono (n + 1) => x[0]) hmul
      simp only [mul, Hex.Vector.getElem_ofFn'] at hhead
      change a.head + b.head = m.head at hhead
      have htail :
          mul (dropHead a) (dropHead b) = dropHead m := by
        rw [← dropHead_mul, hmul]
      apply List.mem_flatMap.mpr
      refine ⟨a.head, List.mem_range.mpr ?_, ?_⟩
      · omega
      · apply List.mem_map.mpr
        refine ⟨(dropHead a, dropHead b),
          (ih (dropHead m) (dropHead a) (dropHead b)).mpr htail, ?_⟩
        have hb : m.head - a.head = b.head := by omega
        change
          (prepend a.head (dropHead a),
            prepend (m.head - a.head) (dropHead b)) = (a, b)
        rw [hb, prepend_head_dropHead, prepend_head_dropHead]

/-- Every monomial decomposition occurs exactly once in `splits`. -/
theorem splits_nodup (m : Mono n) : (splits m).Nodup := by
  induction n with
  | zero =>
      simp [splits]
  | succ n ih =>
      unfold splits
      unfold List.Nodup
      rw [List.pairwise_flatMap]
      constructor
      · intro k hk
        apply (ih (dropHead m)).map
          (fun ab =>
            (prepend k ab.1, prepend (m.head - k) ab.2))
        intro x y hxy h
        apply hxy
        apply Prod.ext
        · have hleft :=
            congrArg (fun z : Mono (n + 1) × Mono (n + 1) => dropHead z.1) h
          simpa using hleft
        · have hright :=
            congrArg (fun z : Mono (n + 1) × Mono (n + 1) => dropHead z.2) h
          simpa using hright
      · apply List.nodup_range.imp
        intro k l hkl x hx y hy hxy
        rcases List.mem_map.mp hx with ⟨⟨a, b⟩, hab, rfl⟩
        rcases List.mem_map.mp hy with ⟨⟨c, d⟩, hcd, rfl⟩
        apply hkl
        have hhead :=
          congrArg
            (fun z : Mono (n + 1) × Mono (n + 1) => z.1[0])
            hxy
        simpa using hhead

/-- The left input divides the monomial least common multiple. -/
theorem dvd_lcm_left (a b : Mono n) : dvd a (lcm a b) = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_lcm]
  exact Nat.le_max_left _ _

/-- The right input divides the monomial least common multiple. -/
theorem dvd_lcm_right (a b : Mono n) : dvd b (lcm a b) = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_lcm]
  exact Nat.le_max_right _ _

/-- The monomial least common multiple divides every common multiple. -/
theorem lcm_dvd (a b c : Mono n)
    (ha : dvd a c = true) (hb : dvd b c = true) :
    dvd (lcm a b) c = true := by
  rw [dvd_eq_true_iff] at ha hb ⊢
  intro i
  rw [getElem_lcm]
  exact Nat.max_le.mpr ⟨ha i, hb i⟩

/-- The monomial greatest common divisor divides the left input. -/
theorem gcd_dvd_left (a b : Mono n) : dvd (gcd a b) a = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_gcd]
  exact Nat.min_le_left _ _

/-- The monomial greatest common divisor divides the right input. -/
theorem gcd_dvd_right (a b : Mono n) : dvd (gcd a b) b = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_gcd]
  exact Nat.min_le_right _ _

/-- Every common divisor divides the monomial greatest common divisor. -/
theorem dvd_gcd (a b c : Mono n)
    (ha : dvd c a = true) (hb : dvd c b = true) :
    dvd c (gcd a b) = true := by
  rw [dvd_eq_true_iff] at ha hb ⊢
  intro i
  rw [getElem_gcd]
  exact Nat.le_min.mpr ⟨ha i, hb i⟩

end Mono

end Hex
