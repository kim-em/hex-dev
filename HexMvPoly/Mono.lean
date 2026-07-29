/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ArrayDecEq
public import HexBasic.OfFn
public import Std.Data.ExtTreeMap.Lemmas

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

/-- All decompositions `a * b = m`. Each exponent is split independently,
so the list has `∏ i, (m[i] + 1)` entries. -/
def splits : {n : Nat} → Mono n → List (Mono n × Mono n)
  | 0, _ => [(zero, zero)]
  | n + 1, m =>
      (List.range (m.head + 1)).flatMap fun k =>
        (splits m.tail).map fun (a, b) =>
          (a.insertIdx 0 k, b.insertIdx 0 (m.head - k))

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

instance instLexOrder : IsMonomialOrder (@lex n) := by
  sorry

instance instGrlexOrder : IsMonomialOrder (@grlex n) := by
  sorry

instance instGrevlexOrder : IsMonomialOrder (@grevlex n) := by
  sorry

@[simp] theorem getElem_zero (i : Fin n) : (zero : Mono n)[i] = 0 := by
  simp [zero]

@[simp] theorem getElem_unit (i j : Fin n) :
    (unit i : Mono n)[j] = if j = i then 1 else 0 := by
  simp [unit]

@[simp] theorem getElem_mul (a b : Mono n) (i : Fin n) :
    (mul a b)[i] = a[i] + b[i] := by
  simp [mul]

@[simp] theorem getElem_lcm (a b : Mono n) (i : Fin n) :
    (lcm a b)[i] = max a[i] b[i] := by
  simp [lcm]

@[simp] theorem getElem_gcd (a b : Mono n) (i : Fin n) :
    (gcd a b)[i] = min a[i] b[i] := by
  simp [gcd]

theorem dvd_eq_true_iff (a b : Mono n) :
    dvd a b = true ↔ ∀ i : Fin n, a[i] ≤ b[i] := by
  simp [dvd]

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
    rw [div, dif_pos hle]
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

theorem div_eq_none_iff (a b : Mono n) :
    div a b = none ↔ ¬ ∀ i : Fin n, a[i] ≤ b[i] := by
  simp [div]

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

theorem splits_mem_iff (m a b : Mono n) :
    (a, b) ∈ splits m ↔ mul a b = m := by
  sorry

theorem dvd_lcm_left (a b : Mono n) : dvd a (lcm a b) = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_lcm]
  exact Nat.le_max_left _ _

theorem dvd_lcm_right (a b : Mono n) : dvd b (lcm a b) = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_lcm]
  exact Nat.le_max_right _ _

theorem gcd_dvd_left (a b : Mono n) : dvd (gcd a b) a = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_gcd]
  exact Nat.min_le_left _ _

theorem gcd_dvd_right (a b : Mono n) : dvd (gcd a b) b = true := by
  simp only [dvd, decide_eq_true_eq]
  intro i
  rw [getElem_gcd]
  exact Nat.min_le_right _ _

end Mono

end Hex
