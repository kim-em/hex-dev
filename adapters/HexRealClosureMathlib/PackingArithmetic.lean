/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Packing
import all HexRealClosureMathlib.Packing
import all HexRealClosure.Algebraic

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K]

/-- A retained original equation transports the exact native packing result.
This is the arithmetic boundary needed by the next coefficient level. -/
theorem eval_pack (entry : Packing context) (p : DensePoly E)
    (key : entry.original = p) (read : E → K) (x : K)
    (equation : eval read x entry.value.polynomial = eval read x entry.original) :
    eval read x (Element.ofPoly (context := context) p).polynomial = eval read x p := by
  have native : entry.value = Element.ofPoly p :=
    entry.native.trans (congrArg Element.ofPoly key)
  rw [← native, equation, key]

/-- Native addition is interpreted from its retained packing equation and
only the reached predecessor coefficient sums. -/
theorem eval_add (entry : Packing context) (a b : Element context)
    (key : entry.original = a.polynomial + b.polynomial)
    (read : E → K) (zero : read 0 = 0) (x : K)
    (data : Transport.Sum read a.polynomial b.polynomial)
    (equation : eval read x entry.value.polynomial = eval read x entry.original) :
    eval read x (a + b).polynomial = eval read x a.polynomial + eval read x b.polynomial := by
  change eval read x (Element.ofPoly (a.polynomial + b.polynomial)).polynomial = _
  rw [eval_pack entry _ key read x equation]
  unfold eval
  rw [Transport.Ring.polynomial_add read zero _ _ data.sums,
    interpret_add (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl),
    Polynomial.eval_add]

/-- Native subtraction uses its original equation and exactly the reached
predecessor coefficient differences. -/
theorem eval_sub (entry : Packing context) (a b : Element context)
    (key : entry.original = a.polynomial - b.polynomial)
    (read : E → K) (zero : read 0 = 0) (x : K)
    (data : Transport.Difference read a.polynomial b.polynomial)
    (equation : eval read x entry.value.polynomial = eval read x entry.original) :
    eval read x (a - b).polynomial = eval read x a.polynomial - eval read x b.polynomial := by
  change eval read x (Element.ofPoly (a.polynomial - b.polynomial)).polynomial = _
  rw [eval_pack entry _ key read x equation]
  unfold eval
  rw [Transport.Ring.polynomial_sub read zero _ _ data.differences,
    interpret_sub (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl),
    Polynomial.eval_sub]

/-- Native multiplication uses its original equation and the actual finite
schoolbook products and accumulator sums of the predecessor. -/
theorem eval_mul (entry : Packing context) (a b : Element context)
    (key : entry.original = a.polynomial * b.polynomial)
    (read : E → K) (zero : read 0 = 0) (x : K)
    (data : Transport.Product read a.polynomial b.polynomial)
    (equation : eval read x entry.value.polynomial = eval read x entry.original) :
    eval read x (a * b).polynomial = eval read x a.polynomial * eval read x b.polynomial := by
  change eval read x (Element.ofPoly (a.polynomial * b.polynomial)).polynomial = _
  rw [eval_pack entry _ key read x equation]
  unfold eval
  rw [Transport.Ring.polynomial_mul read zero _ _ data.products data.sums,
    interpret_mul (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl),
    Polynomial.eval_mul]

/-- Native negation is the executed zero-minus-operand recurrence. -/
theorem eval_neg (entry : Packing context) (a : Element context)
    (key : entry.original = 0 - a.polynomial)
    (read : E → K) (zero : read 0 = 0) (x : K)
    (data : Transport.Difference read 0 a.polynomial)
    (equation : eval read x entry.value.polynomial = eval read x entry.original) :
    eval read x (-a).polynomial = -eval read x a.polynomial := by
  change eval read x (Element.ofPoly (0 - a.polynomial)).polynomial = _
  rw [eval_pack entry _ key read x equation]
  unfold eval
  rw [Transport.Ring.polynomial_sub read zero _ _ data.differences]
  have empty : Transport.polynomial read (0 : DensePoly E) = 0 :=
    (Transport.polynomial_zero read zero 0 (by simp)).mpr rfl
  rw [empty, interpret_sub (fun y : K => y) (fun _ => Iff.rfl) (fun _ _ => rfl),
    interpret_zero, Polynomial.eval_sub, Polynomial.eval_zero, zero_sub]

/-- Lookup retains an actual member of the recorded finite inventory. -/
theorem find_mem (entries : List (Packing context)) (p : DensePoly E)
    {entry : Packing context} (found : Packing.find entries p = some entry) : entry ∈ entries := by
  induction entries with
  | nil => simp [Packing.find] at found
  | cons first rest ih =>
    unfold Packing.find at found
    split at found
    · cases Option.some.inj found
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih found)

/-- The finite lower-level work at each coefficient of an actual higher-level
addition. Every original packing key must occur in the supplied inventory. -/
structure SumData (entries : List (Packing context)) (read : E → K)
    (p q : DensePoly (Element context)) : Prop where
  keys : ∀ i < max p.size q.size,
    (Packing.find entries ((p.coeff i).polynomial + (q.coeff i).polynomial)).isSome = true
  sums : ∀ i < max p.size q.size,
    Transport.Sum read (p.coeff i).polynomial (q.coeff i).polynomial

/-- Construct the next level's reached coefficient sums from the retained
packing equations at the one point chosen for this level. -/
theorem lift_sum (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p q : DensePoly (Element context))
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : SumData entries read p q) :
    Transport.Sum (fun a : Element context => eval read x a.polynomial) p q := by
  constructor
  intro i bound
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp (data.keys i bound)
  exact eval_add entry (p.coeff i) (q.coeff i)
    (Packing.find_native entries _ found).1 read zero x (data.sums i bound)
    (equations entry (find_mem entries _ found))

/-- The finite lower-level work at each coefficient of subtraction. -/
structure DifferenceData (entries : List (Packing context)) (read : E → K)
    (p q : DensePoly (Element context)) : Prop where
  keys : ∀ i < max p.size q.size,
    (Packing.find entries ((p.coeff i).polynomial - (q.coeff i).polynomial)).isSome = true
  differences : ∀ i < max p.size q.size,
    Transport.Difference read (p.coeff i).polynomial (q.coeff i).polynomial

/-- Construct the next level's finite coefficient differences. -/
theorem lift_difference (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p q : DensePoly (Element context))
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : DifferenceData entries read p q) :
    Transport.Difference (fun a : Element context => eval read x a.polynomial) p q := by
  constructor
  intro i bound
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp (data.keys i bound)
  exact eval_sub entry (p.coeff i) (q.coeff i)
    (Packing.find_native entries _ found).1 read zero x (data.differences i bound)
    (equations entry (find_mem entries _ found))

/-- Retain precisely the finite schoolbook products and accumulator additions
executed by the higher-level polynomial multiplication. -/
structure ProductData (entries : List (Packing context)) (read : E → K)
    (p q : DensePoly (Element context)) : Prop where
  productKeys : ∀ i < p.size, ∀ j < q.size,
    (Packing.find entries ((p.coeff i).polynomial * (q.coeff j).polynomial)).isSome = true
  products : ∀ i < p.size, ∀ j < q.size,
    Transport.Product read (p.coeff i).polynomial (q.coeff j).polynomial
  sumKeys : ∀ i < p.size, ∀ j < q.size,
    (Packing.find entries
      ((Transport.productPrefix p q (i+j) i j).polynomial +
        (p.coeff i * q.coeff j).polynomial)).isSome = true
  sums : ∀ i < p.size, ∀ j < q.size,
    Transport.Sum read (Transport.productPrefix p q (i+j) i j).polynomial
      (p.coeff i * q.coeff j).polynomial

/-- Construct all products and reached accumulator sums of the next level.
No law is required outside the literal source loop bounds. -/
theorem lift_product (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p q : DensePoly (Element context))
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : ProductData entries read p q) :
    Transport.Product (fun a : Element context => eval read x a.polynomial) p q := by
  constructor
  · intro i hi j hj
    obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp (data.productKeys i hi j hj)
    exact eval_mul entry (p.coeff i) (q.coeff j)
      (Packing.find_native entries _ found).1 read zero x (data.products i hi j hj)
      (equations entry (find_mem entries _ found))
  · intro i hi j hj
    obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp (data.sumKeys i hi j hj)
    exact eval_add entry (Transport.productPrefix p q (i+j) i j) (p.coeff i * q.coeff j)
      (Packing.find_native entries _ found).1 read zero x (data.sums i hi j hj)
      (equations entry (find_mem entries _ found))

/-- The exact original multiplication keys reached by coefficient scaling. -/
structure ScalingData (entries : List (Packing context)) (read : E → K)
    (scalar : Element context) (p : DensePoly (Element context)) : Prop where
  keys : ∀ i < p.size,
    (Packing.find entries (scalar.polynomial * (p.coeff i).polynomial)).isSome = true
  products : ∀ i < p.size, Transport.Product read scalar.polynomial (p.coeff i).polynomial

/-- Lift the executed coefficient scaling from its original packing equations. -/
theorem lift_scaling (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (scalar : Element context)
    (p : DensePoly (Element context))
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : ScalingData entries read scalar p) :
    Transport.Scaling (fun a : Element context => eval read x a.polynomial) scalar p := by
  constructor
  intro i bound
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp (data.keys i bound)
  exact eval_mul entry scalar (p.coeff i)
    (Packing.find_native entries _ found).1 read zero x (data.products i bound)
    (equations entry (find_mem entries _ found))

/-- Natural casts retain their actual constant-polynomial packing key. -/
theorem eval_nat (entry : Packing context) (n : Nat)
    (key : entry.original = DensePoly.C (n : E))
    (read : E → K) (zero : read 0 = 0) (cast : read (n : E) = (n : K)) (x : K)
    (equation : eval read x entry.value.polynomial = eval read x entry.original) :
    eval read x ((n : Element context).polynomial) = (n : K) := by
  change eval read x (Element.ofPoly (DensePoly.C (n : E))).polynomial = _
  rw [eval_pack entry _ key read x equation]
  unfold eval
  rw [Transport.polynomial_C read zero, interpret_C, Polynomial.eval_C, cast]

/-- Differentiation retains both the cast and multiplication at each reached index. -/
structure DifferentiationData (entries : List (Packing context)) (read : E → K)
    (p : DensePoly (Element context)) : Prop where
  castKeys : ∀ i < p.size - 1,
    (Packing.find entries (DensePoly.C ((i + 1 : Nat) : E))).isSome = true
  casts : ∀ i < p.size - 1, read ((i + 1 : Nat) : E) = ((i + 1 : Nat) : K)
  productKeys : ∀ i < p.size - 1,
    (Packing.find entries ((((i + 1 : Nat) : Element context).polynomial) *
      (p.coeff (i + 1)).polynomial)).isSome = true
  products : ∀ i < p.size - 1,
    Transport.Product read (((i + 1 : Nat) : Element context).polynomial)
      (p.coeff (i + 1)).polynomial

/-- Construct the exact cast-times-coefficient obligations of the next derivative. -/
theorem lift_differentiation (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p : DensePoly (Element context))
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : DifferentiationData entries read p) :
    Transport.Differentiation (fun a : Element context => eval read x a.polynomial) p := by
  constructor
  intro i bound
  obtain ⟨castEntry, castFound⟩ := Option.isSome_iff_exists.mp (data.castKeys i bound)
  obtain ⟨productEntry, productFound⟩ := Option.isSome_iff_exists.mp (data.productKeys i bound)
  have cast := eval_nat castEntry (i + 1) (Packing.find_native entries _ castFound).1
    read zero (data.casts i bound) x (equations castEntry (find_mem entries _ castFound))
  have product := eval_mul productEntry ((i + 1 : Nat) : Element context) (p.coeff (i + 1))
    (Packing.find_native entries _ productFound).1 read zero x (data.products i bound)
    (equations productEntry (find_mem entries _ productFound))
  exact product.trans (congrArg (fun y : K => y * eval read x (p.coeff (i + 1)).polynomial) cast)

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.eval_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.eval_pack

/-- info: 'Hex.RealClosure.Algebraic.Packing.eval_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.eval_add

/-- info: 'Hex.RealClosure.Algebraic.Packing.eval_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.eval_sub

/-- info: 'Hex.RealClosure.Algebraic.Packing.eval_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.eval_mul

/-- info: 'Hex.RealClosure.Algebraic.Packing.eval_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.eval_neg

/-- info: 'Hex.RealClosure.Algebraic.Packing.find_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.find_mem

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_sum

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_difference

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_product

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_scaling

/-- info: 'Hex.RealClosure.Algebraic.Packing.eval_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.eval_nat

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_differentiation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_differentiation
