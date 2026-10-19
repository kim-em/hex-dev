/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TransportRing

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [CommRing K] [DecidableEq K]

/-- The interpreted leading coefficient is nonzero for a nonempty source array. -/
@[expose] def Leading (read : E → K) (p : Hex.DensePoly E) : Prop :=
  0 < p.size → read (p.coeff (p.size - 1)) ≠ 0

/-- The finite scalar obligations of one native polynomial subtraction. -/
structure Difference [Sub E] (read : E → K) (p q : Hex.DensePoly E) : Prop where
  differences : ∀ i < max p.size q.size,
    read (p.coeff i - q.coeff i) = read (p.coeff i) - read (q.coeff i)

/-- The finite scalar obligations of one native polynomial scaling. -/
structure Scaling [Mul E] (read : E → K) (scalar : E) (p : Hex.DensePoly E) : Prop where
  products : ∀ i < p.size,
    read (scalar * p.coeff i) = read scalar * read (p.coeff i)

/-- The finite scalar obligations at each pair and reached accumulator of
one native schoolbook multiplication. -/
structure Product [Add E] [Mul E]
    (read : E → K) (p q : Hex.DensePoly E) : Prop where
  products : ∀ i < p.size, ∀ j < q.size,
    read (p.coeff i * q.coeff j) = read (p.coeff i) * read (q.coeff j)
  sums : ∀ i < p.size, ∀ j < q.size,
    read (productPrefix p q (i + j) i j + p.coeff i * q.coeff j) =
      read (productPrefix p q (i + j) i j) + read (p.coeff i * q.coeff j)

variable [Sub E]

/-- A checked zero difference remains zero from the finite subtraction work.
The result needs no zero reflection on arbitrary expressions. -/
theorem Difference.zero (read : E → K) (zero : read 0 = 0) (p q : Hex.DensePoly E)
    (data : Difference read p q) (accepted : (p - q).isZero = true) :
    (polynomial read p - polynomial read q).isZero = true := by
  have source : p - q = 0 := (Hex.DensePoly.size_eq_zero_iff _).mp
    ((Hex.DensePoly.isZero_eq_true_iff _).mp accepted)
  have mapped := Ring.polynomial_sub read zero p q data.differences
  rw [source] at mapped
  have empty : polynomial read (0 : Hex.DensePoly E) = 0 :=
    (polynomial_zero read zero 0 (by simp)).mpr rfl
  rw [empty] at mapped
  rw [← mapped]
  rfl

variable [Add E] [Mul E]

/-- The finite scalar obligations of one native polynomial addition. -/
structure Sum (read : E → K) (p q : Hex.DensePoly E) : Prop where
  sums : ∀ i < max p.size q.size,
    read (p.coeff i + q.coeff i) = read (p.coeff i) + read (q.coeff i)

/-- The finite cast-times-coefficient obligations of differentiation. -/
structure Differentiation [NatCast E]
    (read : E → K) (p : Hex.DensePoly E) : Prop where
  products : ∀ i < p.size - 1,
    read (((i + 1 : Nat) : E) * p.coeff (i + 1)) =
      ((i + 1 : Nat) : K) * read (p.coeff (i + 1))

/-- Transport the same positive-scaled signed recurrence checked by the native
checker, with finite arithmetic obligations for each actual intermediate. -/
structure Recurrence (read : E → K) (a b c : Hex.DensePoly E)
    (left : E) (quotient : Hex.DensePoly E) (right : E) : Prop where
  leftScale : Scaling read left a
  quotientProduct : Product read quotient b
  rightScale : Scaling read right c
  remainder : Difference read (quotient * b) (Hex.DensePoly.scale right c)
  identity : Difference read (Hex.DensePoly.scale left a)
    (quotient * b - Hex.DensePoly.scale right c)

/-- The finite obligations imply the literal checker identity after coefficient
interpretation, using its actual two subtractions and stored scales. -/
theorem Recurrence.zero (read : E → K) (zero : read 0 = 0) (a b c : Hex.DensePoly E)
    (left : E) (quotient : Hex.DensePoly E) (right : E)
    (data : Recurrence read a b c left quotient right)
    (accepted : (Hex.DensePoly.scale left a -
      (quotient * b - Hex.DensePoly.scale right c)).isZero = true) :
    (Hex.DensePoly.scale (read left) (polynomial read a) -
      (polynomial read quotient * polynomial read b -
        Hex.DensePoly.scale (read right) (polynomial read c))).isZero = true := by
  have mapped := data.identity.zero read zero _ _ accepted
  rw [Ring.polynomial_scale read zero left a data.leftScale.products,
    Ring.polynomial_sub read zero _ _ data.remainder.differences,
    Ring.polynomial_mul read zero quotient b data.quotientProduct.products data.quotientProduct.sums,
    Ring.polynomial_scale read zero right c data.rightScale.products]
    at mapped
  exact mapped

/-- The finite scalar work in the checker's initial reduction of `f*p'`.
The stored quotient and scales are retained literally. -/
structure Initial [NatCast E] (read : E → K) (p f c : Hex.DensePoly E)
    (left : E) (quotient : Hex.DensePoly E) (right : E) : Prop where
  derivative : Differentiation read p
  inputProduct : Product read f p.derivative
  leftScale : Scaling read left (f * p.derivative)
  quotientProduct : Product read quotient p
  rightScale : Scaling read right c
  remainder : Sum read (quotient * p) (Hex.DensePoly.scale right c)
  identity : Difference read (Hex.DensePoly.scale left (f * p.derivative))
    (quotient * p + Hex.DensePoly.scale right c)

/-- The accepted initial zero identity transports by its finite executable
arithmetic, including the actual derivative and multiplication accumulators. -/
theorem Initial.zero [NatCast E]
    (read : E → K) (zero : read 0 = 0) (p f c : Hex.DensePoly E)
    (left : E) (quotient : Hex.DensePoly E) (right : E)
    (data : Initial read p f c left quotient right)
    (accepted : (Hex.DensePoly.scale left (f * p.derivative) -
      (quotient * p + Hex.DensePoly.scale right c)).isZero = true) :
    (Hex.DensePoly.scale (read left) (polynomial read f * (polynomial read p).derivative) -
      (polynomial read quotient * polynomial read p +
        Hex.DensePoly.scale (read right) (polynomial read c))).isZero = true := by
  have mapped := data.identity.zero read zero _ _ accepted
  rw [Ring.polynomial_scale read zero left _ data.leftScale.products,
    Ring.polynomial_mul read zero f p.derivative data.inputProduct.products data.inputProduct.sums,
    Ring.polynomial_derivative read zero p data.derivative.products,
    Ring.polynomial_add read zero _ _ data.remainder.sums,
    Ring.polynomial_mul read zero quotient p data.quotientProduct.products data.quotientProduct.sums,
    Ring.polynomial_scale read zero right c data.rightScale.products]
    at mapped
  exact mapped

/-- The finite scalar work in the checker's separate terminal zero identity. -/
structure Terminal (read : E → K) (a b : Hex.DensePoly E)
    (scale : E) (quotient : Hex.DensePoly E) : Prop where
  scaling : Scaling read scale a
  product : Product read quotient b
  identity : Difference read (Hex.DensePoly.scale scale a) (quotient * b)

/-- Transport the actual accepted terminal identity without running division. -/
theorem Terminal.zero (read : E → K) (zero : read 0 = 0) (a b : Hex.DensePoly E)
    (scale : E) (quotient : Hex.DensePoly E) (data : Terminal read a b scale quotient)
    (accepted : (Hex.DensePoly.scale scale a - quotient * b).isZero = true) :
    (Hex.DensePoly.scale (read scale) (polynomial read a) -
      polynomial read quotient * polynomial read b).isZero = true := by
  have mapped := data.identity.zero read zero _ _ accepted
  rw [Ring.polynomial_scale read zero scale a data.scaling.products,
    Ring.polynomial_mul read zero quotient b data.product.products data.product.sums] at mapped
  exact mapped

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.Difference.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Difference.zero

/-- info: 'Hex.RealClosure.Transport.Recurrence.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Recurrence.zero

/-- info: 'Hex.RealClosure.Transport.Initial.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Initial.zero

/-- info: 'Hex.RealClosure.Transport.Terminal.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Terminal.zero
