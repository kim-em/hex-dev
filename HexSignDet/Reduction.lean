/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Moment

public section

/-! Positive-scaled reduction of moment products. Each checked multiplication
uses only the previous reduced representative and its next indexed factor;
replay never expands the full unreduced moment. -/
namespace Hex.SignDet

variable {E : Type u} [Zero E] [DecidableEq E]

/-- One indexed factor and its positive-scaled remainder identity. -/
structure ReductionStep (E : Type u) [Zero E] [DecidableEq E] where
  index : Nat
  next : DensePoly E
  witness : RemainderStep E

/-- A chain starting at one and ending at a declared Tarski query polynomial. -/
structure Reduction (E : Type u) [Zero E] [DecidableEq E] where
  steps : List (ReductionStep E)
  result : DensePoly E

instance : DecidableEq (ReductionStep E) := fun a b =>
  decidable_of_iff (a.index = b.index ∧ a.next = b.next ∧ a.witness = b.witness)
    (by cases a; cases b; simp only [ReductionStep.mk.injEq])

instance : DecidableEq (Reduction E) := fun a b =>
  decidable_of_iff (a.steps = b.steps ∧ a.result = b.result)
    (by cases a; cases b; simp only [Reduction.mk.injEq])

/-- Ordered indexed factors, repeated by their exponent. The outer checker
validates vector length and exponents before this list is constructed. -/
@[expose] def factors (qs : List (DensePoly E)) (es : List Nat) : List (Nat × DensePoly E) :=
  (qs.zip es).zipIdx.flatMap fun ((q, k), i) => List.replicate k (i, q)

variable [One E] [Add E] [Sub E] [Mul E]

/-- Check the positive product identity and strict remainder degree bound.
The equality is a zero difference, supporting noncanonical representatives. -/
@[expose] def ReductionStep.check (sign : E → Int) (p prev factor : DensePoly E)
    (index : Nat) (s : ReductionStep E) : Bool :=
  decide (s.index = index) &&
  decide (sign s.witness.leftScale = 1) && decide (sign s.witness.rightScale = 1) &&
  (s.next.isZero || decide (s.next.natDegree < p.natDegree)) &&
  SignedRemainderChain.subIsZero (DensePoly.scale s.witness.leftScale (prev * factor))
    (s.witness.quotient * p + DensePoly.scale s.witness.rightScale s.next)

/-- Literal finite replay of a reduction chain, rejecting missing, extra or
reordered factors and steps. The final equation identifies the query polynomial. -/
@[expose] def Reduction.checkFrom (sign : E → Int) (p : DensePoly E) :
    DensePoly E → List (Nat × DensePoly E) → List (ReductionStep E) → DensePoly E → Bool
  | prev, [], [], result => SignedRemainderChain.subIsZero prev result
  | prev, (i, q) :: fs, s :: ss, result =>
    s.check sign p prev q i && checkFrom sign p s.next fs ss result
  | _, _, _, _ => false

/-- Check a reduced moment for a positive-degree head. Nonzero constant heads
must use their zero-root evidence, not a degree-less-than-zero remainder. -/
@[expose] def Reduction.check (sign : E → Int) (p : DensePoly E)
    (qs : List (DensePoly E)) (es : List Nat) (r : Reduction E) : Bool :=
  decide (0 < p.natDegree) && decide (qs.length = es.length) && es.all (· ≤ 2) &&
    checkFrom sign p 1 (factors qs es) r.steps r.result

omit [One E] in
/-- Every accepted step has the exact declared factor and a checked positive
identity. No coefficient inverse or pseudo-division is performed by replay. -/
theorem ReductionStep.check_eq {sign : E → Int} {p prev factor : DensePoly E}
    {index : Nat} {s : ReductionStep E} (h : s.check sign p prev factor index = true) :
    s.index = index ∧ sign s.witness.leftScale = 1 ∧ sign s.witness.rightScale = 1 ∧
    (s.next.isZero = true ∨ s.next.natDegree < p.natDegree) ∧
    SignedRemainderChain.subIsZero (DensePoly.scale s.witness.leftScale (prev * factor))
      (s.witness.quotient * p + DensePoly.scale s.witness.rightScale s.next) = true := by
  simpa only [ReductionStep.check, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, and_assoc] using h

variable [Neg E] [Inv E]

/-- Reduce one indexed product using the shared arithmetic routines. -/
@[expose] def ReductionStep.build (sign : E → Int) (p prev factor : DensePoly E)
    (index : Nat) : ReductionStep E :=
  let div := DensePoly.positivePseudoDiv sign (prev * factor) p
  let (scale, next) := if div.remainder.isZero then (1, div.remainder)
    else Sturm.normalize sign div.remainder
  ⟨index, next, ⟨div.multiplier, div.quotient, scale⟩⟩

/-- Produce the reductions using the shared positive pseudo-division routine
and positive normalization. The result is independently replayable. -/
@[expose] def Reduction.buildFrom (sign : E → Int) (p : DensePoly E) :
    DensePoly E → List (Nat × DensePoly E) → Reduction E
  | prev, [] => ⟨[], prev⟩
  | prev, (i, q) :: fs =>
    let step := ReductionStep.build sign p prev q i
    let tail := buildFrom sign p step.next fs
    ⟨step :: tail.steps, tail.result⟩

/-- Construct a reduced moment; validity is supplied by `Reduction.check` and
its algebraic correspondence, not by an assumption about this producer.
This producer-internal primitive assumes well-shaped exponents. `buildNode`
checks their range and original query length; `QueryReduction.check_bounds`
establishes that accepted preprocessing preserves the operand length. -/
@[expose] def Reduction.build (sign : E → Int) (p : DensePoly E)
    (qs : List (DensePoly E)) (es : List Nat) : Reduction E :=
  buildFrom sign p 1 (factors qs es)

end Hex.SignDet
