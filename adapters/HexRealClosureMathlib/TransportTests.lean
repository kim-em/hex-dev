/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportClosed
public import HexRealClosureMathlib.TransportRegular
public meta import HexPoly.Dense
public meta import HexPoly.Operations
public meta import HexPoly.Instances
public meta import HexPoly.PseudoDiv
public meta import HexPoly.PseudoGcd
public meta import HexRealRoots.SignedRemainderChain
public meta import HexRealClosureMathlib.TransportPolynomial
public meta import HexRealClosureMathlib.TransportProduct

public section

namespace Hex.RealClosure.Transport.Tests


private def read (a : Hex.DensePoly Rat) : Rat := a.eval 2
private def p : Hex.DensePoly (Hex.DensePoly Rat) :=
  Hex.DensePoly.ofCoeffs #[1, Hex.DensePoly.ofCoeffs #[-2, 1], 1]

/-- The interior raw representative is structurally nonzero but denotes zero. -/
example : read (p.coeff 1) = 0 ∧ p.coeff 1 ≠ 0 := by decide +kernel

example : ¬ (∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0) := by
  intro h
  have bad := (h 1 (by decide +kernel)).mp (by decide +kernel)
  exact (by decide +kernel : p.coeff 1 ≠ 0) bad

private theorem zero : read 0 = 0 := by decide +kernel
private theorem leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0 := by
  intro _
  decide +kernel

/-- Normalized size transports despite the noncanonical interior zero. -/
example : (polynomial read p).size = p.size := polynomial_size read zero p leading

example : polynomial read p = Hex.DensePoly.ofCoeffs #[1, 0, 1] := by decide +kernel

/-- Horner uses the finite reached accumulators, with no interior reflection. -/
example : read (p.eval (Hex.DensePoly.C 3)) =
    (polynomial read p).eval (read (Hex.DensePoly.C 3)) := by
  apply Ring.polynomial_eval read zero p (Hex.DensePoly.C 3)
  · intro i hi
    change i < 3 at hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide +kernel
  · intro i hi
    change i < 3 at hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide +kernel

private theorem read_add (a b : Hex.DensePoly Rat) : read (a + b) = read a + read b :=
  Hex.DensePoly.eval_add_semiring a b 2

private theorem read_mul (a b : Hex.DensePoly Rat) : read (a * b) = read a * read b :=
  Hex.DensePoly.eval_mul_commring a b 2

private theorem read_sub (a b : Hex.DensePoly Rat) : read (a - b) = read a - read b :=
  Hex.DensePoly.eval_sub_ring a b 2

private theorem closed : Closed read (fun _ => True) :=
  { zero := trivial
    add := fun _ _ _ _ => trivial
    mul := fun _ _ _ _ => trivial
    sub := fun _ _ _ _ => trivial
    one := trivial
    natCast := fun _ => trivial
    read_zero := zero
    read_add := fun a b _ _ => read_add a b
    read_mul := fun a b _ _ => read_mul a b
    read_sub := fun a b _ _ => read_sub a b
    read_one := by decide +kernel
    read_natCast := fun n => by
      cases n with
      | zero => exact zero
      | succ n =>
        cases n with
        | zero => exact Hex.DensePoly.eval_C_semiring _ _
        | succ n => exact Hex.DensePoly.eval_C_semiring _ _ }

private def sign (a : Rat) : Int := if a < 0 then -1 else if a = 0 then 0 else 1
private def head : Hex.DensePoly (Hex.DensePoly Rat) :=
  Hex.DensePoly.ofCoeffs #[Hex.DensePoly.C (-1 : Rat), 0, 1]
private def coefficient : Hex.DensePoly Rat := Hex.DensePoly.ofCoeffs #[-2, 1]
private def query : Hex.DensePoly (Hex.DensePoly Rat) := Hex.DensePoly.ofCoeffs #[1, coefficient]
private def second : Hex.DensePoly (Hex.DensePoly Rat) :=
  Hex.DensePoly.ofCoeffs #[2 * coefficient, 2]
private def last : Hex.DensePoly Rat := Hex.DensePoly.ofCoeffs #[-12, 16, -4]
private def quotient : Hex.DensePoly (Hex.DensePoly Rat) :=
  Hex.DensePoly.ofCoeffs #[Hex.DensePoly.C (-2 : Rat) * coefficient, 2]
private def certificate : Hex.SignedRemainderChain (Hex.DensePoly Rat) :=
  { chain := #[head, second, Hex.DensePoly.C last]
    degrees := #[2, 1, 0]
    initial := ⟨1, Hex.DensePoly.C (2 * coefficient), 1⟩
    steps := #[⟨4, quotient, 1⟩]
    terminal := some (last, second) }

example : read query.leadingCoeff = 0 ∧ query.leadingCoeff ≠ 0 := by decide +kernel
private theorem accepted : Hex.SignedRemainderChain.check (fun a => sign (read a)) head query certificate = true := by
  simp only [certificate, Hex.SignedRemainderChain.check, Hex.SignedRemainderChain.checkStep,
    Hex.SignedRemainderChain.subIsZero]
  simp only [head, second, last, quotient, coefficient]
  simp only [← Array.all_toList, Array.toList_range]
  decide +kernel
example : certificate.chain.size = 3 := by
  decide +kernel

private theorem data : ChainData read (fun a => sign (read a)) sign head query certificate := by
  apply ChainData.of_closed read (fun _ => True) closed (fun a => sign (read a)) sign
    head query certificate (fun _ _ => trivial) (fun _ _ => trivial)
    { entries := fun _ _ _ _ => trivial
      initialLeft := trivial
      initialRight := trivial
      initialQuotient := fun _ _ => trivial
      stepLeft := fun _ _ => trivial
      stepRight := fun _ _ => trivial
      stepQuotient := fun _ _ _ _ => trivial
      terminalScale := fun _ _ _ => trivial
      terminalQuotient := fun _ _ _ _ _ => trivial }
    ?_ ?_
    { initialLeft := rfl
      initialRight := rfl
      stepLeft := fun _ _ => rfl
      stepRight := fun _ _ => rfl
      terminal := fun _ _ _ => rfl }
  · intro _
    change read (1 : Hex.DensePoly Rat) ≠ 0
    decide +kernel
  · intro r hr
    have member : r = head ∨ r = second ∨ r = Hex.DensePoly.C last := by
      simpa [certificate] using hr
    rcases member with rfl | rfl | rfl
    · intro _
      change read (1 : Hex.DensePoly Rat) ≠ 0
      decide +kernel
    · intro _
      change read (2 : Hex.DensePoly Rat) ≠ 0
      decide +kernel
    · intro _
      change read last ≠ 0
      decide +kernel
/-- The complete accepted source chain transports even though its query and
initial quotient lose their leading coefficients under evaluation at two. -/
example : Hex.SignedRemainderChain.check sign
    (polynomial read head) (polynomial read query) (chain read certificate) = true :=
  chain_check read zero (fun a => sign (read a)) sign head query certificate data accepted

private def reduced : Hex.DensePoly (Hex.DensePoly Rat) :=
  Hex.DensePoly.ofCoeffs #[1 + coefficient * coefficient, coefficient + coefficient]

private def productReduction : Hex.SignDet.Reduction (Hex.DensePoly Rat) :=
  { steps := [⟨0, query, ⟨1, 0, 1⟩⟩,
      ⟨0, reduced, ⟨1, Hex.DensePoly.C (coefficient * coefficient), 1⟩⟩]
    result := reduced }

private theorem reduction_accepted :
    productReduction.check (fun a => sign (read a)) head [query] [2] = true := by
  decide +kernel

/-- Product reduction uses the same closed-domain constructor, including
its final difference. The interpreted next representative loses degree. -/
example : (reduction read productReduction).check sign
    (polynomial read head) [polynomial read query] [2] = true := by
  apply reduction_check read zero closed.read_one (fun a => sign (read a)) sign
    head [query] [2] productReduction data.head
  · exact ReductionData.of_closed read (fun _ => True) closed _ _ head 1 _ _ _ data.head
      (fun _ _ => trivial) (fun i _ => closed.coeff_one read (fun _ => True) i)
      (fun _ _ _ _ => trivial)
      (fun _ _ => ⟨fun _ _ => trivial, trivial, trivial, fun _ _ => trivial⟩)
      (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => trivial)
  · exact reduction_accepted

example : (polynomial read reduced).natDegree = 0 ∧ reduced.natDegree = 1 := by
  decide +kernel

section Regular
attribute [local instance 2000] Field.toGrindField

/-- The Horner consumer works on the regular fractions at a fixed parameter.
Neither its polynomial nor intermediate results need a leading guard. -/
example {F : Type} [Field F] [DecidableEq F] (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (x : Hex.RationalFn F)
    (coefficients : ∀ i < p.size, Hex.RealClosure.Specialize.Regular embedding t (p.coeff i))
    (argument : Hex.RealClosure.Specialize.Regular embedding t x) :
    Hex.RealClosure.Specialize.evalMapped embedding (p.eval x) t =
      (polynomial (fun a => Hex.RealClosure.Specialize.evalMapped embedding a t) p).eval
        (Hex.RealClosure.Specialize.evalMapped embedding x t) := by
  classical
  have data := Evaluation.of_closed _ _ (regular_closed embedding t) p x argument coefficients
  exact Ring.polynomial_eval (fun a => Hex.RealClosure.Specialize.evalMapped embedding a t)
    (Hex.RealClosure.Specialize.evalMapped_zero embedding t)
    p x data.products data.sums

end Regular

end Hex.RealClosure.Transport.Tests
