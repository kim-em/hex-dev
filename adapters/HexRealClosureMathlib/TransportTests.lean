/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportClosed
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
  apply polynomial_eval read zero p (Hex.DensePoly.C 3) leading
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
  ⟨trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, zero,
    fun a b _ _ => read_add a b, fun a b _ _ => read_mul a b⟩

private theorem products (a b : Hex.DensePoly (Hex.DensePoly Rat)) : Product read a b :=
  Product.of_closed read (fun _ => True) closed a b (fun _ _ => trivial) (fun _ _ => trivial)

private theorem scaling (c : Hex.DensePoly Rat) (a : Hex.DensePoly (Hex.DensePoly Rat)) :
    Scaling read c a := ⟨fun i _ => read_mul c (a.coeff i)⟩

private theorem difference (a b : Hex.DensePoly (Hex.DensePoly Rat)) : Difference read a b :=
  ⟨fun i _ => read_sub (a.coeff i) (b.coeff i)⟩

private theorem sums (a b : Hex.DensePoly (Hex.DensePoly Rat)) : Sum read a b :=
  ⟨fun i _ => read_add (a.coeff i) (b.coeff i)⟩

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

private theorem recurrence (a b c : Hex.DensePoly (Hex.DensePoly Rat))
    (left : Hex.DensePoly Rat) (q : Hex.DensePoly (Hex.DensePoly Rat)) (right : Hex.DensePoly Rat) :
    Recurrence read a b c left q right :=
  ⟨scaling _ _, products _ _, scaling _ _, difference _ _, difference _ _⟩

private theorem data : ChainData read (fun a => sign (read a)) sign head query certificate := by
  refine {
    head := ?_
    entries := ?_
    initial := ?_
    initialLeft := rfl
    initialRight := rfl
    recurrences := fun _ _ => recurrence _ _ _ _ _ _
    stepLeft := fun _ _ => rfl
    stepRight := fun _ _ => rfl
    terminal := fun _ _ _ => ⟨scaling _ _, products _ _, difference _ _⟩
    terminalSign := fun _ _ _ => rfl }
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
  · refine ⟨⟨?_⟩, products _ _, scaling _ _, products _ _, scaling _ _, sums _ _, difference _ _⟩
    intro i hi
    change i < 2 at hi
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> decide +kernel

/-- The complete accepted source chain transports even though its query and
initial quotient lose their leading coefficients at the selected root. -/
example : Hex.SignedRemainderChain.check sign
    (polynomial read head) (polynomial read query) (chain read certificate) = true :=
  chain_check read zero (fun a => sign (read a)) sign head query certificate data accepted

end Hex.RealClosure.Transport.Tests
