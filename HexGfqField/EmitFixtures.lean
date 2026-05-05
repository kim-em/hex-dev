import Hex.Conformance.Emit
import HexGfqField.Operations

/-!
JSONL emit driver for the `hex-gfq-field` oracle.

`lake exe hexgfqfield_emit_fixtures` writes one `gfqfield` fixture
record plus five `result` records per case to `stdout` (or to
`$HEX_FIXTURE_OUTPUT` when set).  The companion oracle driver
`scripts/oracle/gfqfield_flint.py` reads the same stream and re-runs
each operation through python-flint's `fq_default_ctx` configured
with the same explicit modulus.

Cases cover `F_p[x] / (m(x))` for every `(p, n)` with
`p ∈ {2, 3, 5, 7}` and `n ∈ {2, 3, 4, 6}` (one case per pair, sixteen
in total).  For each case we emit:

* `mul`  — coefficients of `(a * b) mod m` in `F_p`;
* `inv`  — coefficients of `a⁻¹` (well-defined: `a` is nonzero);
* `div`  — coefficients of `a / b` (well-defined: `b` is nonzero);
* `frob` — coefficients of the Frobenius `a^p`;
* `zpow` — coefficients of `a^zexp` for the integer exponent carried
  by the fixture (positive and negative exponents are exercised
  across the matrix).

Each modulus is asserted irreducible by a per-case axiom; this
matches the existing pattern in `HexGfqField/Conformance.lean` (which
axiomatises irreducibility of `x^4 + 2` over `F_5`) and is required
by the field operations (`inv`, `div`, `zpow`) which take an
`FpPoly.Irreducible` hypothesis.  python-flint independently rejects
non-irreducible moduli at oracle time, so a typo in any axiom would
surface as a CI failure rather than a silent miscompare.
-/

namespace Hex.GFqFieldEmit

open Hex.Conformance.Emit
open Hex
open Hex.GFqField

private def lib : String := "HexGfqField"

private theorem prime_two : Hex.Nat.Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem prime_three : Hex.Nat.Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · simp at hm
  · exact Or.inr rfl

private theorem prime_five : Hex.Nat.Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · simp at hm
  · simp at hm
  · simp at hm
  · exact Or.inr rfl

private theorem prime_seven : Hex.Nat.Prime 7 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · simp at hm
  · simp at hm
  · simp at hm
  · simp at hm
  · simp at hm
  · exact Or.inr rfl

private instance bounds_two : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
private instance bounds_three : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance bounds_five : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance bounds_seven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private instance pm_two : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime prime_two
private instance pm_three : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime prime_three
private instance pm_five : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime prime_five
private instance pm_seven : ZMod64.PrimeModulus 7 :=
  ZMod64.primeModulusOfPrime prime_seven

/-- Build an `FpPoly p` from a `Nat` coefficient list (constant term first).
Used for the per-case `a` / `b` operands at runtime; the moduli below
are constructed directly as struct literals so `decide` can discharge
the positive-degree obligation without recursing through the
`trimTrailingZeros` pass that `ofCoeffs` would interpose. -/
private def mkPoly {p : Nat} [ZMod64.Bounds p] (coeffs : List Nat) : FpPoly p :=
  FpPoly.ofCoeffs (coeffs.toArray.map (fun n => ZMod64.ofNat p n))

/-- Lift an `FpPoly p` to `List Int` via the canonical `[0, p)` representative. -/
private def liftCoeffs {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Int :=
  f.toArray.toList.map (fun c => Int.ofNat c.toNat)

private theorem one_ne_zero_two : (1 : ZMod64 2) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 2) 1 0).mp h
  simp at hm

private theorem one_ne_zero_three : (1 : ZMod64 3) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 3) 1 0).mp h
  simp at hm

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem one_ne_zero_seven : (1 : ZMod64 7) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 7) 1 0).mp h
  simp at hm

/-- Run one case for a fully-specified modulus: emit one `gfqfield`
fixture plus the five op results.  Each call site supplies the
prime witness `hp`, modulus `m`, positive-degree and irreducibility
proofs, the case identifier, the unreduced operand coefficient
lists, and the `zpow` exponent. -/
private def emitAt
    {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hp : Hex.Nat.Prime p)
    (m : FpPoly p) (hpos : 0 < FpPoly.degree m)
    (hirr : FpPoly.Irreducible m)
    (caseId : String) (aCoeffs bCoeffs : List Nat) (zexp : Int) :
    IO Unit := do
  let aPoly : FpPoly p := mkPoly aCoeffs
  let bPoly : FpPoly p := mkPoly bCoeffs
  let xa : FiniteField m hpos hp hirr := ofPoly m hpos hp hirr aPoly
  let xb : FiniteField m hpos hp hirr := ofPoly m hpos hp hirr bPoly
  emitGfqFieldFixture lib caseId (Int.ofNat p)
    (liftCoeffs m) (liftCoeffs (repr xa)) (liftCoeffs (repr xb)) zexp
  emitResult lib caseId "mul"  (polyValue (liftCoeffs (repr (xa * xb))))
  emitResult lib caseId "inv"  (polyValue (liftCoeffs (repr xa⁻¹)))
  emitResult lib caseId "div"  (polyValue (liftCoeffs (repr (xa / xb))))
  emitResult lib caseId "frob" (polyValue (liftCoeffs (repr (frob xa))))
  emitResult lib caseId "zpow" (polyValue (liftCoeffs (repr (zpow xa zexp))))

/-! ## Per-modulus declarations and emit helpers.

Sixteen `(p, n)` pairs.  For each, define the irreducible modulus,
record positive-degree by `decide`, and axiomatise irreducibility.
Each modulus was independently verified irreducible by python-flint
(`fq_default_ctx` rejects non-irreducible moduli). -/

-- p = 2

/-- `x^2 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n2 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 1]
    normalized := Or.inr (by simpa using one_ne_zero_two) }
private theorem m_p2_n2_pos : 0 < FpPoly.degree m_p2_n2 := by decide
private axiom m_p2_n2_irr : FpPoly.Irreducible m_p2_n2

/-- `x^3 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n3 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_two) }
private theorem m_p2_n3_pos : 0 < FpPoly.degree m_p2_n3 := by decide
private axiom m_p2_n3_irr : FpPoly.Irreducible m_p2_n3

/-- `x^4 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n4 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_two) }
private theorem m_p2_n4_pos : 0 < FpPoly.degree m_p2_n4 := by decide
private axiom m_p2_n4_irr : FpPoly.Irreducible m_p2_n4

/-- `x^6 + x + 1` — irreducible over `F_2`. -/
private def m_p2_n6 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 0, 0, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_two) }
private theorem m_p2_n6_pos : 0 < FpPoly.degree m_p2_n6 := by decide
private axiom m_p2_n6_irr : FpPoly.Irreducible m_p2_n6

-- p = 3

/-- `x^2 + 1` — irreducible over `F_3` (-1 is a non-square mod 3). -/
private def m_p3_n2 : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_three) }
private theorem m_p3_n2_pos : 0 < FpPoly.degree m_p3_n2 := by decide
private axiom m_p3_n2_irr : FpPoly.Irreducible m_p3_n2

/-- `x^3 + 2x + 1` — irreducible over `F_3`. -/
private def m_p3_n3 : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 2, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_three) }
private theorem m_p3_n3_pos : 0 < FpPoly.degree m_p3_n3 := by decide
private axiom m_p3_n3_irr : FpPoly.Irreducible m_p3_n3

/-- `x^4 + 2x^3 + 2` — Conway polynomial for `GF(81)`. -/
private def m_p3_n4 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 0, 0, 2, 1]
    normalized := Or.inr (by simpa using one_ne_zero_three) }
private theorem m_p3_n4_pos : 0 < FpPoly.degree m_p3_n4 := by decide
private axiom m_p3_n4_irr : FpPoly.Irreducible m_p3_n4

/-- `x^6 + 2x^4 + x^2 + 2x + 2` — Conway polynomial for `GF(729)`. -/
private def m_p3_n6 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 2, 1, 0, 2, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_three) }
private theorem m_p3_n6_pos : 0 < FpPoly.degree m_p3_n6 := by decide
private axiom m_p3_n6_irr : FpPoly.Irreducible m_p3_n6

-- p = 5

/-- `x^2 + 4x + 2` — Conway polynomial for `GF(25)`. -/
private def m_p5_n2 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 4, 1]
    normalized := Or.inr (by simpa using one_ne_zero_five) }
private theorem m_p5_n2_pos : 0 < FpPoly.degree m_p5_n2 := by decide
private axiom m_p5_n2_irr : FpPoly.Irreducible m_p5_n2

/-- `x^3 + 3x + 3` — Conway polynomial for `GF(125)`. -/
private def m_p5_n3 : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 3, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_five) }
private theorem m_p5_n3_pos : 0 < FpPoly.degree m_p5_n3 := by decide
private axiom m_p5_n3_irr : FpPoly.Irreducible m_p5_n3

/-- `x^4 + 2` — irreducible over `F_5` (matches `HexGfqField.Conformance`). -/
private def m_p5_n4 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 0, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_five) }
private theorem m_p5_n4_pos : 0 < FpPoly.degree m_p5_n4 := by decide
private axiom m_p5_n4_irr : FpPoly.Irreducible m_p5_n4

/-- `x^6 + x^4 + 4x^3 + x^2 + 2` — Conway polynomial for `GF(15625)`. -/
private def m_p5_n6 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1, 4, 1, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_five) }
private theorem m_p5_n6_pos : 0 < FpPoly.degree m_p5_n6 := by decide
private axiom m_p5_n6_irr : FpPoly.Irreducible m_p5_n6

-- p = 7

/-- `x^2 + 6x + 3` — Conway polynomial for `GF(49)`. -/
private def m_p7_n2 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 1]
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
private theorem m_p7_n2_pos : 0 < FpPoly.degree m_p7_n2 := by decide
private axiom m_p7_n2_irr : FpPoly.Irreducible m_p7_n2

/-- `x^3 + 6x^2 + 4` — Conway polynomial for `GF(343)`. -/
private def m_p7_n3 : FpPoly 7 :=
  { coeffs := #[(4 : ZMod64 7), 0, 6, 1]
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
private theorem m_p7_n3_pos : 0 < FpPoly.degree m_p7_n3 := by decide
private axiom m_p7_n3_irr : FpPoly.Irreducible m_p7_n3

/-- `x^4 + 5x^2 + 4x + 3` — Conway polynomial for `GF(2401)`. -/
private def m_p7_n4 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 4, 5, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
private theorem m_p7_n4_pos : 0 < FpPoly.degree m_p7_n4 := by decide
private axiom m_p7_n4_irr : FpPoly.Irreducible m_p7_n4

/-- `x^6 + x^4 + 5x^3 + 4x^2 + 6x + 3` — Conway polynomial for `GF(7^6)`. -/
private def m_p7_n6 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 4, 5, 1, 0, 1]
    normalized := Or.inr (by simpa using one_ne_zero_seven) }
private theorem m_p7_n6_pos : 0 < FpPoly.degree m_p7_n6 := by decide
private axiom m_p7_n6_irr : FpPoly.Irreducible m_p7_n6

end Hex.GFqFieldEmit

open Hex.GFqFieldEmit in
def main : IO Unit := do
  -- p = 2 (Frobenius is squaring; covers GF(4), GF(8), GF(16), GF(64)).
  emitAt prime_two  m_p2_n2 m_p2_n2_pos m_p2_n2_irr "p2/n2/typical" [1, 1] [1, 0, 1]    3
  emitAt prime_two  m_p2_n3 m_p2_n3_pos m_p2_n3_irr "p2/n3/typical" [0, 1, 1] [1, 0, 0, 1] (-2)
  emitAt prime_two  m_p2_n4 m_p2_n4_pos m_p2_n4_irr "p2/n4/typical" [1, 0, 1, 1] [0, 1, 0, 0, 1] 4
  emitAt prime_two  m_p2_n6 m_p2_n6_pos m_p2_n6_irr "p2/n6/typical" [1, 1, 0, 1] [0, 1, 1, 0, 0, 1] (-3)
  -- p = 3.
  emitAt prime_three m_p3_n2 m_p3_n2_pos m_p3_n2_irr "p3/n2/typical" [1, 2] [2, 1] (-2)
  emitAt prime_three m_p3_n3 m_p3_n3_pos m_p3_n3_irr "p3/n3/typical" [2, 1, 1] [1, 0, 2] 3
  emitAt prime_three m_p3_n4 m_p3_n4_pos m_p3_n4_irr "p3/n4/typical" [1, 2, 0, 1] [2, 0, 1, 2] (-3)
  emitAt prime_three m_p3_n6 m_p3_n6_pos m_p3_n6_irr "p3/n6/typical" [1, 0, 2, 1, 0, 2] [2, 1, 0, 0, 1, 1] 2
  -- p = 5.
  emitAt prime_five  m_p5_n2 m_p5_n2_pos m_p5_n2_irr "p5/n2/typical" [3, 2] [4, 1] 4
  emitAt prime_five  m_p5_n3 m_p5_n3_pos m_p5_n3_irr "p5/n3/typical" [2, 3, 4] [1, 0, 2] (-2)
  emitAt prime_five  m_p5_n4 m_p5_n4_pos m_p5_n4_irr "p5/n4/typical" [2, 3] [4, 1, 0, 1] (-2)
  emitAt prime_five  m_p5_n6 m_p5_n6_pos m_p5_n6_irr "p5/n6/typical" [4, 0, 1, 2, 3, 1] [1, 2, 0, 3, 0, 4] 3
  -- p = 7.
  emitAt prime_seven m_p7_n2 m_p7_n2_pos m_p7_n2_irr "p7/n2/typical" [4, 5] [6, 2] 3
  emitAt prime_seven m_p7_n3 m_p7_n3_pos m_p7_n3_irr "p7/n3/typical" [3, 6, 1] [5, 2, 4] (-2)
  emitAt prime_seven m_p7_n4 m_p7_n4_pos m_p7_n4_irr "p7/n4/typical" [1, 2, 4, 6] [5, 3, 0, 1] (-3)
  emitAt prime_seven m_p7_n6 m_p7_n6_pos m_p7_n6_irr "p7/n6/typical" [6, 0, 5, 2, 4, 1] [1, 4, 2, 0, 5, 3] 2
