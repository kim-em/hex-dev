import Init.Grind.Ring.Basic
import HexModArith.Ring
import HexGfqRing.Basic

/-!
Executable quotient-ring operations for canonical representatives in `F_p[x] / (f)`.

This module extends the basic quotient wrapper with normalized addition,
multiplication, negation, subtraction, exponentiation, and the algebra-instance
surface needed by downstream finite-field layers.
-/
namespace Hex

namespace GFqRing

set_option linter.unusedSectionVars false

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- The quotient zero element. -/
def zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) : PolyQuotient f hf :=
  ofPoly f hf 0

/-- The quotient one element. -/
def one (f : FpPoly p) (hf : 0 < FpPoly.degree f) : PolyQuotient f hf :=
  ofPoly f hf 1

/-- Embed a prime-field constant as a quotient-ring constant polynomial. -/
def const (f : FpPoly p) (hf : 0 < FpPoly.degree f) (c : ZMod64 p) :
    PolyQuotient f hf :=
  ofPoly f hf (FpPoly.C c)

/-- Quotient addition reduces the sum of representatives. -/
def add {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x + repr y)

/-- Quotient multiplication reduces the product of representatives. -/
def mul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x * repr y)

/-- Quotient negation reduces the coefficientwise additive inverse. -/
def neg {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (-repr x)

/-- Quotient subtraction reduces the difference of representatives. -/
def sub {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x - repr y)

/-- Quotient exponentiation by square-and-multiply on the exponent bits, costing
`O(log n)` quotient-ring multiplications. -/
def pow {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) : PolyQuotient f hf :=
  let rec go (acc base : PolyQuotient f hf) (k : Nat) : PolyQuotient f hf :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then mul acc base else acc
      go acc' (mul base base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go (one f hf) x n

/-- Natural-number literals in the quotient ring are reduced constant polynomials. -/
def natCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) : PolyQuotient f hf :=
  const f hf (n : ZMod64 p)

/-- Natural scalar multiplication in the quotient ring. -/
def nsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) : PolyQuotient f hf :=
  let rec go (acc base : PolyQuotient f hf) (k : Nat) : PolyQuotient f hf :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then add acc base else acc
      go acc' (add base base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go (zero f hf) x n

/-- Integer literals in the quotient ring. -/
def intCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) : Int → PolyQuotient f hf
  | .ofNat n => natCast f hf n
  | .negSucc n => neg (natCast f hf (n + 1))

/-- Integer scalar multiplication in the quotient ring. -/
def zsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (i : Int) (x : PolyQuotient f hf) : PolyQuotient f hf :=
  match i with
  | .ofNat n => nsmul n x
  | .negSucc n => neg (nsmul (n + 1) x)

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Zero (PolyQuotient f hf) where
  zero := zero f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : One (PolyQuotient f hf) where
  one := one f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Add (PolyQuotient f hf) where
  add := add

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Mul (PolyQuotient f hf) where
  mul := mul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Neg (PolyQuotient f hf) where
  neg := neg

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Sub (PolyQuotient f hf) where
  sub := sub

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Pow (PolyQuotient f hf) Nat where
  pow := pow

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : NatCast (PolyQuotient f hf) where
  natCast := natCast f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} (n : Nat) :
    OfNat (PolyQuotient f hf) n where
  ofNat := natCast f hf n

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : SMul Nat (PolyQuotient f hf) where
  smul := nsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : IntCast (PolyQuotient f hf) where
  intCast := intCast f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : SMul Int (PolyQuotient f hf) where
  smul := zsmul

/-- The canonical representative of the quotient zero is the reduction of `0`. -/
@[simp] theorem repr_zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    repr (0 : PolyQuotient f hf) = reduceMod f 0 :=
  rfl

/-- The multiplicative-identity representative is the reduction of `1`. -/
@[simp] theorem repr_one (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    repr (1 : PolyQuotient f hf) = reduceMod f 1 :=
  rfl

/-- The canonical representative of a constant quotient element is the reduction of `C c`. -/
@[simp] theorem repr_const (f : FpPoly p) (hf : 0 < FpPoly.degree f) (c : ZMod64 p) :
    repr (const f hf c) = reduceMod f (FpPoly.C c) :=
  rfl

private theorem zmod64_eq_zero_of_modulus_one
    (hp : p = 1) (a : ZMod64 p) : a = 0 := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  have ha : a.val.toNat = 0 := by
    exact Nat.lt_one_iff.mp (by simpa [hp] using a.isLt)
  simpa [ZMod64.toNat_eq_val] using ha

private theorem zmod64_zero_ne_one_of_pos_degree
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    (0 : ZMod64 p) ≠ 1 := by
  intro h01
  have h10 : (1 : ZMod64 p) = 0 := h01.symm
  have hp_dvd : p ∣ 1 := (ZMod64.natCast_eq_zero_iff_dvd (p := p) 1).mp h10
  have hp : p = 1 := Nat.dvd_one.mp hp_dvd
  have hall (a : ZMod64 p) : a = 0 := zmod64_eq_zero_of_modulus_one (p := p) hp a
  have hsize : f.coeffs.size = 0 := by
    by_cases hzero : f.coeffs.size = 0
    · exact hzero
    · rcases f.normalized with hsize | hback
      · exact False.elim (hzero hsize)
      · have hpos : 0 < f.coeffs.size := Nat.pos_of_ne_zero hzero
        have hidx : f.coeffs.size - 1 < f.coeffs.size := Nat.sub_lt hpos (by decide)
        have hback_eq :
            f.coeffs.back? = some (f.coeffs[f.coeffs.size - 1]'hidx) := by
          simp [Array.back?_eq_getElem?]
        have hcoeff : f.coeffs[f.coeffs.size - 1]'hidx = (Zero.zero : ZMod64 p) :=
          hall _
        exact False.elim (hback (by simp [hback_eq, hcoeff]))
  have hdeg : FpPoly.degree f = 0 := by
    simp [FpPoly.degree, DensePoly.degree?, DensePoly.size, hsize]
  simp [hdeg] at hf

/-- Modulo any nonconstant polynomial, the zero and one quotient elements are distinct. -/
theorem zero_ne_one (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    (0 : PolyQuotient f hf) ≠ 1 := by
  intro h
  have hpoly : (0 : FpPoly p) = 1 := by
    calc
      (0 : FpPoly p) = repr (0 : PolyQuotient f hf) := by
        simp [repr_zero, reduceMod_zero f hf]
      _ = repr (1 : PolyQuotient f hf) := by
        simp [h]
      _ = (1 : FpPoly p) := by
        change repr (one f hf) = 1
        simpa [one] using reduceMod_one f hf
  have hcoeff : (0 : ZMod64 p) = 1 := by
    by_cases h10 : (1 : ZMod64 p) = 0
    · exact h10.symm
    · have hcoeffs := congrArg DensePoly.coeffs hpoly
      have hzero_coeffs : DensePoly.coeffs (0 : FpPoly p) = #[] := by rfl
      have hone_coeffs : DensePoly.coeffs (1 : FpPoly p) = #[(1 : ZMod64 p)] := by
        change DensePoly.coeffs (DensePoly.C (1 : ZMod64 p)) = #[(1 : ZMod64 p)]
        exact DensePoly.coeffs_C_of_ne_zero h10
      rw [hzero_coeffs, hone_coeffs] at hcoeffs
      simp at hcoeffs
  exact zmod64_zero_ne_one_of_pos_degree f hf hcoeff

/-- `natCast` unfolds to the corresponding constant quotient element. -/
@[simp] theorem natCast_eq_const
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    natCast f hf n = const f hf (n : ZMod64 p) :=
  rfl

/-- The canonical representative of `natCast n` is the reduction of `C (n : ZMod64 p)`. -/
@[simp] theorem repr_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    repr (natCast f hf n) = reduceMod f (FpPoly.C (n : ZMod64 p)) :=
  rfl

/-- Two natural-number casts coincide in the quotient ring whenever their prime-field casts
do. -/
theorem natCast_eq_of_zmod64_natCast_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) {m n : Nat}
    (h : (m : ZMod64 p) = (n : ZMod64 p)) :
    (m : PolyQuotient f hf) = n := by
  change const f hf (m : ZMod64 p) = const f hf (n : ZMod64 p)
  rw [h]

/-- Two natural-number casts coincide in the quotient ring whenever they agree modulo `p`. -/
theorem natCast_eq_of_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) {m n : Nat}
    (h : m % p = n % p) :
    (m : PolyQuotient f hf) = n :=
  natCast_eq_of_zmod64_natCast_eq f hf
    ((ZMod64.natCast_eq_natCast_iff (p := p) m n).2 h)

/-- Equality of natural-number casts is equivalent to equality of the underlying reduced
constant polynomials. Internal stepping stone toward `natCast_eq_natCast_iff_mod_eq`; the forward
direction projects quotient-level natCast equality to `reduceMod`-level equality. -/
theorem natCast_eq_natCast_iff_reduceMod_const_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (m n : Nat) :
    ((m : PolyQuotient f hf) = n) ↔
      reduceMod f (FpPoly.C (m : ZMod64 p)) =
        reduceMod f (FpPoly.C (n : ZMod64 p)) := by
  constructor
  · intro h
    simpa [repr_natCast] using congrArg repr h
  · intro h
    apply ext
    simpa [repr_natCast] using h

/-- Equality of natural-number casts in the quotient ring is exactly equality modulo `p`.
This is the user-facing iff form (consumed for example by `Lean.Grind.IsCharP` on the field
layer); the reverse direction reduces to `natCast_eq_of_mod_eq`. -/
theorem natCast_eq_natCast_iff_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (m n : Nat) :
    ((m : PolyQuotient f hf) = n) ↔ m % p = n % p := by
  constructor
  · intro h
    have hrepr := (natCast_eq_natCast_iff_reduceMod_const_eq f hf m n).1 h
    have hmred :
        reduceMod f (FpPoly.C (m : ZMod64 p)) = FpPoly.C (m : ZMod64 p) := by
      apply reduceMod_eq_self_of_degree_lt
      simpa using hf
    have hnred :
        reduceMod f (FpPoly.C (n : ZMod64 p)) = FpPoly.C (n : ZMod64 p) := by
      apply reduceMod_eq_self_of_degree_lt
      simpa using hf
    have hconst : FpPoly.C (m : ZMod64 p) = FpPoly.C (n : ZMod64 p) := by
      simpa [hmred, hnred] using hrepr
    have hz : (m : ZMod64 p) = (n : ZMod64 p) := by
      have hcoeff := congrArg (fun g : FpPoly p => g.coeff 0) hconst
      simpa [FpPoly.C] using hcoeff
    exact (ZMod64.natCast_eq_natCast_iff (p := p) m n).1 hz
  · intro h
    exact natCast_eq_of_mod_eq f hf h

/-- The canonical representative of a sum reduces the sum of representatives. -/
@[simp] theorem repr_add {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x + y) = reduceMod f (repr x + repr y) :=
  rfl

/-- The canonical representative of a product reduces the product of representatives. -/
@[simp] theorem repr_mul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x * y) = reduceMod f (repr x * repr y) :=
  rfl

/-- The canonical representative of a negation reduces the negation of the representative. -/
@[simp] theorem repr_neg {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (-x) = reduceMod f (-repr x) :=
  rfl

/-- The canonical representative of a difference reduces the difference of representatives. -/
@[simp] theorem repr_sub {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x - y) = reduceMod f (repr x - repr y) :=
  rfl

/-- Quotient exponentiation via the `Pow` instance agrees with the internal `pow` definition. -/
@[simp] theorem repr_pow {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    repr (x ^ n) = repr (pow x n) :=
  rfl

/-- Public alias for `reduceMod_mul_reduceMod_congr`: reducing both factors before quotient
reduction preserves the canonical representative. -/
theorem reduceMod_mul_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a * b) = reduceMod f (reduceMod f a * reduceMod f b) :=
  reduceMod_mul_reduceMod_congr f a b

/-- The canonical representative of a quotient element is already reduced. -/
@[simp] theorem reduceMod_repr {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    reduceMod f (repr x) = repr x := by
  rcases x.2 with ⟨g, hx⟩
  simp [repr, hx]

/-- `ofPoly` applied to the zero polynomial yields the canonical zero quotient element. -/
@[simp] theorem ofPoly_zero_eq_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    ofPoly f hf 0 = (0 : PolyQuotient f hf) :=
  rfl

/-- `ofPoly` applied to the one polynomial yields the canonical one quotient element. -/
@[simp] theorem ofPoly_one_eq_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    ofPoly f hf 1 = (1 : PolyQuotient f hf) :=
  rfl

/-- `ofPoly` applied to a constant polynomial agrees with `const`. -/
@[simp] theorem ofPoly_const_eq_const
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (c : ZMod64 p) :
    ofPoly f hf (FpPoly.C c) = const f hf c :=
  rfl

/-- The representative of a sum of constructed quotient elements is the
canonical reduction of the unreduced polynomial sum. This is the simp normal form
for addition through `ofPoly`. -/
@[simp] theorem repr_add_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (a b : FpPoly p) :
    repr (ofPoly f hf a + ofPoly f hf b) = reduceMod f (a + b) := by
  change reduceMod f (reduceMod f a + reduceMod f b) = reduceMod f (a + b)
  exact (reduceMod_add_reduceMod_congr f a b).symm

/-- The representative of a product of constructed quotient elements is the
canonical reduction of the unreduced polynomial product. This is the simp normal
form for multiplication through `ofPoly`. -/
@[simp] theorem repr_mul_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (a b : FpPoly p) :
    repr (ofPoly f hf a * ofPoly f hf b) = reduceMod f (a * b) := by
  change reduceMod f (reduceMod f a * reduceMod f b) = reduceMod f (a * b)
  exact (reduceMod_mul_reduceMod_congr f a b).symm

/-- The representative of a negated constructed quotient element is the
canonical reduction of the negated canonical representative. -/
@[simp] theorem repr_neg_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (a : FpPoly p) :
    repr (-(ofPoly f hf a)) = reduceMod f (-reduceMod f a) :=
  rfl

/-- The representative of a difference of constructed quotient elements is the
canonical reduction of the difference of their canonical representatives. -/
@[simp] theorem repr_sub_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (a b : FpPoly p) :
    repr (ofPoly f hf a - ofPoly f hf b) =
      reduceMod f (reduceMod f a - reduceMod f b) :=
  rfl

/-- Representative-level left-zero law used to build the quotient `Lean.Grind.Semiring`. -/
theorem repr_zero_add {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (0 + x) = repr x := by
  rw [repr_add, repr_zero]
  calc
    reduceMod f (reduceMod f 0 + repr x)
        = reduceMod f (0 + repr x) := by
          rw [reduceMod_zero f hf]
    _ = reduceMod f (repr x) := by
          rw [FpPoly.zero_add]
    _ = repr x := reduceMod_repr x

/-- Representative-level right-zero law used to build the quotient `Lean.Grind.Semiring`. -/
theorem repr_add_zero {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (x + 0) = repr x := by
  rw [repr_add, repr_zero]
  calc
    reduceMod f (repr x + reduceMod f 0)
        = reduceMod f (repr x + 0) := by
          rw [reduceMod_zero f hf]
    _ = reduceMod f (repr x) := by
          rw [FpPoly.add_zero]
    _ = repr x := reduceMod_repr x

/-- Representative-level commutativity of addition used by quotient additive reasoning. -/
theorem repr_add_comm {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x + y) = repr (y + x) := by
  simp [repr_add, FpPoly.add_comm]

/-- Representative-level associativity of addition used to build the quotient `Lean.Grind.Semiring`. -/
theorem repr_add_assoc {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y z : PolyQuotient f hf) :
    repr ((x + y) + z) = repr (x + (y + z)) := by
  rw [repr_add, repr_add, repr_add, repr_add]
  calc
    reduceMod f (reduceMod f (repr x + repr y) + repr z)
        = reduceMod f ((repr x + repr y) + repr z) := by
          exact reduceMod_add_left_reduceMod f (repr x + repr y) (repr z)
    _ = reduceMod f (repr x + (repr y + repr z)) := by
          rw [FpPoly.add_assoc]
    _ = reduceMod f (repr x + reduceMod f (repr y + repr z)) := by
          exact (reduceMod_add_right_reduceMod f (repr x) (repr y + repr z)).symm

/-- Representative-level left zero multiplication used by the quotient semiring instance. -/
theorem repr_zero_mul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (0 * x) = 0 := by
  rw [repr_mul, repr_zero]
  calc
    reduceMod f (reduceMod f 0 * repr x)
        = reduceMod f (0 * repr x) := by
          rw [reduceMod_zero f hf]
    _ = reduceMod f 0 := by
          rw [FpPoly.zero_mul]
    _ = 0 := reduceMod_zero f hf

/-- Representative-level right zero multiplication used by the quotient semiring instance. -/
theorem repr_mul_zero {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (x * 0) = 0 := by
  rw [repr_mul, repr_zero]
  calc
    reduceMod f (repr x * reduceMod f 0)
        = reduceMod f (repr x * 0) := by
          rw [reduceMod_zero f hf]
    _ = reduceMod f 0 := by
          rw [FpPoly.mul_zero]
    _ = 0 := reduceMod_zero f hf

/-- Representative-level left identity law for multiplication used by the quotient semiring instance. -/
theorem repr_one_mul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (1 * x) = repr x := by
  rw [repr_mul]
  change reduceMod f (reduceMod f 1 * repr x) = repr x
  calc
    reduceMod f (reduceMod f 1 * repr x)
        = reduceMod f (1 * repr x) := by
          exact reduceMod_mul_left_reduceMod f 1 (repr x)
    _ = reduceMod f (repr x) := by
          rw [FpPoly.one_mul]
    _ = repr x := reduceMod_repr x

/-- Representative-level right identity law for multiplication used by the quotient semiring instance. -/
theorem repr_mul_one {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (x * 1) = repr x := by
  rw [repr_mul]
  change reduceMod f (repr x * reduceMod f 1) = repr x
  calc
    reduceMod f (repr x * reduceMod f 1)
        = reduceMod f (repr x * 1) := by
          exact reduceMod_mul_right_reduceMod f (repr x) 1
    _ = reduceMod f (repr x) := by
          rw [FpPoly.mul_one]
    _ = repr x := reduceMod_repr x

/-- Representative-level commutativity of multiplication used by the quotient commutative ring instance. -/
theorem repr_mul_comm {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x * y) = repr (y * x) := by
  simp [repr_mul, FpPoly.mul_comm]

/-- Representative-level associativity of multiplication used to build the quotient `Lean.Grind.Semiring`. -/
theorem repr_mul_assoc {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y z : PolyQuotient f hf) :
    repr ((x * y) * z) = repr (x * (y * z)) := by
  rw [repr_mul, repr_mul, repr_mul, repr_mul]
  calc
    reduceMod f (reduceMod f (repr x * repr y) * repr z)
        = reduceMod f ((repr x * repr y) * repr z) := by
          exact reduceMod_mul_left_reduceMod f (repr x * repr y) (repr z)
    _ = reduceMod f (repr x * (repr y * repr z)) := by
          rw [FpPoly.mul_assoc]
    _ = reduceMod f (repr x * reduceMod f (repr y * repr z)) := by
          exact (reduceMod_mul_right_reduceMod f (repr x) (repr y * repr z)).symm

/-- Representative-level left distributivity used to build the quotient `Lean.Grind.Semiring`. -/
theorem repr_left_distrib {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y z : PolyQuotient f hf) :
    repr (x * (y + z)) = repr (x * y + x * z) := by
  rw [repr_mul, repr_add, repr_add, repr_mul, repr_mul]
  calc
    reduceMod f (repr x * reduceMod f (repr y + repr z))
        = reduceMod f (repr x * (repr y + repr z)) := by
          exact reduceMod_mul_right_reduceMod f (repr x) (repr y + repr z)
    _ = reduceMod f (repr x * repr y + repr x * repr z) := by
          rw [FpPoly.left_distrib]
    _ = reduceMod f
          (reduceMod f (repr x * repr y) + reduceMod f (repr x * repr z)) := by
          exact reduceMod_add_reduceMod_congr f (repr x * repr y) (repr x * repr z)

/-- Representative-level right distributivity used to build the quotient `Lean.Grind.Semiring`. -/
theorem repr_right_distrib {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y z : PolyQuotient f hf) :
    repr ((x + y) * z) = repr (x * z + y * z) := by
  rw [repr_mul, repr_add, repr_add, repr_mul, repr_mul]
  calc
    reduceMod f (reduceMod f (repr x + repr y) * repr z)
        = reduceMod f ((repr x + repr y) * repr z) := by
          exact reduceMod_mul_left_reduceMod f (repr x + repr y) (repr z)
    _ = reduceMod f (repr x * repr z + repr y * repr z) := by
          rw [FpPoly.right_distrib]
    _ = reduceMod f
          (reduceMod f (repr x * repr z) + reduceMod f (repr y * repr z)) := by
          exact reduceMod_add_reduceMod_congr f (repr x * repr z) (repr y * repr z)

/-- Representative-level left inverse law used to build the quotient `Lean.Grind.Ring`. -/
theorem repr_neg_add_self {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (-x + x) = 0 := by
  rw [repr_add, repr_neg]
  calc
    reduceMod f (reduceMod f (-repr x) + repr x)
        = reduceMod f (-repr x + repr x) := by
          exact reduceMod_add_left_reduceMod f (-repr x) (repr x)
    _ = reduceMod f 0 := by
          rw [FpPoly.add_left_neg]
    _ = 0 := by
          exact reduceMod_zero f hf

/-- Quotient-level subtraction law used directly by the `Lean.Grind.Ring` instance. -/
theorem sub_eq_add_neg {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    x - y = x + -y := by
  apply ext
  rw [repr_sub, repr_add, repr_neg]
  calc
    reduceMod f (repr x - repr y)
        = reduceMod f (repr x + -repr y) := by
          rw [FpPoly.sub_eq_add_neg]
    _ = reduceMod f (repr x + reduceMod f (-repr y)) := by
          exact (reduceMod_add_right_reduceMod f (repr x) (-repr y)).symm

/-- Textbook iterated addition `x + x + ⋯ + x` (`n` summands), used only as a proof
device. The public `nsmul` runs binary decomposition via `nsmul.go`; this textbook
form mediates between that implementation and the `Lean.Grind.Semiring` axioms via
`nsmul_eq_linearNSmul`. -/
private def linearNSmul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) : Nat → PolyQuotient f hf
  | 0 => 0
  | n + 1 => linearNSmul x n + x

/-- Recurrence base of `linearNSmul`. Consumed indirectly by the public `nsmul_zero`
through `nsmul_eq_linearNSmul`. -/
@[simp] private theorem linearNSmul_zero {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    linearNSmul x 0 = 0 :=
  rfl

/-- Recurrence step of `linearNSmul`. This is the textbook `n+1 ↦ pred + 1` shape
that `Lean.Grind.Semiring.nsmul_succ` consumes (via `nsmul_eq_linearNSmul`); the
shape is forbidden for the implementation `nsmul.go`, which uses binary
decomposition. -/
@[simp] private theorem linearNSmul_succ {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    linearNSmul x (n + 1) = linearNSmul x n + x :=
  rfl

/-- Even-index binary-decomposition gateway: doubling the base lets the recurrence
step over two summands at once. Consumed by `nsmul_go_eq_acc_add_linearNSmul`'s
even-residue branch. -/
private theorem linearNSmul_double {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    linearNSmul x (2 * n) = linearNSmul (add x x) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have htwo : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [htwo, linearNSmul_succ, linearNSmul_succ, ih, linearNSmul_succ]
      exact ext (repr_add_assoc (linearNSmul (x + x) n) x x)

/-- Odd-index binary-decomposition gateway: one summand peels off and the rest
collapses to the doubled-base recurrence. Consumed by
`nsmul_go_eq_acc_add_linearNSmul`'s odd-residue branch. -/
private theorem linearNSmul_double_add_one {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    linearNSmul x (2 * n + 1) = add x (linearNSmul (add x x) n) := by
  rw [linearNSmul_succ, linearNSmul_double]
  exact ext (repr_add_comm (linearNSmul (x + x) n) x)

/-- Strong-recursion bridge between the binary-decomposition loop `nsmul.go` and
the textbook recurrence `linearNSmul`: any accumulator-base-counter triple
factors as `acc + linearNSmul base k`. Consumed by `nsmul_eq_linearNSmul`. -/
private theorem nsmul_go_eq_acc_add_linearNSmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (acc base : PolyQuotient f hf) (k : Nat) :
    nsmul.go acc base k = add acc (linearNSmul base k) := by
  induction k using Nat.strongRecOn generalizing acc base with
  | ind k ih =>
      rw [nsmul.go.eq_def]
      by_cases hk : k = 0
      · subst hk
        simp only [↓reduceDIte, linearNSmul_zero]
        exact (ext (repr_add_zero acc)).symm
      · rw [dif_neg hk]
        have hlt : k / 2 < k :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide : 1 < 2)
        cases Nat.mod_two_eq_zero_or_one k with
        | inl hmod0 =>
            have hk_eq : k = 2 * (k / 2) := by
              have h := Nat.mod_add_div k 2
              omega
            have hnot : ¬k % 2 = 1 := by omega
            have hdiv : 2 * (k / 2) / 2 = k / 2 :=
              Nat.mul_div_right (k / 2) (by decide : 0 < 2)
            rw [if_neg hnot]
            calc
              nsmul.go acc (add base base) (k / 2)
                  = add acc (linearNSmul (add base base) (k / 2)) := by
                    exact ih (k / 2) hlt acc (add base base)
              _ = add acc (linearNSmul base k) := by
                    rw [hk_eq, hdiv, linearNSmul_double]
        | inr hmod1 =>
            have hk_eq : k = 2 * (k / 2) + 1 := by
              have h := Nat.mod_add_div k 2
              omega
            rw [if_pos hmod1]
            calc
              nsmul.go (add acc base) (add base base) (k / 2)
                  = add (add acc base) (linearNSmul (add base base) (k / 2)) := by
                    exact ih (k / 2) hlt (add acc base) (add base base)
              _ = add acc (add base (linearNSmul (add base base) (k / 2))) := by
                    exact ext (repr_add_assoc acc base
                      (linearNSmul (add base base) (k / 2)))
              _ = add acc (linearNSmul base (2 * (k / 2) + 1)) := by
                    rw [linearNSmul_double_add_one]
              _ = add acc (linearNSmul base k) := by
                    rw [← hk_eq]

/-- Public bridge between the binary-decomposition implementation `nsmul` and the
textbook recurrence `linearNSmul`. Consumed by `nsmul_zero` / `nsmul_succ` to
expose the recurrence shape that `Lean.Grind.Semiring` axiom fields require. -/
private theorem nsmul_eq_linearNSmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    nsmul n x = linearNSmul x n := by
  change nsmul.go (zero f hf) x n = linearNSmul x n
  rw [nsmul_go_eq_acc_add_linearNSmul]
  exact ext (repr_zero_add (linearNSmul x n))

/-- Unfolded base of the `nsmul` recurrence: zero scalar multiplication yields the quotient zero.
The implementation `nsmul.go` runs binary decomposition (via `linearNSmul`); this lemma exposes
the textbook recurrence shape that `Lean.Grind.Semiring`'s `nsmul_zero` axiom field consumes. -/
@[simp] theorem nsmul_zero {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    nsmul 0 x = 0 := by
  rw [nsmul_eq_linearNSmul]
  rfl

/-- Unfolded step of the `nsmul` recurrence. This is a theorem about the projected behaviour, not
the implementation strategy: `nsmul.go` uses binary decomposition (via `linearNSmul_double` /
`linearNSmul_double_add_one`) per the SPEC's prohibition on the textbook `n+1 ↦ pred + 1`
recursion. Consumed by `Lean.Grind.Semiring`'s `nsmul_succ` axiom field. -/
@[simp] theorem nsmul_succ {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) :
    nsmul (n + 1) x = nsmul n x + x := by
  rw [nsmul_eq_linearNSmul, nsmul_eq_linearNSmul]
  rfl

/-- Canonical representative of `nsmul 0 x` is the reduction of `0`. -/
@[simp] theorem repr_nsmul_zero {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (nsmul 0 x) = reduceMod f 0 := by
  rw [nsmul_zero]
  rfl

/-- Canonical representative of `nsmul (n + 1) x` is the reduction of the sum of the previous
nsmul's representative and `repr x`. -/
@[simp] theorem repr_nsmul_succ {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) :
    repr (nsmul (n + 1) x) = reduceMod f (repr (nsmul n x) + repr x) := by
  rw [nsmul_succ, repr_add]

private theorem fpPoly_C_add (a b : ZMod64 p) :
    FpPoly.C (a + b) = (FpPoly.C a + FpPoly.C b : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro i
  by_cases hi : i = 0
  · subst i
    change DensePoly.coeff (DensePoly.C (a + b)) 0 =
      DensePoly.coeff (DensePoly.C a + DensePoly.C b) 0
    rw [DensePoly.coeff_add_semiring, DensePoly.coeff_C,
      DensePoly.coeff_C, DensePoly.coeff_C]
    simp
  · change DensePoly.coeff (DensePoly.C (a + b)) i =
      DensePoly.coeff (DensePoly.C a + DensePoly.C b) i
    rw [DensePoly.coeff_add_semiring, DensePoly.coeff_C,
      DensePoly.coeff_C, DensePoly.coeff_C]
    simp [hi]
    show (0 : ZMod64 p) = 0 + 0
    grind

private theorem const_add (f : FpPoly p) (hf : 0 < FpPoly.degree f) (a b : ZMod64 p) :
    const f hf (a + b) = const f hf a + const f hf b := by
  apply ext
  rw [repr_const, repr_add, repr_const, repr_const]
  have ha :
      reduceMod f (FpPoly.C a) = FpPoly.C a := by
    apply reduceMod_eq_self_of_degree_lt
    simpa using hf
  have hb :
      reduceMod f (FpPoly.C b) = FpPoly.C b := by
    apply reduceMod_eq_self_of_degree_lt
    simpa using hf
  rw [ha, hb, ← fpPoly_C_add]

/-- The `OfNat` literal at `n + 1` decomposes as the `OfNat` literal at `n` plus one in the
quotient ring. Witnesses the `Lean.Grind.Semiring.natCast_succ` axiom field. -/
theorem natCast_succ (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    (OfNat.ofNat (α := PolyQuotient f hf) (n + 1)) =
      OfNat.ofNat (α := PolyQuotient f hf) n + 1 := by
  change natCast f hf (n + 1) = natCast f hf n + natCast f hf 1
  rw [natCast_eq_const, natCast_eq_const, natCast_eq_const]
  have hsucc : ((n + 1 : Nat) : ZMod64 p) = (n : ZMod64 p) + 1 := by
    simpa using Lean.Grind.Semiring.ofNat_succ (α := ZMod64 p) n
  rw [hsucc]
  exact const_add f hf (n : ZMod64 p) (1 : ZMod64 p)

/-- Natural scalar multiplication agrees with multiplication by the corresponding `natCast`.
Witnesses the `Lean.Grind.Semiring.nsmul_eq_natCast_mul` axiom field. -/
theorem nsmul_eq_natCast_mul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) :
    n • x = (Nat.cast n : PolyQuotient f hf) * x := by
  induction n with
  | zero =>
      apply ext
      change repr (nsmul 0 x) = repr ((0 : PolyQuotient f hf) * x)
      rw [repr_nsmul_zero, repr_zero_mul]
      exact reduceMod_zero f hf
  | succ n ih =>
      calc
        (n + 1) • x = n • x + x := by exact nsmul_succ n x
        _ = (Nat.cast n : PolyQuotient f hf) * x + x := by rw [ih]
        _ = ((Nat.cast n : PolyQuotient f hf) + 1) * x := by
          apply ext
          calc
            repr ((Nat.cast n : PolyQuotient f hf) * x + x)
                = repr ((Nat.cast n : PolyQuotient f hf) * x + 1 * x) := by
                  rw [repr_add, repr_add, repr_one_mul]
            _ = repr (((Nat.cast n : PolyQuotient f hf) + 1) * x) := by
                  exact (repr_right_distrib (Nat.cast n : PolyQuotient f hf) 1 x).symm
        _ = (Nat.cast (n + 1) : PolyQuotient f hf) * x := by
          have hcast :
              (Nat.cast (n + 1) : PolyQuotient f hf) =
                (Nat.cast n : PolyQuotient f hf) + 1 := by
            exact natCast_succ f hf n
          rw [hcast]

/-- Integer cast of a non-negative integer unfolds to the corresponding `natCast`. -/
@[simp] theorem intCast_ofNat
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    intCast f hf (.ofNat n) = natCast f hf n :=
  rfl

/-- Integer cast of `-(n + 1)` is the negation of the `(n + 1)` natural-number cast. -/
@[simp] theorem intCast_negSucc
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    intCast f hf (.negSucc n) = -(natCast f hf (n + 1)) :=
  rfl

/-- Canonical representative of `intCast (Int.ofNat n)` is the reduction of `C (n : ZMod64 p)`. -/
@[simp] theorem repr_intCast_ofNat
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    repr (intCast f hf (.ofNat n)) = reduceMod f (FpPoly.C (n : ZMod64 p)) :=
  rfl

/-- Canonical representative of `intCast (Int.negSucc n)` is the reduction of the negation of the
reduced `C (n + 1 : ZMod64 p)`. The double `reduceMod` is the projection of the negation of the
canonical `natCast` representative. -/
@[simp] theorem repr_intCast_negSucc
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    repr (intCast f hf (.negSucc n)) =
      reduceMod f (-reduceMod f (FpPoly.C ((n + 1 : Nat) : ZMod64 p))) :=
  rfl

/-- Integer scalar multiplication by a non-negative integer unfolds to natural scalar
multiplication. -/
@[simp] theorem zsmul_ofNat {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) :
    zsmul (.ofNat n) x = nsmul n x :=
  rfl

/-- Integer scalar multiplication by `-(n + 1)` is the negation of the `(n + 1)` natural scalar
multiplication. -/
@[simp] theorem zsmul_negSucc {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) :
    zsmul (.negSucc n) x = -(nsmul (n + 1) x) :=
  rfl

/-- Canonical representative of `zsmul (Int.ofNat n) x` reduces to the `nsmul`-level
representative. -/
@[simp] theorem repr_zsmul_ofNat {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) :
    repr (zsmul (.ofNat n) x) = repr (nsmul n x) :=
  rfl

/-- Canonical representative of `zsmul (Int.negSucc n) x` is the reduction of the negation of the
`(n + 1)` natural scalar multiplication's representative. -/
@[simp] theorem repr_zsmul_negSucc {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) :
    repr (zsmul (.negSucc n) x) = reduceMod f (-repr (nsmul (n + 1) x)) :=
  rfl

/-- Negation of the quotient zero is the quotient zero. Used by `neg_zsmul_eq` and
`intCast_neg_eq` (the `Lean.Grind.Ring.neg_zsmul` / `intCast_neg` axiom witnesses) for the
boundary `n = 0` case. -/
theorem neg_zero_eq {f : FpPoly p} {hf : 0 < FpPoly.degree f} :
    -(0 : PolyQuotient f hf) = 0 := by
  apply ext
  rw [repr_neg, repr_zero, reduceMod_zero f hf, FpPoly.neg_zero, reduceMod_zero f hf]

/-- Double negation in the quotient ring is the identity. Proved by the textbook additive-group
calculation `-(-x) = -(-x) + (-x + x) = (-(-x) + -x) + x = 0 + x = x`. Used by `neg_zsmul_eq`
and `intCast_neg_eq` for the `Int.negSucc` case. -/
theorem neg_neg_eq {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    -(-x) = x := by
  calc
    -(-x) = -(-x) + 0 := by
      apply ext
      exact (repr_add_zero (-(-x))).symm
    _ = -(-x) + (-x + x) := by
      have h : -x + x = 0 := by
        apply ext
        simpa [repr_zero, reduceMod_zero f hf] using repr_neg_add_self x
      rw [h]
    _ = (-(-x) + -x) + x := by
      apply ext
      exact (repr_add_assoc (-(-x)) (-x) x).symm
    _ = 0 + x := by
      have h : -(-x) + -x = 0 := by
        apply ext
        simpa [repr_zero, reduceMod_zero f hf] using repr_neg_add_self (-x)
      rw [h]
    _ = x := by
      apply ext
      exact repr_zero_add x

/-- Negation distributes over integer scalar multiplication. Witnesses the
`Lean.Grind.Ring.neg_zsmul` axiom field. The three branches handle `i = Int.ofNat 0`,
`i = Int.ofNat (n + 1)`, and `i = Int.negSucc n` separately because `Int.neg` evaluates
differently on each. -/
theorem neg_zsmul_eq {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (i : Int) (a : PolyQuotient f hf) :
    -i • a = -(i • a) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change nsmul 0 a = -(nsmul 0 a)
          rw [nsmul_zero]
          exact (neg_zero_eq (f := f) (hf := hf)).symm
      | succ n =>
          rfl
  | negSucc n =>
      exact (neg_neg_eq (nsmul (n + 1) a)).symm

/-- Negation distributes over integer cast. Witnesses the `Lean.Grind.Ring.intCast_neg` axiom
field. Three branches mirror `neg_zsmul_eq`. -/
theorem intCast_neg_eq (f : FpPoly p) (hf : 0 < FpPoly.degree f)
    (i : Int) :
    ↑(-i) = -(↑i : PolyQuotient f hf) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          exact (neg_zero_eq (f := f) (hf := hf)).symm
      | succ n =>
          rfl
  | negSucc n =>
      exact (neg_neg_eq (natCast f hf (n + 1))).symm

/-- Proof-only linear recurrence `x^(n+1) = x^n * x`, used to discharge the
`pow_zero` / `pow_succ` fields of the `Lean.Grind.Semiring` instance. The
executable `pow` is square-and-multiply (`O(log n)`); `pow_eq_linearPow` ties
the two together. -/
private def linearPow {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) : Nat → PolyQuotient f hf
  | 0 => 1
  | n + 1 => linearPow x n * x

@[simp] private theorem linearPow_zero {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    linearPow x 0 = 1 :=
  rfl

@[simp] private theorem linearPow_succ {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    linearPow x (n + 1) = linearPow x n * x :=
  rfl

private theorem linearPow_mul_assoc {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (a b c : PolyQuotient f hf) :
    a * b * c = a * (b * c) := by
  apply ext
  exact repr_mul_assoc a b c

private theorem linearPow_mul_assoc_raw {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (a b c : PolyQuotient f hf) :
    mul (mul a b) c = mul a (mul b c) := by
  apply ext
  exact repr_mul_assoc a b c

private theorem linearPow_mul_comm {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (a b : PolyQuotient f hf) :
    a * b = b * a := by
  apply ext
  exact repr_mul_comm a b

private theorem linearPow_mul_one_raw {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (a : PolyQuotient f hf) :
    mul a 1 = a := by
  apply ext
  exact repr_mul_one a

private theorem linearPow_one_mul_raw {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (a : PolyQuotient f hf) :
    mul (one f hf) a = a := by
  apply ext
  exact repr_one_mul a

private theorem linearPow_double {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    linearPow x (2 * n) = linearPow (mul x x) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [htwo]
      change linearPow x ((2 * n + 1) + 1) =
        linearPow (mul x x) n * mul x x
      rw [linearPow_succ, linearPow_succ, ih]
      exact linearPow_mul_assoc (linearPow (x * x) n) x x

private theorem linearPow_double_add_one {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    linearPow x (2 * n + 1) = mul x (linearPow (mul x x) n) := by
  rw [linearPow_succ, linearPow_double]
  exact linearPow_mul_comm (linearPow (x * x) n) x

private theorem pow_go_eq_acc_mul_linearPow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (acc base : PolyQuotient f hf) (k : Nat) :
    pow.go acc base k = mul acc (linearPow base k) := by
  induction k using Nat.strongRecOn generalizing acc base with
  | ind k ih =>
      rw [pow.go.eq_def]
      by_cases hk : k = 0
      · simp [hk, linearPow_mul_one_raw]
      · rw [dif_neg hk]
        have hlt : k / 2 < k :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide : 1 < 2)
        cases Nat.mod_two_eq_zero_or_one k with
        | inl hmod0 =>
            have hk_eq : k = 2 * (k / 2) := by
              have h := Nat.mod_add_div k 2
              omega
            have hnot : ¬k % 2 = 1 := by omega
            have hdiv : 2 * (k / 2) / 2 = k / 2 :=
              Nat.mul_div_right (k / 2) (by decide : 0 < 2)
            rw [if_neg hnot]
            calc
              pow.go acc (mul base base) (k / 2)
                  = mul acc (linearPow (mul base base) (k / 2)) := by
                    exact ih (k / 2) hlt acc (mul base base)
              _ = mul acc (linearPow base k) := by
                    rw [hk_eq, hdiv, linearPow_double]
        | inr hmod1 =>
            have hk_eq : k = 2 * (k / 2) + 1 := by
              have h := Nat.mod_add_div k 2
              omega
            rw [if_pos hmod1]
            calc
              pow.go (mul acc base) (mul base base) (k / 2)
                  = mul (mul acc base) (linearPow (mul base base) (k / 2)) := by
                    exact ih (k / 2) hlt (mul acc base) (mul base base)
              _ = mul acc (mul base (linearPow (mul base base) (k / 2))) := by
                    exact @linearPow_mul_assoc_raw p _ _ f hf acc base
                      (linearPow (mul base base) (k / 2))
              _ = mul acc (linearPow base (2 * (k / 2) + 1)) := by
                    rw [linearPow_double_add_one]
              _ = mul acc (linearPow base k) := by
                    rw [← hk_eq]

/-- The executable square-and-multiply `pow` returns the same element as the
proof-only linear recurrence `linearPow`. The `Lean.Grind.Semiring` instance
rewrites by this equality to discharge its `pow_succ` field. -/
private theorem pow_eq_linearPow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    pow x n = linearPow x n := by
  change pow.go (one f hf) x n = linearPow x n
  rw [pow_go_eq_acc_mul_linearPow]
  exact linearPow_one_mul_raw (linearPow x n)

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Lean.Grind.Semiring (PolyQuotient f hf) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply ext
    exact repr_add_zero a
  · intro a b
    apply ext
    exact repr_add_comm a b
  · intro a b c
    apply ext
    exact repr_add_assoc a b c
  · intro a b c
    apply ext
    exact repr_mul_assoc a b c
  · intro a
    apply ext
    exact repr_mul_one a
  · intro a
    apply ext
    exact repr_one_mul a
  · intro a b c
    apply ext
    exact repr_left_distrib a b c
  · intro a b c
    apply ext
    exact repr_right_distrib a b c
  · intro a
    apply ext
    simp [repr_zero, reduceMod_zero f hf, repr_zero_mul a]
  · intro a
    apply ext
    simp [repr_zero, reduceMod_zero f hf, repr_mul_zero a]
  · intro a
    change pow a 0 = 1
    rw [pow_eq_linearPow]
    rfl
  · intro a n
    change pow a (n + 1) = pow a n * a
    rw [pow_eq_linearPow, pow_eq_linearPow]
    rfl
  · intro n
    exact natCast_succ f hf n
  · intro n
    rfl
  · intro n a
    exact nsmul_eq_natCast_mul n a

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Lean.Grind.Ring (PolyQuotient f hf) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply ext
    simpa [repr_zero, reduceMod_zero f hf] using repr_neg_add_self a
  · intro a b
    exact sub_eq_add_neg a b
  · intro i a
    exact neg_zsmul_eq i a
  · intro n a
    rfl
  · intro n
    rfl
  · intro i
    exact intCast_neg_eq f hf i

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Lean.Grind.CommRing (PolyQuotient f hf) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  apply ext
  exact repr_mul_comm a b

end GFqRing

end Hex
