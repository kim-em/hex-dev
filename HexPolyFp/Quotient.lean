import HexPolyFp.Basic

/-!
Project-side quotient API for `F_p[X] / (g)`.

The executable representation keeps canonical representatives reduced by the
existing `FpPoly.modByMonic` path.  The API is intentionally small: it exposes
the quotient operations needed by Rabin-style finite-field arguments while
leaving the deepest irreducible-gcd fact as a narrow helper theorem.
-/

namespace Hex
namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

local instance : DensePoly.DivModLaws (ZMod64 p) :=
  ZMod64.instDivModLawsZMod64Fp p

/-- Canonical representatives for the quotient `F_p[X] / (g)`, reduced modulo
a monic positive-degree modulus. -/
structure Quotient (g : FpPoly p) (hmonic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) where
  val : FpPoly p
  reduced : val.degree?.getD 0 < g.degree?.getD 0

namespace Quotient

variable {g : FpPoly p} {hmonic : DensePoly.Monic g}
variable {hg_pos : 0 < g.degree?.getD 0}

omit [ZMod64.PrimeModulus p] in
@[ext] theorem ext {a b : Quotient g hmonic hg_pos} (h : a.val = b.val) :
    a = b := by
  cases a
  cases b
  simp at h
  subst h
  rfl

/-- Reduce a polynomial to its canonical quotient representative. -/
def reduce (f : FpPoly p) : Quotient g hmonic hg_pos :=
  ⟨FpPoly.modByMonic g f hmonic, by
    rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    exact DensePoly.mod_degree_lt_of_pos_degree f g hg_pos⟩

@[simp] theorem reduce_val (f : FpPoly p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val =
      FpPoly.modByMonic g f hmonic :=
  rfl

theorem reduce_val_eq_mod (f : FpPoly p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val = f % g := by
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]

/-- Polynomial congruence modulo the defining quotient polynomial. -/
def Congr (f h : FpPoly p) : Prop :=
  DensePoly.Congr f h g

theorem reduce_eq_reduce_of_congr {f h : FpPoly p} (hc : Congr (g := g) f h) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p) f h g hc

theorem congr_of_reduce_eq_reduce {f h : FpPoly p}
    (heq :
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h) :
    Congr (g := g) f h := by
  unfold Congr
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  apply @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p) f h g
  have hval := congrArg Quotient.val heq
  have hf := reduce_val_eq_mod (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f
  have hh := reduce_val_eq_mod (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h
  rw [hf, hh] at hval
  exact hval

theorem reduce_eq_reduce_iff_congr (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h ↔
      Congr (g := g) f h :=
  ⟨congr_of_reduce_eq_reduce, reduce_eq_reduce_of_congr⟩

omit [ZMod64.PrimeModulus p] in
/-- Equality of quotient elements is equality of canonical remainders. -/
theorem eq_iff_val_eq {a b : Quotient g hmonic hg_pos} :
    a = b ↔ a.val = b.val :=
  ⟨fun h => by cases h; rfl, ext⟩

/-- Zero in the quotient. -/
def zero : Quotient g hmonic hg_pos :=
  reduce 0

instance : Zero (Quotient g hmonic hg_pos) where
  zero := zero

/-- One in the quotient. -/
def one : Quotient g hmonic hg_pos :=
  reduce 1

instance : One (Quotient g hmonic hg_pos) where
  one := one

/-- The class of the polynomial indeterminate. -/
def X : Quotient g hmonic hg_pos :=
  reduce FpPoly.X

/-- Addition of canonical quotient representatives. -/
def add (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val + b.val)

instance : Add (Quotient g hmonic hg_pos) where
  add := add

/-- Negation of canonical quotient representatives. -/
def neg (a : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (-a.val)

instance : Neg (Quotient g hmonic hg_pos) where
  neg := neg

/-- Subtraction of canonical quotient representatives. -/
def sub (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val - b.val)

instance : Sub (Quotient g hmonic hg_pos) where
  sub := sub

/-- Multiplication of canonical quotient representatives. -/
def mul (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val * b.val)

instance : Mul (Quotient g hmonic hg_pos) where
  mul := mul

@[simp] theorem zero_val :
    (0 : Quotient g hmonic hg_pos).val = FpPoly.modByMonic g 0 hmonic :=
  rfl

@[simp] theorem one_val :
    (1 : Quotient g hmonic hg_pos).val = FpPoly.modByMonic g 1 hmonic :=
  rfl

@[simp] theorem X_val :
    (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).val =
      FpPoly.modByMonic g FpPoly.X hmonic :=
  rfl

@[simp] theorem add_val (a b : Quotient g hmonic hg_pos) :
    (a + b).val = FpPoly.modByMonic g (a.val + b.val) hmonic :=
  rfl

@[simp] theorem neg_val (a : Quotient g hmonic hg_pos) :
    (-a).val = FpPoly.modByMonic g (-a.val) hmonic :=
  rfl

@[simp] theorem sub_val (a b : Quotient g hmonic hg_pos) :
    (a - b).val = FpPoly.modByMonic g (a.val - b.val) hmonic :=
  rfl

@[simp] theorem mul_val (a b : Quotient g hmonic hg_pos) :
    (a * b).val = FpPoly.modByMonic g (a.val * b.val) hmonic :=
  rfl

theorem reduce_add_eq (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) =
      reduce
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        ((reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val +
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h).val) := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_add_mod (ZMod64 p) inferInstance inferInstance inferInstance
    (ZMod64.instDivModLawsZMod64Fp p) f h g

theorem reduce_mul_eq (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f * h) =
      reduce
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        ((reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val *
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h).val) := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
    (ZMod64.instDivModLawsZMod64Fp p) f h g

/-- The xgcd-based inverse candidate, normalized by the leading coefficient of
the computed gcd. -/
def inverseCandidate (a : FpPoly p) : FpPoly p :=
  DensePoly.scale (DensePoly.leadingCoeff (DensePoly.gcd a g))⁻¹
    (DensePoly.xgcd a g).left

/--
Narrow Euclidean obligation for quotient inversion.

For a nonzero canonical representative modulo a monic irreducible positive-degree
polynomial, the normalized left Bezout coefficient is a multiplicative inverse
modulo `g`.
-/
theorem mul_mod_inverseCandidate_eq_one_of_irreducible
    (hg_irr : FpPoly.Irreducible g) {a : FpPoly p}
    (ha_ne : a ≠ 0) (ha_reduced : a.degree?.getD 0 < g.degree?.getD 0) :
    (a * inverseCandidate (g := g) a) % g = (1 : FpPoly p) % g := by
  sorry

/-- Multiplicative inverse candidate in the quotient, with the conventional
junk value `0⁻¹ = 0`.  The cancellation theorem below requires irreducibility. -/
def inv (a : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  if a.val = 0 then
    0
  else
    reduce (inverseCandidate (g := g) a.val)

instance : Inv (Quotient g hmonic hg_pos) where
  inv := inv

theorem inv_zero :
    (0 : Quotient g hmonic hg_pos)⁻¹ = 0 := by
  have hzero_val : (0 : Quotient g hmonic hg_pos).val = 0 := by
    rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
  change inv (0 : Quotient g hmonic hg_pos) = 0
  unfold inv
  change (if (0 : Quotient g hmonic hg_pos).val = 0 then 0
    else reduce (inverseCandidate (g := g) (0 : Quotient g hmonic hg_pos).val)) = 0
  rw [hzero_val]
  simp

theorem mul_inv_cancel (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have ha_val_ne : a.val ≠ 0 := by
    intro hval
    apply ha
    apply ext
    change a.val = (0 : Quotient g hmonic hg_pos).val
    simpa [zero, reduce_val_eq_mod, hval] using
      (DensePoly.modByMonic_zero g hmonic).symm
  apply ext
  change (a * inv (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a).val =
    (1 : Quotient g hmonic hg_pos).val
  unfold inv
  simp [ha_val_ne]
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  change FpPoly.modByMonic g
      (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic)
      hmonic =
    FpPoly.modByMonic g 1 hmonic
  calc
    FpPoly.modByMonic g
        (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic)
        hmonic =
        (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic) % g := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    _ = (a.val * ((inverseCandidate (g := g) a.val) % g)) % g := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    _ = (a.val * inverseCandidate (g := g) a.val) % g := by
          have ha_mod : a.val % g = a.val :=
            DensePoly.mod_eq_self_of_degree_lt a.val g a.reduced
          have hmul_mod :=
            @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
              (ZMod64.instDivModLawsZMod64Fp p) a.val
              (inverseCandidate (g := g) a.val) g
          calc
            (a.val * ((inverseCandidate (g := g) a.val) % g)) % g =
                ((a.val % g) * ((inverseCandidate (g := g) a.val) % g)) % g := by
                  simp [ha_mod]
            _ = (a.val * inverseCandidate (g := g) a.val) % g := hmul_mod.symm
    _ = (1 : FpPoly p) % g :=
          mul_mod_inverseCandidate_eq_one_of_irreducible
            (g := g) hg_irr ha_val_ne a.reduced
    _ = FpPoly.modByMonic g 1 hmonic := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]

end Quotient
end FpPoly
end Hex
