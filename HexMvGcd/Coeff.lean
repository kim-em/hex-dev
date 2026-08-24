/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ring
public import HexMvPoly.Ring

@[expose] public section
set_option backward.proofsInPublic true

/-!
The coefficient-side operations and laws used by multivariate gcd algorithms.

The executable structures are deliberately weaker than their law packages.
In particular, `GcdOps.exactDiv` may return a stable junk value when its right
argument does not exactly divide its left argument; every computational caller
must validate a proposed quotient by multiplying it back.
-/

namespace Hex

universe u

/-- Executable gcd-domain operations. `exactDiv` has a law only on known exact
division by a nonzero element. -/
class GcdOps (R : Type u) where
  gcd : R → R → R
  exactDiv : R → R → R
  isUnit : R → Bool
  normUnit : R → R

/-- The canonical associate selected by `GcdOps`. -/
def normalize {R : Type u} [Mul R] [GcdOps R] (a : R) : R :=
  a * GcdOps.normUnit a

/-- Executable extended gcd in a coefficient ring where pairs admit Bézout
coefficients. -/
class BezoutOps (R : Type u) extends GcdOps R where
  xgcd : R → R → R × R

/-- Algebraic laws for `GcdOps`, separated from the executable operations so
certificate checkers do not carry proof data at runtime. -/
class LawfulGcdOps (R : Type u) [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] : Prop where
  dvd_iff : ∀ a b : R, a ∣ b ↔ ∃ c, b = a * c
  one_ne_zero : (1 : R) ≠ 0
  no_zero_div : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0
  gcd_dvd_left : ∀ a b : R, GcdOps.gcd a b ∣ a
  gcd_dvd_right : ∀ a b : R, GcdOps.gcd a b ∣ b
  dvd_gcd : ∀ a b d : R, d ∣ a → d ∣ b → d ∣ GcdOps.gcd a b
  gcd_normalized : ∀ a b : R,
    normalize (GcdOps.gcd a b) = GcdOps.gcd a b
  exactDiv_cancel : ∀ a b : R,
    b ≠ 0 → GcdOps.exactDiv (a * b) b = a
  isUnit_iff : ∀ a : R, GcdOps.isUnit a = true ↔ ∃ b, a * b = 1
  normUnit_unit : ∀ a : R, ∃ b, GcdOps.normUnit a * b = 1
  normalize_mul : ∀ a b : R, normalize (a * b) = normalize a * normalize b
  normalize_idem : ∀ a : R, normalize (normalize a) = normalize a
  normalize_unit : ∀ a : R, GcdOps.isUnit a = true → normalize a = 1

/-- Correctness of executable extended gcd. -/
class LawfulBezoutOps (R : Type u) [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R] : Prop where
  xgcd_bezout : ∀ a b : R,
    let uv := BezoutOps.xgcd a b
    uv.1 * a + uv.2 * b = normalize (GcdOps.gcd a b)

/-- Proof-only existence and maximality of gcds. This class intentionally does
not select an executable gcd operation. -/
class GcdDomainLaws (S : Type u) [Lean.Grind.CommRing S] [Dvd S] : Prop where
  dvd_iff : ∀ a b : S, a ∣ b ↔ ∃ c, b = a * c
  one_ne_zero : (1 : S) ≠ 0
  no_zero_div : ∀ a b : S, a * b = 0 → a = 0 ∨ b = 0
  gcd_exists : ∀ a b : S, ∃ g : S,
    g ∣ a ∧ g ∣ b ∧ ∀ d, d ∣ a → d ∣ b → d ∣ g

/-- Euclid cancellation in the form used by gcd-certificate maximality. -/
class CoprimeCancelLaws (S : Type u) [Lean.Grind.CommRing S] [Dvd S] : Prop where
  cancel_coprime : ∀ g a b d : S,
    (∀ e, e ∣ a → e ∣ b → ∃ u, e * u = 1) →
    d ∣ g * a → d ∣ g * b → d ∣ g

/-- A total coefficient homomorphism into a bounded prime field. The map is
certificate data rather than a typeclass because several maps may be useful
for one coefficient ring. -/
structure CoeffHom (R : Type u) (p : Nat) [Zero R] [One R] [Add R]
    [Mul R] [ZMod64.Bounds p] where
  toField : R → ZMod64 p
  map_zero : toField 0 = 0
  map_one : toField 1 = 1
  map_add : ∀ a b, toField (a + b) = toField a + toField b
  map_mul : ∀ a b, toField (a * b) = toField a * toField b

end Hex
