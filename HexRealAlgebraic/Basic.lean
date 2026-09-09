/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Nearest

public section

/-!
Canonical real algebraic numbers. Construction checks reality at the stored
separation precision; arithmetic reuses canonical algebraic arithmetic and
checks closure once on its result. The companion proves those checks succeed.
-/

namespace Hex

/-- Canonical algebraic numbers whose stored reality test succeeds. -/
@[expose]
def RealAlgebraicNumber := {a : AlgebraicNumber // a.isReal = true}

namespace RealAlgebraicNumber

/-- The underlying canonical algebraic number. -/
@[expose] def toAlgebraic (a : RealAlgebraicNumber) : AlgebraicNumber := a.val

/-- Package an algebraic number with a proof that it is real. -/
@[expose] def ofAlgebraic (a : AlgebraicNumber) (h : a.isReal = true) :
    RealAlgebraicNumber := ⟨a, h⟩

/-- Reject nonreal inputs; a successful check supplies the erased witness. -/
@[expose] def ofAlgebraic? (a : AlgebraicNumber) : Option RealAlgebraicNumber :=
  if h : a.isReal = true then some (ofAlgebraic a h) else none

/-- Exactify a lazy algebraic root and check reality. -/
@[expose] def ofRoot? (a : AlgebraicRoot) : Option RealAlgebraicNumber :=
  ofAlgebraic? a.exact

/-- Checked construction succeeds precisely on real inputs. -/
@[simp] theorem ofAlgebraic?_isSome (a : AlgebraicNumber) :
    (ofAlgebraic? a).isSome = true ↔ a.isReal = true := by
  simp [ofAlgebraic?]

/-- Successful checked construction preserves the canonical value. -/
@[simp] theorem ofAlgebraic?_eq_some (a : AlgebraicNumber) (b : RealAlgebraicNumber) :
    ofAlgebraic? a = some b ↔ a = b.toAlgebraic := by
  unfold ofAlgebraic?
  split
  · simp only [Option.some.injEq]
    exact ⟨fun h => congrArg toAlgebraic h, fun h => Subtype.ext h⟩
  · constructor
    · simp
    · intro h
      subst a
      exact False.elim (by exact ‹¬ b.toAlgebraic.isReal = true› b.property)

/-- Structural equality is equality of the underlying canonical values. -/
@[ext] theorem ext {a b : RealAlgebraicNumber} (h : a.toAlgebraic = b.toAlgebraic) :
    a = b := Subtype.ext h

/-- Zero uses the explicit stored zero isolation, without any root search. -/
@[expose] def zero : RealAlgebraicNumber := ⟨0, by
  rw [AlgebraicNumber.isReal, AlgebraicNumber.zero_square]
  decide⟩

instance : Zero RealAlgebraicNumber := ⟨zero⟩
instance : Inhabited RealAlgebraicNumber := ⟨zero⟩
instance : BEq RealAlgebraicNumber := ⟨fun a b => a.toAlgebraic == b.toAlgebraic⟩

/-- Internal closure check, unreachable-by-pipeline-invariant on operation results.
Arbitrary complex input must use the checked constructor. -/
@[expose] def Internal.pack (a : AlgebraicNumber) : RealAlgebraicNumber :=
  (ofAlgebraic? a).getD
    (Hex.panicWith zero "RealAlgebraicNumber: nonreal operation result")

/-- A real operation result passes the internal closure check unchanged. -/
@[simp] theorem pack_val (a : AlgebraicNumber) (h : a.isReal = true) :
    (Internal.pack a).toAlgebraic = a := by
  simp only [Internal.pack, ofAlgebraic?, dite_eq_left h, Option.getD_some]
  rfl

/-- Canonical rational construction followed by its reality check. -/
@[expose] def ofRat (q : Rat) : RealAlgebraicNumber := Internal.pack (AlgebraicNumber.ofRat q)

instance : One RealAlgebraicNumber := ⟨ofRat 1⟩
instance : NatCast RealAlgebraicNumber := ⟨fun n => ofRat (n : Rat)⟩
instance : IntCast RealAlgebraicNumber := ⟨fun n => ofRat (n : Rat)⟩
instance (priority := 90) (n : Nat) : OfNat RealAlgebraicNumber (n + 2) :=
  ⟨ofRat (n + 2 : Nat)⟩

/-- Canonical addition followed by its reality check. -/
@[expose] def add (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  Internal.pack (a.toAlgebraic + b.toAlgebraic)
/-- Canonical subtraction followed by its reality check. -/
@[expose] def sub (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  Internal.pack (a.toAlgebraic - b.toAlgebraic)
/-- Canonical multiplication followed by its reality check. -/
@[expose] def mul (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  Internal.pack (a.toAlgebraic * b.toAlgebraic)
/-- Canonical negation followed by its reality check. -/
@[expose] def neg (a : RealAlgebraicNumber) : RealAlgebraicNumber := Internal.pack (-a.toAlgebraic)
/-- Canonical inversion, with zero inverse zero, followed by its reality check. -/
@[expose] def inv (a : RealAlgebraicNumber) : RealAlgebraicNumber := Internal.pack a.toAlgebraic⁻¹
/-- Canonical division, including division by zero, followed by its reality check. -/
@[expose] def div (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  Internal.pack (a.toAlgebraic / b.toAlgebraic)
/-- Reuse the canonical repeated-squaring algorithm, checking only its result. -/
@[expose] def natPow (a : RealAlgebraicNumber) (n : Nat) : RealAlgebraicNumber :=
  Internal.pack (a.toAlgebraic.natPow n)
/-- Reuse canonical integer powers, checking only the final result. -/
@[expose] def intPow (a : RealAlgebraicNumber) (n : Int) : RealAlgebraicNumber :=
  Internal.pack (a.toAlgebraic.intPow n)
/-- Canonical rational scalar multiplication followed by its reality check. -/
@[expose] def smul (q : Rat) (a : RealAlgebraicNumber) : RealAlgebraicNumber :=
  Internal.pack (AlgebraicNumber.smul q a.toAlgebraic)

instance : Add RealAlgebraicNumber := ⟨add⟩
instance : Sub RealAlgebraicNumber := ⟨sub⟩
instance : Mul RealAlgebraicNumber := ⟨mul⟩
instance : Neg RealAlgebraicNumber := ⟨neg⟩
instance : Inv RealAlgebraicNumber := ⟨inv⟩
instance : Div RealAlgebraicNumber := ⟨div⟩
instance : Pow RealAlgebraicNumber Nat := ⟨natPow⟩
instance : Pow RealAlgebraicNumber Int := ⟨intPow⟩
instance : SMul Rat RealAlgebraicNumber := ⟨smul⟩
instance : SMul Nat RealAlgebraicNumber := ⟨fun n a => smul (n : Rat) a⟩
instance : SMul Int RealAlgebraicNumber := ⟨fun n a => smul (n : Rat) a⟩

/-- Conjugation reuses the real branch of canonical conjugation. -/
@[expose] def conj (a : RealAlgebraicNumber) : RealAlgebraicNumber :=
  ⟨a.toAlgebraic.conj, by
    have h := a.property
    simp [AlgebraicNumber.conj, toAlgebraic, h]⟩

/-- Conjugation fixes a real algebraic number. -/
@[simp] theorem conj_eq (a : RealAlgebraicNumber) : a.conj = a := by
  apply ext
  simp [conj, toAlgebraic, AlgebraicNumber.conj, a.property]

/-- A complex enclosure from the canonical approximation algorithm. -/
@[expose] def approxBall (a : RealAlgebraicNumber) (prec : Int := 64) :
    DyadicComplexBall := a.toAlgebraic.approx prec

/-- The real centre of an enclosure of radius at most two to minus precision. -/
@[expose] def approx (a : RealAlgebraicNumber) (prec : Int := 64) : Dyadic :=
  (a.approxBall prec).re

instance : Repr RealAlgebraicNumber where
  reprPrec a prec := Repr.addAppParen (Std.Format.text
    s!"(RealAlgebraicNumber.ofAlgebraic? ({repr a.toAlgebraic})).getD (Hex.panicWith RealAlgebraicNumber.zero \"RealAlgebraicNumber.repr: nonreal result\")") prec

end RealAlgebraicNumber
end Hex
