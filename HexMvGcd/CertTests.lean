/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Cert
import all HexMvGcd.Cert
import all HexMvGcd.CertData
import all HexMvGcd.Normalize
import all HexMvGcd.View
import all HexMvPoly.Recursive
import all HexMvPoly.Basic
import all HexMvPoly.Ring
import all HexPoly.Dense
import all HexPoly.Operations

@[expose] public section

/-! Kernel regressions for canonical integer replay inside rational lifts. -/

namespace Hex.MvPoly.CertTests

open Hex

abbrev P := MvPoly 1 Int Mono.lex
abbrev Q := MvPoly 1 Rat Mono.lex

def left : P := C 2 * X 0 + C 2
def right : P := C 2 * X 0 + C 4

/-- Operations that would accept every scalar as a unit. These must never
be captured by a rational certificate or used for its integer replay. -/
@[instance_reducible] def badOps : GcdOps Int where
  gcd := fun _ _ => 1
  exactDiv := Int.ediv
  isUnit := fun _ => true
  normUnit := fun _ => 1

def leftContent : Cert.Content Int Cert.NoLeaves 0 Mono.lex :=
  .ofSteps (C 2) [.mk (C 2) 0 1 .unit, .mk (C 2) 1 1 .unit]

def rightContent : Cert.Content Int Cert.NoLeaves 0 Mono.lex :=
  .ofSteps (C 2) [.mk (C 2) 0 (C 2) .unit, .mk (C 2) 1 1 .unit]

/-- The Bézout equation is valid, but the two contents are not coprime. -/
def badSource : IntCoprimeCert 1 Mono.lex :=
  .splitBezout 0 Mono.lex (C (-1)) 1 (C 2) leftContent rightContent .unit

def forged : CoprimeCert 1 Rat Mono.lex := by
  letI : GcdOps Int := badOps
  exact .ratLift 1 1 left right badSource

theorem forged_rejected :
    checkCoprime (intModelToRat left) (intModelToRat right) forged = false := by
  decide +kernel

theorem source_rejected :
    (Cert.checkOps (S := Int) (E := Cert.NoLeaves)
      (fun _ _ _ _ _ impossible => nomatch impossible) 1).coprime
        Mono.lex left right badSource = false := by
  change (_ && false) = false
  exact Bool.and_false _

theorem not_coprime : ¬ CoprimeCofactors left right := by
  intro h
  have hl : (C 2 : P) ∣ left := ⟨X 0 + 1, by decide +kernel⟩
  have hr : (C 2 : P) ∣ right := ⟨X 0 + C 2, by decide +kernel⟩
  have hu := (polyIsUnit_iff (C 2 : P)).mpr (h (C 2) hl hr)
  have hn : polyIsUnit (C 2 : P) = false := by decide +kernel
  rw [hn] at hu
  contradiction

def goodLift : RatLiftCert 1 Mono.lex :=
  ⟨2, 3, X 0 + 1, X 0 + C 2, .bezout (C (-1)) 1⟩

def scaledLeft : Q := C 2 * (X 0 + 1)
def scaledRight : Q := C 3 * (X 0 + C 2)

theorem lift_accepted : checkRatLift scaledLeft scaledRight goodLift = true := by
  decide +kernel

theorem wrapper_accepted : checkCoprime scaledLeft scaledRight
    (.ratLift 2 3 (X 0 + 1) (X 0 + C 2) (.bezout (C (-1)) 1)) = true := by
  decide +kernel

theorem zero_scale_rejected :
    checkRatLift 0 scaledRight { goodLift with scaleL := 0 } = false := by
  decide +kernel

theorem wrong_scale_rejected :
    checkRatLift scaledLeft scaledRight { goodLift with scaleR := 4 } = false := by
  decide +kernel

theorem bad_evidence_rejected :
    checkRatLift scaledLeft scaledRight { goodLift with cert := .unit } = false := by
  decide +kernel

/-- Even a dictionary in the caller's scope cannot change integer replay. -/
theorem local_ops_rejected :
    letI : GcdOps Int := badOps
    checkRatLift scaledLeft scaledRight { goodLift with cert := .unit } = false := by
  decide +kernel

/-- Primitive but noncoprime models must fail even when a caller claims
that every integer polynomial is a unit. -/
def repeatedLift : CoprimeCert 1 Rat Mono.lex := by
  letI : GcdOps Int := badOps
  exact .ratLift 1 1 (X 0 + 1) (X 0 + 1) .unit

theorem repeated_rejected :
    checkCoprime (X 0 + 1) (X 0 + 1) repeatedLift = false := by
  decide +kernel

abbrev TestLeaves : Cert.Leaves := fun _ _ _ _ => Unit

def nestedLeaf : Cert.Coprime Int TestLeaves 1 Mono.lex :=
  .splitBezout 0 Mono.lex 0 1 1
    (.ofSteps 1 [.mk 1 0 1 (.leaf ())]) (.ofSteps 1 []) .unit

theorem leaf_rejected :
    Cert.stripCoprime? (.leaf () : Cert.Coprime Int TestLeaves 0 Mono.lex) = none := by
  rfl

theorem nested_leaf_rejected : Cert.stripCoprime? nestedLeaf = none := by
  rfl

/-- No ordinary integer certificate admits a rational-representation leaf. -/
theorem no_integer_lift (model : RatModel Int) : False := model.not_int

/-- info: 'Hex.MvPoly.CertTests.forged_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forged_rejected

/-- info: 'Hex.MvPoly.CertTests.wrapper_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrapper_accepted

/-- info: 'Hex.MvPoly.CertTests.repeated_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repeated_rejected

/-- info: 'Hex.MvPoly.CertTests.no_integer_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_integer_lift

end Hex.MvPoly.CertTests
