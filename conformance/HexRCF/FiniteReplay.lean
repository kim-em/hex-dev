/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients.Replay
public section

namespace Hex.RCF.FiniteReplayTests
open Hex RealCoefficients
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private abbrev hw : atomWitness SquareTwo.polynomial SquareTwo.square := by decide
private abbrev hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide
private abbrev root := SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square hw hp
private theorem real : SquareTwo.square.meetsRealAxis = true := by decide
private def values : Fin 2 → PolyQuot SquareTwo.polynomial root :=
  ![SquareTwo.coordinate SquareTwo.square hw hp, 1]
private def formula : RealFormula.QF 3 :=
  .and (.atom ⟨MvPoly.X 2 ^ 2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 2, .lt⟩) (.atom ⟨MvPoly.X 2 - 2, .lt⟩))
private def input : Replay.Input SquareTwo.polynomial SquareTwo.square hw hp Nat 2 :=
  ⟨values, formula, .existsReal, [values 0], 7⟩
private def proposed := Replay.build input real 256 5

#guard match proposed with
  | .ok cert => Replay.check input cert == .ok true
  | .error _ => false

-- Mutations reuse the exact frozen envelope, without restarting search.
#guard match proposed with
  | .ok cert =>
      Replay.check {input with context := 8} cert == .error .binding &&
      Replay.check {input with quantifier := .forallReal} cert == .error .binding &&
      Replay.check {input with formula := .not formula} cert == .error .binding &&
      Replay.check {input with values := ![values 1, values 0]} cert == .error .binding &&
      Replay.check {input with divisors := []} cert == .error .binding
  | .error _ => false

#guard match proposed with
  | .ok cert =>
      Replay.check input {cert with data.signs.entries := []} == .error .evidence &&
      Replay.check input {cert with data.signs.lower := 0} == .error .evidence &&
      Replay.check input {cert with data.rootSigns.entries := []} == .error .evidence &&
      Replay.check input {cert with data.radical.context := 8} == .error .evidence
  | .error _ => false

-- Rebinding a false sentence preserves false as an accepted diagnostic.
#guard match proposed with
  | .ok cert =>
      let universal := {input with quantifier := .forallReal}
      Replay.check universal {cert with input := universal} == .ok false
  | .error _ => false

-- All original guards preflight even if the supplied evidence is also invalid.
#guard match proposed with
  | .ok cert =>
      let invalid := {input with divisors := [0]}
      Replay.check invalid {cert with input := invalid, data.signs.entries := []} == .error .divisor
  | .error _ => false

#guard match proposed with
  | .ok cert =>
      let missing := {input with divisors := [123456789]}
      Replay.check missing {cert with input := missing} == .error .evidence
  | .error _ => false

#guard match Replay.build {input with divisors := [0]} real 0 0 with
  | .error .divisor => true
  | _ => false

-- Zero atoms have no carrier roots; their original guards still preflight.
#guard match Replay.build {input with formula := .atom ⟨0, .eq⟩, quantifier := .forallReal} real 256 5 with
  | .ok cert => Replay.check cert.input cert == .ok true &&
      cert.data.isolation.isolations.intervals.isEmpty
  | .error _ => false

-- The complete producer succeeds even when its direct proposal depth is zero.
#guard (Replay.buildTotal input real 0).toOption.map (Replay.check input) == some (.ok true)
#guard (Replay.buildTotal {input with quantifier := .forallReal} real 0).toOption.map
  (Replay.check {input with quantifier := .forallReal}) == some (.ok false)
#guard Replay.buildTotal {input with divisors := [0]} real 0 matches .error .divisor

/-- info: 'Hex.RCF.RealCoefficients.Replay.buildTotal_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Replay.buildTotal_checked
/-- info: 'Hex.RCF.RealCoefficients.Replay.buildTotal_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Replay.buildTotal_spec

/-- info: 'Hex.RCF.RealCoefficients.Replay.check_domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Replay.check_domains
/-- info: 'Hex.RCF.RealCoefficients.Replay.check_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Replay.check_spec
/-- info: 'Hex.RCF.RealCoefficients.Replay.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Replay.check_sound
/-- info: 'Hex.RCF.RealCoefficients.Replay.check_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Replay.check_original

/-- info: 'Hex.RCF.RealCoefficients.Replay.build_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Replay.build_spec

end Hex.RCF.FiniteReplayTests
