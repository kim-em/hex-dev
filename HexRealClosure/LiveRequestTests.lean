/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveRequest
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.LiveRequest

public section

namespace Hex.RealClosure.Tower.Live.Tests

private def registry : BaseContext.Registry := fun _ => none
private abbrev rational := BaseContext.rational registry

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def check {base : BaseContext.PackedContext registry} {request : Request registry}
    (collection : Collection base request) : IO Unit := do
  let target := collection.shared.input.context
  require (target.signature.roots.length == 2) "live request duplicated root ancestry"
  require (collection.frames.length == 5) "live request changed frame order or count"
  let some betaFrame := collection.frames[1]? | throw (IO.userError "missing beta frame")
  let some beta := betaFrame.values[0]? | throw (IO.userError "missing beta")
  let some alphaFrame := collection.frames[3]? | throw (IO.userError "missing alpha frame")
  let some alpha := alphaFrame.values[0]? | throw (IO.userError "missing alpha")
  require (target.equal (alpha * alpha) (1 + 1) && target.equal (beta * beta) alpha)
    "transport lost a defining equation"
  require (target.sign alpha == 1 && target.sign beta == 1)
    "transport changed a selected root"
  for (index, value) in [(0, beta), (2, alpha)] do
    let some frame := collection.frames[index]? | throw (IO.userError "missing root dependency frame")
    let some descriptor := frame.descriptors[0]? | throw (IO.userError "missing root dependency descriptor")
    require (target.sign (descriptor.raw.head.eval value) == 0)
      "transported descriptor does not vanish at its retained generator"
    match descriptor.raw.lower with
    | .finite lower =>
      require (target.compare lower value == .lt)
        "retained generator does not lie above its transported lower bound"
    | .negInf => pure ()
    | .posInf => throw (IO.userError "invalid lower bound")
    match descriptor.raw.upper with
    | .finite upper =>
      require (target.compare value upper == .lt)
        "retained generator does not lie below its transported upper bound"
    | .posInf => pure ()
    | .negInf => throw (IO.userError "invalid upper bound")
  let some operands := collection.frames[4]? | throw (IO.userError "missing operand frame")
  let some computed := operands.values[0]? | throw (IO.userError "missing computed value")
  require (target.equal computed (beta + alpha)) "transport lost a computed live value"
  let some polynomial := operands.polynomials[0]? | throw (IO.userError "missing polynomial")
  require (target.equal (polynomial.eval beta) 0) "transport lost live polynomial coefficients"
  for frame in collection.frames do
    for descriptor in frame.descriptors do
      require (descriptor.raw.context == target.signature) "descriptor retained its old binding"
      require ((SignDet.Descriptor.validate target.sign target.signature descriptor.raw).isSome)
        "transport returned unchecked descriptor data"

def run : IO Unit := do
  let base := Context.base rational
  let some empty := Request.gather? (.pack rational) []
    | throw (IO.userError "empty live request failed")
  require (empty.frames.isEmpty) "empty request gained frames"
  let pointRequest := rootRequest (Root.point (parent := base) (1+1))
  let some point := Request.gather? (.pack rational) pointRequest
    | throw (IO.userError "point live request failed")
  let some pointFrame := point.frames[0]? | throw (IO.userError "point frame missing")
  let some pointValue := pointFrame.values[0]? | throw (IO.userError "point value missing")
  require (point.shared.input.context.equal pointValue (1+1) && pointFrame.descriptors.isEmpty)
    "point request did not retain its value without root evidence"
  let incompatible := Context.base rational.infinitesimal
  let bad : Request registry := [⟨incompatible, { values := [1] }⟩]
  require ((Request.gather? (.pack rational) bad).isNone)
    "rational target accepted an owner with an extra infinitesimal"
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x*x - DensePoly.C (1+1),
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := [] }
    | throw (IO.userError "alpha descriptor failed")
  let alphaRoot := Root.ofSelection base (.selected descriptor)
  let parent := alphaRoot.context
  let alpha := alphaRoot.value
  let y : parent.Poly := DensePoly.ofCoeffs #[0, 1]
  let some dependent := SignDet.Descriptor.validate parent.sign parent.signature
      { context := parent.signature, head := y*y - DensePoly.C alpha,
        lower := .finite 0, upper := .finite (1+1), indices := [], signs := [] }
    | throw (IO.userError "beta descriptor failed")
  let betaRoot := Root.ofSelection parent (.selected dependent)
  let child := betaRoot.context
  let beta := betaRoot.value
  let embedded := betaRoot.embed alpha
  let polynomial : child.Poly := DensePoly.ofCoeffs #[-embedded, 0, 1]
  let operands : Frame child := { values := [beta+embedded], polynomials := [polynomial] }
  let request := rootRequest betaRoot ++ rootRequest alphaRoot ++ [⟨child, operands⟩]
  let some collection := request.gather? (.pack rational.infinitesimal)
    | throw (IO.userError "dependency-closed live gathering failed")
  check collection
  let some enlarged := collection.enlarge?
    | throw (IO.userError "live enlargement failed")
  require (decide (enlarged.previous.value 0 = 0))
    "live enlargement did not preserve zero for one-hop transport"
  check enlarged.collection
  let target := enlarged.collection.shared.input.context
  let some first := collection.frames[0]? | throw (IO.userError "missing original descriptor frame")
  let some refreshed := enlarged.collection.frames[0]? | throw (IO.userError "missing refreshed frame")
  let some fresh := refreshed.descriptors[0]? | throw (IO.userError "missing fresh descriptor")
  require ((SignDet.Descriptor.validate target.sign target.signature
    { fresh.raw with context := collection.shared.input.context.signature }).isNone)
    "new target accepted stale descriptor evidence"
  let some oldAlpha := collection.frames[3]? | throw (IO.userError "missing old alpha")
  let some oldValue := oldAlpha.values[0]? | throw (IO.userError "missing old value")
  require (match target.read (collection.shared.input.context.write oldValue) with
    | .error _ => true | .ok _ => false) "new target accepted stale serialized value"
  let some oldOperands := collection.frames[4]? | throw (IO.userError "missing old operands")
  let some oldPolynomial := oldOperands.polynomials[0]? | throw (IO.userError "missing old polynomial")
  require (match target.readPoly (collection.shared.input.context.writePoly oldPolynomial) with
    | .error _ => true | .ok _ => false) "new target accepted stale serialized polynomial"
  require (first.descriptors.length == refreshed.descriptors.length) "descriptor count changed"
  let some twice := enlarged.collection.enlarge?
    | throw (IO.userError "second live enlargement failed")
  require (decide (twice.previous.value 0 = 0))
    "second enlargement did not preserve zero for one-hop transport"
  check twice.collection
  require (twice.collection.shared.input.context.sign twice.parameter == 1 &&
    twice.collection.shared.input.context.compare twice.parameter
      (twice.previous.value enlarged.parameter) == .lt)
    "successive enlargement lost parameter order"
  require (parent.equal (alpha*alpha) (1+1) && child.equal (beta*beta) embedded)
    "original contexts stopped working"

#eval run

end Hex.RealClosure.Tower.Live.Tests
