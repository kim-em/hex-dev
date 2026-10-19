/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootBuild
public import HexRCF.RealCoefficients.ScalarPacket
public section

namespace Hex.RCF.RealCoefficients.SourceBuild
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

inductive Error where
  | roots (error : RootBuild.Error)
  | equation
  | enclosure
  | ambiguous
  | unselected
  deriving Repr

/-- Native proposals for one source root and the two independent scalar
packets demanded by source authentication. The sign equalities only describe
the proposed literal fields; they are not proof evidence about real values. -/
structure Result (parent : Tower.Context registry) where
  root : Descriptor parent.Value Signature parent.sign parent.signature
  equation : ScalarPacket.Proposal
  enclosure : ScalarPacket.Proposal
  zero : equation.sign = 0
  positive : enclosure.sign = 1

/-- Visit every enumerated root. Failure to produce a row is terminal, and a
second positive window match rejects an ambiguous source rather than choosing
an arbitrary conjugate. No equation or enclosure is silently substituted. -/
def select (polynomial window : DensePoly parent.Value)
    (roots : List (Descriptor parent.Value Signature parent.sign parent.signature)) :
    Except Error (Result parent) := do
  let mut selected : Option (Result parent) := none
  for root in roots do
    let context := Algebraic.Context.adjoin root parent.isClean
    let some equation := ScalarPacket.buildParts context parent.codec polynomial
      | throw .equation
    if zero : equation.sign = 0 then
      let some enclosure := ScalarPacket.buildParts context parent.codec window
        | throw .enclosure
      if positive : enclosure.sign = 1 then
        if selected.isSome then throw .ambiguous
        selected := some ⟨root,equation,enclosure,zero,positive⟩
      else unless enclosure.sign = 0 || enclosure.sign = -1 do throw .enclosure
    else throw .equation
  match selected with
  | none => throw .unselected
  | some result => return result

/-- Enumerate with the existing owner root producer and select exactly one
root using the supplied enclosure polynomial. The usual window is the source
isolating-square margin. Its original-source interpretation and selected-root
identity are subsequently checked by `SourceIdentity.quoteWith`; this producer
does not prove them, reconstruct a frozen parent, or establish completeness. -/
def build (polynomial window : DensePoly parent.Value) : Except Error (Result parent) := do
  let roots ← RootBuild.build polynomial |>.mapError Error.roots
  select polynomial window roots.roots

end Hex.RCF.RealCoefficients.SourceBuild
