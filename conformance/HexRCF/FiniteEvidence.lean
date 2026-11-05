/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public meta import HexRCF.ProofEvidence
public meta import HexRCF.RealCoefficients.FieldRuntime
public meta section

namespace Hex.RCF.FiniteEvidence
open Lean Meta Hex

private meta def polynomial (argument : Expr) : MetaM ZPoly := do
  -- An ordinary-imported reducible alias needs no executable import of its
  -- defining module. Normalize that alias before evaluating the literal data.
  RealCoefficients.FieldRuntime.evalZPoly (← withReducible (whnf argument))

/-- Inspect every presentation in this root's own proof closure. Only the
explicit original source polynomials may carry an irreducibility class.
Required degrees prevent the intended common/nested case from disappearing. -/
meta def checkClasses (root : Name) (sources : Array ZPoly)
    (requiredDegrees : Array Nat := #[]) : MetaM Nat := do
  let dependencies ← ProofEvidence.projectDependencies #[root]
  let arguments ← ProofEvidence.closedArguments dependencies
    ``RealCoefficients.Field.literalRep 4 0
  unless !arguments.isEmpty do throwError "no actual finite presentation in {root}"
  let mut presentations : Array ZPoly := #[]
  for argument in arguments do
    let value ← polynomial argument
    unless presentations.contains value do
      presentations := presentations.push value
  let parameters ← ProofEvidence.classArguments dependencies ``ZPoly.CheckedIrreducible
  let quoted ← parameters.mapM polynomial
  for polynomial in presentations do
    if !sources.contains polynomial && quoted.contains polynomial then
      throwError "{root} quotes irreducibility of a non-source presentation: {polynomial.toArray}"
  for degree in requiredDegrees do
    unless presentations.any (·.natDegree == degree) do
      throwError "{root} no longer contains its degree-{degree} presentation"
  return presentations.size

end Hex.RCF.FiniteEvidence
