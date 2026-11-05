/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.PolynomialSigns
public meta import HexRCF.RealCoefficients.PolynomialSigns
public meta import HexMvPoly.Ring
public meta import Lean.Elab.Command
public section

namespace Hex.RCF.PolynomialSignsConformance
open Hex RealCoefficients Hex.OrderedFn.Oracle Lean

private abbrev E := PolynomialBounds.Poly 1
private def parameter : E := MvPoly.X (0 : Fin 1)
private def bounds (_ : Fin 1) : Bounds := Bounds.singleton 2

run_meta withoutExporting do
  let keys : List E := [parameter, parameter - 2, -parameter, parameter * parameter, parameter]
  let some (entries, index) := PolynomialSigns.build? bounds keys |
    throwError "polynomial signs failed to build a separating indexed table"
  unless entries.size == 4 && PolynomialSigns.check bounds entries &&
      keys.all (fun key => (PolynomialSigns.lookup entries index key).isSome) do
    throwError "polynomial signs lost sharing, validation or coverage"
  unless PolynomialSigns.lookup entries index parameter == some 1 &&
      PolynomialSigns.lookup entries index (parameter - 2) == some 0 &&
      PolynomialSigns.lookup entries index (-parameter) == some (-1) do
    throwError "polynomial signs changed a positive, zero or negative value"
  unless (PolynomialSigns.lookup entries index (parameter + 1)).isNone &&
      (PolynomialSigns.lookup entries (.node entries.size .empty .empty) parameter).isNone &&
      (PolynomialSigns.lookup entries .empty parameter).isNone do
    throwError "polynomial signs supplied evidence for an absent key or malformed route"
  let wrong := entries.map fun entry => {entry with value := entry.value + 1}
  unless !(PolynomialSigns.check bounds wrong) do
    throwError "polynomial signs accepted changed values"
  let extra : LiteralSign.Entry E := ⟨parameter + 1, -1, none⟩
  unless !(PolynomialSigns.check bounds (entries.push extra)) do
    throwError "polynomial signs skipped an unused corrupt row"
  let tied : LiteralSign.Index := .node 0 .empty .empty
  let some first := entries[0]? | throwError "polynomial signs table is empty"
  unless (tied.lookup entries (fun _ _ => .eq) (first.key + 1)).isNone do
    throwError "polynomial signs trusted a comparator tie instead of exact key equality"
  let broad := fun _ : Fin 1 => (⟨0, 4, by decide⟩ : Bounds)
  unless (PolynomialSigns.build? broad [parameter]).isNone &&
      (PolynomialSigns.build? broad [parameter - parameter]).isSome do
    throwError "polynomial signs confused unresolved signs and exact cancellation"
  Lean.logInfo "POLYNOMIAL_SIGNS: shared exact keys; checked positive/zero/negative; missing, malformed, changed, unused-corrupt and unresolved evidence rejected"

end Hex.RCF.PolynomialSignsConformance
