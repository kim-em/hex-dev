/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexReflect
import HexMvPolyMathlib

/-!
# HexReflect scope conformance

**Oracle:** none.

**Mode:** `always`.

**Covered operations:** `reifyCommRing`, `convert`, and `Conversion.mkProof`
over the carrier `Hex.MvPoly 2 Int Mono.lex` in the closed scope and with
`HexMvPolyMathlib` opened.

**Covered properties:** opening the `HexMvPolyMathlib` scope selects a
different exact `Lean.Grind.CommRing` instance for the same carrier type, so
the two requests carry distinct exact-instance keys; each scope reifies,
converts, and produces a kernel-checked interpretation proof against its own
instance. A type name alone is never a cache key.

**Covered edge cases:** the same carrier type under two instance scopes.
-/

namespace Hex.ReflectScopeConformance

open Lean Meta Hex Hex.Reflect

private def carrier : MetaM Lean.Expr := do
  let cmp ← mkAppOptM ``Hex.Mono.lex #[mkNatLit 2]
  mkAppOptM ``Hex.MvPoly #[mkNatLit 2, mkConst ``Int, none, cmp, none, none]

/-- Reify `p * q + p` over the carrier, report the head constant of the exact
commutative-ring instance recorded by the classification, and kernel-check the
interpretation proof. -/
private def probe (label : String) : MetaM Unit := do
  let ty ← carrier
  withLocalDeclD `p ty fun p => do
  withLocalDeclD `q ty fun q => do
    let e ← mkAppM ``HAdd.hAdd #[← mkAppM ``HMul.hMul #[p, q], p]
    let outcome ← Hex.Reflect.run (cfg := { checkProofs := true }) do
      let .success r _ ← reifyCommRing e | throwError "declined"
      let ring ← ringOf r
      let s ← sealAtoms
      let .success c _ ← convert r s .grevlex | throwError "conversion declined"
      let .success result _ ← c.mkProof e { checkProofs := true } | throwError "proof declined"
      return (ring.commRingInst.getAppFn.constName!, c.terms.length, result)
    let (inst, terms, result) := outcome
    let proofTy ← mkForallFVars #[p, q] (← inferType result.proof)
    let proofVal ← mkLambdaFVars #[p, q] result.proof
    let name ← mkFreshUserName `Hex.ReflectScopeConformance.proof
    addDecl (.thmDecl { name, levelParams := [], type := proofTy, value := proofVal })
    logInfo m!"{label}: instance {inst}, terms {terms}, kernel accepted"

/-- info: closed scope: instance Hex.MvPoly.instGrindCommRing, terms 2, kernel accepted -/
#guard_msgs in
run_meta probe "closed scope"

open scoped HexMvPolyMathlib in
/-- info: open scope: instance CommRing.toGrindCommRing, terms 2, kernel accepted -/
#guard_msgs in
run_meta probe "open scope"

end Hex.ReflectScopeConformance
