/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexReflect
import HexReflect.TestProviders
import HexReflectMathlib

/-!
# HexReflect scope conformance

**Oracle:** none.

**Mode:** `always`.

**Covered operations:** `reifyCommRing`, `convert`, and `Conversion.mkProof`
over the carrier `Hex.MvPoly 2 Int Mono.lex` in the closed scope and with
`HexMvPolyMathlib` opened; the `HexReflectMathlib` correspondence theorems at
the rational coefficient provider.

**Covered properties:** opening the `HexMvPolyMathlib` scope selects a
different exact `Lean.Grind.CommRing` instance for the same carrier type, so
the two requests carry distinct exact-instance keys; each scope reifies,
converts, and produces a kernel-checked interpretation proof against its own
instance. Changing the selected instance within one session, through a
`SymM` instance override, reclassifies the carrier rather than reusing the
stale classification. A type name alone is never a cache key. The
`MvPolynomial` correspondence applies to a non-integer coefficient
homomorphism.

**Covered edge cases:** the same carrier type under two instance scopes, and
under two instances within one session.
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

-- Within one session: reify with the closed-scope instance, override the
-- `Lean.Grind.CommRing` instance for the carrier with the Mathlib-derived one,
-- and reify again. The second request is classified afresh and both proofs are
-- kernel-checked against their own instance.
/--
info: in-session change: instances Hex.MvPoly.instGrindCommRing then CommRing.toGrindCommRing, distinct classification ids, kernel accepted twice
-/
#guard_msgs in
run_meta do
  let ty ← carrier
  withLocalDeclD `p ty fun p => do
  withLocalDeclD `q ty fun q => do
    let e ← mkAppM ``HAdd.hAdd #[← mkAppM ``HMul.hMul #[p, q], p]
    let mathlibInst ← mkAppOptM ``CommRing.toGrindCommRing #[ty, none]
    let (insts, ids, results) ← Hex.Reflect.run (cfg := { checkProofs := true }) do
      let .success r1 _ ← reifyCommRing e | throwError "declined"
      let ring1 ← ringOf r1
      let u := ring1.u
      let canonTy ← (Lean.Meta.Sym.canon ty : Lean.Meta.Sym.SymM Lean.Expr)
      (Lean.Meta.Sym.registerInstance
        (mkApp (mkConst ``Lean.Grind.CommRing [u]) canonTy) mathlibInst : Lean.Meta.Sym.SymM Unit)
      let .success r2 _ ← reifyCommRing e | throwError "declined after override"
      let ring2 ← ringOf r2
      let s ← sealAtoms
      let .success c1 _ ← convert r1 s .grevlex | throwError "conversion declined"
      let .success c2 _ ← convert r2 s .grevlex | throwError "conversion declined"
      let .success p1 _ ← c1.mkProof e { checkProofs := true } | throwError "proof declined"
      let .success p2 _ ← c2.mkProof e { checkProofs := true } | throwError "proof declined"
      return ((ring1.commRingInst.getAppFn.constName!, ring2.commRingInst.getAppFn.constName!),
        (r1.ringId, r2.ringId), (p1, p2))
    for result in [results.1, results.2] do
      let proofTy ← mkForallFVars #[p, q] (← inferType result.proof)
      let proofVal ← mkLambdaFVars #[p, q] result.proof
      let name ← mkFreshUserName `Hex.ReflectScopeConformance.proof
      addDecl (.thmDecl { name, levelParams := [], type := proofTy, value := proofVal })
    unless ids.1 != ids.2 do throwError "classification identity was reused"
    logInfo m!"in-session change: instances {insts.1} then {insts.2}, distinct classification \
      ids, kernel accepted twice"

/-! # Companion correspondence at a non-integer provider -/

open HexReflectMathlib in
/-- The rational provider's coefficient homomorphism is the identity on `ℚ`,
which agrees with the integer cast on reflected coefficients; the general
`MvPolynomial` correspondence therefore applies to its quoted values. The
denotation is stated at the Grind ring derived from Mathlib's `CommRing ℚ`,
the exact instance the companion theorems fix. -/
example {n : Nat} (ctx : Lean.RArray ℚ) {e : RingExpr} {ts : List (Mono n × Int)}
    (h : convertTerms? n none e = some ts) :
    MvPolynomial.eval₂ (RingHom.id ℚ) (ctxValuation ctx n)
        (HexMvPolyMathlib.equiv (ofIntTerms (cmp := Mono.lex) Int.cast ts)) =
      @Lean.Grind.CommRing.Expr.denote ℚ
        (@Lean.Grind.CommRing.toRing ℚ (CommRing.toGrindCommRing ℚ)) ctx e :=
  eval₂_equiv_ringHom_ofIntTerms (RingHom.id ℚ) Int.cast (fun _ => rfl) ctx h

end Hex.ReflectScopeConformance
