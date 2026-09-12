/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexReflectMathlib
import HexMvGcd.Instances
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Residue coefficient conformance

**Oracle:** none.
**Mode:** `always`.
**Covered operations:** coefficient selection, matrix-entry reification, and
kernel checking of the interpretation proof over `ZMod 3`.
**Covered properties:** residue polynomial equality, retained primality and ring
instances for downstream gcd operations, injectivity for extension fields,
and preservation of executable ring operations.
**Covered edge cases:** composite and oversized characteristic, missing field
and characteristic evidence, incompatible ring operations, characteristic
zero, and unknown characteristic.
-/

namespace Hex.ReflectResidueConformance

open Lean Meta Hex.Reflect HexReflectMathlib
open scoped HexModArithMathlib.ZMod64

local instance : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
local instance : ZMod64.PrimeModulus 3 := ⟨by decide⟩
local instance : Lean.Grind.IsCharP (ZMod 3) 3 := isCharP_of_charP 3

private def matrixInput (x : ZMod 3) : Matrix (Fin 1) (Fin 1) (ZMod 3) := !![x ^ 3 - x]

private def expected : MvPoly 1 (ZMod64 3) Mono.grevlex :=
  MvPoly.X 0 ^ 3 - MvPoly.X 0

-- These operations must retain their executable implementations under the scope.
example (a b : ZMod64 3) : a * b = ZMod64.mul a b := rfl
example (a : ZMod64 3) (n : Nat) : a ^ n = ZMod64.pow a n := rfl
example (a b : ZMod64 3) : a - b = ZMod64.sub a b := rfl
example : Hex.LawfulGcdOps (ZMod64 3) := inferInstance

example (F : Type u) [Field F] [CharP F 3] : Function.Injective (residueHom 3 F) :=
  residueHom_injective 3 F

private def kernelCheck (xs : Array Expr) (proof : Expr) : MetaM Unit := do
  let name ← mkFreshUserName `Hex.ReflectResidueConformance.proof
  let type ← mkForallFVars xs (← inferType proof)
  let value ← mkLambdaFVars xs proof
  addDecl (.thmDecl { name, levelParams := [], type, value })

/-- info: ZMod 3 matrix: residue coefficients, X₀³ - X₀, kernel accepted -/
#guard_msgs in
run_meta do
  let ty := mkApp (mkConst ``ZMod) (mkNatLit 3)
  withLocalDeclD `x ty fun x => do
    let matrix ← mkAppM ``matrixInput #[x]
    let input ← mkAppM ``HSub.hSub #[← mkAppM ``HPow.hPow #[x, mkNatLit 3], x]
    let matrixEntry := mkApp2 matrix (toExpr (0 : Fin 1)) (toExpr (0 : Fin 1))
    unless ← isDefEq input matrixEntry do throwError "wrong matrix entry"
    let outcome ← reflectRingBatch #[input] (cfg := { checkProofs := true })
    let .success batch _ := outcome | throwError "{outcome.toMessageData (fun _ => "batch") }"
    let some entry := batch.entries[0]? | throwError "empty batch"
    unless entry.conversion.provider.id == residueCoefficientsId do
      throwError "wrong coefficient provider"
    unless batch.sealed.n == 1 do throwError "wrong atom count"
    let expectedE := mkConst ``expected
    -- The kernel checks the actual quoted residue polynomial against X³ - X,
    -- independently of the source interpretation proof.
    let eq ← mkEq entry.result.value expectedE
    let proof ← mkDecideProof eq
    kernelCheck #[] proof
    let matrixEq ← mkEq entry.result.interpretation matrixEntry
    kernelCheck #[x] (← mkExpectedTypeHint entry.result.proof matrixEq)
    for inst in entry.conversion.provider.auxInstances do
      Meta.check inst
    unless entry.conversion.provider.auxInstances.size == 3 do
      throwError "missing downstream coefficient instances"
    logInfo "ZMod 3 matrix: residue coefficients, X₀³ - X₀, kernel accepted"

private def checkAux (coeffType : Expr) : List Expr → MetaM Unit
  | [] => do
    let target ← mkAppOptM ``Hex.LawfulGcdOps
      #[coeffType, none, none, none, none, none, none]
    Meta.check (← synthInstance target)
    Meta.check (← synthInstance (mkApp (mkConst ``CommRing [.zero]) coeffType))
  | inst :: rest => do
    withLetDecl `coefficientInstance (← inferType inst) inst fun _ =>
      checkAux coeffType rest

local instance : Fact (_root_.Nat.Prime 5) := ⟨by decide⟩

/-- info: ZMod 5: auxiliary instances supply lawful gcd and Mathlib ring -/
#guard_msgs in
run_meta do
  let ty := mkApp (mkConst ``ZMod) (mkNatLit 5)
  withLocalDeclD `x ty fun x => do
    let outcome ← reflectRing x
    let .success entry _ := outcome | throwError "{outcome.toMessageData (fun _ => "entry")}"
    unless entry.conversion.provider.id == residueCoefficientsId do throwError "wrong provider"
    checkAux entry.conversion.provider.coeffType entry.conversion.provider.auxInstances.toList
    kernelCheck #[x] entry.result.proof
    logInfo "ZMod 5: auxiliary instances supply lawful gcd and Mathlib ring"

private def declineProbe (p : Nat) (reason : String) : MetaM Unit := do
  let ty := mkApp (mkConst ``ZMod) (mkNatLit p)
  withLocalDeclD `x ty fun x => do
    let .declined (.providerCondition id message) _ ← reflectRing x
      | throwError "expected a provider condition decline"
    unless id == residueCoefficientsId && message == reason do
      throwError "wrong decline: {message}"

/-- info: composite, modulus one, and oversized characteristic decline with reasons -/
#guard_msgs in
run_meta do
  declineProbe 6 "residue coefficients require prime characteristic"
  declineProbe 1 "residue coefficients require prime characteristic"
  declineProbe 2147483648 "residue coefficients require characteristic p < 2^31"
  declineProbe 4294967291 "residue coefficients require characteristic p < 2^31"
  logInfo "composite, modulus one, and oversized characteristic decline with reasons"

/-- info: non-fields, zero and unknown characteristic retain integers -/
#guard_msgs in
run_meta do
  let ty := mkConst ``Int
  withLocalDeclD `x ty fun x => do
    Hex.Reflect.run do
      let .success r _ ← reifyCommRing x | throwError "reification declined"
      let ring ← ringOf r
      let .notApplicable ← residueCoeffProvider 3 ring
        | throwError "non-field should retain integer fallback"
      -- Exercise dispatch's two non-applicable paths independently of the
      -- characteristic instances a particular toolchain provides for Int.
      for charInst? in [none, some (mkConst ``True.intro, 0)] do
        let .notApplicable ← residueCoefficients.recognize { ring with charInst? }
          | throwError "residue provider should not apply"
      let .success entry _ ← ringBatch #[x] | throwError "integer batch declined"
      let some result := entry.entries[0]? | throwError "empty batch"
      unless result.conversion.provider.id == intCoefficientsId do
        throwError "integer fallback changed"
    logInfo "non-fields, zero and unknown characteristic retain integers"

/-- info: arbitrary characteristic-three field: missing CharP declines, supplied CharP reifies -/
#guard_msgs in
run_meta do
  withLocalDeclD `F (mkSort (.succ .zero)) fun f => do
  withLocalDecl `field .instImplicit (mkApp (mkConst ``Field [.zero]) f) fun field => do
  withLocalDeclD `x f fun x => do
    Hex.Reflect.run do
      let .success r _ ← reifyCommRing x | throwError "reification declined"
      let .declined (.providerCondition _ message) _ ← residueCoeffProvider 3 (← ringOf r)
        | throwError "expected missing CharP decline"
      unless message == "residue coefficients require Mathlib CharP evidence" do
        throwError "wrong decline"
    let charTy ← mkAppOptM ``CharP #[f, none, mkNatLit 3]
    withLocalDecl `char .instImplicit charTy fun char => do
      let charProof ← mkAppOptM ``isCharP_of_charP #[f, none, mkNatLit 3, char]
      withLetDecl `grindChar (← inferType charProof) charProof fun grindChar => do
        let input ← mkAppM ``HSub.hSub #[← mkAppM ``HPow.hPow #[x, mkNatLit 3], x]
        let outcome ← reflectRing input (cfg := { checkProofs := true })
        let .success entry _ := outcome
          | throwError "{outcome.toMessageData (fun _ => "entry")}"
        unless entry.conversion.provider.id == residueCoefficientsId do
          throwError "wrong provider"
        kernelCheck #[f, field, x, char, grindChar] entry.result.proof
        let eq ← mkEq entry.result.value (mkConst ``expected)
        kernelCheck #[] (← mkDecideProof eq)
        withLocalDecl `otherRing .instImplicit
            (mkApp (mkConst ``Lean.Grind.CommRing [.zero]) f) fun _ => do
          Hex.Reflect.run do
            let .success r _ ← reifyCommRing x | throwError "reification declined"
            let .declined (.providerCondition _ message) _ ← residueCoeffProvider 3 (← ringOf r)
              | throwError "expected incompatible-operation decline"
            unless message ==
                "the classified ring operations do not agree with the Mathlib field" do
              throwError "wrong decline"
    logInfo "arbitrary characteristic-three field: missing CharP declines, supplied CharP reifies"

end Hex.ReflectResidueConformance

namespace Hex.ReflectResidueClosedConformance

open Lean Meta Hex.Reflect HexReflectMathlib

-- No coefficient-ring scope, local bounds, or local Grind characteristic
-- instance is active here. Mathlib discovers the target characteristic.
/-- info: closed scope: executable coefficient instances, kernel accepted -/
#guard_msgs in
run_meta do
  let ty := mkApp (mkConst ``ZMod) (mkNatLit 3)
  withLocalDeclD `x ty fun x => do
    let input ← mkAppM ``HSub.hSub #[← mkAppM ``HPow.hPow #[x, mkNatLit 3], x]
    let outcome ← reflectRing input (cfg := { checkProofs := true })
    let .success entry _ := outcome
      | throwError "{outcome.toMessageData (fun _ => "entry")}"
    let provider := entry.conversion.provider
    unless provider.id == residueCoefficientsId && entry.conversion.terms.length == 2 do
      throwError "wrong residue conversion"
    unless provider.zeroInst.getAppFn.isConstOf ``Hex.ZMod64.instZero &&
        provider.addInst.getAppFn.isConstOf ``Hex.ZMod64.instAdd do
      throwError "coefficient operations depend on caller scope"
    let name ← mkFreshUserName `Hex.ReflectResidueClosedConformance.proof
    let type ← mkForallFVars #[x] (← inferType entry.result.proof)
    let value ← mkLambdaFVars #[x] entry.result.proof
    addDecl (.thmDecl { name, levelParams := [], type, value })
    logInfo "closed scope: executable coefficient instances, kernel accepted"

-- Even at the largest supported prime, the certificate follows from the
-- field characteristic; the kernel does not run trial division.
example (F : Type u) [Field F] [CharP F 2147483647] :
    ZMod64.PrimeModulus 2147483647 :=
  residuePrime 2147483647 F (by decide)

end Hex.ReflectResidueClosedConformance

namespace Hex.ReflectResidueFallbackConformance

open Lean Meta Hex.Reflect

private def probe (ty : Expr) (xs : Array Expr) (p : Nat) : MetaM Unit :=
  withLocalDeclD `x ty fun x => do
    let input ← mkAppM ``HAdd.hAdd #[x, x]
    let outcome ← reflectRing input (cfg := { checkProofs := true })
    let .success entry _ := outcome
      | throwError "{outcome.toMessageData (fun _ => "entry")}"
    unless entry.reflected.charInst?.map (·.2) == some p do
      throwError "expected characteristic {p}"
    unless entry.conversion.provider.id == intCoefficientsId do
      throwError "non-field lost integer fallback"
    let name ← mkFreshUserName `Hex.ReflectResidueFallbackConformance.proof
    let type ← mkForallFVars (xs.push x) (← inferType entry.result.proof)
    let value ← mkLambdaFVars (xs.push x) entry.result.proof
    addDecl (.thmDecl { name, levelParams := [], type, value })

/-- info: prime-characteristic rings without field instances: integer fallback, kernel accepted -/
#guard_msgs in
run_meta do
  -- A concrete prime modulus without Mathlib's `Fact (Nat.Prime 7)`.
  probe (mkApp (mkConst ``ZMod) (mkNatLit 7)) #[] 7
  -- An arbitrary characteristic-three commutative ring, with no Field assumption.
  withLocalDeclD `R (mkSort (.succ .zero)) fun r => do
  withLocalDecl `ring .instImplicit (mkApp (mkConst ``CommRing [.zero]) r) fun ring => do
    let charTy ← mkAppOptM ``CharP #[r, none, mkNatLit 3]
    withLocalDecl `char .instImplicit charTy fun char => do
      probe r #[r, ring, char] 3
  logInfo "prime-characteristic rings without field instances: integer fallback, kernel accepted"

end Hex.ReflectResidueFallbackConformance
