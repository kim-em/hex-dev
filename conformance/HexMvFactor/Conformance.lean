/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvFactor

/-!
Executable conformance checks for multivariate integer factorization.

Oracle: SymPy `factor_list` and Wang/EEZ internals
Mode: always
Covered operations:
- `checkDecomp`, `checkIrred`, `obligations`, `checkSplit`,
  `checkComplete`, and `NoKronecker`
- `factorWith`, `factor?`, `irredCert?`, `completeWith`, and `complete?`
- `probe`, `distribute?`, point-shell enumeration, and Hensel-input handoff
- `kron`, `unKron?`, and `kronDecide`
Covered properties:
- every exposed success replays against its original subject
- structural content, monomial content, normalization, distinctness, and
  multiplicity merging
- point rejection order, exact leading assignment, and Hensel invariants
- irreducibility-route priority and rejection of corrupted certificates
- mixed-radix round trips and checked reducibility splits
Covered edge cases:
- zero, units, constants, monomials, arity zero and arity one
- repeated factors, nonconstant shared leading coefficients, and split scalar
  leading content
- degree-dropping, non-squarefree, unlucky, and accepted evaluation points
- exhausted point and prime budgets and explicit Kronecker fallback
-/

namespace Hex.MvFactor.Conformance

open Hex
open Hex.MvPoly
open Hex.MvFactor
open scoped Hex

private abbrev P0 := MvPoly 0 Int Mono.lex
private abbrev P1 := MvPoly 1 Int Mono.lex
private abbrev P2 := MvPoly 2 Int Mono.lex

private def ux : P1 := X 0
private def x : P2 := X 0
private def y : P2 := X 1
private def innerY : P1 := X 0

/-! Checker and structural contracts. -/

private def checkedProduct : Decomp 2 Mono.lex :=
  ⟨1, [⟨x + y, 2⟩, ⟨x + 1, 1⟩]⟩

#guard checkDecomp ((x + y) ^ 2 * (x + 1)) checkedProduct
#guard checkDecomp (0 : P2) ⟨0, []⟩
#guard !checkDecomp ((x + 1) ^ 3)
  ⟨1, [⟨x + 1, 1⟩, ⟨x + 1, 2⟩]⟩
#guard !checkDecomp 1 (⟨1, [⟨x + y, 0⟩]⟩ : Decomp 2 Mono.lex)

#guard
  match structural? (0 : P2) with
  | some answer => answer.content == 0 && answer.factors.isEmpty
  | none => false

#guard
  match structural? (C 12 : P0) with
  | some answer => answer.content == 12 && answer.factors.isEmpty
  | none => false

#guard
  let subject := C 6 * x ^ 2 * y
  match structural? subject with
  | some answer =>
      answer.content == 6 && answer.factors.length == 2 &&
        checkDecomp subject answer
  | none => false

private def zeroStep : GcdCert 0 Int Mono.lex := .mk 0 1 1 .unit
private def oneStep : GcdCert 0 Int Mono.lex := .mk 1 0 1 .unit
private def primitiveX : ContentCert 0 Int Mono.lex :=
  .ofSteps 1 [zeroStep, oneStep]
private def degreeOneCert : IrredCert 1 Mono.lex :=
  .degreeOne 0 Mono.lex primitiveX
private def noPoint : Fin 0 → Int := fun i => nomatch i
private def imageCert : IrredCert 1 Mono.lex :=
  .image 0 Mono.lex noPoint primitiveX
private def corruptPrimitiveX : ContentCert 0 Int Mono.lex :=
  match primitiveX with
  | .mk _ steps => .mk 2 steps

#guard checkIrred ux degreeOneCert && obligations ux degreeOneCert == []
#guard checkIrred ux imageCert &&
  obligations ux imageCert == [DensePoly.ofList [0, 1]]
#guard !checkIrred ux (.degreeOne 0 Mono.lex corruptPrimitiveX)

private def reducibleSplit : Split 2 Mono.lex := ⟨x + 1, y + 2⟩

#guard checkSplit ((x + 1) * (y + 2)) reducibleSplit
#guard !checkSplit (x + 1) (⟨1, x + 1⟩ : Split 2 Mono.lex)
#guard !checkSplit ((x + 1) * (y + 2)) ⟨x + 2, y + 1⟩

private def completeX : Complete 1 Mono.lex :=
  ⟨⟨1, [⟨ux, 1⟩]⟩, [degreeOneCert]⟩

#guard checkComplete ux completeX && NoKronecker completeX
#guard checkComplete (C 12 : P1) ⟨⟨12, []⟩, []⟩
#guard !checkComplete (0 : P1) ⟨⟨0, []⟩, []⟩

/-! Public bounded search. -/

private def accepted {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] (subject : MvPoly n Int cmp) : Bool :=
  match factor? subject with
  | .ok answer => checkDecomp subject answer.raw
  | .error stoppedAnswer => checkDecomp subject stoppedAnswer.found.raw

#guard accepted (0 : P2)
#guard accepted (C 6 * x ^ 2 * y)
#guard accepted ((x + y + 1) ^ 3 * (x + 1))

#guard
  match factor? ((ux + 1) * (ux + 2)) with
  | .ok answer => answer.raw.factors.length == 2 &&
      checkDecomp ((ux + 1) * (ux + 2)) answer.raw
  | .error _ => false

#guard
  match factor? (C 12 : P0) with
  | .ok answer => answer.raw.content == 12 && answer.raw.factors.isEmpty
  | .error _ => false

#guard
  let subject := (x + y + 1) ^ 2 * (x + 1) ^ 5
  match factor? subject with
  | .ok answer =>
      answer.raw.factors.length == 2 &&
        answer.raw.factors.any (fun entry => entry.multiplicity == 5) &&
        checkDecomp subject answer.raw
  | .error _ => false

private def noPoints : Config :=
  { Config.default with rand := Rand.ofSeed 91, pointFuel := 0 }

private def initialPointFailure (failure : Failure 1 Mono.lex) : Bool :=
  match failure with
  | .point 0 none => true
  | _ => false

private def isPointFailure (failure : Failure 1 Mono.lex) : Bool :=
  match failure with
  | .point _ _ => true
  | _ => false

#guard
  match factorWith noPoints (ux + 1) with
  | .ok _ => false
  | .error stoppedAnswer =>
      initialPointFailure stoppedAnswer.reason &&
        checkDecomp (ux + 1) stoppedAnswer.found.raw &&
        stoppedAnswer.rand == noPoints.rand

#guard
  match factorWith Config.default (0 : P2) with
  | .ok (answer, _) => answer.raw.content == 0 && checkDecomp 0 answer.raw
  | .error _ => false

#guard
  let cfg := { Config.default with primeFuel := 0 }
  match factorWith cfg ((ux + 1) * (ux + 2)) with
  | .ok _ => false
  | .error stoppedAnswer =>
      isPointFailure stoppedAnswer.reason &&
        checkDecomp ((ux + 1) * (ux + 2)) stoppedAnswer.found.raw

private def withKronecker : Config :=
  { Config.default with kronecker := true }
private def noImage : Config :=
  { withKronecker with pointFuel := 0 }
private def quadratic : P2 := x ^ 2 + y ^ 2 + 1

#guard
  match irredCert? withKronecker (x + y + 1) with
  | .ok (cert, _) =>
      cert.noKronecker && obligations (x + y + 1) cert == [] &&
        checkIrred (x + y + 1) cert
  | .error _ => false

#guard
  match irredCert? withKronecker quadratic with
  | .ok (cert, _) =>
      cert.noKronecker && !(obligations quadratic cert).isEmpty &&
        checkIrred quadratic cert
  | .error _ => false

#guard
  match irredCert? noImage quadratic with
  | .ok (cert@(.kronecker _ _), _) => checkIrred quadratic cert
  | _ => false

#guard
  match complete? (C 12 : P0) with
  | .ok answer => answer.raw.certs.isEmpty && checkComplete (C 12 : P0) answer.raw
  | .error _ => false

#guard
  match complete? (C 6 * x ^ 2 * y) with
  | .ok answer => answer.raw.certs.length == 2 &&
      NoKronecker answer.raw && checkComplete (C 6 * x ^ 2 * y) answer.raw
  | .error _ => false

#guard
  let subject := (ux + 1) ^ 3 * (ux ^ 2 + 1)
  match complete? subject with
  | .ok answer => answer.raw.decomp.factors.length == 2 &&
      checkComplete subject answer.raw
  | .error _ => false

#guard
  match completeWith Config.default (0 : P2) with
  | .error stoppedAnswer =>
      (match stoppedAnswer.reason with | .zero => true | _ => false) &&
        checkDecomp 0 stoppedAnswer.found.raw
  | .ok _ => false

#guard
  match completeWith Config.default (x + y + 1) with
  | .ok (answer, _) => NoKronecker answer.raw &&
      checkComplete (x + y + 1) answer.raw
  | .error _ => false

#guard
  match completeWith withKronecker quadratic with
  | .ok (answer, _) => checkComplete quadratic answer.raw
  | .error _ => false

/-! Point selection, leading assignment, and Hensel handoff. -/

private def atZero : Fin 1 → Int := fun _ => 0
private def atFive : Fin 1 → Int := fun _ => 5
private def variableLeading : Decomp 1 Mono.lex :=
  ⟨1, [⟨innerY, 1⟩]⟩
private def constantLeading : Decomp 1 Mono.lex := ⟨1, []⟩
private def splitLeading : Decomp 1 Mono.lex :=
  ⟨6, [⟨innerY, 1⟩]⟩

#guard
  match probe Config.default 0 Mono.lex atZero (y * x + 1)
      variableLeading (Rand.ofSeed 0) with
  | .error .degreeDrop => true
  | _ => false

#guard
  match probe Config.default 0 Mono.lex atZero ((x + 1) ^ 2)
      constantLeading (Rand.ofSeed 0) with
  | .error .notSquarefree => true
  | _ => false

private def splitTarget : P2 :=
  (C 2 * y * x + 1) * (C 3 * x + y)

#guard
  match probe Config.default 0 Mono.lex atFive splitTarget splitLeading
      (Rand.ofSeed 9) with
  | .ok (acceptedProbe, _) =>
      acceptedProbe.images.length == 2 &&
        MvHensel.uniProduct acceptedProbe.images ==
          MvHensel.imageAt 0 Mono.lex atFive splitTarget &&
        MvHensel.mvProduct acceptedProbe.leading ==
          MvHensel.lcIn 0 Mono.lex splitTarget
  | .error _ => false

private def image₁ : ZPoly := DensePoly.ofList [1, 10]
private def image₂ : ZPoly := DensePoly.ofList [5, 3]

#guard
  match distribute? 0 Mono.lex atFive splitLeading [image₁, image₂] 1 with
  | some (leading, images) =>
      leading == [C 2 * innerY, C 3] && images == [image₁, image₂]
  | none => false

#guard nonDivisors 6 [12] |>.isNone
#guard distribute? 0 Mono.lex atFive
  (⟨2, [⟨innerY + 1, 2⟩]⟩ : Decomp 1 Mono.lex)
  [DensePoly.ofList [1, 9]] 8 |>.isNone
#guard distribute? 0 Mono.lex atFive constantLeading [] 1 |>.isNone

private def acceptedProbe : Probe 1 Mono.lex Mono.lex :=
  { point := atFive
    images := [image₁, image₂]
    leading := [C 2 * innerY, C 3]
    uni := [image₁, image₂] }

#guard
  match (ZMod64.primesBelow 7 1)[0]? with
  | none => false
  | some prime =>
      match inputAtPrime 0 splitTarget acceptedProbe prime 2 with
      | .ok input => MvHensel.valid input
      | .error _ => false

#guard (shellPoints 1 0).length == 1
#guard (shellPoints 2 1).length == 8
#guard
  let seed := Rand.ofSeed 44
  let cfg := { Config.default with pointFuel := 0 }
  let result := scoutPoints cfg 0 Mono.lex (x + 1) constantLeading seed
  result.attempts == 0 && result.accepted.isEmpty && result.rand == seed

private def unluckyProbe : Probe 1 Mono.lex Mono.lex :=
  { point := fun _ => -1
    images := [DensePoly.ofList [-1, 1], DensePoly.ofList [1, 1]]
    leading := [1, 1]
    uni := [] }

#guard
  match tryProbe Config.default 0 (x ^ 2 + y) unluckyProbe
      (Rand.ofSeed 7) with
  | .ok (.declined .recombine) => true
  | _ => false

/-! Complete mixed-radix fallback. -/

private def degrees : Fin 2 → Nat := fun _ => 1
private def packed : P2 := C 3 + C 2 * x + y + x * y

#guard kron degrees packed == DensePoly.ofList [3, 2, 1, 1]
#guard kron degrees (0 : P2) == 0
#guard kron degrees (C 5 : P2) == DensePoly.ofList [5]
#guard unKron? (cmp := Mono.lex) degrees (kron degrees packed) == some packed
#guard (unKron? (cmp := Mono.lex) degrees (DensePoly.monomial 4 1)).isNone
#guard unKron? (cmp := Mono.lex) degrees (DensePoly.ofList [5]) == some (C 5 : P2)

#guard
  match kronDecide (x + y) with
  | .irreducible cert => checkIrred (x + y) cert
  | .reducible _ => false

#guard
  match (kronDecide ((x + 1) * (y + 1)) : Verdict 2 Mono.lex) with
  | .reducible split => checkSplit ((x + 1) * (y + 1)) split
  | .irreducible _ => false

#guard
  match (kronDecide ((x + y + 1) * (x - y + 2)) : Verdict 2 Mono.lex) with
  | .reducible split => checkSplit ((x + y + 1) * (x - y + 2)) split
  | .irreducible _ => false

end Hex.MvFactor.Conformance
