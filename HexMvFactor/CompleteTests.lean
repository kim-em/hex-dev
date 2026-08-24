/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Factor
public import HexMvFactor.Factor

public section

namespace Hex.MvFactor.CompleteTests

open Hex
open Hex.MvPoly
open Hex.MvFactor

private abbrev P0 := MvPoly 0 Int Mono.lex
private abbrev P1 := MvPoly 1 Int Mono.lex
private abbrev P2 := MvPoly 2 Int Mono.lex
private abbrev P32 := MvPoly 32 Int Mono.lex
private abbrev P4096 := MvPoly 4096 Int Mono.lex

private def ux : P1 := X 0
private def x : P2 := X 0
private def y : P2 := X 1

private def quadratic : P2 := x ^ 2 + y ^ 2 + 1
private def hardPoint : P2 := x ^ 4 + y ^ 3
private def highMono : Mono 32 := Hex.Vector.ofFn' fun _ => 2
private def highSparse : P32 := MvPoly.monomial highMono 1 + 1
private def hugeMono : Mono 4096 := Hex.Vector.ofFn' fun _ => 1
private def hugeSparse : P4096 := MvPoly.monomial hugeMono 1 + 1

private def withKronecker : Config :=
  { Config.default with kronecker := true }

private def noImage : Config :=
  { withKronecker with pointFuel := 0 }

/- The obligation-free route precedes both image search and Kronecker. -/
#guard
  match irredCert? withKronecker (x + y + 1) with
  | .ok (cert, _) =>
      cert.noKronecker && (obligations (x + y + 1) cert).isEmpty &&
        checkIrred (x + y + 1) cert
  | _ => false

/- A successful image is retained even when the complete fallback is enabled. -/
#guard
  match irredCert? withKronecker quadratic with
  | .ok (cert, _) =>
      cert.noKronecker && !(obligations quadratic cert).isEmpty &&
        checkIrred quadratic cert
  | _ => false

/- BZ stores positive-leading factors and moves the sign to its scalar;
   the image obligation deliberately retains the primitive part's sign. -/
#guard
  match irredCert? Config.default (-quadratic) with
  | .ok (cert, _) =>
      cert.noKronecker && !(obligations (-quadratic) cert).isEmpty &&
        checkIrred (-quadratic) cert
  | _ => false

/- With image search disabled, the actual Kronecker factorization and sweep
   produce the certificate. -/
#guard
  match irredCert? noImage quadratic with
  | .ok (cert@(.kronecker _ _), _) => checkIrred quadratic cert
  | _ => false

private def disabled : Config :=
  { Config.default with pointFuel := 0, kronecker := false }

#guard
  match irredCert? disabled quadratic with
  | .error (.irreducible factor) => factor == quadratic
  | _ => false

private def noKronBudget : Config :=
  { noImage with kroneckerDeg := 0 }

#guard
  match irredCert? noKronBudget quadratic with
  | .error (.irreducible factor) => factor == quadratic
  | _ => false

/- The sparse degree guard must reject before attempting to allocate the
   `3^32`-position dense image represented by this two-term polynomial. -/
private def noHugeImage : Config :=
  { Config.default with
    pointFuel := 0
    kronecker := true
    kroneckerDeg := 0 }

#guard
  let degrees := kronDegrees highSparse
  match kronDegree? (fun i => degrees[i]) highSparse with
  | some degree => 1_000_000 < degree
  | none => false

#guard (kronCert? noHugeImage highSparse).isNone

#guard
  match irredCert? noHugeImage highSparse with
  | .error (.irreducible factor) => factor == highSparse
  | _ => false

/- Many degree-one variables make exact weights grow as `2^i`.  A zero
   budget keeps the entire precheck in the saturated values zero and one. -/
#guard
  let degrees := kronDegrees hugeSparse
  kronDegreeUpTo? 0 (fun i => degrees[i]) hugeSparse == some 1

#guard (kronCert? noHugeImage hugeSparse).isNone

/- Zero has a checked decomposition but deliberately no complete answer. -/
#guard
  match completeWith Config.default (0 : P2) with
  | .error stoppedAnswer =>
      (match stoppedAnswer.reason with | .zero => true | _ => false) &&
        checkDecomp 0 stoppedAnswer.found.raw
  | .ok _ => false

/- Constants, including arity zero, have no polynomial obligations. -/
#guard
  match complete? (C 12 : P0) with
  | .ok answer =>
      answer.raw.certs.isEmpty && checkComplete (C 12 : P0) answer.raw
  | .error _ => false

/- Monomial variables receive degree-one certificates with their
   multiplicities preserved. -/
#guard
  let subject : P2 := C 6 * x ^ 2 * y
  match complete? subject with
  | .ok answer =>
      answer.raw.decomp.factors.length == 2 &&
        answer.raw.certs.length == 2 && NoKronecker answer.raw &&
        checkComplete subject answer.raw
  | .error _ => false

/- Repeated factors stay merged and are certified once. -/
#guard
  let subject : P1 := (ux + 1) ^ 3 * (ux ^ 2 + 1)
  match complete? subject with
  | .ok answer =>
      answer.raw.decomp.factors.length == 2 &&
        answer.raw.decomp.factors.any (fun entry => entry.multiplicity == 3) &&
        checkComplete subject answer.raw
  | .error _ => false

/- At seed one the factorizer first sees the irreducible `x^4 + 1` image.
   Its advanced state makes certificate scouting stop at the reducible
   `x^4 - 1` image, so this exercises `completeWith`'s real fallback. -/
private def completeUsesKron (seed : Nat) : Bool :=
  let cfg : Config :=
    { Config.default with
      rand := Rand.ofSeed seed
      pointFuel := 3
      pointScouts := 1
      pointShell := 1
      kronecker := true }
  match completeWith cfg hardPoint with
  | .ok (answer, _) => !NoKronecker answer.raw
  | .error _ => false

#guard completeUsesKron 1

end Hex.MvFactor.CompleteTests
