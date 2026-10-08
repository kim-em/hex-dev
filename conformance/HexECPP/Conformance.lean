/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP
public import HexECPP.Fixture65
public import HexECPP.Fixture17
public import HexECPP.Fixture256
public import HexECPP.Fixture512
public import HexECPP.ImportConformance
public import HexECPP.PariFixtures

public meta import HexArith.Montgomery.Context
public meta import HexECPP.Affine
public meta import HexECPP.Cert
public meta import HexECPP.Data
public meta import HexECPP.Fixture17
public meta import HexECPP.Fixture256
public meta import HexECPP.Fixture65
public meta import HexECPP.Import
public meta import HexECPP.ImportConformance
public meta import HexECPP.Replay
public meta import HexPrimality.Cert
public meta import HexPrimality.Search

public meta import HexECPP.Fixture512

public section

/-!
Core ECPP conformance. Oracle: PARI for the frozen subjects and an independent
Python affine replay and PARI `elladd`/`ellmul` in
`scripts/oracle/ecpp_pari.py`; mode: required. The emitted oracle cases
exhaust point pairs and scalar schedules up to twice the field size on
`y² = x³ + 3` and `y² = x³ + x` over `F₅`, `F₇`, and `F₁₁`.
Covered operations: addition, scalar replay, recursive checking, and bounded
PARI conversion. The guards pin all exceptional addition branches, witness
consumption, strict size equality, subject binding, corrupt data, nonunit
projective normalization, and complete 65/256/512-bit certificates.
-/

open Hex.ECPP

private def P : Point := .affine 1 2
private def N : Point := .affine 1 5

#guard onCurve 7 0 3 1 2
#guard add? 7 0 .infinity P [] == some (P, [])
#guard add? 7 0 P .infinity [] == some (P, [])
#guard add? 7 0 P N [] == some (.infinity, [])
#guard add? 7 0 P P [2] == some (.affine 6 3, [])
#guard add? 7 0 P (.affine 6 3) [3] == some (.affine 2 2, [])
#guard add? 7 0 P P [] == none
#guard add? 7 0 P P [3] == none
#guard add? 7 0 P (.affine 1 3) [] == none
#guard add? 7 0 P P [2, 4] == some (.affine 6 3, [4])
#guard add? 35 0 (.affine 1 0) (.affine 1 0) [] ==
  some (.infinity, [])
#guard add? 35 0 (.affine 1 5) (.affine 6 5) [7] == none
#guard add? 35 0 (.affine 1 5) (.affine 6 5) [35] == none
#guard (modSub 7 1 6) == 2
#guard (Point.affine 6 3).canonical 7
#guard !(Point.affine 7 3).canonical 7
#guard sizeBound 35 13
#guard 243 * 17 % 35 == 1
#guard 15 % 5 == 0 && 15 % 7 == 1 && 16 % 7 == 2
#guard match proposeScalar ImportConformance.budget 7 0 13 P with
  | .ok (.infinity, _) => true
  | _ => false
#guard !(sizeBound 16 9)
#guard !(sizeBound 64 9)
#guard HexArith.bitLength 13 == 4
#guard (13 : Nat).testBit 3 && (13 : Nat).testBit 2 && !((13 : Nat).testBit 1) && (13 : Nat).testBit 0
#guard !(replayDone 7 0 3 0 P [1])

#guard checkAt 18446744073709551629 Fixture65.cert
#guard checkAt 17 Fixture17.cert
#guard !checkAt 19 Fixture17.cert
#guard !checkAt 18446744073709551631 Fixture65.cert
#guard !checkStep 3 0 0 0 0 0 [] 2
#guard !checkStep 21 0 0 0 0 0 [] 2
#guard !checkStep 35 0 3 1 2 17 [] 35
#guard match Fixture65.cert with
  | .step n a b x y d (_ :: tail) child =>
      !check (.step n a b x y d (0 :: tail) child)
  | _ => false
#guard match Fixture65.cert with
  | .step n a b x y d ws child => !check (.step n a b x y d (ws ++ [1]) child)
  | _ => false
#guard match Fixture65.cert with
  | .step n a b x y d ws  _ => !check (.step n a b x y d ws (.base (.small 2)))
  | _ => false
#guard match Fixture65.cert with
  | .step n a b x y d ws child =>
      !check (.step n a b x (y + 1) d ws child) &&
      !check (.step n a b x y 0 ws child) &&
      !check (.step n n b x y d ws child) &&
      !check (.step n a n x y d ws child) &&
      !check (.step n a b n y d ws child) &&
      !check (.step n a b x n d ws child) &&
      !check (.step n a b x y n ws child)
  | _ => false
#guard match Fixture65.cert with
  | .step n a b x y d (_ :: tail) child =>
      !check (.step n a b x y d (n :: tail) child)
  | _ => false

#guard match normalizeProjective 35 ⟨15, 16, 15⟩ with
  | .error .nonunitProjective => true
  | _ => false
#guard match convertRow ImportConformance.budget
    ⟨35, 23, 1, 0, ⟨15, 16, 15⟩⟩ (.base (.small 13)) with
  | .error .nonunitProjective => true
  | _ => false
#guard match normalizeProjective 49 ⟨7, 2, 7⟩ with
  | .error .nonunitProjective => true
  | _ => false
#guard match convertRow ImportConformance.budget
    ⟨49, 37, 1, 0, ⟨7, 2, 7⟩⟩ (.base (.small 13)) with
  | .error .nonunitProjective => true
  | _ => false
#guard match parsePari ⟨2, 1, 1, 1, 1, 1, 1⟩ "[123]" with
  | .error .exhausted => true
  | _ => false
#guard match parsePari ImportConformance.budget "[[1,2]]" with
  | .error .malformed => true
  | _ => false
#guard match parsePari ImportConformance.budget "[[1,2,3,4,[5,6,7,8]]]" with
  | .error .malformed => true
  | _ => false
#guard match parsePari ImportConformance.budget "[1.5]" with
  | .error .unsupported => true
  | _ => false
#guard match convertRow ImportConformance.budget
    ⟨35, 23, 2, 0, ⟨1, 2, 1⟩⟩ (.base (.small 13)) with
  | .error .invalidArithmetic => true
  | _ => false
#guard match convertText
    { ImportConformance.budget with maxInverseOps := 0 }
    ImportConformance.pari65 Fixture65.child with
  | .error e => e.kind == .exhausted
  | _ => false
#guard match convertText ImportConformance.budget
    ImportConformance.pari65 (.small 2) with
  | .error e => e.kind == .subjectMismatch
  | _ => false
#guard match convertText ImportConformance.budget
    ImportConformance.pari65 (.small 115013243398093) with
  | .error e => e.kind == .invalidEndpoint
  | _ => false
#guard match convertCounted defaultImportBudget Hex.Nat.defaultPrimeCertBudget
    (Hex.Rand.ofSeed 1) 201 ⟨[], 13⟩ with
  | .error e => e.kind == .exhausted
  | _ => false
#guard match convertCounted defaultImportBudget Hex.Nat.defaultPrimeCertBudget
    (Hex.Rand.ofSeed 1) 10 ⟨[], 13⟩ with
  | .ok (cert, _) => checkAt 13 cert
  | _ => false

#guard checkAt Fixture256.cert.subject Fixture256.cert
#guard checkAt Fixture512.cert.subject Fixture512.cert
