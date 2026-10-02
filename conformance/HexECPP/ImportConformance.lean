/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Import
public import HexECPP.Fixture65
meta import HexECPP.Import
meta import HexECPP.Fixture65

public section

/-!
# Import allocation conformance

Oracle: independent arithmetic and frozen PARI data; mode: required through
the main ECPP oracle. Operations: parsed and counted conversion, preflight,
text parsing. Properties: preflight precedes endpoint work, exact inclusive
allocation boundaries, and original row locations. Edges: every row field,
negative oversized integers, excessive rows, invalid endpoints within budget,
and oversized endpoints even when endpoint fuel is inadmissible.
-/

namespace Hex.ECPP.ImportConformance

def budget : ImportBudget :=
  ⟨4096, 100, 10, 128, 128, 256, 100⟩

def pari65 : String :=
  "[[18446744073709551629, -8423788454, 160388, 1, [10598342506117936052, 2225259013356795550]]]"

#guard match convertText budget pari65 Fixture65.child with
  | .ok cert => checkAt 18446744073709551629 cert
  | .error _ => false

private def countedKind (b : ImportBudget) (input : PariCertificate)
    (row : Nat) (kind : ImportErrorKind) (fuel : Nat := 10) : Bool :=
  match convertCounted b Hex.Nat.defaultPrimeCertBudget
      (Hex.Rand.ofSeed 1) fuel input with
  | .error e => e.row == row && e.kind == kind
  | .ok _ => false

-- Fifteen is composite: an in-budget endpoint reaches endpoint checking.
#guard countedKind { budget with maxIntegerBits := 2 } ⟨[], 15⟩ 0 .exhausted
#guard countedKind { budget with maxIntegerBits := 4 } ⟨[], 15⟩ 0 .invalidEndpoint
#guard countedKind { budget with maxIntegerBits := 3 } ⟨[], 8⟩ 0 .exhausted
#guard (convertCounted { budget with maxIntegerBits := 2 }
  Hex.Nat.defaultPrimeCertBudget (Hex.Rand.ofSeed 1) 10 ⟨[], 2⟩).isOk

private def row : PariRow := ⟨3, 0, 1, 0, ⟨0, 0, 1⟩⟩
private def largeRows : List PariRow :=
  [{ row with n := 16 }, { row with t := -16 },
   { row with s := 16 }, { row with a := -16 },
   { row with point := ⟨-16, 0, 1⟩ },
   { row with point := ⟨0, -16, 1⟩ },
   { row with point := ⟨0, 0, -16⟩ }]

-- An invalid endpoint exposes whether any oversized field reaches search.
#guard largeRows.all fun r =>
  countedKind { budget with maxIntegerBits := 4 } ⟨[row, r], 15⟩ 1 .exhausted
#guard countedKind { budget with maxRows := 1 } ⟨[row, row], 15⟩ 0 .exhausted
#guard countedKind { budget with maxIntegerBits := 4 } ⟨[row], 16⟩ 1 .exhausted
-- Row preflight also precedes the independent endpoint-fuel allocation.
#guard countedKind { budget with maxIntegerBits := 4 }
  ⟨[{ row with a := 16 }], 15⟩ 0 .exhausted 101
#guard largeRows.all fun r =>
  match convert { budget with maxIntegerBits := 4 } ⟨[row, r], 15⟩ (.small 2) with
  | .error e => e.row == 1 && e.kind == .exhausted
  | .ok _ => false
#guard (preflight { budget with maxRows := 2, maxIntegerBits := 4 }
  ⟨[row, { row with t := -15, a := 15, point := ⟨-15, 15, -15⟩ }], 15⟩).isOk

-- Parsing respects small explicit bit policies as well as bytes and digits.
#guard match parsePari { budget with maxIntegerBits := 3 } "8" with
  | .error .exhausted => true
  | _ => false
#guard (parsePari { budget with maxIntegerBits := 4 } "15").isOk
#guard (parsePari { budget with maxInputBytes := 2 } "13").isOk
#guard match parsePari { budget with maxInputBytes := 1 } "13" with
  | .error .exhausted => true
  | _ => false
#guard (parsePari { budget with maxDigits := 2 } "13").isOk
#guard match parsePari { budget with maxDigits := 1 } "13" with
  | .error .exhausted => true
  | _ => false
#guard match convertText budget "[[7,-5,1,0,[1,2]],[7,0]]" (.small 13) with
  | .error e => e.row == 1 && e.kind == .malformed
  | _ => false
#guard match convertText budget "[[7,-5,1,0,[1,2]],[7,0,0,0,[1,2]]]" (.small 13) with
  | .error e => e.row == 1 && e.kind == .invalidArithmetic
  | _ => false
#guard match parsePari budget "[[[[0]]]]" with
  | .error .unsupported => true
  | _ => false

-- The 65-bit supplied row has an 18-bit cofactor and a 47-bit child scalar.
#guard (convertText { budget with
    maxInputBytes := pari65.utf8ByteSize
    maxRows := 1
    maxIntegerBits := 65
    maxScalarBits := 47
    maxInverseOps := 68 }
  pari65 Fixture65.child).isOk
#guard match convertText { budget with maxIntegerBits := 64 } pari65 Fixture65.child with
  | .error e => e.row == 0 && e.kind == .exhausted
  | _ => false
#guard match convertText { budget with maxScalarBits := 46 } pari65 Fixture65.child with
  | .error e => e.row == 0 && e.kind == .exhausted
  | _ => false
#guard match convertText { budget with maxInverseOps := 67 } pari65 Fixture65.child with
  | .error e => e.row == 0 && e.kind == .exhausted
  | _ => false

end Hex.ECPP.ImportConformance
