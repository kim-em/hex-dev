/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexModular.SymMod
public meta import HexPolyZGcd.Fast
public import HexModular.SymMod
public import HexPolyZGcd.Fast

public section

/-!
Checked heuristic integer-polynomial gcd candidates.

Evaluation and symmetric-adic reconstruction are candidate production only.
Accidental common factors in the evaluated cofactors are harmless because the
result is returned exclusively through `checkedCandidate?`.
-/

namespace Hex

namespace ZPoly

/-- Symmetric base-`base` digits of an integer, low digit first. -/
private def symDigits (base : Nat) : Int → Nat → List Int
  | _, 0 => []
  | value, fuel + 1 =>
      if value = 0 then
        []
      else
        let digit := Modular.symMod value base
        digit :: symDigits base ((value - digit) / Int.ofNat base) fuel

/-- Reconstruct a polynomial from symmetric digits at a proved valid base. -/
private def heuReconstruct (value : Int) (base degreeBound : Nat)
    (_hbase : 1 < base) : ZPoly :=
  DensePoly.ofList (symDigits base value (degreeBound + 2))

/-- One GCDHEU candidate.  Content is split before evaluation and restored
after primitive normalization of the symmetric-adic reconstruction. -/
private def heuCandidateAt (f h : ZPoly) (base : Nat)
    (hbase : 1 < base) : ZPoly :=
  let f0 := primitivePart f
  let h0 := primitivePart h
  let fv := DensePoly.eval f0 (Int.ofNat base)
  let hv := DensePoly.eval h0 (Int.ofNat base)
  let value : Int := Int.ofNat (Int.gcd fv hv)
  let degreeBound := min f0.size h0.size
  let primitive := normalizePrimitiveSign
    (primitivePart (heuReconstruct value base degreeBound hbase))
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  normalizePrimitiveSign (DensePoly.scale commonContent primitive)

/-- One checked GCDHEU candidate when the symmetric-digit base is valid.
Invalid bases have no candidate rather than denoting the zero polynomial. -/
def heuCandidateAt? (f h : ZPoly) (base : Nat) : Option ZPoly :=
  if hbase : 1 < base then some (heuCandidateAt f h base hbase) else none

/-- Maximum absolute input coefficient. -/
private def coeffNorm (f : ZPoly) : Nat :=
  f.toArray.foldl (fun n c => max n c.natAbs) 0

/-- A positive estimate of the evaluated integer's bit size. -/
private def projectedBits (f h : ZPoly) (base : Nat) : Nat :=
  let degree := max f.size h.size
  let coeffBits := Nat.log2 (max 2 (max (coeffNorm f) (coeffNorm h))) + 1
  let baseBits := Nat.log2 (max 2 base) + 1
  max 1 (coeffBits + degree * baseBits)

/-- Retry with growing bases until the projected bit-size budget is exhausted.
The budget, rather than a fixed retry count, controls work as evaluations grow.
-/
private def heuLoop (f h : ZPoly) (base remainingBits : Nat)
    (hbase : 1 < base) : Option GcdCert :=
  let cost := projectedBits f h base
  if cost > remainingBits then
    none
  else
    match checkedCandidate? f h (heuCandidateAt f h base hbase) with
    | some cert => some cert
    | none => heuLoop f h (2 * base + 1) (remainingBits - cost) (by omega)
termination_by remainingBits
decreasing_by
  have hcostOne : 1 ≤ projectedBits f h base := by
    unfold projectedBits
    exact Nat.le_max_left 1 _
  omega

/-- Checked heuristic route with a 4096-bit projected evaluation budget. -/
def heuCert? (f h : ZPoly) : Option GcdCert :=
  let norm := max (coeffNorm f) (coeffNorm h)
  let base := max 3 (2 * norm + 1)
  heuLoop f h base 4096 (by omega)

/-! Route-level pins: one genuine hit and one accidental evaluated factor. -/

#guard
  let common : ZPoly := DensePoly.ofList [1, 1]
  let f := common * DensePoly.ofList [2, 1]
  let h := common * DensePoly.ofList [3, 1]
  match heuCandidateAt? f h 101 with
  | some candidate => (checkedCandidate? f h candidate).isSome
  | none => false

#guard
  let f : ZPoly := DensePoly.ofList [0, 1]
  let h : ZPoly := DensePoly.ofList [5, 1]
  -- Both evaluations at `5` share `5`, reconstructing the false candidate
  -- `x`; exact trial division must reject it.
  match heuCandidateAt? f h 5 with
  | some candidate => (checkedCandidate? f h candidate).isNone
  | none => false

-- Bases zero and one cannot silently stand for the zero candidate.
#guard (heuCandidateAt? (1 : ZPoly) 1 0).isNone
#guard (heuCandidateAt? (1 : ZPoly) 1 1).isNone

end ZPoly

end Hex
