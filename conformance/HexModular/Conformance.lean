/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModular

/-!
Core conformance checks for integer CRT and rational reconstruction.

Oracle: SymPy CRT plus an independent Python `fractions.Fraction` Euclidean
reconstruction driver
Mode: always
Covered operations:
- `symMod`
- `Crt.init` and `Crt.push`
- `CrtVec.init` and `CrtVec.push`
- `euclidUntil`
- `ratReconCheck`, `ratRecon?`, and `ratReconWide?`
- `ratReconVec?` and `ratReconMaxQuot?`
- `crtLoop`
Covered properties:
- symmetric representatives preserve residues and obey the half-modulus bound
- scalar and vector CRT pushes preserve old residues, record new residues, and
  multiply the accumulated modulus
- Euclidean stopping rows satisfy their modular linear relation
- every accepted rational reconstruction satisfies its congruence and bounds
- vector reconstruction uses one positive bounded common denominator
- maximal-quotient candidates satisfy their promised congruence
- the multimodular loop skips rejected images and returns only a caller result
Covered edge cases:
- modulus zero and one
- the even-modulus symmetric tie in both signs
- the outer-reduction regression and non-coprime CRT moduli
- zero-length vectors and a denominator first discovered in the last coordinate
- reconstruction failure, negative numerators, and non-unique input bounds
- skipped images, rejected moduli, zero fuel, and fuel exhaustion
-/

namespace Hex.Modular.Conformance

private def congruent (x y : Int) (m : Nat) : Bool :=
  x % (m : Int) == y % (m : Int)

private def crtContract (old next : Crt) (residue : Int) (m : Nat) : Bool :=
  next.modulus == old.modulus * m &&
    congruent next.value residue m &&
    congruent next.value old.value old.modulus &&
    2 * next.value.natAbs ≤ next.modulus

private def crtVecContract {k : Nat} (old next : CrtVec k)
    (residues : Vector Int k) (m : Nat) : Bool :=
  next.modulus == old.modulus * m &&
    (List.finRange k).all (fun i =>
      congruent next.value[i] residues[i] m &&
        congruent next.value[i] old.value[i] old.modulus &&
        2 * next.value[i].natAbs ≤ next.modulus)

/-! Symmetric representatives: ordinary, degenerate, and tie cases. -/

#guard symMod 17 10 = -3
#guard symMod (-37) 0 = -37
#guard symMod 3 6 = 3 && symMod (-3) 6 = 3

#guard congruent (symMod 987654321 1009) 987654321 1009
#guard 2 * (symMod 987654321 1009).natAbs ≤ 1009

/-! Scalar CRT: one push, invalid moduli, and the outer reduction. -/

#guard
  match Crt.init.push 2 5 with
  | some next => crtContract Crt.init next 2 5
  | none => false

#guard (Crt.init.push 4 0).isNone && (Crt.init.push 4 1).isNone

#guard
  match Crt.init.push 1 3 with
  | none => false
  | some first =>
      match first.push 0 2 with
      | some next => next.value == -2 && crtContract first next 0 2
      | none => false

#guard
  match Crt.init.push 1 6 with
  | none => false
  | some first => (first.push 2 9).isNone

/-! Vector CRT: one inverse shared by the coordinates and the same failures. -/

#guard (CrtVec.init 3).modulus = 1 && (CrtVec.init 3).value = #v[0, 0, 0]

#guard
  let residues : Vector Int 3 := #v[1, -1, 2]
  let init := CrtVec.init 3
  match init.push residues 5 with
  | some next => crtVecContract init next residues 5
  | none => false

#guard
  let residues : Vector Int 0 := #v[]
  let init := CrtVec.init 0
  match init.push residues 7 with
  | some next => crtVecContract init next residues 7
  | none => false

#guard
  let firstResidues : Vector Int 3 := #v[1, 2, -1]
  let nextResidues : Vector Int 3 := #v[0, 1, 1]
  match (CrtVec.init 3).push firstResidues 3 with
  | none => false
  | some first =>
      match first.push nextResidues 2 with
      | some next => crtVecContract first next nextResidues 2
      | none => false

#guard ((CrtVec.init 3).push #v[1, 2, 3] 1).isNone

/-! Truncated Euclid rows: typical, zero modulus, and signed inputs. -/

#guard euclidUntil 101 51 2 = { r := 1, t := 2 }
#guard euclidUntil 0 37 4 = { r := 0, t := 0 }
#guard
  let row := euclidUntil (-1009) (-613) 17
  row.r ≤ 17 && congruent row.r (row.t * (-613)) 1009

/-! Bounded scalar reconstruction and its exposed checker. -/

#guard ratReconCheck 68 101 8 8 (Rat.divInt 2 3)
#guard !ratReconCheck 68 101 8 8 (Rat.divInt 1 3)
#guard !ratReconCheck 1 0 8 8 1

#guard ratRecon? 68 101 8 8 = some (Rat.divInt 2 3)
#guard (ratRecon? 50 101 1 1).isNone
#guard ratRecon? 33 101 8 8 = some (Rat.divInt (-2) 3)

#guard ratReconWide? 68 101 = some (Rat.divInt 2 3)
#guard (ratReconWide? 17 0).isNone
#guard ratReconWide? 33 101 = some (Rat.divInt (-2) 3)

-- The checker, not uniqueness, is the contract when the bounds violate
-- `2 P Q < m`.
#guard
  match ratRecon? 3 8 4 4 with
  | some x => ratReconCheck 3 8 4 4 x
  | none => true

/-! Common-denominator vector reconstruction. -/

private def ratVecContract {k : Nat} (a y : Vector Int k)
    (m : Nat) (P Q d : Int) : Bool :=
  0 < d && d ≤ Q &&
    (List.finRange k).all (fun i =>
      (d * a[i] - y[i]) % (m : Int) == 0 && (y[i].natAbs : Int) ≤ P)

#guard
  let a : Vector Int 2 := #v[51, 1]
  match ratReconVec? a 101 2 4 with
  | some (y, d) => y == #v[1, 2] && d == 2 && ratVecContract a y 101 2 4 d
  | none => false

#guard
  let a : Vector Int 0 := #v[]
  match ratReconVec? a 101 2 4 with
  | some (y, d) => y == #v[] && d == 1 && ratVecContract a y 101 2 4 d
  | none => false

#guard
  let a : Vector Int 2 := #v[0, 76]
  match ratReconVec? a 101 2 4 with
  | some (y, d) => y == #v[0, 1] && d == 4 && ratVecContract a y 101 2 4 d
  | none => false

#guard
  let a : Vector Int 2 := #v[51, 76]
  match ratReconVec? a 101 2 4 with
  | some (y, d) => y == #v[2, 1] && d == 4 && ratVecContract a y 101 2 4 d
  | none => false

/-! Maximal-quotient reconstruction promises congruence only. -/

#guard (ratReconMaxQuot? 1 0).isNone
#guard ratReconMaxQuot? 0 101 = some 0
#guard
  match ratReconMaxQuot? 68 101 with
  | some x => (Int.ofNat x.den * 68 - x.num) % 101 == 0
  | none => false

/-! The fuelled loop: acceptance, empty fuel, and skipped/rejected inputs. -/

private def targetImage (target : Int) (m : Nat) : Option (Vector Int 1) :=
  some #v[target % (m : Int)]

private def acceptAt (bound : Nat) (state : CrtVec 1) : Option Int :=
  if bound < state.modulus then some state.value[0] else none

#guard crtLoop (targetImage 7) (acceptAt 10) #[3, 5, 7] 3 = some 7
#guard crtLoop (targetImage 7) (acceptAt 10) #[3, 5, 7] 0 = none
#guard crtLoop (targetImage 7) (fun _ => (none : Option Int)) #[3, 5, 7] 2 = none

#guard
  let image := fun m => if m = 4 then none else targetImage 10 m
  crtLoop image (acceptAt 20) #[4, 1, 6, 5, 7] 5 = some 10

end Hex.Modular.Conformance
