/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRank.Fixtures
import Hex.Conformance.Emit
import Lean.Data.Json

namespace Hex.GenericRank.Emit

open Hex Fixtures Lean

def polynomial [Zero C] (encode : C → Json) (p : Poly k C) : Json :=
  toJson (p.termsList.map fun (e, c) => Json.arr #[toJson e.toList, encode c])

def matrix (encode : C → Json) (A : Matrix C n m) : Json :=
  toJson (A.rows.toList.map fun row => row.toList.map encode)

/-- Emit a construction-checked rank and the producer's signed pivot minor.
The existing carrier oracle independently checks both over the fraction field. -/
def emitCase {C : Type} [Lean.Grind.CommRing C] [DecidableEq C]
    [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (base : String) (modulus : Nat) (encode : C → Json) (c : Case k C) : IO Unit := do
  let some cert := genericCert? c.matrix
    | throw <| IO.userError s!"generic rank certificate rejected: {base}/{k}/{c.name}"
  unless cert.rank == c.expected do
    throw <| IO.userError s!"generic rank disagrees with construction: {base}/{k}/{c.name}"
  let json := Json.mkObj [
    ("kind", toJson "generic_rank"), ("lib", toJson "HexGenericRank"),
    ("carrier", toJson "mv"), ("base", toJson base), ("arity", toJson k),
    ("modulus", toJson modulus), ("case", toJson c.name),
    ("n", toJson c.n), ("m", toJson c.m),
    ("matrix", matrix (polynomial encode) c.matrix),
    ("support", matrix (fun p => toJson p.termCount) c.matrix),
    ("pivot_rows", toJson (cert.rows.toList.map Fin.val)),
    ("pivot_cols", toJson (cert.cols.toList.map Fin.val)),
    ("denom", polynomial encode cert.denom), ("result", toJson c.expected)]
  Hex.Conformance.Emit.emitLine json.compress

private instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
private instance : ZMod64.PrimeModulus 2 := ⟨by decide⟩
set_option maxRecDepth 100000 in
private instance : ZMod64.PrimeModulus 2147483647 := ⟨by decide⟩
private instance : ZMod64.Bounds 2147483647 := ⟨by decide, by decide⟩

private instance : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance : ZMod64.PrimeModulus 3 := ⟨by decide⟩

def cancellation [Lean.Grind.CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
    (rank : Nat) : Case 1 C :=
  let x : Poly 1 C := MvPoly.X 0
  ⟨"characteristic-cancellation", 3, 3,
    ofRows 3 3 #[#[x, x, 0], #[x, 0, x], #[0, x, x]], rank⟩

def emitAll : IO Unit := do
  let rat (q : Rat) := Json.arr #[toJson q.num, toJson q.den]
  let residue (q : ZMod64 3) := toJson q.toNat
  for c in cases (MvPoly.X 0 : Poly 2 Int) (MvPoly.X 1) (MvPoly.X 0 + MvPoly.X 1) do
    emitCase "ZZ" 0 toJson c
  for c in cases (MvPoly.X 0 : Poly 3 Int) (MvPoly.X 1) (MvPoly.X 2) do
    emitCase "ZZ" 0 toJson c
  for c in cases (MvPoly.C (1/2) * MvPoly.X 0 : Poly 2 Rat)
      (MvPoly.C (2/3) * MvPoly.X 1) (MvPoly.X 0 + MvPoly.X 1) do
    emitCase "QQ" 0 rat c
  for c in cases (MvPoly.C (1/2) * MvPoly.X 0 : Poly 3 Rat)
      (MvPoly.C (2/3) * MvPoly.X 1) (MvPoly.X 2) do
    emitCase "QQ" 0 rat c
  for c in cases (MvPoly.X 0 : Poly 2 (ZMod64 3)) (MvPoly.X 1) (MvPoly.X 0 + MvPoly.X 1) do
    emitCase "GF" 3 residue c
  for c in cases (MvPoly.X 0 : Poly 3 (ZMod64 3)) (MvPoly.X 1) (MvPoly.X 2) do
    emitCase "GF" 3 residue c
  emitCase "GF" 3 residue ⟨"frobenius", 1, 1,
    ofRows 1 1 #[#[(MvPoly.X 0 : Poly 1 (ZMod64 3)) ^ 3 - MvPoly.X 0]], 1⟩
  for c in cases (MvPoly.C 1073741823 * MvPoly.X 0 : Poly 2 (ZMod64 2147483647))
      (MvPoly.C 2147483646 * MvPoly.X 1) (MvPoly.X 0 + MvPoly.X 1) do
    emitCase "GF" 2147483647 (fun q : ZMod64 2147483647 => toJson q.toNat) c
  emitCase "ZZ" 0 toJson (cancellation (C := Int) 3)
  emitCase "GF" 2 (fun q : ZMod64 2 => toJson q.toNat) (cancellation 2)
  emitCase "GF" 3 residue (cancellation 3)

end Hex.GenericRank.Emit

def main : IO Unit := Hex.GenericRank.Emit.emitAll
