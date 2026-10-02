/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexRank
import HexPolyFp.PrimeField
import HexResultant.ExactDiv
import HexMvGcd

/-!
JSONL emit driver for the `hex-rank` oracle.

`lake exe hexrank_emit_fixtures` writes one fixture record per case plus the
result records for the operations `rank`, `colProfile`, `rowProfile`, `denom`
and `cert`, to `stdout` (or to `$HEX_FIXTURE_OUTPUT` when set). The oracle
driver `scripts/oracle/rank_carriers.py` recomputes each operation with
python-flint (`Int`, `Rat`, `ZMod64 p`) or SymPy's `DomainMatrix` over the exact
polynomial domain (`DensePoly`, `MvPoly`), and re-verifies every emitted
certificate with its own arithmetic.

Fixture records use the shared `matrix`, `ratmatrix`, `modmatrix`,
`polymatrix` and `mvpolymatrix` kinds of `Hex.Conformance.Emit`.
Result encodings: `rank` is an integer; `colProfile` and `rowProfile` are
integer lists (`rowProfile` sorted); `denom` is
`{"rows": [...], "cols": [...], "denom": <entry>}` with the Lean-reported index
selection, so that the oracle takes the determinant of its own submatrix
there; `cert` is `{"rank", "rows", "cols", "denom": <entry>, "adj": [[<entry>]]}`.
An `<entry>` is an integer, a rational `{"num", "den"}`, a residue in
`[0, p)`, an ascending coefficient list (`{"num": [...], "den": [...]}` for
rational and integer polynomials, an integer list for residue polynomials),
or a term list `[[exponents], coeff]`.
-/

namespace Hex.RankEmit

open Hex.Conformance.Emit
open Hex
open Hex.Matrix

private def lib : String := "HexRank"

/-! JSON encoders for result values. -/

private def jInt (n : Int) : String := toString n

private def jList (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

private def jIntList (xs : List Int) : String := jList (xs.map jInt)

private def jNatList (xs : List Nat) : String := jIntList (xs.map Int.ofNat)

private def jRat (q : Rat) : String :=
  "{\"num\":" ++ jInt q.num ++ ",\"den\":" ++ jInt q.den ++ "}"

/-- Integer polynomials share the rational fixture encoding. -/
private def jIntPoly (f : DensePoly Int) : String :=
  let cs := f.toArray.toList
  "{\"num\":" ++ jIntList cs ++ ",\"den\":" ++ jIntList (cs.map fun _ => 1) ++ "}"

private def jZModPoly {p : Nat} [ZMod64.Bounds p] (f : DensePoly (ZMod64 p)) : String :=
  jIntList (f.toArray.toList.map fun c => (c.toNat : Int))

private def jRatPoly (f : DensePoly Rat) : String :=
  let cs := f.toArray.toList
  "{\"num\":" ++ jIntList (cs.map (·.num)) ++ ",\"den\":" ++
    jIntList (cs.map fun q => (q.den : Int)) ++ "}"

private def jMvPoly {k : Nat} (f : MvPoly k Int Mono.lex) : String :=
  jList (f.termsList.map fun term =>
    "[" ++ jNatList term.1.toList ++ "," ++ jInt term.2 ++ "]")

private def jMatrix {R : Type} {n m : Nat} (enc : R → String) (M : Matrix R n m) : String :=
  jList (M.rows.toList.map fun row => jList (row.toList.map enc))

private def jFin {k : Nat} (v : Vector (Fin k) r) : String :=
  jNatList (v.toList.map Fin.val)

private def jSortedFin {k : Nat} (v : Vector (Fin k) r) : String :=
  jNatList ((v.toList.map Fin.val).mergeSort (· ≤ ·))

private def jCert {R : Type} {n m : Nat} (enc : R → String) (c : RankCert R n m) : String :=
  "{\"rank\":" ++ toString c.rank ++ ",\"rows\":" ++ jFin c.rows ++ ",\"cols\":" ++
    jFin c.cols ++ ",\"denom\":" ++ enc c.denom ++ ",\"adj\":" ++ jMatrix enc c.adj ++ "}"

private def jDenom {R : Type} {n m : Nat} (enc : R → String) (D : ReducedForm R n m) : String :=
  "{\"rows\":" ++ jFin D.profile.rows ++ ",\"cols\":" ++ jFin D.profile.cols ++
    ",\"denom\":" ++ enc D.denom ++ "}"

/-- Emit the five result records for one case over any carrier. -/
private def emitOps {R : Type} [Lean.Grind.CommRing R] [DecidableEq R] {n m : Nat}
    (enc : R → String) (quot : R → R → R) (id : String) (A : Matrix R n m) : IO Unit := do
  let D := rowReduceWith quot A
  let c := rankCertWith quot A
  -- every emitted certificate passes the oracle-independent checker; the
  -- oracle's re-verification is the cross-check on `checkRank` itself
  unless checkRank A c do
    throw <| IO.userError s!"HexRank: checkRank rejected the produced certificate for {id}"
  emitResult lib id "rank" (toString D.profile.rank)
  emitResult lib id "colProfile" (jFin D.profile.cols)
  emitResult lib id "rowProfile" (jSortedFin D.profile.rows)
  emitResult lib id "denom" (jDenom enc D)
  emitResult lib id "cert" (jCert enc c)

/-! Carriers. -/

private def mkMat {R : Type} [Zero R] (n m : Nat) (rows : Array (Array R)) : Matrix R n m :=
  Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

private def emitInt {n m : Nat} (id : String) (A : Matrix Int n m) : IO Unit := do
  emitMatrixFixture lib id (A.rows.toList.map fun row => row.toList)
  emitOps jInt HexArith.Int.exactDiv id A

private def emitRat {n m : Nat} (id : String) (A : Matrix Rat n m) : IO Unit := do
  emitRatMatrixFixture lib id (A.rows.toList.map fun row => row.toList)
  emitOps jRat Hex.exactDiv id A

private theorem primeTwo : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem primeFive : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact Or.inr rfl

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance primeModTwo : ZMod64.PrimeModulus 2 := ZMod64.primeModulusOfPrime primeTwo
private instance primeModFive : ZMod64.PrimeModulus 5 := ZMod64.primeModulusOfPrime primeFive

private def zm (p : Nat) [ZMod64.Bounds p] (x : Int) : ZMod64 p :=
  ZMod64.ofNat p (x % p).toNat

private def emitZMod (p : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p] {n m : Nat}
    (id : String) (A : Matrix (ZMod64 p) n m) : IO Unit := do
  emitModMatrixFixture lib id p (A.rows.toList.map fun row => row.toList.map fun c => c.toNat)
  emitOps (fun c => jInt (c.toNat : Int)) Hex.exactDiv id A

private def emitZPoly {n m : Nat} (id : String) (A : Matrix ZPoly n m) : IO Unit := do
  emitPolyMatrixRatFixture lib id n m
    (if n = 0 ∨ m = 0 then [] else A.rows.toList.map fun row =>
      row.toList.map fun f => f.toArray.toList.map fun c => ((c : Int) : Rat))
  emitOps jIntPoly Hex.exactDiv id A

private def emitRatPoly {n m : Nat} (id : String) (A : Matrix (DensePoly Rat) n m) : IO Unit := do
  emitPolyMatrixRatFixture lib id n m
    (if n = 0 ∨ m = 0 then [] else A.rows.toList.map fun row => row.toList.map fun f => f.toArray.toList)
  emitOps jRatPoly Hex.exactDiv id A

private def emitZModPoly (p : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p] {n m : Nat}
    (id : String) (A : Matrix (DensePoly (ZMod64 p)) n m) : IO Unit := do
  emitPolyMatrixZModFixture lib id p n m
    (if n = 0 ∨ m = 0 then [] else A.rows.toList.map fun row => row.toList.map fun f =>
      f.toArray.toList.map fun c => (c.toNat : Int))
  emitOps jZModPoly Hex.exactDiv id A

private def emitMv (k : Nat) {n m : Nat} (id : String) (A : Matrix (MvPoly k Int Mono.lex) n m) :
    IO Unit := do
  -- the fixture's minor size `r` is the rank, the largest size of a nonzero minor
  emitMvPolyMatrixFixture lib id k "lex" n m
    (A.rows.toList.map fun row => row.toList.map fun f =>
      f.termsList.map fun term => (term.1.toList, term.2))
    (rankWith Hex.exactDiv A)
  emitOps jMvPoly Hex.exactDiv id A

/-! Integer cases. -/

private def zpoly (cs : List Int) : ZPoly := DensePoly.ofList cs
private def qpoly (cs : List Rat) : DensePoly Rat := DensePoly.ofList cs
private def fpoly (p : Nat) [ZMod64.Bounds p] (cs : List Int) : DensePoly (ZMod64 p) :=
  DensePoly.ofList (cs.map (zm p))

/-- Deterministic small entries for product constructions. -/
private def small (salt i j : Nat) : Int :=
  ((i * 7 + j * 3 + salt * 5) % 11 : Nat) - 5

private def leftFactor (n r salt : Nat) : Matrix Int n r :=
  Matrix.ofFn fun i j => small salt i.val j.val
private def rightFactor (r m salt : Nat) : Matrix Int r m :=
  Matrix.ofFn fun i j => small (salt + 1) (i.val + 2) (j.val + 1)

private def bigEntry (i j : Nat) : Int :=
  (2 : Int) ^ (250 + i * 7 + j * 3) + (i + 1) * (j + 2) * 1234567

private def emitAll : IO Unit := do
  -- degenerate shapes
  emitInt "shape/0x0" (0 : Matrix Int 0 0)
  emitInt "shape/0x3" (0 : Matrix Int 0 3)
  emitInt "shape/3x0" (0 : Matrix Int 3 0)
  -- zero matrices
  emitInt "zero/2x2" (0 : Matrix Int 2 2)
  emitInt "zero/3x4" (0 : Matrix Int 3 4)
  -- 1×1
  emitInt "one/zero" (mkMat 1 1 #[#[0]])
  emitInt "one/seven" (mkMat 1 1 #[#[7]])
  emitInt "one/neg-three" (mkMat 1 1 #[#[-3]])
  -- the matrix on which Bareiss stops
  emitInt "skip/first-column" (mkMat 2 2 #[#[0, 1], #[0, 0]])
  -- a skipped column in the middle with a pivot after it
  emitInt "skip/middle-column" (mkMat 3 4 #[#[1, 2, 0, 3], #[2, 4, 0, 1], #[3, 6, 0, 4]])
  -- the row-profile example: profile {0, 2}, swap order would give {1, 2}
  emitInt "profile/rows-0-2" (mkMat 3 3 #[#[0, 1, 0], #[0, 2, 0], #[1, 0, 0]])
  -- wide and tall products of every rank
  for r in [0, 1, 2, 3] do
    let L : Matrix Int 3 r := leftFactor 3 r r
    let Rm : Matrix Int r 5 := rightFactor r 5 r
    emitInt s!"product/3x5-rank-{r}" (L * Rm)
    let L' : Matrix Int 5 r := leftFactor 5 r (r + 3)
    let Rm' : Matrix Int r 3 := rightFactor r 3 (r + 3)
    emitInt s!"product/5x3-rank-{r}" (L' * Rm')
  -- full rank with a non-identity elimination order: denom = ± det
  emitInt "order/antidiagonal" (mkMat 3 3 #[#[0, 0, 1], #[0, 1, 0], #[1, 0, 0]])
  emitInt "order/late-pivot" (mkMat 3 3 #[#[0, 2, 1], #[3, 0, 4], #[5, 6, 0]])
  -- several hundred bits per entry
  emitInt "big/4x4" (Matrix.ofFn (n := 4) (m := 4) fun i j => bigEntry i.val j.val)
  emitInt "big/3x4-rank-2"
    ((Matrix.ofFn (n := 3) (m := 2) fun i j => bigEntry i.val j.val) *
      (Matrix.ofFn (n := 2) (m := 4) fun i j => bigEntry (i.val + 3) (j.val + 1)))
  -- degenerate shapes over the other carriers
  emitRat "rat/shape-3x0" (0 : Matrix Rat 3 0)
  emitZMod 5 "zmod5/shape-2x0" (0 : Matrix (ZMod64 5) 2 0)
  emitZPoly "zpoly/shape-0x0" (0 : Matrix ZPoly 0 0)
  emitRatPoly "qpoly/shape-3x0" (0 : Matrix (DensePoly Rat) 3 0)
  emitZModPoly 5 "fpoly5/shape-0x2" (0 : Matrix (DensePoly (ZMod64 5)) 0 2)
  emitMv 2 "mv2/shape-2x0" (0 : Matrix (MvPoly 2 Int Mono.lex) 2 0)
  -- rationals
  emitRat "rat/2x2-rank-1" (mkMat 2 2 #[#[1/2, 1/3], #[1/4, 1/6]])
  emitRat "rat/2x3-rank-2" (mkMat 2 3 #[#[1/2, 1/3, 1], #[1/5, 1, 2]])
  emitRat "rat/3x3-rank-2" (mkMat 3 3 #[#[1, 1/2, 1/3], #[2, 1, 2/3], #[0, 1, 5]])
  -- residues: [[1, 1], [1, 3]] has rank 1 over GF(2) and rank 2 over GF(5)
  emitZMod 2 "zmod2/1-1-1-3" (mkMat 2 2 #[#[zm 2 1, zm 2 1], #[zm 2 1, zm 2 3]])
  emitZMod 5 "zmod5/1-1-1-3" (mkMat 2 2 #[#[zm 5 1, zm 5 1], #[zm 5 1, zm 5 3]])
  emitZMod 5 "zmod5/3x4" (mkMat 3 4 #[#[zm 5 2, zm 5 4, zm 5 1, zm 5 0],
    #[zm 5 3, zm 5 1, zm 5 4, zm 5 2], #[zm 5 0, zm 5 0, zm 5 0, zm 5 3]])
  -- dense polynomials: a nonconstant second pivot, and a singular matrix
  emitZPoly "zpoly/2x2-nonconstant-pivot" (mkMat 2 2 #[#[zpoly [0, 1], zpoly [2]],
    #[zpoly [3], zpoly [0, 1]]])
  emitZPoly "zpoly/2x2-singular" (mkMat 2 2 #[#[zpoly [0, 1], zpoly [0, 0, 1]],
    #[zpoly [1], zpoly [0, 1]]])
  emitZPoly "zpoly/2x3" (mkMat 2 3 #[#[zpoly [1, 1], zpoly [0, 1], zpoly [2]],
    #[zpoly [0, 0, 1], zpoly [1], zpoly [0, 3]]])
  emitRatPoly "qpoly/2x2-nonconstant-pivot" (mkMat 2 2 #[#[qpoly [0, 1], qpoly [1/2]],
    #[qpoly [1/3], qpoly [0, 1]]])
  emitRatPoly "qpoly/2x2-singular" (mkMat 2 2 #[#[qpoly [0, 1], qpoly [0, 0, 1]],
    #[qpoly [1/2], qpoly [0, 1/2]]])
  -- X^p - X over GF(p): generic rank 1, specialised rank 0 at every point of GF(p)
  emitZModPoly 5 "fpoly5/x-pow-p-minus-x" (mkMat 1 1 #[#[fpoly 5 [0, -1, 0, 0, 0, 1]]])
  emitZModPoly 5 "fpoly5/2x2" (mkMat 2 2 #[#[fpoly 5 [0, 1], fpoly 5 [1]],
    #[fpoly 5 [1], fpoly 5 [0, 1]]])
  -- multivariate polynomials
  let x2 : MvPoly 2 Int Mono.lex := MvPoly.X 0
  let y2 : MvPoly 2 Int Mono.lex := MvPoly.X 1
  emitMv 2 "mv2/2x2-full" (mkMat 2 2 #[#[x2, y2], #[y2, x2]])
  emitMv 2 "mv2/2x2-singular" (mkMat 2 2 #[#[x2, y2], #[x2 * y2, y2 * y2]])
  let x3 : MvPoly 3 Int Mono.lex := MvPoly.X 0
  let y3 : MvPoly 3 Int Mono.lex := MvPoly.X 1
  let z3 : MvPoly 3 Int Mono.lex := MvPoly.X 2
  emitMv 3 "mv3/3x3-rank-1" ((mkMat 3 1 #[#[x3], #[y3], #[z3]]) *
    (mkMat 1 3 #[#[x3, y3, MvPoly.C 1]]))
  emitMv 3 "mv3/3x3-rank-2"
    (mkMat 3 3 #[#[x3, y3, z3], #[y3, z3, x3], #[x3 + y3, y3 + z3, z3 + x3]])
  let v : Fin 6 → MvPoly 6 Int Mono.lex := fun i => MvPoly.X i
  emitMv 6 "mv6/generic-2x3"
    (Matrix.ofFn (n := 2) (m := 3) fun i j => v ⟨i.val * 3 + j.val, by omega⟩)

end Hex.RankEmit

def main : IO Unit :=
  Hex.RankEmit.emitAll
