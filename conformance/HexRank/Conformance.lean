/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRank
import HexMatrix.Notation
import HexPolyFp.PrimeField
import HexResultant.ExactDiv
import HexMvGcd

/-!
Core conformance checks for `hex-rank`.

Run this file through the conformance Lake target (not direct `lake env lean`):
the integer guards need the native code generated for `HexArith.Int.exactDiv`.

Oracle: `scripts/oracle/rank_carriers.py` (`rank`, `colProfile`, `rowProfile`,
`denom`, `cert` ops, via the `hexrank_emit_fixtures` stream)
Mode: always
Covered operations:
- `rankWith`, `rankProfileWith`, `rowReduceWith`, `rankCertWith`, `checkRank`
  and the `Int` entry points `rank`, `rankProfile`, `rowReduceFF`, `rankCert`
Covered properties:
- every produced certificate passes `checkRank`, over `Int`, `Rat`,
  `ZMod64 p`, `DensePoly Rat`, `ZPoly`, `DensePoly (ZMod64 p)` and `MvPoly`
- mutated certificates (wrong rank, one entry of `adj` changed, `denom := 0`,
  a repeated row index) fail `checkRank`
- the reduced form rescales earlier pivot rows to the last pivot
  (`[[2, 0], [0, 3]]` reduces to `[[6, 0], [0, 6]]` with `denom = 6`)
- the row profile is the lexicographically first independent row set, not the
  swap-order set
- `RankCert.matrix_eq_zero` at rank `0`, discharged by `decide +kernel`
Covered edge cases:
- `0 × 0`, `0 × m`, `n × 0`, zero matrices, `1 × 1` including negative entries
- `[[0, 1], [0, 0]]`, on which the square Bareiss loop stops
- `[[1, 1], [1, 3]]` over `GF(2)` (rank 1) against `GF(5)` (rank 2)
- `[X^p - X]` over `GF(p)[X]`: generic rank 1, although it vanishes at every
  point of `GF(p)` (a `rankAt`-style observation, not an oracle op)
-/

namespace Hex.RankConformance

open Hex Hex.Matrix
open scoped Hex

/-! Integer cases. -/

private def stop : Matrix Int 2 2 := #m[0, 1; 0, 0]
private def diag : Matrix Int 2 2 := #m[2, 0; 0, 3]
private def profileEx : Matrix Int 3 3 := #m[0, 1, 0; 0, 2, 0; 1, 0, 0]
private def wide : Matrix Int 3 4 := #m[1, 2, 3, 4; 2, 4, 6, 8; 1, 0, 1, 0]
private def anti : Matrix Int 3 3 := #m[0, 0, 1; 0, 1, 0; 1, 0, 0]
private def zero34 : Matrix Int 3 4 := 0

#guard rank stop = 1
#guard (rankProfile stop).rows.toList = [0]
#guard (rankProfile stop).cols.toList = [1]
#guard (rowReduceFF diag).denom = 6
#guard (rowReduceFF diag).matrix = #m[6, 0; 0, 6]
#guard (rankProfile profileEx).rows.toList = [2, 0]
#guard (rankProfile profileEx).cols.toList = [0, 1]
#guard rank wide = 2
#guard (rowReduceFF wide).denom = -2
#guard rank anti = 3
#guard (rankCert anti).denom = 1
#guard rank zero34 = 0
#guard (rowReduceFF zero34).denom = 1
#guard rank (0 : Matrix Int 0 0) = 0
#guard rank (0 : Matrix Int 0 5) = 0
#guard rank (0 : Matrix Int 5 0) = 0
#guard rank #m[(-3 : Int)] = 1
#guard (rankCert #m[(-3 : Int)]).denom = -3
#guard (rankCert #m[(-3 : Int)]).adj.rows.toList.map (·.toList) = [[1]]

/-! Every produced certificate checks. -/

#guard checkRank stop (rankCert stop)
#guard checkRank diag (rankCert diag)
#guard checkRank profileEx (rankCert profileEx)
#guard checkRank wide (rankCert wide)
#guard checkRank anti (rankCert anti)
#guard checkRank zero34 (rankCert zero34)
#guard checkRank (0 : Matrix Int 0 3) (rankCert 0)
#guard checkRank (0 : Matrix Int 3 0) (rankCert 0)
#guard (certifyRank wide).isSome

/-! Mutated certificates are rejected. -/

private def wideCert : RankCert Int 3 4 := rankCert wide

#guard checkRank wide ⟨1, #v[0], #v[0], 1, #m[(1 : Int)]⟩ = false
#guard checkRank wide { wideCert with denom := 0 } = false
#guard checkRank wide { wideCert with adj := Matrix.ofFn fun i j =>
  if i.val = 0 ∧ j.val = 0 then wideCert.adj[(i, j)] + 1 else wideCert.adj[(i, j)] } = false
-- the producer's certificate has `rows = [0, 2]`, `cols = [0, 1]`, `denom = -2`
#guard checkRank wide ⟨2, #v[0, 2], #v[0, 1], -2, #m[0, -2; -1, 1]⟩ = true
#guard checkRank wide ⟨2, #v[0, 0], #v[0, 1], -2, #m[0, -2; -1, 1]⟩ = false
#guard checkRank wide ⟨3, #v[0, 1, 2], #v[0, 1, 2], 1, Matrix.identity 3⟩ = false

/-! The kernel replays the checker on a closed certificate, and the soundness
theorem applies to it: a certificate of rank `0` certifies the zero matrix. -/

example : checkRank wide (rankCert wide) = true := by decide +kernel

example : zero34 = 0 :=
  RankCert.matrix_eq_zero (A := zero34) (c := rankCert zero34) (by decide +kernel) rfl

/-! Rationals. -/

private def ratA : Matrix Rat 2 3 := #m[(1 : Rat) / 2, 1 / 3, 1; 1 / 5, 1, 2]

#guard rankWith Hex.exactDiv ratA = 2
#guard checkRank ratA (rankCertWith Hex.exactDiv ratA)
#guard rankWith Hex.exactDiv (#m[(1 : Rat) / 2, 1 / 3; 1 / 4, 1 / 6]) = 1

/-! Residues: `[[1, 1], [1, 3]]` has rank `1` over `GF(2)` and rank `2` over
`GF(5)`. -/

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

private def zm (p : Nat) [ZMod64.Bounds p] (x : Nat) : ZMod64 p := ZMod64.ofNat p x

private def mod2 : Matrix (ZMod64 2) 2 2 := #m[zm 2 1, zm 2 1; zm 2 1, zm 2 3]
private def mod5 : Matrix (ZMod64 5) 2 2 := #m[zm 5 1, zm 5 1; zm 5 1, zm 5 3]

#guard rankWith Hex.exactDiv mod2 = 1
#guard rankWith Hex.exactDiv mod5 = 2
#guard checkRank mod2 (rankCertWith Hex.exactDiv mod2)
#guard checkRank mod5 (rankCertWith Hex.exactDiv mod5)

/-! Dense polynomials. The second pivot of `[[x, 2], [3, x]]` is `x² - 6`,
so the elimination divides by a nonconstant polynomial. -/

private def zpoly (cs : List Int) : ZPoly := DensePoly.ofList cs
private def qpoly (cs : List Rat) : DensePoly Rat := DensePoly.ofList cs
private def fpoly (cs : List Nat) : DensePoly (ZMod64 5) := DensePoly.ofList (cs.map (zm 5))

private def zpA : Matrix ZPoly 2 2 := #m[zpoly [0, 1], zpoly [2]; zpoly [3], zpoly [0, 1]]
private def zpSing : Matrix ZPoly 2 2 := #m[zpoly [0, 1], zpoly [0, 0, 1]; zpoly [1], zpoly [0, 1]]
private def qpA : Matrix (DensePoly Rat) 2 2 :=
  #m[qpoly [0, 1], qpoly [1 / 2]; qpoly [1 / 3], qpoly [0, 1]]
private def frob : Matrix (DensePoly (ZMod64 5)) 1 1 := #m[fpoly [0, 4, 0, 0, 0, 1]]

#guard rankWith Hex.exactDiv zpA = 2
#guard (rowReduceWith Hex.exactDiv zpA).denom = zpoly [-6, 0, 1]
#guard rankWith Hex.exactDiv zpSing = 1
#guard checkRank zpA (rankCertWith Hex.exactDiv zpA)
#guard checkRank zpSing (rankCertWith Hex.exactDiv zpSing)
#guard rankWith Hex.exactDiv qpA = 2
#guard checkRank qpA (rankCertWith Hex.exactDiv qpA)
-- `X^5 - X` has generic rank `1` over `GF(5)[X]` although it vanishes at every
-- point of `GF(5)`: the generic rank is not a specialised rank.
#guard rankWith Hex.exactDiv frob = 1
#guard checkRank frob (rankCertWith Hex.exactDiv frob)

/-! Multivariate polynomials. -/

private def x2 : MvPoly 2 Int Mono.lex := MvPoly.X 0
private def y2 : MvPoly 2 Int Mono.lex := MvPoly.X 1
private def mvFull : Matrix (MvPoly 2 Int Mono.lex) 2 2 := #m[x2, y2; y2, x2]
private def mvSing : Matrix (MvPoly 2 Int Mono.lex) 2 2 := #m[x2, y2; x2 * y2, y2 * y2]
private def v6 : Fin 6 → MvPoly 6 Int Mono.lex := fun i => MvPoly.X i
private def generic23 : Matrix (MvPoly 6 Int Mono.lex) 2 3 :=
  Matrix.ofFn fun i j => v6 ⟨i.val * 3 + j.val, by omega⟩

#guard rankWith Hex.exactDiv mvFull = 2
#guard rankWith Hex.exactDiv mvSing = 1
#guard rankWith Hex.exactDiv generic23 = 2
#guard checkRank mvFull (rankCertWith Hex.exactDiv mvFull)
#guard checkRank mvSing (rankCertWith Hex.exactDiv mvSing)
#guard checkRank generic23 (rankCertWith Hex.exactDiv generic23)
-- `denom` is one of the classical `2 × 2` minors: `x₀ x₄ - x₁ x₃`.
#guard (rankCertWith Hex.exactDiv generic23).denom = v6 0 * v6 4 - v6 1 * v6 3


/-! # The kernel certificate

`rankWitness` on the `3 × 4` example, its witness replayed by `checkRankList`
in the kernel, and mutated witnesses rejected. -/

def kernelEx : Matrix Int 3 4 := #m[1, 2, 3, 4; 2, 4, 6, 8; 1, 0, 1, 0]

/-- The witness `rankWitness kernelEx` produces. -/
def kernelWitness : RankWitness := { rank := 2, modulus := 2147483647, rows := [0, 2], cols := [0, 1], vt := [[0, 1073741824], [1, 1073741823]], denom := -2, z := [[-4, 0]] }

#guard rankWitness kernelEx = some kernelWitness
#guard (rankWitness (0 : Matrix Int 0 0)).map (·.rank) = some 0
#guard (rankWitness (0 : Matrix Int 2 3)).map (·.rank) = some 0

example : checkRankList 3 4 (toLists kernelEx) kernelWitness = true := by decide +kernel
example : checkRankList 3 4 (toLists kernelEx) { kernelWitness with denom := 0 } = false := by
  decide +kernel
example : checkRankList 3 4 (toLists kernelEx) { kernelWitness with rank := 3 } = false := by
  decide +kernel
example : checkRankList 3 4 (toLists kernelEx) { kernelWitness with rows := [0, 1] } = false := by
  decide +kernel
example : checkRankList 3 4 (toLists kernelEx)
    { kernelWitness with vt := kernelWitness.vt.map fun c => c.map (· + 1) } = false := by
  decide +kernel
example : checkRankList 3 4 (toLists kernelEx)
    { kernelWitness with z := kernelWitness.z.map fun r => r.map (· + 1) } = false := by
  decide +kernel

end Hex.RankConformance
