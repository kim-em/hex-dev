/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.KernelResidue.Denote

public section

/-! Kernel replay over natural residues, checked across a module boundary. -/

namespace Hex.MvPoly.KernelResidueTests

abbrev PL := Kernel.PolyList Nat

@[expose] def listP : PL := [([1, 0], 1), ([0, 1], 1), ([0, 0], 1)]

/-- Dot product over canonical polynomial lists. -/
@[expose] def listDot : List PL → List PL → PL
  | a :: as, b :: bs => Kernel.addMod 5 (Kernel.mulMod 5 a b) (listDot as bs)
  | _, _ => []

/-- The first `n` columns of a row-list matrix. -/
@[expose] def listColumns : Nat → List (List PL) → List (List PL)
  | 0, _ => []
  | n + 1, rows =>
      rows.map (fun row => row.getD 0 []) ::
        listColumns n (rows.map (fun row => row.drop 1))

/-- Matrix multiplication used only by the closed certificate replay below. -/
@[expose] def listMatMul (columns : Nat) (a b : List (List PL)) :
    List (List PL) :=
  let bs := listColumns columns b
  a.map fun row => bs.map (listDot row)

/-- Entrywise equality through the polynomial list equality checker. -/
@[expose] def listMatrixBeq : List (List PL) → List (List PL) → Bool
  | [], [] => true
  | a :: as, b :: bs =>
      (a.zip b).all (fun e => Kernel.beq e.1 e.2) &&
        Nat.beq a.length b.length && listMatrixBeq as bs
  | _, _ => false

@[expose] def listDiag4 (a : PL) : List (List PL) :=
  [[a, [], [], []], [[], a, [], []], [[], [], a, []], [[], [], [], a]]

/- The tridiagonal matrix has diagonal p = x + y + 1 and off-diagonal 1.
Its adjugate and determinant are independent residue literals modulo 5, so replay
checks real cross-term cancellation rather than repeating an expression. -/
@[expose] def listTri4 : List (List PL) :=
  [[listP, [([0, 0], 1)], [], []],
   [[([0, 0], 1)], listP, [([0, 0], 1)], []],
   [[], [([0, 0], 1)], listP, [([0, 0], 1)]],
   [[], [], [([0, 0], 1)], listP]]

@[expose] def listAdj4 : List (List PL) :=
  let a : PL :=
    [([3, 0], 1), ([2, 1], 3), ([2, 0], 3), ([1, 2], 3), ([1, 1], 1),
     ([1, 0], 1), ([0, 3], 1), ([0, 2], 3), ([0, 1], 1), ([0, 0], 4)]
  let b : PL :=
    [([2, 0], 4), ([1, 1], 3), ([1, 0], 3), ([0, 2], 4), ([0, 1], 3)]
  let c : PL :=
    [([3, 0], 1), ([2, 1], 3), ([2, 0], 3), ([1, 2], 3), ([1, 1], 1),
     ([1, 0], 2), ([0, 3], 1), ([0, 2], 3), ([0, 1], 2)]
  let d : PL :=
    [([2, 0], 4), ([1, 1], 3), ([1, 0], 3),
     ([0, 2], 4), ([0, 1], 3), ([0, 0], 4)]
  let p : PL := [([1, 0], 1), ([0, 1], 1), ([0, 0], 1)]
  let m : PL := [([0, 0], 4)]
  [[a, b, p, m], [b, c, d, p], [p, d, c, b], [m, p, b, a]]

@[expose] def listDet4 : PL :=
  [([4, 0], 1), ([3, 1], 4), ([3, 0], 4), ([2, 2], 1), ([2, 1], 2),
   ([2, 0], 3), ([1, 3], 4), ([1, 2], 2), ([1, 1], 1), ([1, 0], 3),
   ([0, 4], 1), ([0, 3], 4), ([0, 2], 3), ([0, 1], 3), ([0, 0], 4)]

example : listAdj4.all (fun row => row.all (Kernel.isCanonicalMod 5 2)) = true := by
  decide +kernel

example : listTri4.all (fun row => row.all (Kernel.isCanonicalMod 5 2)) = true := by
  decide +kernel

example : Kernel.isCanonicalMod 5 2 listDet4 = true := by
  decide +kernel

/-- A tridiagonal adjugate certificate modulo 5, using only natural-residue
polynomial operations during kernel replay. -/
theorem certificate :
    listMatrixBeq (listMatMul 4 listTri4 listAdj4) (listDiag4 listDet4) = true := by
  decide +kernel

example : listMatrixBeq (listMatMul 4 listAdj4 listTri4) (listDiag4 listDet4) = true := by
  decide +kernel

-- Reject a corrupted determinant and mismatched matrix dimensions.
example : listMatrixBeq (listMatMul 4 listTri4 listAdj4)
    (listDiag4 (Kernel.addMod 5 listDet4 [([0, 0], 1)])) = false := by
  decide +kernel

example : listMatrixBeq [[listP]] [[listP, []]] = false := by decide +kernel

-- The additive-identity probe imposes no ring law on unreduced naturals.
example : Kernel.isCanonicalMod 3 1 [([0], 3)] = false := by decide +kernel
example : Kernel.isCanonicalMod 3 1 [([0], 4)] = false := by decide +kernel
example : Kernel.isCanonicalMod 3 1 [([0], 2)] = true := by decide +kernel
example : Kernel.isCanonicalMod 3 1 [([0], 0)] = false := by decide +kernel
example : Kernel.isCanonicalMod 3 1 [([0, 0], 1)] = false := by decide +kernel
example : Kernel.isCanonicalMod 3 1 [([0], 1), ([1], 1)] = false := by decide +kernel
example : Kernel.isCanonicalMod 3 1 [([1], 1), ([1], 2)] = false := by decide +kernel

example : Kernel.addMod 3 [([0], 2)] [] = [([0], 2)] := by decide +kernel
example : Kernel.addMod 3 [([0], 2)] [([0], 2)] = [([0], 1)] := by decide +kernel
example : Kernel.isZero (Kernel.addMod 3 [([0], 2)] [([0], 1)]) = true := by
  decide +kernel
example : Kernel.negMod 3 [([0], 2)] = [([0], 1)] := by decide +kernel
example : Kernel.smulMod 3 7 [([0], 2)] = [([0], 2)] := by decide +kernel
example : Kernel.subMod 5 listP listP = [] := by decide +kernel

-- Composite moduli require zero-product filtering; primality is unnecessary.
example : Kernel.mulMod 4 [([1], 2)] [([1], 2)] = [] := by decide +kernel
example : Kernel.smulMod 4 2 [([1], 2)] = [] := by decide +kernel
example : Kernel.negMod 4 [([1], 2)] = [([1], 2)] := by decide +kernel
example : Kernel.isCanonicalMod 1 1 [([0], 1)] = false := by decide +kernel
example : Kernel.isCanonicalMod 1 1 [] = true := by decide +kernel

local instance : Hex.ZMod64.Bounds 5 := ⟨by decide, by decide⟩

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2)
    (Kernel.subMod 5 listP listP) = 0 := by
  have hp : Kernel.CanonicalMod 5 2 listP :=
    Kernel.isCanonicalMod_iff.mp (by decide +kernel)
  exact (Kernel.isZero_mod_iff 5 (Kernel.subMod_canonical 5 hp hp)).mp (by decide +kernel)

example (a : Hex.MvPoly 2 (Hex.ZMod64 5) Hex.Mono.grevlex) :
    Kernel.denoteMod 5 (Kernel.ofResidues 5 (Kernel.toList a)) = a :=
  Kernel.denoteMod_ofResidues 5 a

example : Kernel.isCanonicalMod 5 2 (Kernel.mulMod 5 listP listP) = true := by
  decide +kernel

example : Kernel.oneMod 5 2 = [([0, 0], 1)] := by decide +kernel
example : Kernel.oneMod 1 2 = [] := by decide +kernel
example : Kernel.isCanonicalMod 0 1 [] = true := by decide +kernel
example : Kernel.isCanonicalMod 0 1 [([0], 1)] = false := by decide +kernel

private theorem canonicalP : Kernel.CanonicalMod 5 2 listP :=
  Kernel.isCanonicalMod_iff.mp (by decide +kernel)

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) [] = 0 :=
  Kernel.denoteMod_nil 5

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (Kernel.oneMod 5 2) = 1 :=
  Kernel.denoteMod_oneMod 5

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2)
    (Kernel.addMod 5 listP listP) =
      Kernel.denoteMod 5 listP + Kernel.denoteMod 5 listP :=
  Kernel.denoteMod_addMod 5 canonicalP canonicalP

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2)
    (Kernel.mulMod 5 listP listP) =
      Kernel.denoteMod 5 listP * Kernel.denoteMod 5 listP :=
  Kernel.denoteMod_mulMod 5 canonicalP canonicalP

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2)
    (Kernel.subMod 5 listP listP) =
      Kernel.denoteMod 5 listP - Kernel.denoteMod 5 listP :=
  Kernel.denoteMod_subMod 5 canonicalP canonicalP

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2)
    (Kernel.negMod 5 listP) = -Kernel.denoteMod 5 listP :=
  Kernel.denoteMod_negMod 5 canonicalP

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2)
    (Kernel.smulMod 5 7 listP) = Hex.MvPoly.C (Hex.ZMod64.ofNat 5 7) *
      Kernel.denoteMod 5 listP :=
  Kernel.denoteMod_smulMod 5 7 canonicalP

-- Canonicality is also available beyond the executable carrier's word bound.
example : Kernel.CanonicalMod (2^32) 2
    (Kernel.mulMod (2^32) listP listP) :=
  Kernel.mulMod_canonical _
    (Kernel.isCanonicalMod_iff.mp (by decide +kernel))
    (Kernel.isCanonicalMod_iff.mp (by decide +kernel))

section Trivial
local instance : Hex.ZMod64.Bounds 1 := ⟨by decide, by decide⟩

example : Kernel.denoteMod 1 (cmp := Hex.Mono.lex) (n := 2) (Kernel.oneMod 1 2) = 1 :=
  Kernel.denoteMod_oneMod 1
end Trivial

/-- info: 'Hex.MvPoly.KernelResidueTests.certificate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms certificate

end Hex.MvPoly.KernelResidueTests
