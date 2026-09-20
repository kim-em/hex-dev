/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexKronecker.Kernel

@[expose] public section

/-! Mixed Kronecker certificates retain input trees and serialize only witnesses.
Resource preflight observes every tree subtree; kernel replay uses root bounds. -/

namespace Hex.Kronecker

abbrev TreeMatrix := List (List Expr)

def treeValid (k : Nat) (a : TreeMatrix) : Bool :=
  a.all (fun row => row.all (Expr.wellFormed k))

def treeShape (k n m : Nat) (a : TreeMatrix) : Bool :=
  a.length == n && a.all (fun row => row.length == m) && treeValid k a

def treeBounds (cap k : Nat) (a : TreeMatrix) : List (List Bounds) :=
  a.map (List.map (fun e => (e.analyze cap k []).1))

def treeObserved (cap k : Nat) (a : TreeMatrix) : List Bounds :=
  a.flatten.foldl (fun observed e => (e.analyze cap k observed).2) []

def evalTreeMatrix (s : SizeBound) (a : TreeMatrix) : List (List Int) :=
  a.map (List.map (evalKron (2 ^ s.digitBits) s.strides))

/-- Admission includes the trees' subexpressions, even when their roots cancel. -/
def sizeMulTree (budget : Budget) (mode : MulMode) (k n r m : Nat)
    (a : TermMatrix) (b : TreeMatrix) (c : TermMatrix) : Except SizeError SizeBound :=
  if !(matrixShape k n r a && treeShape k r m b && matrixShape k n m c) then
    .error .matrixShape
  else
    let cap := 2 ^ budget.maxPackedBits
    let ab := matrixBounds cap k a
    let bb := treeBounds cap k b
    let cb := matrixBounds cap k c
    let products := productBounds cap k (boundColumns k m bb) ab
    let common := commonBounds cap k products.flatten cb.flatten
    let observed := ab.flatten ++ treeObserved cap k b ++ cb.flatten ++ products.flatten
    .ok ((makeSize budget common observed).withMode budget mode r)

def sizeMulTreeMod (budget : Budget) (mode : MulMode) (k n r m p : Nat)
    (a : TermMatrix) (b : TreeMatrix) (c q : TermMatrix) : Except SizeError SizeBound :=
  if p == 0 then .error .modulus
  else if !(matrixShape k n r a && treeShape k r m b &&
      matrixShape k n m c && matrixShape k n m q) then .error .matrixShape
  else if !(a.all (fun row => row.all (termResidues p)) &&
      b.all (fun row => row.all (Expr.residues p)) &&
      c.all (fun row => row.all (termResidues p))) then .error .residue
  else if !(q.all (fun row => row.all (Hex.MvPoly.Kernel.isCanonical k))) then .error .quotient
  else
    let cap := 2 ^ budget.maxPackedBits
    let ab := matrixBounds cap k a
    let bb := treeBounds cap k b
    let cb := matrixBounds cap k c
    let qb := matrixBounds cap k q
    let products := productBounds cap k (boundColumns k m bb) ab
    let differences := differenceBounds cap products.flatten cb.flatten
    let scaled := qb.flatten.map ((Bounds.mk (zeroDegrees k) (min p cap)).mul cap)
    let common := commonBounds cap k differences scaled
    let observed := ab.flatten ++ treeObserved cap k b ++ cb.flatten ++ qb.flatten ++
      products.flatten ++ differences ++ scaled
    .ok ((makeSize budget common observed).withMode budget mode r)

def sizeTreeTermsEq (budget : Budget) (k : Nat) (lhs : Expr)
    (rhs : Hex.MvPoly.Kernel.PolyList Int) : Except SizeError SizeBound :=
  if !lhs.wellFormed k then .error .atomIndex
  else if !termShape k rhs then .error .termShape
  else
    let cap := 2 ^ budget.maxPackedBits
    let (l, observed) := lhs.analyze cap k []
    let r := termBounds cap k rhs
    .ok (makeSize budget (l.add cap r) (r :: observed))

def sizeTreeTermsEqMod (budget : Budget) (k p : Nat) (lhs : Expr)
    (rhs q : Hex.MvPoly.Kernel.PolyList Int) : Except SizeError SizeBound :=
  if p == 0 then .error .modulus
  else if !lhs.wellFormed k then .error .atomIndex
  else if !termShape k rhs then .error .termShape
  else if !(lhs.residues p && termResidues p rhs) then .error .residue
  else if !Hex.MvPoly.Kernel.isCanonical k q then .error .quotient
  else
    let cap := 2 ^ budget.maxPackedBits
    let (l, observed) := lhs.analyze cap k []
    let r := termBounds cap k rhs
    let quotient := termBounds cap k q
    let scaled := (Bounds.mk (zeroDegrees k) (min p cap)).mul cap quotient
    let difference := l.add cap r
    .ok (makeSize budget (difference.add cap scaled)
      (difference :: scaled :: quotient :: r :: observed))

namespace Kernel

def treeMatrix (k : Nat) (a : TreeMatrix) : List (List Bounds) :=
  a.map (List.map (fun e => ⟨e.degrees k, e.height⟩))

/-- The packing base is natural, so its powers use the kernel's native natural
arithmetic before the coefficient multiplication in the integers. -/
noncomputable def packNat (base : Nat) (ss : List Nat)
    (ts : Hex.MvPoly.Kernel.PolyList Int) : Int :=
  List.rec 0 (fun (e,c) _ rest =>
    Int.add (Int.mul c (Int.ofNat (Nat.pow base (code ss e)))) rest) ts

def packNatImpl (base : Nat) (ss : List Nat) : Hex.MvPoly.Kernel.PolyList Int → Int
  | [] => 0
  | (e,c) :: ts => Int.add (Int.mul c (Int.ofNat (Nat.pow base (code ss e)))) (packNatImpl base ss ts)

@[csimp] theorem packNat_eq_impl : packNat = packNatImpl := by
  funext base ss ts
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t; simp only [packNat, packNatImpl] at *; rw [ih]

/-- Pack witness rows using native natural powers. -/
def packRows (s : SizeBound) (a : TermMatrix) : List (List Int) :=
  a.map (List.map (packNat (2 ^ s.digitBits) s.strides))

/-- Only transform and result polynomials are packed from term lists. -/
def mulTree (mode : MulMode) (k n r m : Nat)
    (a : TermMatrix) (b : TreeMatrix) (c : TermMatrix)
    (innerBits slotBits : Nat := 0) : Bool :=
  (matrixShape k n r a && treeShape k r m b && matrixShape k n m c) &&
    let products := product k (boundColumns k m (treeMatrix k b)) (matrix k a)
    let s := plan (common k products.flatten (matrix k c).flatten) innerBits slotBits
    checkRows mode s r (Hex.Matrix.Packed.columns m (evalTreeMatrix s b))
      (packRows s a) (packRows s c)

def mulTreeMod (mode : MulMode) (k n r m p : Nat)
    (a : TermMatrix) (b : TreeMatrix) (c q : TermMatrix)
    (innerBits slotBits : Nat := 0) : Bool :=
  !Nat.beq p 0 &&
    (matrixShape k n r a && treeShape k r m b && matrixShape k n m c && matrixShape k n m q) &&
    (a.all (fun row => row.all (termResidues p)) &&
      b.all (fun row => row.all (Expr.residues p)) && c.all (fun row => row.all (termResidues p))) &&
    q.all (fun row => row.all (Hex.MvPoly.Kernel.isCanonical k)) &&
    let products := product k (boundColumns k m (treeMatrix k b)) (matrix k a)
    let differences := difference products.flatten (matrix k c).flatten
    let scaled := (matrix k q).flatten.map (mul ⟨zeroDegrees k, p⟩)
    let s := plan (common k differences scaled) innerBits slotBits
    checkRowsMod mode s r p (Hex.Matrix.Packed.columns m (evalTreeMatrix s b))
      (packRows s a) (packRows s c) (packRows s q)

def treeTermsEq (k : Nat) (lhs : Expr) (rhs : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  lhs.wellFormed k && termShape k rhs &&
    let s := plan (add ⟨lhs.degrees k, lhs.height⟩ (terms k rhs))
    Int.beq' (evalKron (2 ^ s.digitBits) s.strides lhs)
      (packNat (2 ^ s.digitBits) s.strides rhs)

def treeTermsEqMod (k p : Nat) (lhs : Expr) (rhs q : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  !Nat.beq p 0 && lhs.wellFormed k && termShape k rhs &&
    lhs.residues p && termResidues p rhs && Hex.MvPoly.Kernel.isCanonical k q &&
    let s := plan (add (add ⟨lhs.degrees k, lhs.height⟩ (terms k rhs))
      (mul ⟨zeroDegrees k, p⟩ (terms k q)))
    Int.beq' (Int.sub (evalKron (2 ^ s.digitBits) s.strides lhs)
      (packNat (2 ^ s.digitBits) s.strides rhs))
      (Int.mul (p : Int) (packNat (2 ^ s.digitBits) s.strides q))

end Kernel

/-- Programmatic forms enforce resource policy before any packed evaluation. -/
def checkMulTree (budget : Budget) (mode : MulMode) (k n r m : Nat)
    (a : TermMatrix) (b : TreeMatrix) (c : TermMatrix) : Bool :=
  match sizeMulTree budget mode k n r m a b c with
  | .error _ => false
  | .ok s => s.accepts budget && Kernel.mulTree mode k n r m a b c s.innerBits (s.outerSlotBits?.getD 0)

def checkMulTreeMod (budget : Budget) (mode : MulMode) (k n r m p : Nat)
    (a : TermMatrix) (b : TreeMatrix) (c q : TermMatrix) : Bool :=
  match sizeMulTreeMod budget mode k n r m p a b c q with
  | .error _ => false
  | .ok s => s.accepts budget && Kernel.mulTreeMod mode k n r m p a b c q s.innerBits (s.outerSlotBits?.getD 0)

def checkTreeTermsEq (budget : Budget) (k : Nat) (lhs : Expr)
    (rhs : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  match sizeTreeTermsEq budget k lhs rhs with
  | .error _ => false
  | .ok s => s.accepts budget && Kernel.treeTermsEq k lhs rhs

def checkTreeTermsEqMod (budget : Budget) (k p : Nat) (lhs : Expr)
    (rhs q : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  match sizeTreeTermsEqMod budget k p lhs rhs q with
  | .error _ => false
  | .ok s => s.accepts budget && Kernel.treeTermsEqMod k p lhs rhs q

end Hex.Kronecker
