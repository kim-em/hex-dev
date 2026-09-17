/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexKronecker.Check

@[expose] public section

namespace Hex.Kronecker.Kernel

/-- Native counterpart of the primitive integer equality recursor. -/
def intEqImpl (a b : Int) : Bool := a == b

@[csimp] theorem intEq_eq_impl : Int.beq' = intEqImpl := by
  funext a b
  exact Int.beq'_eq_beq a b

def degreesEqImpl : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && degreesEqImpl as bs
  | _, _ => false

noncomputable def degreesEq (as : List Nat) : List Nat → Bool :=
  List.rec (fun bs => match bs with | [] => true | _ :: _ => false)
    (fun a _ rest bs => match bs with | [] => false | b :: bs => Nat.beq a b && rest bs) as

@[csimp] theorem degreesEq_eq_impl : degreesEq = degreesEqImpl := by
  funext as bs
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih => cases bs <;> simp_all [degreesEq, degreesEqImpl]

/-- Validate a supplied root plan before evaluating the packed identity. -/
def exprEqPlan (k : Nat) (lhs rhs : Expr) (ds : List Nat) (w : Nat) : Bool :=
  lhs.wellFormed k && rhs.wellFormed k &&
    degreesEq ds (maxDegrees (lhs.degrees k) (rhs.degrees k)) &&
    Nat.blt (Nat.mul 2 (Nat.add lhs.height rhs.height)) (Nat.pow 2 w) &&
    Int.beq' (evalKron (Nat.pow 2 w) (makeStrides 1 ds) lhs)
      (evalKron (Nat.pow 2 w) (makeStrides 1 ds) rhs)

/-- Replay only the mathematical certificate. Resource limits belong to preflight. -/
def exprEq (k : Nat) (lhs rhs : Expr) : Bool :=
  lhs.wellFormed k && rhs.wellFormed k &&
    let degrees := maxDegrees (lhs.degrees k) (rhs.degrees k)
    let strides := makeStrides 1 degrees
    let base := 2 ^ ((lhs.height + rhs.height).log2 + 2)
    Int.beq' (evalKron base strides lhs) (evalKron base strides rhs)

/-- Exact root bounds; no resource report or saturation is evaluated here. -/
def add (a b : Bounds) : Bounds :=
  ⟨maxDegrees a.degrees b.degrees, a.height + b.height⟩

def mul (a b : Bounds) : Bounds :=
  ⟨addDegrees a.degrees b.degrees, a.height * b.height⟩

noncomputable def terms (k : Nat) (ts : Hex.MvPoly.Kernel.PolyList Int) : Bounds :=
  List.rec (Bounds.zero k) (fun (e, c) _ rest => add ⟨e, c.natAbs⟩ rest) ts

@[simp] theorem terms_nil (k : Nat) : terms k [] = Bounds.zero k := rfl
@[simp] theorem terms_cons (k : Nat) (e : List Nat) (c : Int)
    (ts : Hex.MvPoly.Kernel.PolyList Int) :
    terms k ((e,c)::ts) = add ⟨e, c.natAbs⟩ (terms k ts) := rfl

def termsImpl (k : Nat) : Hex.MvPoly.Kernel.PolyList Int → Bounds
  | [] => Bounds.zero k
  | (e, c) :: ts => add ⟨e, c.natAbs⟩ (termsImpl k ts)

@[csimp] theorem terms_eq_impl : terms = termsImpl := by
  funext k ts
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t; simp only [terms_cons, termsImpl, ih]

/-- Only the fields consumed by evaluation. The caller supplies outer packing
widths, whose side conditions `dotValid` checks on the actual packed values. -/
def plan (b : Bounds) (innerBits slotBits : Nat := 0) : SizeBound :=
  { degrees := b.degrees, strides := makeStrides 1 b.degrees
    digitBits := b.height.log2 + 2, coefficientBound := b.height
    digits := 0, packedBits := 0, innerBits := innerBits, outerSlotBits? := some slotBits }

def termsEq (k : Nat) (lhs rhs : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  termShape k lhs && termShape k rhs &&
    let s := plan (add (terms k lhs) (terms k rhs))
    Int.beq' (packTerms (2 ^ s.digitBits) s.strides lhs) (packTerms (2 ^ s.digitBits) s.strides rhs)

def exprEqMod (k p : Nat) (lhs rhs : Expr) (q : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  !Nat.beq p 0 && lhs.wellFormed k && rhs.wellFormed k &&
    lhs.residues p && rhs.residues p && Hex.MvPoly.Kernel.isCanonical k q &&
    let s := plan (add (add ⟨lhs.degrees k, lhs.height⟩ ⟨rhs.degrees k, rhs.height⟩)
      (mul ⟨zeroDegrees k, p⟩ (terms k q)))
    Int.beq' (Int.sub (evalKron (2 ^ s.digitBits) s.strides lhs) (evalKron (2 ^ s.digitBits) s.strides rhs))
      (Int.mul (p : Int) (packTerms (2 ^ s.digitBits) s.strides q))

def termsEqMod (k p : Nat) (lhs rhs q : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  !Nat.beq p 0 && termShape k lhs && termShape k rhs &&
    termResidues p lhs && termResidues p rhs && Hex.MvPoly.Kernel.isCanonical k q &&
    let s := plan (add (add (terms k lhs) (terms k rhs))
      (mul ⟨zeroDegrees k, p⟩ (terms k q)))
    Int.beq' (Int.sub (packTerms (2 ^ s.digitBits) s.strides lhs) (packTerms (2 ^ s.digitBits) s.strides rhs))
      (Int.mul (p : Int) (packTerms (2 ^ s.digitBits) s.strides q))

def matrix (k : Nat) (a : TermMatrix) : List (List Bounds) := a.map (List.map (terms k))

def dot (k : Nat) : List Bounds → List Bounds → Bounds
  | a :: as, b :: bs => add (mul a b) (dot k as bs)
  | _, _ => Bounds.zero k

def product (k : Nat) (cols rows : List (List Bounds)) : List (List Bounds) :=
  rows.map (fun row => cols.map (dot k row))

def common (k : Nat) : List Bounds → List Bounds → Bounds
  | a :: as, b :: bs => (add a b).sup (common k as bs)
  | _, _ => Bounds.zero k

def difference : List Bounds → List Bounds → List Bounds
  | a :: as, b :: bs => add a b :: difference as bs
  | _, _ => []

def mulTerms (mode : MulMode) (k n r m : Nat) (a b c : TermMatrix)
    (innerBits slotBits : Nat := 0) : Bool :=
  (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c) &&
    let products := product k (boundColumns k m (matrix k b)) (matrix k a)
    let s := plan (common k products.flatten (matrix k c).flatten) innerBits slotBits
    checkRows mode s r (Hex.Matrix.Packed.columns m (packMatrix s b)) (packMatrix s a) (packMatrix s c)

def mulTermsMod (mode : MulMode) (k n r m p : Nat) (a b c q : TermMatrix)
    (innerBits slotBits : Nat := 0) : Bool :=
  !Nat.beq p 0 &&
    (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c && matrixShape k n m q) &&
    (a.all (fun row => row.all (termResidues p)) &&
      b.all (fun row => row.all (termResidues p)) && c.all (fun row => row.all (termResidues p))) &&
    q.all (fun row => row.all (Hex.MvPoly.Kernel.isCanonical k)) &&
    let products := product k (boundColumns k m (matrix k b)) (matrix k a)
    let differences := difference products.flatten (matrix k c).flatten
    let scaled := (matrix k q).flatten.map (mul ⟨zeroDegrees k, p⟩)
    let s := plan (common k differences scaled) innerBits slotBits
    checkRowsMod mode s r p (Hex.Matrix.Packed.columns m (packMatrix s b))
      (packMatrix s a) (packMatrix s c) (packMatrix s q)

end Hex.Kronecker.Kernel
