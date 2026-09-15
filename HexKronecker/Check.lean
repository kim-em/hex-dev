/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKronecker.MatrixSize

@[expose] public section

namespace Hex.Kronecker

/-- Check a tree identity after both budget comparisons and index validation. -/
def checkExprEq (budget : Budget) (k : Nat) (lhs rhs : Expr) : Bool :=
  match sizeExprEq budget k lhs rhs with
  | .error _ => false
  | .ok s => s.accepts budget &&
      (evalKron (2 ^ s.digitBits) s.strides lhs == evalKron (2 ^ s.digitBits) s.strides rhs)

/-- Check an identity directly on supplied integer supports. -/
def checkTermsEq (budget : Budget) (k : Nat) (lhs rhs : Hex.MvPoly.Kernel.PolyList Int) :
    Bool :=
  match sizeTermsEq budget k lhs rhs with
  | .error _ => false
  | .ok s => s.accepts budget &&
      (packTerms (2 ^ s.digitBits) s.strides lhs == packTerms (2 ^ s.digitBits) s.strides rhs)

def checkExprEqMod (budget : Budget) (k p : Nat) (lhs rhs : Expr)
    (q : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  match sizeExprEqMod budget k p lhs rhs q with
  | .error _ => false
  | .ok s => s.accepts budget &&
      (evalKron (2 ^ s.digitBits) s.strides lhs - evalKron (2 ^ s.digitBits) s.strides rhs ==
        (p : Int) * packTerms (2 ^ s.digitBits) s.strides q)

def checkTermsEqMod (budget : Budget) (k p : Nat)
    (lhs rhs q : Hex.MvPoly.Kernel.PolyList Int) : Bool :=
  match sizeTermsEqMod budget k p lhs rhs q with
  | .error _ => false
  | .ok s => s.accepts budget &&
      (packTerms (2 ^ s.digitBits) s.strides lhs - packTerms (2 ^ s.digitBits) s.strides rhs ==
        (p : Int) * packTerms (2 ^ s.digitBits) s.strides q)

def packMatrix (s : SizeBound) (a : TermMatrix) : List (List Int) :=
  a.map (fun row => row.map (packTerms (2 ^ s.digitBits) s.strides))

/-- The absolute-value limit used by the existing signed packed dot product. -/
def SizeBound.absLimit (s : SizeBound) : Nat := 2 ^ (s.innerBits - 1)

/-- Replay the established packed primitive's side conditions on the packed
inner values. The preflight already accounts for these operands. -/
def dotValid (mode : MulMode) (s : SizeBound) (r : Nat) (a b : List Int) : Bool :=
  match mode with
  | .plain => true
  | .signedPacked =>
      a.length == r && b.length == r &&
      Hex.Matrix.Packed.allAbsLt s.absLimit a && Hex.Matrix.Packed.allAbsLt s.absLimit b &&
      r * s.absLimit * s.absLimit < 2 ^ s.outerSlotBits?.getD 0

/-- Reuse the ordinary integer dot product or its existing signed packed form. -/
def dotValue (mode : MulMode) (s : SizeBound) (r : Nat) (a b : List Int) : Int :=
  match mode with
  | .plain => Hex.Matrix.Packed.dotInt a b
  | .signedPacked =>
      let w := s.outerSlotBits?.getD 0
      Hex.Matrix.Packed.dotIntPacked w r
        (Hex.Matrix.Packed.packSignedCut w r a) (Hex.Matrix.Packed.packSignedCol w r b)

def checkRow (mode : MulMode) (s : SizeBound) (r : Nat) (a : List Int) :
    List (List Int) → List Int → Bool
  | [], [] => true
  | col :: cols, c :: cs => dotValid mode s r a col &&
      dotValue mode s r a col == c && checkRow mode s r a cols cs
  | _, _ => false

def checkRows (mode : MulMode) (s : SizeBound) (r : Nat) (cols : List (List Int)) :
    List (List Int) → List (List Int) → Bool
  | [], [] => true
  | a :: as, c :: cs => checkRow mode s r a cols c && checkRows mode s r cols as cs
  | _, _ => false

def checkMulTerms (budget : Budget) (mode : MulMode := .plain) (k n r m : Nat)
    (a b c : TermMatrix) : Bool :=
  match sizeMulTerms budget mode k n r m a b c with
  | .error _ => false
  | .ok s => s.accepts budget && checkRows mode s r
      (Hex.Matrix.Packed.columns m (packMatrix s b)) (packMatrix s a) (packMatrix s c)

def checkRowMod (mode : MulMode) (s : SizeBound) (r p : Nat) (a : List Int) :
    List (List Int) → List Int → List Int → Bool
  | [], [], [] => true
  | col :: cols, c :: cs, q :: qs => dotValid mode s r a col &&
      dotValue mode s r a col - c == (p : Int) * q && checkRowMod mode s r p a cols cs qs
  | _, _, _ => false

def checkRowsMod (mode : MulMode) (s : SizeBound) (r p : Nat) (cols : List (List Int)) :
    List (List Int) → List (List Int) → List (List Int) → Bool
  | [], [], [] => true
  | a :: as, c :: cs, q :: qs => checkRowMod mode s r p a cols c q &&
      checkRowsMod mode s r p cols as cs qs
  | _, _, _ => false

def checkMulTermsMod (budget : Budget) (mode : MulMode := .plain) (k n r m p : Nat)
    (a b c q : TermMatrix) : Bool :=
  match sizeMulTermsMod budget mode k n r m p a b c q with
  | .error _ => false
  | .ok s => s.accepts budget && checkRowsMod mode s r p
      (Hex.Matrix.Packed.columns m (packMatrix s b)) (packMatrix s a) (packMatrix s c) (packMatrix s q)

end Hex.Kronecker
