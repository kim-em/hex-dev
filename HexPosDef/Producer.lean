/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDef.Certificate
public import HexArith.ExactDiv
public import HexMatrix.Scaled
public import HexRowReduce.Solve

public section

/-! No-swap fraction-free elimination and independently checked classification. -/

namespace Hex.PosDef

namespace Producer

/-- Operations used only by native production, outside the arithmetic checker. -/
structure Arithmetic (R : Type) extends Lists.Arithmetic R where
  sub : R → R → R
  div : R → Int → R
  real : R → Option Int

def intArithmetic : Arithmetic Int :=
  { Lists.intArithmetic with
    sub := Int.sub
    div := HexArith.Int.exactDiv
    real := some }

def gaussianArithmetic : Arithmetic Gaussian :=
  { Lists.gaussianArithmetic with
    sub := fun a b => a - b
    div := fun a d => ⟨HexArith.Int.exactDiv a.re d, HexArith.Int.exactDiv a.im d⟩
    real := fun a => if a.im = 0 then some a.re else none }

/-- Both blocks retain the original matrix dimension. -/
structure State (R : Type) (n : Nat) where
  left : Hex.Matrix R n n
  right : Hex.Matrix R n n
  previous : Int

def initial (a : Arithmetic R) (B : Hex.Matrix R n n) : State R n :=
  ⟨B, Hex.Matrix.ofFn (fun i j => if i = j then a.one else a.zero), 1⟩

/-- One update uses the old left coefficient for both blocks. -/
def step (a : Arithmetic R) (s : State R n) (k : Fin n) (p : Int) : State R n :=
  let pivot := s.left[(k, k)]
  let update (block : Hex.Matrix R n n) := Hex.Matrix.ofFn fun i j =>
    if k.val < i.val then
      a.div (a.sub (a.mul pivot block[(i, j)]) (a.mul s.left[(i, k)] block[(k, j)])) s.previous
    else block[(i, j)]
  ⟨update s.left, update s.right, p⟩

/-- Stop at the first nonpositive real pivot; never divide by that pivot. -/
def loop (a : Arithmetic R) : Nat → Nat → State R n → Except Error (Certificate R)
  | 0, _, _ => .error .rejected
  | fuel + 1, k, s =>
    if hk : k < n then
      match a.real s.left[((⟨k, hk⟩ : Fin n), (⟨k, hk⟩ : Fin n))] with
      | none => .error .rejected
      | some p =>
        if p ≤ 0 then
          .ok (.negative (.nonpositive ((s.right.getRow ⟨k, hk⟩).toList.map a.conj)))
        else loop a fuel (k + 1) (step a s ⟨k, hk⟩ p)
    else
      .ok (.positive (.triangular ((List.finRange n).map fun i =>
        (s.right.getRow i).toList.take (i.val + 1))))

/-- Symmetry is checked before elimination. -/
def general (a : Arithmetic R) (B : Hex.Matrix R n n) : Except Error (Certificate R) :=
  match ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)).find?
      (fun (i, j) => !(a.eq B[(i, j)] (a.conj B[(j, i)]))) with
  | some (i, j) => .ok (.negative (.notHermitian i.val j.val))
  | none =>
    if (List.finRange n).all (fun i => (List.finRange n).all fun j =>
        if i = j then a.positive B[(i, i)] else a.eq B[(i, j)] a.zero) then
      let identity := (initial a B).right
      .ok (.positive (.triangular ((List.finRange n).map fun i =>
        (identity.getRow i).toList.take (i.val + 1))))
    else loop a (n + 1) 0 (initial a B)

/-- A producer result becomes public only after independent validation. -/
def validate (check : Certificate R → Bool) :
    Except Error (Certificate R) → Except Error (Certificate R)
  | .error e => .error e
  | .ok c => if check c then .ok c else .error .rejected

theorem validate_check (check : Certificate R → Bool)
    (candidate : Except Error (Certificate R)) (c : Certificate R)
    (h : validate check candidate = .ok c) : check c = true := by
  cases candidate with
  | error e => simp [validate] at h
  | ok c' =>
    simp only [validate] at h
    split at h
    next hc => cases h; exact hc
    next => contradiction

end Producer

namespace Int

/-- Dispatch to the checker for the returned polarity. -/
@[expose] def check (n : Nat) (rows : List (List Int)) : Certificate Int → Bool
  | .positive c => checkPositive n rows c
  | .negative c => checkNegative n rows c

/-- Solve exactly over the rationals, then clear denominators with a positive scale. -/
def vectorCandidate (B : Hex.Matrix Int n n) : Except Error (Certificate Int) := do
  let A := B.map (fun z => (z : Rat))
  match Hex.Matrix.solve A (Vector.replicate n 1) with
  | .error _ => .error (.unsupported "the positive-vector solve is inconsistent")
  | .ok (v, _) =>
    let scaled := Hex.Matrix.Lists.Scaled.encode v.toList
    let c : PositiveCert Int := .positiveVector scaled.nums
    if checkPositive n B.rowLists c then .ok (.positive c)
    else .error (.unsupported "the matrix has no accepted positive-vector certificate from the solve")

/-- Classify a square integer matrix. The general method is the default. -/
def certify (B : Hex.Matrix Int n n) (method : Method := .triangular) :
    Except Error (Certificate Int) :=
  Producer.validate (check n B.rowLists) (match method with
    | .triangular => Producer.general Producer.intArithmetic B
    | .positiveVector => vectorCandidate B)

/-- Successful return implies independent checker acceptance, without an elimination invariant. -/
theorem certify_check (B : Hex.Matrix Int n n) (method : Method) (c : Certificate Int)
    (h : certify B method = .ok c) : check n B.rowLists c = true :=
  Producer.validate_check _ _ c h

end Int

namespace Gaussian

/-- Dispatch to the Gaussian checker for the returned polarity. -/
@[expose] def check (n : Nat) (rows : List (List Gaussian)) : Certificate Gaussian → Bool
  | .positive c => checkPositive n rows c
  | .negative c => checkNegative n rows c

/-- Classify a square Gaussian-integer matrix by no-swap elimination. -/
def certify (B : Hex.Matrix Gaussian n n) : Except Error (Certificate Gaussian) :=
  Producer.validate (check n B.rowLists) (Producer.general Producer.gaussianArithmetic B)

/-- Gaussian successful-return self-validation is independent of exact-division correctness. -/
theorem certify_check (B : Hex.Matrix Gaussian n n) (c : Certificate Gaussian)
    (h : certify B = .ok c) : check n B.rowLists c = true :=
  Producer.validate_check _ _ c h

end Gaussian

end Hex.PosDef
