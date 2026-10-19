/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import Lean
public section

namespace CharPolyBlockProbe

structure Step where
  block : List (List Int)
  column : List Int
  vectors : List (List Int)
  coefficients : List Int

@[expose] def dot : List Int → List Int → Int
  | a :: as, b :: bs => Int.add (Int.mul a b) (dot as bs)
  | _, _ => 0

@[expose] def eqList : List Int → List Int → Bool
  | a :: as, b :: bs => decide (a = b) && eqList as bs
  | [], [] => true
  | _, _ => false

@[expose] def eqRows : List (List Int) → List (List Int) → Bool
  | a :: as, b :: bs => eqList a b && eqRows as bs
  | [], [] => true
  | _, _ => false

@[expose] def mulVecCheck (w : List Int) : List (List Int) → List Int → Bool
  | r :: rs, x :: xs => decide (dot r w = x) && mulVecCheck w rs xs
  | [], [] => true
  | _, _ => false

@[expose] def tails : List (List Int) → List (List Int)
  | [] => []
  | [] :: rs => [] :: tails rs
  | (_ :: r) :: rs => r :: tails rs

@[expose] def heads : List (List Int) → List Int
  | [] => []
  | [] :: rs => 0 :: heads rs
  | (x :: _) :: rs => x :: heads rs

@[expose] def moments (B : List (List Int)) (r : List Int) :
    List Int → List Int → List (List Int) → Bool
  | [], _, [] => true
  | [t], w, [] => decide (Int.neg (dot r w) = t)
  | t :: ts@(_ :: _), w, v :: vs => decide (Int.neg (dot r w) = t) &&
      mulVecCheck w B v && moments B r ts v vs
  | _, _, _ => false

@[expose] def toeplitz (v : List Int) : List Int → List Int → List Int → Bool
  | [], _, [] => true
  | t :: ts, rev, q :: qs => decide (dot (t :: rev) v = q) &&
      toeplitz v ts (t :: rev) qs
  | _, _, _ => false

@[expose] def steps : List (List Int) → List Step → List Int → Bool
  | [], [], p => eqList p [1]
  | (a :: r) :: rs, s :: ss, p =>
      let B := s.block
      eqRows (tails rs) B && eqList p s.coefficients &&
      (match s.column with
        | one :: negA :: ts => decide (one = 1) && decide (Int.neg a = negA) &&
            Nat.beq ts.length rs.length && moments B r ts (heads rs) s.vectors
        | _ => false) &&
      let previous := match ss with
        | next :: _ => next.coefficients
        | [] => [1]
      toeplitz previous s.column [] s.coefficients && steps B ss previous
  | _, _, _ => false

@[expose] def rowsLen (n : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => Nat.beq r.length n && rowsLen n rs

@[expose] def check (n : Nat) (A : List (List Int)) (c : List Step) (p : List Int) :=
  Nat.beq A.length n && rowsLen n A && steps A c p

meta section

open Lean Meta Elab Tactic in
elab "check_block_kernel" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, check, _) := target.eq? | throwError "expected equality"
  let proof := mkAppN (mkConst ``of_decide_eq_true) #[target,
    ← synthInstance (← mkAppM ``Decidable #[target]),
    ← mkEqRefl (mkConst ``Bool.true)]
  let _ := check
  let proof ← withOptions (Lean.Elab.async.set · false) <| mkAuxTheorem target proof
  goal.assign proof
  replaceMainGoal []

end

end CharPolyBlockProbe
