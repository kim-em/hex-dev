/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.BoundedChildren

public section

namespace Hex.PermGroup.Search.Bounded

variable {G : Group n} {P : Predicate n} {budget : Budget}

/-- A leaf predicate is one constraint test. Its membership queries share the
sift allowance with coverage checks. Successful leaves are retained even if
certificate allocation subsequently exhausts its allowance. -/
@[expose] def leaf (C : Constraint G P) (Q : Tester P budget) (t : Node G)
    {S : Array (Perm n)} {words : Vector Program S.size} (hs : t.suffix = .leaf S words)
    (a : Accumulator G P) (m : Meter budget) : Result C t a budget :=
  match m.spend .refinements 1 with
  | .error failure => Result.stop C t a failure
  | .ok meter =>
    match Q t.rep.val meter with
    | .exhausted failure => Result.stop C t a failure
    | .ok value meter =>
      if hp : value.val = true then
        have ht : P.test t.rep.val = true := value.property.symm.trans hp
        match meter.sift a.group t.rep.val with
        | .exhausted failure => Result.stop C t a failure
        | .ok member meter =>
          if hm : member.val = true then
            Result.finish C t a a (fun _ hq => hq) (fun _ => .leaf) (by
              have he : a.group.contains t.rep.val = true := member.property.symm.trans hm
              simp only [checkTree, hs, he, Bool.or_true]) meter
          else
            Result.finish C t a (a.adjoin t.rep ht) (a.adjoin_grows t.rep ht) (fun _ => .leaf) (by
              simp only [checkTree, hs, ht, Bool.not_true, Bool.false_or]
              exact ((a.adjoin t.rep ht).group.contains_iff _).mpr (a.mem_adjoin t.rep ht)) meter
      else
        Result.finish C t a a (fun _ hq => hq) (fun _ => .leaf) (by
          have ht : P.test t.rep.val = false := value.property.symm.trans (Bool.eq_false_iff.mpr hp)
          simp only [checkTree, hs, ht, Bool.not_false, Bool.true_or]) meter

end Hex.PermGroup.Search.Bounded
