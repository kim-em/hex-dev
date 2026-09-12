/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Key

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std
attribute [local instance] lexOrd

/-- Prefix a native subtree key by the codes of its frozen ancestors. -/
@[expose] def prefixKey (cs : List Nat) (key : Key n) : Key n :=
  { key with codes := cs ++ key.codes }

theorem prefixKey_nil (key : Key n) : prefixKey [] key = key := rfl

theorem prefixKey_append (cs ds : List Nat) (key : Key n) :
    prefixKey cs (prefixKey ds key) = prefixKey (cs ++ ds) key := by
  simp only [prefixKey, List.append_assoc]

/-- A common ancestor prefix leaves the complete native comparison unchanged. -/
theorem prefixKey_cmp (cs : List Nat) (a b : Key n) :
    Key.cmp (prefixKey cs a) (prefixKey cs b) = Key.cmp a b := by
  have hcodes : compare (cs ++ a.codes) (cs ++ b.codes) = compare a.codes b.codes := by
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simpa only [List.cons_append, List.compare_cons_cons, ReflCmp.compare_self,
        Ordering.then] using ih
  simp only [Key.cmp, prefixKey, hcodes]

theorem prefixKey_le (cs : List Nat) {a b : Key n} (h : Key.Le a b) :
    Key.Le (prefixKey cs a) (prefixKey cs b) := by
  simpa only [Key.Le, prefixKey_cmp] using h

theorem prefixKey_max (cs : List Nat) (a b : Key n) :
    prefixKey cs (Key.max a b) = Key.max (prefixKey cs a) (prefixKey cs b) := by
  unfold Key.max
  rw [prefixKey_cmp]
  split <;> rfl

end Hex.GraphIso.Nauty.Sparse
