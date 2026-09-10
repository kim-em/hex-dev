/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Spec.CanonSpec

public section

/-! Maximum and incumbent folds for specification keys. -/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Taking the maximum of specification keys is associative. -/
theorem keyMax_assoc (x y z : Key n) :
    keyMax (keyMax x y) z = keyMax x (keyMax y z) := by
  refine keyCmp_antisym ?_ ?_
  · rcases keyMax_mem x (keyMax y z) with hm | hm <;> rw [hm]
    · exact keyCmp_ge_trans (keyMax_not_lt_left _ z)
        (keyMax_not_lt_left x y)
    · rcases keyMax_mem y z with hm2 | hm2 <;> rw [hm2]
      · exact keyCmp_ge_trans (keyMax_not_lt_left _ z)
          (keyMax_not_lt_right x y)
      · exact keyMax_not_lt_right _ z
  · rcases keyMax_mem (keyMax x y) z with hm | hm <;> rw [hm]
    · rcases keyMax_mem x y with hm2 | hm2 <;> rw [hm2]
      · exact keyMax_not_lt_left x (keyMax y z)
      · exact keyCmp_ge_trans (keyMax_not_lt_right x _)
          (keyMax_not_lt_left y z)
    · exact keyCmp_ge_trans (keyMax_not_lt_right x _)
        (keyMax_not_lt_right y z)

theorem keysMax_keyMax : ∀ (l : List (Key n)) (b c : Key n),
    keysMax (keyMax b c) l = keyMax b (keysMax c l)
  | [], _, _ => rfl
  | c' :: l, b, c => by
    rw [keysMax, keysMax, keyMax_assoc]
    exact keysMax_keyMax l b (keyMax c c')

theorem foldl_incMax {f : Option (Key n) → Nat → Option (Key n)}
    {key : Nat → Key n} :
    ∀ (os : List Nat),
      (∀ (acc : Option (Key n)), ∀ o ∈ os,
        f acc o = some (incMax acc (key o))) →
      ∀ t : Key n, os.foldl f (some t) = some (keysMax t (os.map key))
  | [], _, _ => rfl
  | o :: os, h, t => by
    rw [List.foldl_cons, h (some t) o (List.mem_cons_self ..),
      List.map_cons, keysMax]
    exact foldl_incMax os
      (fun acc o' ho' => h acc o' (List.mem_cons_of_mem _ ho')) _

theorem foldl_incMax_cons {f : Option (Key n) → Nat → Option (Key n)}
    {key : Nat → Key n} {o : Nat} {os : List Nat}
    (h : ∀ (acc : Option (Key n)), ∀ x ∈ o :: os,
      f acc x = some (incMax acc (key x)))
    (tail0 : Option (Key n)) :
    (o :: os).foldl f tail0 =
      some (incMax tail0 (keysMax (key o) (os.map key))) := by
  rw [List.foldl_cons, h tail0 o (List.mem_cons_self ..)]
  have hrec := foldl_incMax os
    (fun acc x hx => h acc x (List.mem_cons_of_mem _ hx))
  rcases tail0 with _ | t
  · rw [show incMax none (key o) = key o from rfl, hrec]
    rfl
  · rw [show incMax (some t) (key o) = keyMax t (key o) from rfl, hrec,
      keysMax_keyMax]
    rfl

end Hex.GraphIso.Nauty
