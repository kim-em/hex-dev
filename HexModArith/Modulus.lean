/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Prime

public section

/-!
Bundled word-sized moduli and the runtime prime supply for `hex-mod-arith`.

The structures in this module carry the dependent `ZMod64.Bounds` evidence
needed to instantiate modular arithmetic at a modulus selected at runtime.
-/
namespace Hex

namespace ZMod64

/-- A usable word-sized modulus together with the evidence required by
`ZMod64`. -/
structure Modulus where
  /-- The natural-number modulus. -/
  m : Nat
  /-- Positivity and word-size bounds for the modulus. -/
  [bounds : Bounds m]

/-- A usable word-sized modulus known to be prime. This is the data-carrying
counterpart of the `PrimeModulus` typeclass. -/
structure Prime extends Modulus where
  /-- Project-local primality evidence for the bundled modulus. -/
  prime : Hex.Nat.Prime m

/-- Scan downward through candidates, appending at most `remaining` primes to
`out`. The candidate decreases on every iteration, including rejected
composites, so the scan is fuelled by the finite interval below `candidate`. -/
private def primesBelow.go (remaining candidate : Nat)
    (hbound : candidate < 2 ^ 31) (out : Array Prime) :
    Array Prime :=
  if remaining = 0 || candidate < 2 then
    out
  else if hprime : Hex.Nat.isPrimeTrial candidate = true then
    have prime : Hex.Nat.Prime candidate := Hex.Nat.isPrimeTrial_isPrime hprime
    let bounds : Bounds candidate := { pPos := prime.pos, pLtR := hbound }
    let entry : Prime := { m := candidate, bounds, prime }
    primesBelow.go (remaining - 1) (candidate - 1) (by omega) (out.push entry)
  else
    primesBelow.go remaining (candidate - 1) (by omega) out
termination_by candidate
decreasing_by all_goals simp_all; omega

/-- Return at most the requested number of successive primes below `2^31`, in
descending order starting at `start`. Runtime trial division produces the
primality evidence stored in every result; candidates above the `ZMod64` bound
are skipped by clamping the start of the scan. -/
def primesBelow (start : Nat) : Nat → Array Prime
  | count =>
      primesBelow.go count (min start (2 ^ 31 - 1)) (by omega) #[]

private theorem primesBelow.go_prefix (remaining candidate : Nat)
    (hbound : candidate < 2 ^ 31) (out : Array Prime) :
    out.toList.IsPrefix (go remaining candidate hbound out).toList := by
  rw [go]
  split
  · exact List.prefix_refl _
  · split
    · exact List.IsPrefix.trans (by simp [List.IsPrefix]) (go_prefix _ _ _ _)
    · exact go_prefix _ _ _ _
termination_by candidate
decreasing_by all_goals simp_all; omega

private theorem primesBelow.go_sorted (remaining candidate : Nat)
    (hbound : candidate < 2 ^ 31) (out : Array Prime)
    (hs : out.toList.Pairwise (fun a b => b.m < a.m))
    (hb : ∀ q ∈ out, candidate < q.m) :
    (go remaining candidate hbound out).toList.Pairwise (fun a b => b.m < a.m) := by
  rw [go]
  split
  · exact hs
  · rename_i h
    have hpos : 0 < candidate := by simp only [Bool.or_eq_true, decide_eq_true_eq] at h; omega
    split
    · apply go_sorted
      · simp only [Array.toList_push, List.pairwise_append, List.pairwise_singleton,
          List.mem_singleton, true_and]
        exact ⟨hs, by intro a ha b hb'; subst b; exact hb a (by simpa using ha)⟩
      · intro q hq
        rcases Array.mem_push.mp hq with hq | rfl
        · have := hb q hq; omega
        · dsimp; omega
    · apply go_sorted _ _ _ _ hs
      intro q hq
      have := hb q hq
      omega
termination_by candidate

private theorem primesBelow.go_count (remaining candidate : Nat)
    (hbound : candidate < 2 ^ 31) (out : Array Prime) (hc : 2 ≤ candidate) :
    (go remaining candidate hbound out).size = out.size + remaining ∨
      ∃ q ∈ go remaining candidate hbound out, q.m = 2 := by
  rw [go]
  split
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    left
    have : remaining = 0 := by omega
    simp [this]
  · rename_i h
    have hr : 0 < remaining := by simp only [Bool.or_eq_true, decide_eq_true_eq] at h; omega
    split
    · rename_i hp
      dsimp only
      let entry : Prime := { m := candidate, bounds := { pPos := (Hex.Nat.isPrimeTrial_isPrime hp).pos, pLtR := hbound }, prime := Hex.Nat.isPrimeTrial_isPrime hp }
      by_cases hc' : 2 ≤ candidate - 1
      · rcases go_count (remaining - 1) (candidate - 1) _ (out.push entry) hc' with he | he
        · left
          rw [he, Array.size_push]
          omega
        · exact Or.inr he
      · right
        have hc2 : candidate = 2 := by omega
        refine ⟨entry, ?_, hc2⟩
        apply Array.mem_toList_iff.mp
        apply List.IsPrefix.subset (go_prefix _ _ _ _)
        simp [entry]
    · rename_i hp
      have hc' : 2 ≤ candidate - 1 := by
        by_cases hc2 : candidate = 2
        · subst candidate
          exact False.elim (hp (by decide))
        · omega
      exact go_count remaining (candidate - 1) _ out hc'
termination_by candidate

/-- The supply contains strictly decreasing, and hence distinct, moduli. -/
theorem primesBelow_sorted (start count : Nat) :
    (primesBelow start count).toList.Pairwise (fun a b => b.m < a.m) :=
  primesBelow.go_sorted _ _ _ _ (by simp) (by simp)

/-- A supply starting at least at two either fills its budget or includes two. -/
theorem primesBelow_count {start : Nat} (hs : 2 ≤ start) (count : Nat) :
    (primesBelow start count).size = count ∨
      ∃ q ∈ primesBelow start count, q.m = 2 := by
  simpa only [primesBelow, Array.size_empty, Nat.zero_add] using primesBelow.go_count count (min start (2 ^ 31 - 1)) (by omega) #[] (by omega)

#guard (primesBelow 11 4).map (fun p => p.m) == #[11, 7, 5, 3]

end ZMod64

end Hex
