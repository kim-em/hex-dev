/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
Deterministic, seedable randomness for Las Vegas search, per the
hex-finite-field SPEC's "Randomness" section (which sites `Hex.Rand` here in
hex-basic: it has no dependencies and consumers in several subtrees).

The generator is splitmix64. Its contract is executable and testable — range
correctness (`Rand.nat_lt`), deterministic replay, explicit state
advancement, rejection sampling with no modulo reduction of an incomplete
interval, and bounded termination — and deliberately not a mathematical
uniformity or independence claim: a 64-bit-state generator has at most `2^64`
streams and cannot induce a uniform draw on an arbitrary larger bound.
Probability analyses in consumer SPECs are carried out against an ideal
sampler and never transferred to this concrete generator.

The discipline for consumers: every randomised function takes `Rand` as an
explicit argument and returns the advanced state (no monad, no `IO`, no
global generator); randomness affects how long a search runs, never what it
returns; fuel is explicit, and exhaustion is a documented outcome carrying
the advanced state, never a wrong answer or an unbounded loop.
-/

namespace Hex

/-- A splitmix64 state. Deterministic, seedable, and reproducible across runs
and platforms; this is a source of arbitrary values for Las Vegas search, not
a cryptographic generator, and nothing in the tree may treat it as one. -/
structure Rand where
  /-- The 64-bit generator state. -/
  state : UInt64
deriving Repr, DecidableEq

/-- Advance the splitmix64 state and produce one 64-bit output. -/
def Rand.next (r : Rand) : UInt64 × Rand :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Why a bounded draw failed. -/
inductive RandError where
  /-- The requested bound was `0`, so no value below it exists. -/
  | zeroBound
  /-- Rejection sampling ran out of fuel; the attempt count and the advanced
  state are returned so the caller can resume rather than replay a failed
  stream. -/
  | exhausted (attempts : Nat) (rand : Rand)
deriving Repr

/-- Concatenate `w` fresh 64-bit words into one natural number below
`2 ^ (64 * w)`. -/
def Rand.words (r : Rand) : Nat → Nat × Rand
  | 0 => (0, r)
  | w + 1 =>
      let (x, r') := r.next
      let (rest, r'') := Rand.words r' w
      (rest <<< 64 ||| x.toNat, r'')

private def Rand.natGo (bound limit w : Nat) :
    Nat → Nat → Rand → Except RandError (Nat × Rand)
  | 0, attempts, r => .error (.exhausted attempts r)
  | fuel + 1, attempts, r =>
      let (c, r') := Rand.words r w
      if c < limit then .ok (c % bound, r')
      else Rand.natGo bound limit w fuel (attempts + 1) r'

/-- Draw a natural number below `bound` by rejection sampling: form a
candidate from enough 64-bit words and reject the incomplete top interval
(rather than folding it in with `next % bound`, which would add modulo
bias). `fuel` bounds the rejection retries, including the initial candidate;
`bound = 0` returns `zeroBound`. -/
def Rand.nat (r : Rand) (bound fuel : Nat) : Except RandError (Nat × Rand) :=
  if bound = 0 then .error .zeroBound
  else
    let w := bound.log2 / 64 + 1
    let t := 1 <<< (64 * w)
    Rand.natGo bound (t - t % bound) w fuel 0 r

/-- Construct the initial state from a seed. -/
def Rand.ofSeed (seed : Nat) : Rand := ⟨UInt64.ofNat seed⟩

private theorem Rand.natGo_lt {bound limit w : Nat} (hb : 0 < bound) :
    ∀ (fuel attempts : Nat) (r : Rand) {v : Nat} {r' : Rand},
      Rand.natGo bound limit w fuel attempts r = .ok (v, r') → v < bound := by
  intro fuel
  induction fuel with
  | zero =>
      intro attempts r v r' h
      simp [Rand.natGo] at h
  | succ fuel ih =>
      intro attempts r v r' h
      unfold Rand.natGo at h
      by_cases hc : (Rand.words r w).1 < limit
      · simp only [hc, if_pos] at h
        cases h
        exact Nat.mod_lt _ hb
      · simp only [hc, if_neg, not_false_iff] at h
        exact ih (attempts + 1) (Rand.words r w).2 h

/-- Range correctness: a successful bounded draw is below the bound. -/
theorem Rand.nat_lt {r : Rand} {bound fuel v : Nat} {r' : Rand}
    (h : Rand.nat r bound fuel = .ok (v, r')) : v < bound := by
  unfold Rand.nat at h
  by_cases hb : bound = 0
  · rw [if_pos hb] at h
    cases h
  · rw [if_neg hb] at h
    exact Rand.natGo_lt (Nat.pos_of_ne_zero hb) fuel 0 r h

/-! Regression coverage: the canonical splitmix64 known-answer values (the
seed-`0` first output is the reference vector from the original
implementation), deterministic replay, and bounded-draw behaviour on every
result shape. -/

#guard (Rand.ofSeed 0).next.1 = 0xe220a8397b1dcdaf
#guard (Rand.ofSeed 42).next.1 = 0xbdd732262feb6e95
#guard (Rand.ofSeed 42).next.2.next.1 = 0x28efe333b266f103
#guard (Rand.ofSeed 42).next.2.next.2.next.1 = 0x47526757130f9f52
#guard (Rand.ofSeed 7).next.1 = (Rand.ofSeed 7).next.1   -- replay
#guard (match (Rand.ofSeed 1).nat 10 8 with
        | .ok (v, _) => v < 10
        | .error _ => false)
#guard (match (Rand.ofSeed 1).nat 0 8 with
        | .error .zeroBound => true
        | _ => false)
#guard (match (Rand.ofSeed 1).nat 5 0 with
        | .error (.exhausted 0 _) => true
        | _ => false)
-- A bound above one word draws two words and still lands in range.
#guard (match (Rand.ofSeed 3).nat (2 ^ 80) 8 with
        | .ok (v, _) => v < 2 ^ 80
        | .error _ => false)

end Hex
