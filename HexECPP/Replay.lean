/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Affine
public import HexArith.Montgomery.Context

public section

/-!
# Deterministic scalar replay

The caller supplies only inverse witnesses. The scalar is the child subject;
the bit schedule is computed from `HexArith.bitLength` and `Nat.testBit`.
-/

namespace Hex.ECPP

/-- Replay the remaining `bits` of `q`, from high index to low index. -/
@[expose]
def replayBits (n a b q : Nat) (Q : Point) :
    (bits : Nat) → Point → List Nat → Option (Point × List Nat)
  | 0, R, inverses => some (R, inverses)
  | bits + 1, R, inverses => do
      let (D, inverses) ← checkedAdd? n a b R R inverses
      let (S, inverses) ←
        if q.testBit bits then checkedAdd? n a b D Q inverses
        else some (D, inverses)
      replayBits n a b q Q bits S inverses

/-- Execute exactly the bits of the child subject. -/
@[expose]
def replay (n a b q : Nat) (Q : Point) (inverses : List Nat) :
    Option (Point × List Nat) :=
  replayBits n a b q Q (HexArith.bitLength q) .infinity inverses

/-- Acceptance requires infinity and exhaustion of the entire transcript. -/
@[expose]
def replayDone (n a b q : Nat) (Q : Point) (inverses : List Nat) : Bool :=
  match replay n a b q Q inverses with
  | some (.infinity, []) => true
  | _ => false

/-- Every point returned by an accepted replay prefix is a canonical point
on the supplied curve. The induction follows the actual bit schedule. -/
theorem replayBits_facts {n a b q : Nat} (Q : Point) :
    ∀ bits R S ws rest,
      R.canonical n = true → R.onCurve n a b = true →
      replayBits n a b q Q bits R ws = some (S, rest) →
      S.canonical n = true ∧ S.onCurve n a b = true
  | 0, R, S, ws, rest, hcan, hcurve, h => by
      simp only [replayBits, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hcan, hcurve⟩
  | bits + 1, R, S, ws, rest, _, _, h => by
      cases hD : checkedAdd? n a b R R ws with
      | none => simp [replayBits, hD] at h
      | some pair =>
          rcases pair with ⟨D, ws₁⟩
          have hDf := checkedAdd_facts hD
          cases hbit : q.testBit bits with
          | false =>
              have hrec : replayBits n a b q Q bits D ws₁ =
                  some (S, rest) := by
                simpa [replayBits, hD, hbit] using h
              exact replayBits_facts Q bits D S ws₁ rest hDf.2.1 hDf.2.2 hrec
          | true =>
              cases hT : checkedAdd? n a b D Q ws₁ with
              | none => simp [replayBits, hD, hbit, hT] at h
              | some pair =>
                  rcases pair with ⟨T, ws₂⟩
                  have hTf := checkedAdd_facts hT
                  have hrec : replayBits n a b q Q bits T ws₂ =
                      some (S, rest) := by
                    simpa [replayBits, hD, hbit, hT] using h
                  exact replayBits_facts Q bits T S ws₂ rest
                    hTf.2.1 hTf.2.2 hrec

/-- A successful scalar replay returns canonical coordinates satisfying the curve equation. -/
theorem replay_facts {n a b q : Nat} {Q S : Point} {ws rest : List Nat}
    (h : replay n a b q Q ws = some (S, rest)) :
    S.canonical n = true ∧ S.onCurve n a b = true := by
  exact replayBits_facts Q (HexArith.bitLength q) .infinity S ws rest
    (by rfl) (by rfl) h

/-- Scalar acceptance means infinity with no unused inverse witnesses. -/
theorem replayDone_eq_true_iff {n a b q : Nat} {Q : Point}
    {inverses : List Nat} :
    replayDone n a b q Q inverses = true ↔
      replay n a b q Q inverses = some (.infinity, []) := by
  unfold replayDone
  cases h : replay n a b q Q inverses with
  | none => simp
  | some pair =>
    rcases pair with ⟨P, ws⟩
    cases P <;> cases ws <;> simp

/-- The next binary digit extends the truncated scalar by its positional value. -/
theorem bit_mod_succ (q k : Nat) :
    q % 2 ^ (k + 1) =
      q % 2 ^ k + (q.testBit k).toNat * 2 ^ k := by
  rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]

/-- The exact strict integer ECPP size bound. -/
@[expose]
def sizeBound (n q : Nat) : Bool :=
  let r := q - 1
  let r2 := r * r
  if n < r2 then
    let c := r2 - n
    16 * n * q < c * c
  else false

/-- Acceptance implies positivity of the difference before natural subtraction. -/
theorem sizeBound_first {n q : Nat} (h : sizeBound n q = true) :
    n < (q - 1) * (q - 1) := by
  by_cases hh : n < (q - 1) * (q - 1)
  · exact hh
  · simp [sizeBound, hh] at h

/-- Acceptance implies the second strict integer ECPP inequality. -/
theorem sizeBound_second {n q : Nat} (h : sizeBound n q = true) :
    16 * n * q <
      (((q - 1) * (q - 1) - n) * ((q - 1) * (q - 1) - n)) := by
  have hh := sizeBound_first h
  simpa [sizeBound, hh] using h

/-- Both strict inequalities, including the guard before subtraction, exactly
characterize arithmetic size acceptance. -/
theorem sizeBound_eq_true_iff {n q : Nat} :
    sizeBound n q = true ↔ n < (q - 1) * (q - 1) ∧
      16 * n * q < ((q - 1) * (q - 1) - n) ^ 2 := by
  by_cases h : n < (q - 1) * (q - 1) <;> simp [sizeBound, h, Nat.pow_two]

end Hex.ECPP
