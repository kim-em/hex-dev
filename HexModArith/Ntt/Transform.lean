/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.Butterfly

public section

/-!
Radix-two transforms over reusable `NttPlan` data.

The forward loop is decimation in frequency, matching Harvey's forward
butterfly, and interleaves the two recursive frequency classes to return the
ordinary coefficient order.  The inverse loop deinterleaves those classes and
uses the inverse butterfly in decimation-in-time order.  Raw representatives
remain redundant throughout each loop and are normalized only at the public
array boundaries.
-/

namespace Hex

namespace ZMod64

namespace NttPlan

/-- A transform plan always has positive length. -/
theorem length_pos {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) : 0 < n := by
  obtain ⟨k, rfl⟩ := plan.length_pow_two
  exact Nat.two_pow_pos k

/-- Recover the executable power-of-two exponent used by the transform loop. -/
theorem length_eq_pow_log2 {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) : n = 2 ^ n.log2 := by
  obtain ⟨k, rfl⟩ := plan.length_pow_two
  simp

/-- A valid transform length is strictly smaller than its prime modulus. -/
theorem length_lt_modulus {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) : n < p := by
  have hp2 : 2 ≤ p := (PrimeModulus.prime (p := p)).two_le
  have hnle : n ≤ p - 1 := Nat.le_of_dvd (by omega) plan.length_dvd
  omega

/-- The transform length is nonzero as a prime-field residue. -/
theorem length_ne_zero {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) : (n : ZMod64 p) ≠ 0 := by
  intro hzero
  have hp_dvd_n := (ZMod64.natCast_eq_zero_iff_dvd n).mp hzero
  have hp_le_n := Nat.le_of_dvd plan.length_pos hp_dvd_n
  exact (Nat.not_le_of_gt plan.length_lt_modulus) hp_le_n

/-- The stored inverse-length scale cancels the transform length. -/
theorem invLength_mul_length {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) : plan.invLength * (n : ZMod64 p) = 1 := by
  rw [plan.invLength_eq]
  exact ZMod64.inv_mul_eq_one_of_ne_zero plan.length_ne_zero

/-- Read a forward twiddle, wrapping the requested exponent into the plan. -/
def forwardTwiddle {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (i : Nat) : NttTwiddle p :=
  plan.forwardTwiddles[i % n]'(by
    rw [plan.forward_size]
    exact Nat.mod_lt _ plan.length_pos)

/-- Read an inverse twiddle, wrapping the requested exponent into the plan. -/
def inverseTwiddle {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (i : Nat) : NttTwiddle p :=
  plan.inverseTwiddles[i % n]'(by
    rw [plan.inverse_size]
    exact Nat.mod_lt _ plan.length_pos)

/-- A forward twiddle is the corresponding wrapped root power. -/
theorem forwardTwiddle_value {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (i : Nat) :
    (plan.forwardTwiddle i).value = plan.root ^ (i % n) := by
  exact plan.forward_value (i % n) (Nat.mod_lt _ plan.length_pos)

/-- An inverse twiddle is the corresponding wrapped inverse-root power. -/
theorem inverseTwiddle_value {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (i : Nat) :
    (plan.inverseTwiddle i).value = plan.invRoot ^ (i % n) := by
  exact plan.inverse_value (i % n) (Nat.mod_lt _ plan.length_pos)

/-- An exact-order transform root is nonzero. -/
theorem root_ne_zero {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) : plan.root ≠ 0 := by
  intro hzero
  have hpow := plan.root_order.pow_eq_one
  rw [hzero, ZMod64.zero_pow (Nat.ne_of_gt plan.length_pos)] at hpow
  exact ZMod64.one_ne_zero hpow.symm

/-- Matching inverse and forward root powers cancel. -/
theorem invRoot_pow_mul_root_pow {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (e : Nat) :
    plan.invRoot ^ e * plan.root ^ e = 1 := by
  rw [plan.invRoot_eq]
  have hinv : plan.root⁻¹ * plan.root = 1 :=
    ZMod64.inv_mul_eq_one_of_ne_zero plan.root_ne_zero
  induction e with
  | zero => simp
  | succ e ih =>
      rw [ZMod64.pow_succ, ZMod64.pow_succ]
      calc
        plan.root⁻¹ ^ e * plan.root⁻¹ * (plan.root ^ e * plan.root) =
            (plan.root⁻¹ ^ e * plan.root ^ e) *
              (plan.root⁻¹ * plan.root) := by grind
        _ = 1 := by rw [ih, hinv]; simp

end NttPlan

namespace Ntt

/-- Interleave two frequency classes.  Equal-length inputs produce the usual
even/odd merge; the trailing clauses make the helper total. -/
def interleave {α : Type u} : List α → List α → List α
  | [], right => right
  | left, [] => left
  | x :: xs, y :: ys => x :: y :: interleave xs ys

/-- Split a list into its even- and odd-indexed entries. -/
def deinterleave {α : Type u} : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
      let halves := deinterleave rest
      (x :: halves.1, y :: halves.2)

/-- Deinterleaving reverses an equal-length interleave. -/
theorem deinterleave_interleave {α : Type u} (left right : List α)
    (hlength : left.length = right.length) :
    deinterleave (interleave left right) = (left, right) := by
  induction left generalizing right with
  | nil =>
      have hnil : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          simp only [interleave, deinterleave]
          rw [ih ys htail]

/-- One forward DIF stage over two equal-sized halves. -/
def forwardStage {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (NttRaw2 p) → List (NttRaw2 p) →
      List (NttRaw2 p) × List (NttRaw2 p)
  | _, [], _ => ([], [])
  | _, _, [] => ([], [])
  | i, x :: xs, y :: ys =>
      let output := forwardButterfly (plan.forwardTwiddle (i * stride)) x y
      let rest := forwardStage plan stride (i + 1) xs ys
      (output.1 :: rest.1, output.2 :: rest.2)

/-- One inverse DIT stage over two equal-sized recursive results. -/
def inverseStage {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (NttRaw4 p) → List (NttRaw4 p) →
      List (NttRaw4 p) × List (NttRaw4 p)
  | _, [], _ => ([], [])
  | _, _, [] => ([], [])
  | i, x :: xs, y :: ys =>
      let output := inverseButterfly (plan.inverseTwiddle (i * stride)) x y
      let rest := inverseStage plan stride (i + 1) xs ys
      (output.1 :: rest.1, output.2 :: rest.2)

/-- Canonical-residue specification of one forward DIF stage. -/
def forwardStageSpec {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (ZMod64 p) → List (ZMod64 p) →
      List (ZMod64 p) × List (ZMod64 p)
  | _, [], _ => ([], [])
  | _, _, [] => ([], [])
  | i, x :: xs, y :: ys =>
      let twiddle := plan.root ^ ((i * stride) % n)
      let rest := forwardStageSpec plan stride (i + 1) xs ys
      ((x + y) :: rest.1, (twiddle * (x - y)) :: rest.2)

/-- Canonical-residue specification of one inverse DIT stage. -/
def inverseStageSpec {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (ZMod64 p) → List (ZMod64 p) →
      List (ZMod64 p) × List (ZMod64 p)
  | _, [], _ => ([], [])
  | _, _, [] => ([], [])
  | i, x :: xs, y :: ys =>
      let twiddle := plan.invRoot ^ ((i * stride) % n)
      let rest := inverseStageSpec plan stride (i + 1) xs ys
      ((x + twiddle * y) :: rest.1, (x - twiddle * y) :: rest.2)

/-- Normalizing a raw forward stage gives its residue-level specification. -/
theorem normalize_forwardStage {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat)
    (left right : List (NttRaw2 p)) :
    let raw := forwardStage plan stride i left right
    (raw.1.map NttRaw2.normalize, raw.2.map NttRaw2.normalize) =
      forwardStageSpec plan stride i
        (left.map NttRaw2.normalize) (right.map NttRaw2.normalize) := by
  induction left generalizing i right with
  | nil => simp [forwardStage, forwardStageSpec]
  | cons x xs ih =>
      cases right with
      | nil => simp [forwardStage, forwardStageSpec]
      | cons y ys =>
          simp only [forwardStage, forwardStageSpec, List.map_cons]
          have hfst := congrArg Prod.fst (ih (i + 1) ys)
          have hsnd := congrArg Prod.snd (ih (i + 1) ys)
          simp only at hfst hsnd
          rw [hfst, hsnd]
          simp only [NttPlan.forwardTwiddle_value,
            normalize_forward_fst, normalize_forward_snd]

/-- Normalizing a raw inverse stage gives its residue-level specification. -/
theorem normalize_inverseStage {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat)
    (left right : List (NttRaw4 p)) :
    let raw := inverseStage plan stride i left right
    (raw.1.map NttRaw4.normalize, raw.2.map NttRaw4.normalize) =
      inverseStageSpec plan stride i
        (left.map NttRaw4.normalize) (right.map NttRaw4.normalize) := by
  induction left generalizing i right with
  | nil => simp [inverseStage, inverseStageSpec]
  | cons x xs ih =>
      cases right with
      | nil => simp [inverseStage, inverseStageSpec]
      | cons y ys =>
          simp only [inverseStage, inverseStageSpec, List.map_cons]
          have hfst := congrArg Prod.fst (ih (i + 1) ys)
          have hsnd := congrArg Prod.snd (ih (i + 1) ys)
          simp only at hfst hsnd
          rw [hfst, hsnd]
          simp only [NttPlan.inverseTwiddle_value,
            normalize_inverse_fst, normalize_inverse_snd]

/-- One inverse twiddle cancels the corresponding forward twiddle inside a
butterfly. -/
private theorem inverse_forward_pair {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (e : Nat) (x y : ZMod64 p) :
    let forward := (x + y, plan.root ^ e * (x - y))
    (forward.1 + plan.invRoot ^ e * forward.2,
      forward.1 - plan.invRoot ^ e * forward.2) =
        (x + x, y + y) := by
  have hcancel := plan.invRoot_pow_mul_root_pow e
  have hproduct :
      plan.invRoot ^ e * (plan.root ^ e * (x - y)) = x - y := by
    calc
      plan.invRoot ^ e * (plan.root ^ e * (x - y)) =
          (plan.invRoot ^ e * plan.root ^ e) * (x - y) := by grind
      _ = x - y := by rw [hcancel]; simp
  simp only
  rw [hproduct]
  apply Prod.ext <;> simp only
  · grind
  · grind

/-- Applying the inverse stage to one forward stage doubles both original
halves. -/
theorem inverse_forwardStageSpec {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat)
    (left right : List (ZMod64 p)) (hlength : left.length = right.length) :
    let forward := forwardStageSpec plan stride i left right
    inverseStageSpec plan stride i forward.1 forward.2 =
      (left.map fun value => value + value,
        right.map fun value => value + value) := by
  induction left generalizing i right with
  | nil =>
      have hnil : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          have hrest := ih (i + 1) ys htail
          have hpair := inverse_forward_pair plan ((i * stride) % n) x y
          simp only [forwardStageSpec, inverseStageSpec, List.map_cons]
          have hfst := congrArg Prod.fst hrest
          have hsnd := congrArg Prod.snd hrest
          simp only at hfst hsnd
          rw [hfst, hsnd]
          have hpairFst := congrArg Prod.fst hpair
          have hpairSnd := congrArg Prod.snd hpair
          simp only at hpairFst hpairSnd
          rw [hpairFst, hpairSnd]

/-- Inverse stages commute with a common scalar on both halves. -/
theorem inverseStageSpec_scale {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat) (c : ZMod64 p)
    (left right : List (ZMod64 p)) (hlength : left.length = right.length) :
    inverseStageSpec plan stride i
        (left.map fun value => c * value) (right.map fun value => c * value) =
      let output := inverseStageSpec plan stride i left right
      (output.1.map fun value => c * value,
        output.2.map fun value => c * value) := by
  induction left generalizing i right with
  | nil =>
      have hnil : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          have hrest := ih (i + 1) ys htail
          simp only [List.map_cons, inverseStageSpec]
          have hfst := congrArg Prod.fst hrest
          have hsnd := congrArg Prod.snd hrest
          simp only at hfst hsnd
          rw [hfst, hsnd]
          apply Prod.ext <;> simp only
          · congr 1
            grind
          · congr 1
            rw [Lean.Grind.Ring.sub_eq_add_neg,
              Lean.Grind.Ring.sub_eq_add_neg]
            grind

/-- A residue-level forward stage preserves both equal half lengths. -/
theorem forwardStageSpec_lengths {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat)
    (left right : List (ZMod64 p)) (hlength : left.length = right.length) :
    let output := forwardStageSpec plan stride i left right
    output.1.length = left.length ∧ output.2.length = right.length := by
  induction left generalizing i right with
  | nil =>
      have hnil : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [forwardStageSpec]
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          have hrest := ih (i + 1) ys htail
          simp only [forwardStageSpec, List.length_cons]
          exact ⟨congrArg Nat.succ hrest.1, congrArg Nat.succ hrest.2⟩

/-- A residue-level inverse stage preserves both equal half lengths. -/
theorem inverseStageSpec_lengths {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat)
    (left right : List (ZMod64 p)) (hlength : left.length = right.length) :
    let output := inverseStageSpec plan stride i left right
    output.1.length = left.length ∧ output.2.length = right.length := by
  induction left generalizing i right with
  | nil =>
      have hnil : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [inverseStageSpec]
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          have hrest := ih (i + 1) ys htail
          simp only [inverseStageSpec, List.length_cons]
          exact ⟨congrArg Nat.succ hrest.1, congrArg Nat.succ hrest.2⟩

/-- Recursive DIF forward transform.  `fuel` is the remaining radix-two
depth and `stride` is the root-power stride at this level. -/
def forwardGo {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (NttRaw2 p) → List (NttRaw2 p)
  | 0, values => values
  | fuel + 1, values =>
      let halves := values.splitAt (values.length / 2)
      let stage := forwardStage plan stride 0 halves.1 halves.2
      interleave
        (forwardGo plan (2 * stride) fuel stage.1)
        (forwardGo plan (2 * stride) fuel stage.2)

/-- Recursive DIT inverse transform.  Its input is in ordinary DFT order, so
the even and odd frequency classes are separated before recursion. -/
def inverseGo {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (NttRaw4 p) → List (NttRaw4 p)
  | 0, values => values
  | fuel + 1, values =>
      let halves := deinterleave values
      let left := inverseGo plan (2 * stride) fuel halves.1
      let right := inverseGo plan (2 * stride) fuel halves.2
      let stage := inverseStage plan stride 0 left right
      stage.1 ++ stage.2

/-- Residue-level recursive specification of the forward radix-two loop. -/
def forwardRadix {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (ZMod64 p) → List (ZMod64 p)
  | 0, values => values
  | fuel + 1, values =>
      let halves := values.splitAt (values.length / 2)
      let stage := forwardStageSpec plan stride 0 halves.1 halves.2
      interleave
        (forwardRadix plan (2 * stride) fuel stage.1)
        (forwardRadix plan (2 * stride) fuel stage.2)

/-- Residue-level recursive specification of the inverse radix-two loop. -/
def inverseRadix {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride : Nat) :
    Nat → List (ZMod64 p) → List (ZMod64 p)
  | 0, values => values
  | fuel + 1, values =>
      let halves := deinterleave values
      let left := inverseRadix plan (2 * stride) fuel halves.1
      let right := inverseRadix plan (2 * stride) fuel halves.2
      let stage := inverseStageSpec plan stride 0 left right
      stage.1 ++ stage.2

private theorem map_interleave {α β : Type u} (f : α → β)
    (left right : List α) :
    (interleave left right).map f = interleave (left.map f) (right.map f) := by
  induction left generalizing right with
  | nil => simp [interleave]
  | cons x xs ih =>
      cases right with
      | nil => simp [interleave]
      | cons y ys => simp [interleave, ih]

private theorem map_deinterleave {α β : Type u} (f : α → β)
    (values : List α) :
    let halves := deinterleave values
    (halves.1.map f, halves.2.map f) = deinterleave (values.map f) := by
  induction values using deinterleave.induct with
  | case1 => rfl
  | case2 x => rfl
  | case3 x y rest ih =>
      simp only [deinterleave, List.map_cons]
      have hfst := congrArg Prod.fst ih
      have hsnd := congrArg Prod.snd ih
      simp only at hfst hsnd
      rw [hfst, hsnd]

private theorem splitAt_map {α β : Type u} (f : α → β)
    (count : Nat) (values : List α) :
    (values.map f).splitAt count =
      let halves := values.splitAt count
      (halves.1.map f, halves.2.map f) := by
  induction count generalizing values with
  | zero => simp
  | succ count ih =>
      cases values with
      | nil => simp
      | cons x xs => simp

/-- Interleaving preserves the combined input length. -/
theorem length_interleave {α : Type u} (left right : List α) :
    (interleave left right).length = left.length + right.length := by
  induction left generalizing right with
  | nil => simp [interleave]
  | cons x xs ih =>
      cases right with
      | nil => simp [interleave]
      | cons y ys =>
          simp only [interleave, List.length_cons, ih]
          omega

/-- A forward stage preserves both equal half lengths. -/
theorem forwardStage_lengths {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat)
    (left right : List (NttRaw2 p)) (hlength : left.length = right.length) :
    let output := forwardStage plan stride i left right
    output.1.length = left.length ∧ output.2.length = right.length := by
  induction left generalizing i right with
  | nil =>
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [forwardStage]
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          have hrest := ih (i + 1) ys htail
          simp only [forwardStage, List.length_cons]
          exact ⟨congrArg Nat.succ hrest.1, congrArg Nat.succ hrest.2⟩

/-- An inverse stage preserves both equal half lengths. -/
theorem inverseStage_lengths {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride i : Nat)
    (left right : List (NttRaw4 p)) (hlength : left.length = right.length) :
    let output := inverseStage plan stride i left right
    output.1.length = left.length ∧ output.2.length = right.length := by
  induction left generalizing i right with
  | nil =>
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [inverseStage]
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          have hrest := ih (i + 1) ys htail
          simp only [inverseStage, List.length_cons]
          exact ⟨congrArg Nat.succ hrest.1, congrArg Nat.succ hrest.2⟩

/-- Deinterleaving an even list produces two equal halves. -/
theorem deinterleave_lengths {α : Type u} (values : List α) (m : Nat)
    (hlength : values.length = 2 * m) :
    let halves := deinterleave values
    halves.1.length = m ∧ halves.2.length = m := by
  induction m generalizing values with
  | zero =>
      have hnil : values = [] := List.length_eq_zero_iff.mp (by omega)
      subst values
      simp [deinterleave]
  | succ m ih =>
      cases values with
      | nil => simp at hlength
      | cons x xs =>
          cases xs with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlength
              omega
          | cons y ys =>
              have htail : ys.length = 2 * m := by
                simp only [List.length_cons] at hlength
                omega
              have hrest := ih ys htail
              simp only [deinterleave, List.length_cons]
              exact ⟨congrArg Nat.succ hrest.1, congrArg Nat.succ hrest.2⟩

/-- The raw forward loop preserves a power-of-two input length. -/
theorem length_forwardGo {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride fuel : Nat)
    (values : List (NttRaw2 p)) (hlength : values.length = 2 ^ fuel) :
    (forwardGo plan stride fuel values).length = 2 ^ fuel := by
  induction fuel generalizing stride values with
  | zero => simpa [forwardGo] using hlength
  | succ fuel ih =>
      have hdouble : values.length = 2 * 2 ^ fuel := by
        simpa [Nat.pow_succ, Nat.mul_comm] using hlength
      let halves := values.splitAt (values.length / 2)
      have hhalf : values.length / 2 = 2 ^ fuel := by omega
      have hleft : halves.1.length = 2 ^ fuel := by
        simp only [halves, List.splitAt_eq, List.length_take]
        rw [hhalf, hdouble, Nat.min_eq_left (by omega)]
      have hright : halves.2.length = 2 ^ fuel := by
        simp only [halves, List.splitAt_eq, List.length_drop]
        rw [hhalf, hdouble]
        omega
      let stage := forwardStage plan stride 0 halves.1 halves.2
      have hstage := forwardStage_lengths plan stride 0 halves.1 halves.2
        (hleft.trans hright.symm)
      have hstageLeft : stage.1.length = 2 ^ fuel := hstage.1.trans hleft
      have hstageRight : stage.2.length = 2 ^ fuel := hstage.2.trans hright
      simp only [forwardGo]
      rw [length_interleave, ih _ _ hstageLeft, ih _ _ hstageRight]
      rw [Nat.pow_succ]
      omega

/-- The raw inverse loop preserves a power-of-two input length. -/
theorem length_inverseGo {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride fuel : Nat)
    (values : List (NttRaw4 p)) (hlength : values.length = 2 ^ fuel) :
    (inverseGo plan stride fuel values).length = 2 ^ fuel := by
  induction fuel generalizing stride values with
  | zero => simpa [inverseGo] using hlength
  | succ fuel ih =>
      have hdouble : values.length = 2 * 2 ^ fuel := by
        simpa [Nat.pow_succ, Nat.mul_comm] using hlength
      let halves := deinterleave values
      have hhalves := deinterleave_lengths values (2 ^ fuel) hdouble
      have hleft := ih (2 * stride) halves.1 hhalves.1
      have hright := ih (2 * stride) halves.2 hhalves.2
      let left := inverseGo plan (2 * stride) fuel halves.1
      let right := inverseGo plan (2 * stride) fuel halves.2
      have hstage := inverseStage_lengths plan stride 0 left right
        (hleft.trans hright.symm)
      simp only [inverseGo, List.length_append]
      rw [hstage.1, hstage.2, hleft, hright]
      rw [Nat.pow_succ]
      omega

/-- The raw forward loop represents its residue-level radix specification at
every recursive depth. -/
theorem normalize_forwardGo {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride fuel : Nat)
    (values : List (NttRaw2 p)) :
    (forwardGo plan stride fuel values).map NttRaw2.normalize =
      forwardRadix plan stride fuel (values.map NttRaw2.normalize) := by
  induction fuel generalizing stride values with
  | zero => rfl
  | succ fuel ih =>
      simp only [forwardGo, forwardRadix, List.length_map]
      rw [splitAt_map]
      let halves := values.splitAt (values.length / 2)
      let stage := forwardStage plan stride 0 halves.1 halves.2
      have hstage := normalize_forwardStage plan stride 0 halves.1 halves.2
      have hfst := congrArg Prod.fst hstage
      have hsnd := congrArg Prod.snd hstage
      simp only at hfst hsnd
      rw [map_interleave, ih, ih, hfst, hsnd]

/-- The raw inverse loop represents its residue-level radix specification at
every recursive depth. -/
theorem normalize_inverseGo {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride fuel : Nat)
    (values : List (NttRaw4 p)) :
    (inverseGo plan stride fuel values).map NttRaw4.normalize =
      inverseRadix plan stride fuel (values.map NttRaw4.normalize) := by
  induction fuel generalizing stride values with
  | zero => rfl
  | succ fuel ih =>
      simp only [inverseGo, inverseRadix]
      let halves := deinterleave values
      have hhalves := map_deinterleave NttRaw4.normalize values
      have hhalvesFst := congrArg Prod.fst hhalves
      have hhalvesSnd := congrArg Prod.snd hhalves
      simp only at hhalvesFst hhalvesSnd
      have hleft := ih (2 * stride) halves.1
      have hright := ih (2 * stride) halves.2
      let left := inverseGo plan (2 * stride) fuel halves.1
      let right := inverseGo plan (2 * stride) fuel halves.2
      have hstage := normalize_inverseStage plan stride 0 left right
      have hfst := congrArg Prod.fst hstage
      have hsnd := congrArg Prod.snd hstage
      simp only at hfst hsnd
      rw [List.map_append, hfst, hsnd, hleft, hright]
      rw [hhalvesFst, hhalvesSnd]

/-- The residue-level forward radix recurrence preserves a power-of-two
length. -/
theorem length_forwardRadix {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride fuel : Nat)
    (values : List (ZMod64 p)) (hlength : values.length = 2 ^ fuel) :
    (forwardRadix plan stride fuel values).length = 2 ^ fuel := by
  let raw := values.map NttRaw2.ofZMod
  have hraw : raw.length = 2 ^ fuel := by simpa [raw] using hlength
  have hnormalize := normalize_forwardGo plan stride fuel raw
  have hlengthEq := congrArg List.length hnormalize
  simp only [List.length_map] at hlengthEq
  have hrawNorm : raw.map NttRaw2.normalize = values := by
    simp [raw, List.map_map, Function.comp_def]
  rw [hrawNorm] at hlengthEq
  rw [← hlengthEq]
  exact length_forwardGo plan stride fuel raw hraw

/-- The residue-level inverse radix recurrence preserves a power-of-two
length. -/
theorem length_inverseRadix {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride fuel : Nat)
    (values : List (ZMod64 p)) (hlength : values.length = 2 ^ fuel) :
    (inverseRadix plan stride fuel values).length = 2 ^ fuel := by
  let raw := values.map NttRaw4.ofZMod
  have hraw : raw.length = 2 ^ fuel := by simpa [raw] using hlength
  have hnormalize := normalize_inverseGo plan stride fuel raw
  have hlengthEq := congrArg List.length hnormalize
  simp only [List.length_map] at hlengthEq
  have hrawNorm : raw.map NttRaw4.normalize = values := by
    simp [raw, List.map_map, Function.comp_def]
  rw [hrawNorm] at hlengthEq
  rw [← hlengthEq]
  exact length_inverseGo plan stride fuel raw hraw

/-- The unscaled inverse radix recurrence cancels the forward recurrence and
multiplies every coefficient by the transform length. -/
theorem inverse_forwardRadix {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (stride fuel : Nat)
    (values : List (ZMod64 p)) (hlength : values.length = 2 ^ fuel) :
    inverseRadix plan stride fuel (forwardRadix plan stride fuel values) =
      values.map fun value => ((2 ^ fuel : Nat) : ZMod64 p) * value := by
  induction fuel generalizing stride values with
  | zero =>
      simp only [forwardRadix, inverseRadix, Nat.pow_zero]
      calc
        values = values.map id := (List.map_id values).symm
        _ = values.map (fun value => ((1 : Nat) : ZMod64 p) * value) := by
          apply List.map_congr_left
          intro value hvalue
          grind
  | succ fuel ih =>
      have hdouble : values.length = 2 * 2 ^ fuel := by
        simpa [Nat.pow_succ, Nat.mul_comm] using hlength
      let halves := values.splitAt (values.length / 2)
      have hhalf : values.length / 2 = 2 ^ fuel := by omega
      have hleft : halves.1.length = 2 ^ fuel := by
        simp only [halves, List.splitAt_eq, List.length_take]
        rw [hhalf, hdouble, Nat.min_eq_left (by omega)]
      have hright : halves.2.length = 2 ^ fuel := by
        simp only [halves, List.splitAt_eq, List.length_drop]
        rw [hhalf, hdouble]
        omega
      have hhalves : halves.1.length = halves.2.length :=
        hleft.trans hright.symm
      let stage := forwardStageSpec plan stride 0 halves.1 halves.2
      have hstage := forwardStageSpec_lengths plan stride 0 halves.1 halves.2 hhalves
      have hstageLeft : stage.1.length = 2 ^ fuel := hstage.1.trans hleft
      have hstageRight : stage.2.length = 2 ^ fuel := hstage.2.trans hright
      let left := forwardRadix plan (2 * stride) fuel stage.1
      let right := forwardRadix plan (2 * stride) fuel stage.2
      have hleftLength : left.length = 2 ^ fuel :=
        length_forwardRadix plan (2 * stride) fuel stage.1 hstageLeft
      have hrightLength : right.length = 2 ^ fuel :=
        length_forwardRadix plan (2 * stride) fuel stage.2 hstageRight
      have hsplit : deinterleave (interleave left right) = (left, right) :=
        deinterleave_interleave left right (hleftLength.trans hrightLength.symm)
      have hleftRoundtrip := ih (2 * stride) stage.1 hstageLeft
      have hrightRoundtrip := ih (2 * stride) stage.2 hstageRight
      have hscale := inverseStageSpec_scale plan stride 0
        (((2 ^ fuel : Nat) : ZMod64 p)) stage.1 stage.2
        (hstageLeft.trans hstageRight.symm)
      have hstageInverse :=
        inverse_forwardStageSpec plan stride 0 halves.1 halves.2 hhalves
      simp only [forwardRadix, inverseRadix]
      change
        let split := deinterleave (interleave left right)
        let inverseLeft := inverseRadix plan (2 * stride) fuel split.1
        let inverseRight := inverseRadix plan (2 * stride) fuel split.2
        let output := inverseStageSpec plan stride 0 inverseLeft inverseRight
        output.1 ++ output.2 =
          values.map fun value => ((2 ^ (fuel + 1) : Nat) : ZMod64 p) * value
      rw [hsplit]
      simp only
      rw [hleftRoundtrip, hrightRoundtrip, hscale, hstageInverse]
      simp only [List.map_map, Function.comp_def]
      rw [← List.map_append]
      have hjoin : halves.1 ++ halves.2 = values := by
        simpa only [halves, List.splitAt_eq] using
          List.take_append_drop (values.length / 2) values
      rw [hjoin]
      apply List.map_congr_left
      intro value hvalue
      rw [Nat.pow_succ]
      grind

/-- Residue-level forward result computed by the radix specification. -/
def forwardRadixArray {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p)) : Array (ZMod64 p) :=
  (forwardRadix plan 1 n.log2 values.toList).toArray

/-- Residue-level inverse result, including the final `n⁻¹` scaling. -/
def inverseRadixArray {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p)) : Array (ZMod64 p) :=
  (inverseRadix plan 1 n.log2 values.toList).toArray.map fun value =>
    plan.invLength * value

/-- The scaled residue-level inverse exactly cancels the forward transform on
an array of the plan length. -/
theorem inverseRadixArray_forwardRadixArray {p n : Nat}
    [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p))
    (hsize : values.size = n) :
    inverseRadixArray plan (forwardRadixArray plan values) = values := by
  rw [← Array.toList_inj]
  simp only [inverseRadixArray, forwardRadixArray, Array.toList_map,
    List.toList_toArray]
  have hlength : values.toList.length = 2 ^ n.log2 := by
    simpa [hsize] using plan.length_eq_pow_log2
  have hcast : (((2 ^ n.log2 : Nat) : ZMod64 p)) = (n : ZMod64 p) :=
    congrArg (fun length : Nat => (length : ZMod64 p))
      plan.length_eq_pow_log2.symm
  rw [inverse_forwardRadix plan 1 n.log2 values.toList hlength]
  simp only [List.map_map, Function.comp_def]
  calc
    values.toList.map
          (fun value => plan.invLength *
            (((2 ^ n.log2 : Nat) : ZMod64 p) * value)) =
        values.toList.map id := by
      apply List.map_congr_left
      intro value hvalue
      calc
        plan.invLength * (((2 ^ n.log2 : Nat) : ZMod64 p) * value) =
            (plan.invLength * (n : ZMod64 p)) * value := by
          rw [hcast]
          grind
        _ = value := by rw [plan.invLength_mul_length]; simp
    _ = values.toList := List.map_id values.toList

/-- Forward radix-two transform.  A length mismatch is normal checked
failure; successful execution reuses every root power from `plan`. -/
def forward? {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p)) :
    Option (Array (ZMod64 p)) :=
  if values.size = n then
    some <| (forwardGo plan 1 n.log2
      (values.toList.map NttRaw2.ofZMod)).toArray.map NttRaw2.normalize
  else
    none

/-- Inverse radix-two transform, including multiplication by `n⁻¹` after
the raw inverse loop. -/
def inverse? {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p)) :
    Option (Array (ZMod64 p)) :=
  if values.size = n then
    some <| (inverseGo plan 1 n.log2
      (values.toList.map NttRaw4.ofZMod)).toArray.map fun value =>
        plan.invLength * value.normalize
  else
    none

/-- Successful forward execution is exactly its residue-level radix
specification. -/
theorem forward?_eq_radix {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p))
    (hsize : values.size = n) :
    forward? plan values = some (forwardRadixArray plan values) := by
  unfold forward? forwardRadixArray
  rw [ite_eq_left hsize]
  congr 1
  rw [← Array.toList_inj]
  simp only [Array.toList_map]
  rw [normalize_forwardGo]
  rw [List.map_map]
  rw [show List.map (NttRaw2.normalize ∘ NttRaw2.ofZMod) values.toList =
      values.toList by simp [Function.comp_def]]

/-- Successful inverse execution is exactly its residue-level radix
specification. -/
theorem inverse?_eq_radix {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p))
    (hsize : values.size = n) :
    inverse? plan values = some (inverseRadixArray plan values) := by
  unfold inverse? inverseRadixArray
  rw [ite_eq_left hsize]
  congr 1
  rw [← Array.toList_inj]
  simp only [Array.toList_map]
  calc
    List.map (fun value => plan.invLength * value.normalize)
        (inverseGo plan 1 n.log2 (List.map NttRaw4.ofZMod values.toList)) =
        List.map (fun value => plan.invLength * value)
          (List.map NttRaw4.normalize
            (inverseGo plan 1 n.log2
              (List.map NttRaw4.ofZMod values.toList))) := by
          rw [List.map_map]
          rfl
    _ = List.map (fun value => plan.invLength * value)
          (inverseRadix plan 1 n.log2
            (List.map NttRaw4.normalize
              (List.map NttRaw4.ofZMod values.toList))) := by
          rw [normalize_inverseGo]
    _ = List.map (fun value => plan.invLength * value)
          (inverseRadix plan 1 n.log2 values.toList) := by
          rw [show List.map NttRaw4.normalize
              (List.map NttRaw4.ofZMod values.toList) = values.toList by
            rw [List.map_map]
            simp [Function.comp_def]]

/-- Forward execution rejects exactly a length mismatch. -/
theorem forward?_eq_none_iff {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p)) :
    forward? plan values = none ↔ values.size ≠ n := by
  unfold forward?
  split <;> simp_all

/-- Inverse execution rejects exactly a length mismatch. -/
theorem inverse?_eq_none_iff {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p)) :
    inverse? plan values = none ↔ values.size ≠ n := by
  unfold inverse?
  split <;> simp_all

/-- Every successful forward transform has the plan length. -/
theorem forward?_size {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values result : Array (ZMod64 p))
    (hrun : forward? plan values = some result) : result.size = n := by
  unfold forward? at hrun
  split at hrun
  · rename_i hsize
    cases hrun
    simp only [Array.size_map, List.size_toArray]
    calc
      (forwardGo plan 1 n.log2
          (values.toList.map NttRaw2.ofZMod)).length = 2 ^ n.log2 := by
        apply length_forwardGo
        simpa [hsize] using plan.length_eq_pow_log2
      _ = n := plan.length_eq_pow_log2.symm
  · contradiction

/-- Every successful inverse transform has the plan length. -/
theorem inverse?_size {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values result : Array (ZMod64 p))
    (hrun : inverse? plan values = some result) : result.size = n := by
  unfold inverse? at hrun
  split at hrun
  · rename_i hsize
    cases hrun
    simp only [Array.size_map, List.size_toArray]
    calc
      (inverseGo plan 1 n.log2
          (values.toList.map NttRaw4.ofZMod)).length = 2 ^ n.log2 := by
        apply length_inverseGo
        simpa [hsize] using plan.length_eq_pow_log2
      _ = n := plan.length_eq_pow_log2.symm
  · contradiction

/-- On an array of the plan length, public forward execution followed by
public inverse execution returns the original array. -/
theorem inverse?_forward? {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (values : Array (ZMod64 p))
    (hsize : values.size = n) :
    Option.bind (forward? plan values) (inverse? plan) = some values := by
  have hforward := forward?_eq_radix plan values hsize
  have hforwardSize :=
    forward?_size plan values (forwardRadixArray plan values) hforward
  rw [hforward]
  simp only [Option.bind_some]
  rw [inverse?_eq_radix plan (forwardRadixArray plan values) hforwardSize]
  rw [inverseRadixArray_forwardRadixArray plan values hsize]

end Ntt

end ZMod64

end Hex
