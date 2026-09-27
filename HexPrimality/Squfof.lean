/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith

public section

/-! A bounded, deterministic square-form search. All recurrence arithmetic is exact;
only the final checked divisor is exposed as a factor. -/

namespace Hex.Nat.Squfof

structure Limits where
  multipliers : Nat := 16
  steps : Nat := 65536
  queueCapacity : Nat := 128
deriving Repr, DecidableEq

inductive Outcome where
  | factor (divisor : Nat)
  | noFactor
  | exhausted
  | unsupported
deriving Repr, DecidableEq

structure Result where
  outcome : Outcome
  attempts : Nat
  steps : Nat
  peakQueue : Nat
deriving Repr, DecidableEq

/-- The prescribed multiplier order. -/
def multipliers : List Nat :=
  [1, 3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155]

structure Form where
  qprev : Nat
  p : Nat
  q : Nat
deriving Repr, DecidableEq

abbrev Pair := Nat × Nat

inductive Stop where
  | factor
  | repeated
  | exhausted
  | queueFull
  | arithmetic
  | skipped
deriving Repr, DecidableEq

structure Attempt (n : Nat) where
  divisor : Option {d : Nat // 1 < d ∧ d < n ∧ d ∣ n} := none
  stop : Stop := .skipped
  steps : Nat := 0
  peakQueue : Nat := 0
  forwardSteps : Nat := 0
  reverseSteps : Nat := 0
  remaining : Nat := 0
deriving Repr, DecidableEq

private def validated (n d : Nat) : Option {x : Nat // 1 < x ∧ x < n ∧ x ∣ n} :=
  if h : 1 < d ∧ d < n ∧ n % d = 0 then
    some ⟨d, h.1, h.2.1, Nat.dvd_of_mod_eq_zero h.2.2⟩
  else none

private def terminal (n d : Nat) (forwardSteps reverseSteps peak : Nat) : Attempt n :=
  match validated n d with
  | some x => ⟨some x, .factor, forwardSteps + reverseSteps, peak,
      forwardSteps, reverseSteps, 0⟩
  | none => ⟨none, .skipped, forwardSteps + reverseSteps, peak,
      forwardSteps, reverseSteps, 0⟩

private def nonnegative (x : Int) : Option Nat :=
  if x < 0 then none else some x.toNat

/-- One exact continued-fraction transition, given its quotient and next `P`. -/
def nextForm (f : Form) (b : Nat) (pnext : Int) : Option Form := do
  let p ← nonnegative pnext
  let q ← nonnegative ((f.qprev : Int) + (b : Int) * ((f.p : Int) - pnext))
  if q = 0 then none else some ⟨f.q, p, q⟩

/-- Reverse initialization from a square form. -/
def reverseForm (D S : Nat) (f : Form) (r : Nat) : Option Form := do
  if r = 0 then none else
  let p ← nonnegative ((f.p : Int) + (r : Int) * (((S : Int) - (f.p : Int)) / (r : Int)))
  let numerator := (D : Int) - (p : Int) * (p : Int)
  if numerator ≤ 0 ∨ numerator % (r : Int) ≠ 0 then none else
  let q ← nonnegative (numerator / (r : Int))
  if q = 0 then none else some ⟨r, p, q⟩

/-- The first matching queued form removes itself and the whole FIFO prefix. -/
def afterMatch (queue : List Pair) (r p : Nat) : Option (List Pair) :=
  match queue with
  | [] => none
  | (g, t) :: rest =>
    if g = r ∧ t = p % r then some rest else afterMatch rest r p

private theorem afterMatch_length {queue rest : List Pair} {r p : Nat}
    (h : afterMatch queue r p = some rest) : rest.length ≤ queue.length := by
  induction queue generalizing rest with
  | nil => simp [afterMatch] at h
  | cons entry tail ih =>
    simp only [afterMatch] at h
    split at h
    · cases h
      simp
    · have hh := ih h
      simp only [List.length_cons]
      omega

private structure Saved where
  form : Form
  queue : List Pair
  index : Nat

private def stopped (n : Nat) (reason : Stop) (fwd rev peak remaining : Nat) : Attempt n :=
  { stop := reason, steps := fwd + rev, peakQueue := peak,
    forwardSteps := fwd, reverseSteps := rev, remaining }

private def search (n k D S L capacity : Nat) :
    Nat → Form → List Pair → Nat → Option Saved → Nat → Nat → Nat → Attempt n
  | 0, _, _, _, _, fwd, rev, peak => stopped n .exhausted fwd rev peak 0
  | fuel + 1, form, queue, index, saved, fwd, rev, peak => Id.run do
      if form.q = 0 then return stopped n .arithmetic fwd rev peak (fuel + 1)
      let b := (S + form.p) / form.q
      let pnext : Int := (b : Int) * (form.q : Int) - (form.p : Int)
      match saved with
      | some old =>
        let rev := rev + 1
        if pnext = (form.p : Int) then
          let candidate := terminal n (Nat.gcd form.q n) fwd rev peak
          if candidate.divisor.isSome then return { candidate with remaining := fuel }
          else return (search n k D S L capacity fuel old.form old.queue old.index
            none fwd rev peak)
        match nextForm form b pnext with
        | none => return stopped n .arithmetic fwd rev peak fuel
        | some next => return (search n k D S L capacity fuel next queue index
            saved fwd rev peak)
      | none =>
        let fwd := fwd + 1
        let g := form.q / Nat.gcd form.q (2 * k)
        let mut queue := queue
        let mut peak := peak
        if g ≤ L then
          if queue.length = capacity then
            return stopped n .queueFull fwd rev peak fuel
          queue := queue ++ [(g, form.p % g)]
          peak := max peak queue.length
        match nextForm form b pnext with
        | none => return stopped n .arithmetic fwd rev peak fuel
        | some next =>
          if index % 2 = 0 then
            let r := Nat.sqrt next.q
            if r * r = next.q then
              match afterMatch queue r next.p with
              | some rest =>
                if r = 1 then return stopped n .repeated fwd rev peak fuel
                return search n k D S L capacity fuel next rest (index + 1)
                  none fwd rev peak
              | none =>
                match reverseForm D S next r with
                | none => return stopped n .arithmetic fwd rev peak fuel
                | some reverse =>
                  return search n k D S L capacity fuel reverse queue (index + 1)
                    (some ⟨next, queue, index + 1⟩) fwd rev peak
          return search n k D S L capacity fuel next queue (index + 1)
            none fwd rev peak

private theorem search_queue (n k D S L capacity fuel : Nat) (form : Form)
    (queue : List Pair) (index : Nat) (saved : Option Saved)
    (fwd rev peak : Nat) (hq : queue.length ≤ capacity)
    (hs : ∀ old, saved = some old → old.queue.length ≤ capacity)
    (hp : peak ≤ capacity) :
    (search n k D S L capacity fuel form queue index saved fwd rev peak).peakQueue ≤ capacity := by
  induction fuel generalizing form queue index saved fwd rev peak with
  | zero => simpa [search, stopped] using hp
  | succ fuel ih =>
    simp only [search, Id.run, pure]
    repeat' split
    all_goals simp_all [stopped, terminal, List.length_append]
    all_goals try apply ih
    all_goals try simp_all [List.length_append]
    all_goals try omega
    all_goals first
      | (split <;> simpa using hp)
      | (have hlen := afterMatch_length (by assumption); simp_all [List.length_append]; omega)

/-- Run one multiplier with the same kernel used by the public schedule. -/
def runMultiplier (n k : Nat) (limits : Limits) : Attempt n :=
  let g := Nat.gcd k n
  if let some d := validated n g then
    terminal n d.val 0 0 0
  else if g = n then
    stopped n .skipped 0 0 0 limits.steps
  else
    let M := k * n
    let D := if M % 4 = 1 then 2 * M else M
    let S := Nat.sqrt D
    if S * S = D then
      terminal n (Nat.gcd S n) 0 0 0
    else
      let Q := D - S * S
      if Q = 0 then stopped n .arithmetic 0 0 0 limits.steps
      else
        let a := search n k D S (Nat.sqrt (Nat.sqrt (4 * D)))
          limits.queueCapacity limits.steps ⟨1, S, Q⟩ [] 0 none 0 0 0
        { a with steps := limits.steps - a.remaining }

private theorem terminal_steps (n d fwd rev peak : Nat) :
    (terminal n d fwd rev peak).steps = fwd + rev := by
  unfold terminal
  split <;> rfl

private theorem terminal_queue (n d fwd rev peak : Nat) :
    (terminal n d fwd rev peak).peakQueue = peak := by
  unfold terminal
  split <;> rfl

private theorem runMultiplier_steps (n k : Nat) (limits : Limits) :
    (runMultiplier n k limits).steps ≤ limits.steps := by
  unfold runMultiplier
  dsimp only
  repeat' split
  all_goals simp only [terminal_steps, stopped, Nat.zero_add]
  all_goals omega

private theorem runMultiplier_queue (n k : Nat) (limits : Limits) :
    (runMultiplier n k limits).peakQueue ≤ limits.queueCapacity := by
  unfold runMultiplier
  dsimp only
  repeat' split
  all_goals simp only [terminal_queue, stopped]
  all_goals try (apply search_queue <;> simp)
  all_goals omega

private inductive CheckedOutcome (n : Nat) where
  | factor (d : {x : Nat // 1 < x ∧ x < n ∧ x ∣ n})
  | noFactor
  | exhausted
  | unsupported

private structure CheckedResult (n : Nat) where
  outcome : CheckedOutcome n
  attempts : Nat
  steps : Nat
  peakQueue : Nat

private def CheckedResult.public {n : Nat} (r : CheckedResult n) : Result :=
  ⟨match r.outcome with
   | .factor d => .factor d.val
   | .noFactor => .noFactor
   | .exhausted => .exhausted
   | .unsupported => .unsupported,
   r.attempts, r.steps, r.peakQueue⟩

private def runSchedule (n : Nat) (limits : Limits) :
    List Nat → Nat → Nat → Nat → Bool → CheckedResult n
  | [], attempts, steps, peak, exhausted =>
    ⟨if exhausted then .exhausted else .noFactor, attempts, steps, peak⟩
  | k :: ks, attempts, steps, peak, exhausted =>
    let a := runMultiplier n k limits
    let attempts := attempts + 1
    let steps := steps + a.steps
    let peak := max peak a.peakQueue
    match a.divisor with
    | some d => ⟨.factor d, attempts, steps, peak⟩
    | none => runSchedule n limits ks attempts steps peak
        (exhausted || a.stop == .exhausted || a.stop == .queueFull)

private theorem runSchedule_bounds (n : Nat) (limits : Limits) (ks : List Nat)
    (attempts steps peak : Nat) (exhausted : Bool)
    (hs : steps ≤ attempts * limits.steps)
    (hp : peak ≤ limits.queueCapacity) :
    let r := runSchedule n limits ks attempts steps peak exhausted
    r.attempts ≤ attempts + ks.length ∧
      r.steps ≤ r.attempts * limits.steps ∧
      r.peakQueue ≤ limits.queueCapacity := by
  induction ks generalizing attempts steps peak exhausted with
  | nil =>
    simpa [runSchedule] using And.intro (Nat.le_refl attempts) (And.intro hs hp)
  | cons k ks ih =>
    let a := runMultiplier n k limits
    have ha : a.steps ≤ limits.steps := runMultiplier_steps n k limits
    have hq : a.peakQueue ≤ limits.queueCapacity := runMultiplier_queue n k limits
    have hs' : steps + a.steps ≤ (attempts + 1) * limits.steps := by
      rw [Nat.add_mul]
      omega
    have hp' : max peak a.peakQueue ≤ limits.queueCapacity := by omega
    cases hd : a.divisor with
    | none =>
      have h := ih (attempts + 1) (steps + a.steps) (max peak a.peakQueue)
        (exhausted || a.stop == .exhausted || a.stop == .queueFull) hs' hp'
      simpa [runSchedule, a, hd, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h
    | some d =>
      simp only [runSchedule, a, hd, List.length_cons]
      exact ⟨by omega, hs', hp'⟩

/-- Bounded SQUFOF proper-factor search below `2^64`. -/
private def factorCore (n : Nat) (limits : Limits) : CheckedResult n :=
  if n < 4 then ⟨.noFactor, 0, 0, 0⟩
  else if 2 ^ 64 ≤ n then ⟨.unsupported, 0, 0, 0⟩
  else if n % 2 = 0 then
    match validated n 2 with
    | some d => ⟨.factor d, 0, 0, 0⟩
    | none => ⟨.noFactor, 0, 0, 0⟩
  else
    let s := Nat.sqrt n
    if s * s = n then
      match validated n s with
      | some d => ⟨.factor d, 0, 0, 0⟩
      | none => ⟨.noFactor, 0, 0, 0⟩
    else if limits.multipliers = 0 ∨ limits.steps = 0 then
      ⟨.exhausted, 0, 0, 0⟩
    else
      let allowed := min limits.multipliers 16
      let r := runSchedule n limits (multipliers.take allowed) 0 0 0 false
      if allowed < 16 && r.outcome matches .noFactor then
        { r with outcome := .exhausted }
      else r

private theorem factorCore_bounds (n : Nat) (limits : Limits) :
    let r := factorCore n limits
    r.attempts ≤ min limits.multipliers 16 ∧
      r.steps ≤ r.attempts * limits.steps ∧
      r.peakQueue ≤ limits.queueCapacity := by
  let allowed := min limits.multipliers 16
  let r := runSchedule n limits (multipliers.take allowed) 0 0 0 false
  have hb : r.attempts ≤ allowed ∧ r.steps ≤ r.attempts * limits.steps ∧
      r.peakQueue ≤ limits.queueCapacity := by
    have h := runSchedule_bounds n limits (multipliers.take allowed) 0 0 0 false
      (by simp) (by simp)
    have hl : (multipliers.take allowed).length ≤ allowed := by
      simp only [List.length_take]
      omega
    dsimp only [r] at *
    exact ⟨by omega, h.2.1, h.2.2⟩
  unfold factorCore
  dsimp only
  repeat' split
  all_goals simp_all [r, allowed]

def factor (n : Nat) (limits : Limits := {}) : Result :=
  (factorCore n limits).public

theorem factor_attempts (n : Nat) (limits : Limits) :
    (factor n limits).attempts ≤ min limits.multipliers 16 :=
  (factorCore_bounds n limits).1

theorem factor_steps (n : Nat) (limits : Limits) :
    (factor n limits).steps ≤ (factor n limits).attempts * limits.steps :=
  (factorCore_bounds n limits).2.1

theorem factor_queue (n : Nat) (limits : Limits) :
    (factor n limits).peakQueue ≤ limits.queueCapacity :=
  (factorCore_bounds n limits).2.2

private theorem CheckedResult.public_spec {n d : Nat} (r : CheckedResult n)
    (h : r.public.outcome = .factor d) : 1 < d ∧ d < n ∧ d ∣ n := by
  cases r with
  | mk outcome attempts steps peakQueue =>
    cases outcome with
    | factor x =>
      simp only [CheckedResult.public, Outcome.factor.injEq] at h
      subst d
      exact x.property
    | noFactor => simp [CheckedResult.public] at h
    | exhausted => simp [CheckedResult.public] at h
    | unsupported => simp [CheckedResult.public] at h

theorem factor_spec {n : Nat} {limits : Limits} {d : Nat}
    (h : (factor n limits).outcome = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n :=
  CheckedResult.public_spec (factorCore n limits) h

end Hex.Nat.Squfof
