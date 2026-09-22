/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Complete

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Insert a realized full encoding by the largest-differing-index rule.
An impossible rule or duplicate word is an internal error, never a guessed
order. The caller binds all heads, contexts and full derivative slots. -/
def Thom.insert {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) :
    List (Descriptor E Ctx sign context) → Except BuildError (List (Descriptor E Ctx sign context))
  | [] => .ok [d]
  | e :: es =>
    match compareSigns d.raw.signs e.raw.signs with
    | some .lt => .ok (d :: e :: es)
    | some .gt => match insert d es with
      | .ok rest => .ok (e :: rest)
      | .error err => .error err
    | _ => .error .system

/-- Successful ordering preserves every descriptor and introduces none. -/
theorem Thom.insert_perm {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) {ds out : List (Descriptor E Ctx sign context)}
    (h : insert d ds = .ok out) : out.Perm (d :: ds) := by
  induction ds generalizing out with
  | nil => simpa [insert] using h.symm
  | cons e es ih =>
    cases hc : compareSigns d.raw.signs e.raw.signs with
    | none => simp [insert, hc] at h
    | some order =>
      cases order with
      | eq => simp [insert, hc] at h
      | lt =>
        have he : out = d :: e :: es := by simpa [insert, hc] using h.symm
        rw [he]
      | gt =>
        cases hi : insert d es with
        | error err => simp [insert, hc, hi] at h
        | ok rest =>
          have he : out = e :: rest := by simpa [insert, hc, hi] using h.symm
          rw [he]
          exact (List.Perm.cons e (ih hi)).trans (List.Perm.swap _ _ _)

/-- Convert a full table to count-one descriptors in Thom order. This helper
checks each raw descriptor against the same complete replay, so an invented
word or a count greater than one cannot become a root descriptor. -/
def Descriptor.rootsFrom (sign : E → Int) (context : Ctx) (raw : RawDescriptor E Ctx)
    (t : Replay E Ctx) : List (List Int × Nat) →
      Except BuildError (List (Descriptor E Ctx sign context))
  | [] => .ok []
  | (signs, count) :: rows =>
    if count ≠ 1 then .error .system
    else match Descriptor.ofReplay? sign context (raw.full signs) t with
      | none => .error .replay
      | some d => match rootsFrom sign context raw t rows with
        | .error err => .error err
        | .ok ds => Thom.insert d ds

/-- Successful root-list construction keeps exactly the table's encoding
words. It cannot drop a difficult row or add a guessed root while sorting. -/
theorem Descriptor.rootsFrom_perm (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx) {rows : List (List Int × Nat)}
    {out : List (Descriptor E Ctx sign context)}
    (h : rootsFrom sign context raw t rows = .ok out) :
    (out.map fun d => d.raw.signs).Perm (rows.map Prod.fst) := by
  induction rows generalizing out with
  | nil =>
    have he : out = [] := by simpa [rootsFrom] using h.symm
    simp [he]
  | cons row rows ih =>
    obtain ⟨signs, count⟩ := row
    by_cases hn : count ≠ 1
    · simp [rootsFrom, hn] at h
    · cases hd : ofReplay? sign context (raw.full signs) t with
      | none => simp [rootsFrom, hn, hd] at h
      | some d =>
        cases hr : rootsFrom sign context raw t rows with
        | error err => simp [rootsFrom, hn, hd, hr] at h
        | ok ds =>
          have hi : Thom.insert d ds = .ok out := by simpa [rootsFrom, hn, hd, hr] using h
          have hs : d.raw.signs = signs := by rw [ofReplay_raw hd]; rfl
          have hp := (Thom.insert_perm d hi).map (fun d => d.raw.signs)
          simp only [List.map_cons, hs] at hp
          exact hp.trans (List.Perm.cons signs (ih hr))

variable [Neg E] [Inv E]

/-- Enumerate all full encodings and order them by Thom's rule. Only invalid
root domains return `none`; unproved producer/Thom invariants stay separate
internal diagnostics. Constants have an empty table and therefore no roots. -/
def Descriptor.buildRoots (sign : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) : Except BuildError (Option (List (Descriptor E Ctx sign context))) :=
  match Sturm.prepare sign p a b with
  | none => .ok none
  | some domain =>
    let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
    match buildPrepared context domain (raw.full []).queries with
    | .error err => .error err
    | .ok t => match rootsFrom sign context raw t.val (t.val.table t.property).rows.toList with
      | .error err => .error err
      | .ok roots => .ok (some roots)

end Hex.SignDet
