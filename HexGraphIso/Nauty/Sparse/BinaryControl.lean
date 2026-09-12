/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountResult
public import HexGraphIso.Nauty.Sparse.CountFrame
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Control at the singleton splitter's conditional fragment finalization.
Uniform predicate classes do not close a boundary or enqueue a fragment. -/
@[expose] def CountTrace.Control.binary (c : CountTrace.Control n) (first cut last : Nat) :
    CountTrace.Control n :=
  if cut ≠ last ∧ cut ≠ first then (c.hash cut).pair first cut last else c

/-- Observations of conditional binary-fragment finalization, including
its exact label and index writes and unchanged scratch storage. -/
structure Binary.Result (level first cut last : Nat) (s : RefineSt n)
    (lab starts : Array Nat) (r : RefineSt n) : Prop where
  control : CountTrace.control r = (CountTrace.control s).binary first cut last
  ptn : r.ptn = if cut ≠ last ∧ cut ≠ first then s.ptn.set! (cut - 1) level else s.ptn
  count : r.numcells = if cut ≠ last ∧ cut ≠ first then s.numcells + 1 else s.numcells
  label : r.lab = lab
  starts_eq : r.cellstart =
    if cut ≠ last ∧ cut ≠ first then
      let middle := if cut = first + 1 then starts.set! lab[first]! n else starts
      if last = cut + 1 then middle.set! lab[cut]! n else middle
    else starts
  ends : r.cellend = if cut ≠ last ∧ cut ≠ first then
      (s.cellend.set! first (cut - 1)).set! cut (last - 1) else s.cellend
  frame : CountFrame { s with lab, cellstart := starts } r

/-- The singleton splitter's actual endpoint, sentinel, hash and queue
finalization has the stated observations; the label and cache arrays keep
their executed representation and ownership transfers. -/
theorem binary_control (level first cut last : Nat) (s : RefineSt n) (lab starts : Array Nat) :
    let r := Id.run do
      let mut s := s
      let mut starts := starts
      if cut != last && cut != first then
        if cut == first + 1 then starts := starts.set! lab[first]! n
        if last == cut + 1 then starts := starts.set! lab[cut]! n
        s := { s with
          numcells := s.numcells + 1, ptn := s.ptn.set! (cut - 1) level
          cellend := (s.cellend.set! first (cut - 1)).set! cut (last - 1) }
        s := s.hash cut
        if cut - first <= last - cut && !s.active.mem first then s := s.push first
        else s := s.push cut
      return { s with lab, cellstart := starts }
    Binary.Result level first cut last s lab starts r := by
  simp only
  apply Id.of_wp_run_eq rfl (fun r : RefineSt n => Binary.Result level first cut last s lab starts r)
  mvcgen
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp_all +zetaDelta [RefineSt.hash, RefineSt.push,
    CountTrace.control, CountTrace.Control.binary, CountTrace.Control.pair,
    CountTrace.Control.hash, CountTrace.Control.push]
  all_goals grind [CountFrame]

end Hex.GraphIso.Nauty.Sparse
