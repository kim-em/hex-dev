/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPrimality.Sieve
public import HexPrimality.Sieve
meta import HexArith.Nat.Prime
public import Lean

public section

/-!
The `#rebuild_primeTable` generator for the committed table and its
sieve-backed verification block.

`#rebuild_primeTable bound sqrtBound batches` runs the compiled sieve,
independently cross-checks every represented bit of the final state
against `isPrimeTrial`, and prints the source to commit: the `primeTable`
literal, the batched intermediate `sieveState` literals, one
kernel-replayed `sieveChunk` equation per batch, the `sieveGoRange_add`
chain to `sieve_eq_final`, and the `primeTable_eq_bits` comparison. The
generator carries no soundness claim of its own — a wrong state or
literal fails the emitted `decide +kernel` checks — but the trial-division
cross-check means a bad emission is caught here rather than at the
committed file.

Batching is what makes the verification scale: each chunk is one bounded
kernel reduction, and raising `bound` past `10^4` is a bench-driven
change (the SPEC's "table verification" family) rather than a code
change.
-/

namespace Hex.SieveElab

open Lean Elab Command

private meta def renderChunk (width start size : Nat) (idx : Nat) : String :=
  let prev := if idx == 1 then s!"(sieveInit {width})" else s!"sieveState{idx - 1}"
  s!"private theorem sieveChunk{idx} :\n    sieveGoRange {width} {start} {size} {prev} = sieveState{idx} := by\n  decide +kernel\n"

private meta def renderChain (bound sqrtB width cnt : Nat)
    (plan : List (Nat × Nat)) : String := Id.run do
  let mut steps : List String := []
  let mut consumed := 0
  let mut start := 1
  let mut idx := 1
  let total := plan.length
  for (st, size) in plan do
    let rest := cnt - consumed - size
    if idx == total then
      steps := steps ++ [s!"sieveChunk{idx}"]
    else
      steps := steps ++
        [s!"show ({cnt - consumed} : Nat) = {size} + {rest} from rfl",
         "sieveGoRange_add", s!"sieveChunk{idx}",
         s!"show ({st} + {size} : Nat) = {st + size} from rfl"]
    consumed := consumed + size
    start := st + size
    idx := idx + 1
  let rws := String.intercalate ",\n    " steps
  return s!"private theorem sieve_eq_final : sieve {bound} {sqrtB} = sieveState{total} := by\n  show sieveGoRange {width} 1 {cnt} (sieveInit {width}) = _\n  rw [{rws}]\n"

private meta def renderTable (primes : List Nat) : String := Id.run do
  let mut linesAcc : List String := []
  let mut line := "  #["
  let mut first := true
  for p in primes do
    let tok := (if first then "" else " ") ++ toString p ++ ","
    if line.length + tok.length > 76 then
      linesAcc := linesAcc ++ [line]
      line := "    " ++ toString p ++ ","
    else
      line := line ++ tok
    first := false
  -- close: replace the trailing comma of the last token
  let closed := (line.dropEnd 1).toString ++ "]"
  return String.intercalate "\n" (linesAcc ++ [closed])

/-- Generate the committed table and its verification block; see the
module docstring. -/
syntax (name := rebuildPrimeTable) "#rebuild_primeTable" num num num : command

@[command_elab rebuildPrimeTable] meta def elabRebuildPrimeTable :
    CommandElab := fun stx => do
  match stx with
  | `(#rebuild_primeTable $b:num $sq:num $k:num) => do
      let bound := b.getNat
      let sqrtB := sq.getNat
      let batches := k.getNat
      unless 0 < batches do
        throwError "#rebuild_primeTable: need at least one batch"
      unless bound ≤ sqrtB * sqrtB do
        throwError "#rebuild_primeTable: need bound ≤ sqrtBound², got \
          {bound} > {sqrtB * sqrtB}"
      let width := Hex.Nat.indexWidth bound
      unless width ≤ 2 ^ 32 do
        throwError "#rebuild_primeTable: width {width} exceeds the mask \
          coverage 2^32"
      let cnt := Hex.Nat.indexWidth (sqrtB + 1) - 1
      unless 0 < cnt do
        throwError "#rebuild_primeTable: no candidates below the square \
          root; the bound is too small for a sieve run"
      -- Near-equal batch plan.
      let base := cnt / batches
      let extra := cnt % batches
      let mut plan : List (Nat × Nat) := []
      let mut start := 1
      for i in [0:batches] do
        let size := base + (if i < extra then 1 else 0)
        if 0 < size then
          plan := plan ++ [(start, size)]
          start := start + size
      -- Run the compiled sieve batch by batch.
      let mut states : List Nat := []
      let mut st := Hex.Nat.sieveInit width
      for (s0, size) in plan do
        st := Hex.Nat.sieveGoRange width s0 size st
        states := states ++ [st]
      -- Independent cross-check of every represented bit.
      for t in [1:width] do
        let v := Hex.Nat.numOfIndex t
        unless st.testBit t == Hex.Nat.isPrimeTrial v do
          throwError "#rebuild_primeTable: internal error: the sieve and \
            trial division disagree at index {t} (value {v}); please \
            report this"
      -- Read the table off the final state.
      let primes := 2 :: 3 :: Hex.Nat.bitsToList st bound
      let mut out := s!"-- generated by #rebuild_primeTable {bound} {sqrtB} {batches}\n"
      out := out ++ s!"def primeTableBound : Nat := {bound}\n\n"
      out := out ++ "def primeTable : Array Nat :=\n" ++ renderTable primes ++ "\n\n"
      out := out ++ s!"-- #rebuild_primeTable {bound} {sqrtB} {batches}\n\n"
      let mut idx := 1
      for state in states do
        out := out ++ s!"private def sieveState{idx} : Nat :=\n  {state}\n\n"
        idx := idx + 1
      idx := 1
      for (s0, size) in plan do
        out := out ++ renderChunk width s0 size idx ++ "\n"
        idx := idx + 1
      out := out ++ renderChain bound sqrtB width cnt plan
      logInfo out
  | _ => throwUnsupportedSyntax

end Hex.SieveElab
