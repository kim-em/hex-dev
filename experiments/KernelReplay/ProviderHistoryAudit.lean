/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
-- Independent dependency auditing needs the full imported checked bodies.
import KernelReplay.AxiomClosure
import HexRealClosure.BaseHistoryTests
import HexRealClosureTheory.ConstructedCatalog

open Lean Meta Elab
open Hex.RealClosure.BaseContext Hex.RealClosure.Tower
open Hex.RealClosure.Algebraic.KernelReplay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let roots := #[``RealPrefix.Step.present, ``RealPrefix.append,
    ``RealPrefix.append_keys, ``RealPrefix.append_embedding, ``RealPrefix.extend?,
    ``RealPrefix.extend?_prefix, ``RealPrefix.extend?_mem,
    ``Catalog.construct?, ``Catalog.construct?_success, ``Catalog.Construction.installed,
    ``Catalog.Construction.preserved, ``Catalog.Construction.covers,
    ``Live.Request.providerKeys, ``Live.Request.gatherConstructed?,
    ``Live.Request.gatherConstructed?_of_success, ``Live.Request.gatherConstructed?_gathered,
    ``RealPrefix.Model.StepCorrect, ``RealPrefix.Model.append, ``RealPrefix.Model.append_context,
    ``RealPrefix.Model.progress, ``RealPrefix.Model.progress_correct,
    ``RealPrefix.Model.extend?_model, ``RealPrefix.Model.extend?_success,
    ``RealPrefix.Model.extend?_embedding, ``Catalog.Construction.models,
    ``Live.Request.gatherConstructed?_success, ``Live.Request.gatherConstructed?_model,
    ``HistoryTests.offer, ``HistoryTests.reader, ``HistoryTests.construct_two,
    ``HistoryTests.duplicate_keys, ``HistoryTests.missing_second, ``HistoryTests.reuse_existing]
  for name in roots do
    let info ← getConstInfo name
    let some body := info.value? (allowOpaque := true) |
      throwError "provider history body is missing: {name}"
    for expression in #[info.type, body] do
      if expression.hasSorry || expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then
        throwError "provider history body is incomplete: {name}"
  let axioms ← AxiomClosure.collect roots
  unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "provider history changed its complete checked-body axiom closure: {axioms}"
  logInfo m!"provider history direct checked-body audit: {roots.size} roots, dependencies={axioms}"
