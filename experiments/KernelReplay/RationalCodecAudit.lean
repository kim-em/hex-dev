/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
-- Independent dependency auditing needs the full imported checked bodies.
import KernelReplay.AxiomClosure
import HexRealClosure.BaseJsonTests

open Lean Meta Elab
open Hex.RealClosure
open Hex.RealClosure.Algebraic.KernelReplay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let roots := #[``BaseContext.rational_chain, ``BaseContext.Context.write_rational,
    ``BaseContext.Element.codec_encode_rational, ``BaseContext.Element.codec_decode_rational,
    ``Tower.Context.base_codec, ``BaseJsonTests.encode_rational, ``BaseJsonTests.decode_rational,
    ``BaseJsonTests.decode_three, ``BaseJsonTests.decode_negative, ``BaseJsonTests.decode_bind]
  for name in roots do
    let info ← getConstInfo name
    let some body := info.value? (allowOpaque := true) |
      throwError "rational codec body is missing: {name}"
    for expression in #[info.type, body] do
      if expression.hasSorry || expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then
        throwError "rational codec body is incomplete: {name}"
  let axioms ← AxiomClosure.collect roots
  unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "rational codec changed its complete checked-body axiom closure: {axioms}"
  logInfo m!"rational codec direct checked-body audit: {roots.size} roots, dependencies={axioms}"
