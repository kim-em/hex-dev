/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Evidence
public import HexSignDet.Codec.Laws
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Evidence
import all Lean.Data.Json.Basic

public section

namespace Hex.SignDet.Codec
open Lean

variable {E Ctx : Type} [Zero E] [DecidableEq E]

/-- Structured encoding preserves every supplied remainder witness, whether
or not the arithmetic identity will pass independent replay. -/
theorem read_remainder (value : ValueCodec E) (h : value.Lawful) (s : RemainderStep E) :
    readRemainder value (remainder value s) = .ok s := by
  have hv := h
  unfold ValueCodec.Lawful at hv
  simp [readRemainder, remainder, tuple, Json.getArr?, bind, Except.bind, pure,
    Except.pure, hv, read_poly value h]

theorem read_terminal (value : ValueCodec E) (h : value.Lawful) (t : E × DensePoly E) :
    readTerminal value (terminal value t) = .ok t := by
  have hv := h
  unfold ValueCodec.Lawful at hv
  simp [readTerminal, terminal, tuple, Json.getArr?, bind, Except.bind, pure,
    Except.pure, hv, read_poly value h]

theorem read_chain (value : ValueCodec E) (h : value.Lawful) (c : SignedRemainderChain E) :
    readChain value (chain value c) = .ok c := by
  simp [readChain, chain, tuple, Json.getArr?, bind, Except.bind, pure, Except.pure,
    read_array _ _ (read_poly value h), read_jsonArray read_nat,
    read_remainder value h, read_array _ _ (read_remainder value h),
    read_option _ _ (read_terminal value h)]

/-- All twelve fields roundtrip, including the two complete chain witnesses,
endpoint signs and variation counts. No semantic certificate premise is used. -/
theorem read_tarski (value : ValueCodec E) (context : ValueCodec Ctx)
    (hv : value.Lawful) (hc : context.Lawful) (c : TarskiCertificate E E Ctx) :
    readTarski value context (tarski value context c) = .ok c := by
  have ctx := hc
  unfold ValueCodec.Lawful at ctx
  simp [readTarski, tarski, tuple, Json.getArr?, bind, Except.bind, pure, Except.pure,
    ctx, read_poly value hv, read_endpoint value hv, read_chain value hv,
    read_jsonArray read_int]

/-- A reduction's factor index is structural data. Its bound is checked by
parsing, independently of the scale and polynomial identities. -/
theorem read_step (value : ValueCodec E) (h : value.Lawful)
    (s : ReductionStep E) (bound : s.index < arity) :
    readReductionStep value arity (reductionStep value s) = .ok s := by
  simp [readReductionStep, reductionStep, tuple, Json.getArr?, bind, Except.bind,
    pure, Except.pure, index, bound, read_poly value h, read_remainder value h]

theorem read_reduction (value : ValueCodec E) (h : value.Lawful)
    (r : Reduction E) (bound : ∀ s ∈ r.steps, s.index < arity) :
    readReduction value arity (reduction value r) = .ok r := by
  have hs := read_list_of (reductionStep value) (readReductionStep value arity) r.steps
    (fun s hs => read_step value h s (bound s hs))
  simp [readReduction, reduction, tuple, Json.getArr?, bind, Except.bind,
    pure, Except.pure, hs, read_poly value h]

theorem read_preparation (value : ValueCodec E) (h : value.Lawful)
    (r : QueryReduction E) (bound : ∀ s ∈ r.steps, s.index < arity) :
    readPreparation value arity (preparation value r) = .ok r := by
  have hs := read_list_of (reductionStep value) (readReductionStep value arity) r.steps
    (fun s hs => read_step value h s (bound s hs))
  simp [readPreparation, preparation, hs, bind, Except.bind, pure, Except.pure]

end Hex.SignDet.Codec
