/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Coefficients
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Json

public section

namespace Hex.SignDet.Codec

variable {E Ctx : Type} [Zero E] [DecidableEq E]

/-- Polynomial decoding uses only its stored coefficients. -/
theorem read_poly_covered (value : ValueCodec E) (p : DensePoly E)
    (h : value.Covers (Coefficients.poly p)) :
    readPoly value (poly value p) = .ok p :=
  read_poly_of value p (fun x hx => h x
    (by simpa only [Coefficients.poly, Array.mem_toList_iff] using hx))

omit [Zero E] [DecidableEq E] in
theorem read_endpoint_covered (value : ValueCodec E) (e : Endpoint E)
    (h : value.Covers (Coefficients.endpoint e)) :
    readEndpoint value (endpoint value e) = .ok e := by
  apply read_endpoint_of
  intro x hx
  subst e
  exact h x (by simp [Coefficients.endpoint])

/-- A witness needs coverage of its scales as well as its quotient. -/
theorem read_remainder_covered (value : ValueCodec E) (s : RemainderStep E)
    (h : value.Covers (Coefficients.remainder s)) :
    readRemainder value (remainder value s) = .ok s := by
  simp only [Coefficients.remainder, ValueCodec.covers_append,
    ValueCodec.covers_cons, ValueCodec.covers_nil, and_true] at h
  simp [readRemainder, remainder, tuple, Json.getArr_arr, bind, Except.bind,
    pure, Except.pure, h.1.1, h.2, read_poly_covered value s.quotient h.1.2]

theorem read_terminal_covered (value : ValueCodec E) (t : E × DensePoly E)
    (h : value.Covers (Coefficients.terminal t)) :
    readTerminal value (terminal value t) = .ok t := by
  simp only [Coefficients.terminal, ValueCodec.covers_append,
    ValueCodec.covers_cons, ValueCodec.covers_nil, and_true] at h
  simp [readTerminal, terminal, tuple, Json.getArr_arr, bind, Except.bind,
    pure, Except.pure, h.1, read_poly_covered value t.2 h.2]

theorem read_chain_covered (value : ValueCodec E) (c : SignedRemainderChain E)
    (h : value.Covers (Coefficients.chain c)) :
    readChain value (chain value c) = .ok c := by
  simp only [Coefficients.chain, ValueCodec.covers_append, ValueCodec.covers_flatMap] at h
  have polys := read_array_of (poly value) (readPoly value) c.chain
    (fun p hp => read_poly_covered value p (h.1.1.1 p (by simpa using hp)))
  have steps := read_array_of (remainder value) (readRemainder value) c.steps
    (fun s hs => read_remainder_covered value s (h.1.2 s (by simpa using hs)))
  have terminal := read_option_of (Codec.terminal value) (readTerminal value) c.terminal
    (fun t ht => read_terminal_covered value t (h.2 t (by simpa using ht)))
  simp [readChain, chain, tuple, Json.getArr_arr, bind, Except.bind, pure, Except.pure,
    polys, read_jsonArray read_nat, read_remainder_covered value c.initial h.1.1.2,
    steps, terminal]

/-- Finite coefficient coverage and the literal context suffice for all twelve
Tarski fields. No global completeness of either reader is required. -/
theorem read_tarski_covered (value : ValueCodec E) (context : ValueCodec Ctx)
    (c : TarskiCertificate E E Ctx) (h : value.Covers (Coefficients.tarski c))
    (hc : context.decode (context.encode c.context) = .ok c.context) :
    readTarski value context (tarski value context c) = .ok c := by
  simp only [Coefficients.tarski, ValueCodec.covers_append] at h
  simp [readTarski, tarski, tuple, Json.getArr_arr, bind, Except.bind, pure, Except.pure,
    hc, read_poly_covered value c.head h.1.1.1.1.1,
    read_poly_covered value c.queryPoly h.1.1.1.1.2,
    read_endpoint_covered value c.lower h.1.1.1.2,
    read_endpoint_covered value c.upper h.1.1.2,
    read_chain_covered value c.squarefree h.1.2,
    read_chain_covered value c.remainders h.2, read_jsonArray read_int]

theorem read_step_covered (value : ValueCodec E) (s : ReductionStep E)
    (h : value.Covers (Coefficients.step s)) (bound : s.index < arity) :
    readReductionStep value arity (reductionStep value s) = .ok s := by
  simp only [Coefficients.step, ValueCodec.covers_append] at h
  simp [readReductionStep, reductionStep, tuple, Json.getArr_arr, bind, Except.bind,
    pure, Except.pure, index, bound, read_poly_covered value s.next h.1,
    read_remainder_covered value s.witness h.2]

theorem read_reduction_covered (value : ValueCodec E) (r : Reduction E)
    (h : value.Covers (Coefficients.reduction r))
    (bound : ∀ s ∈ r.steps, s.index < arity) :
    readReduction value arity (reduction value r) = .ok r := by
  simp only [Coefficients.reduction, ValueCodec.covers_append,
    ValueCodec.covers_flatMap] at h
  have steps := read_list_of (reductionStep value) (readReductionStep value arity) r.steps
    (fun s hs => read_step_covered value s (h.1 s hs) (bound s hs))
  simp [readReduction, reduction, tuple, Json.getArr_arr, bind, Except.bind,
    pure, Except.pure, steps, read_poly_covered value r.result h.2]

theorem read_preparation_covered (value : ValueCodec E) (r : QueryReduction E)
    (h : value.Covers (Coefficients.preparation r))
    (bound : ∀ s ∈ r.steps, s.index < arity) :
    readPreparation value arity (preparation value r) = .ok r := by
  simp only [Coefficients.preparation, ValueCodec.covers_flatMap] at h
  have steps := read_list_of (reductionStep value) (readReductionStep value arity) r.steps
    (fun s hs => read_step_covered value s (h s hs) (bound s hs))
  simp [readPreparation, preparation, steps, bind, Except.bind, pure, Except.pure]

/-- Exact stored contexts required by one node, in wire order. -/
@[expose] def nodeContexts (n : Node E Ctx) : List Ctx :=
  n.context :: n.moments.toList.map (fun c => c.context)

/-- Partial readers need cover only the literal fields of this node. Matrix
dimensions and reduction indices retain their independent parser checks. -/
theorem read_node_covered (value : ValueCodec E) (context : ValueCodec Ctx)
    (n : Node E Ctx) (hv : value.Covers (Coefficients.node n))
    (hc : context.Covers (nodeContexts n)) (shape : Shape n) :
    readNode value context (node value context n) = .ok n := by
  simp only [Coefficients.node, ValueCodec.covers_append, ValueCodec.covers_flatMap] at hv
  have ctx := hc n.context (by simp [nodeContexts])
  have moments := read_vector_of (tarski value context) (readTarski value context) n.moments
    (fun c h => read_tarski_covered value context c (hv.1.1.2 c h)
      (hc c.context (by
        simp only [nodeContexts, List.mem_cons, List.mem_map]
        exact Or.inr ⟨c, h, rfl⟩)))
  have reductions := read_vector_of (option (reduction value))
    (readOption (readReduction value n.queries.length)) n.reductions
    (fun r hr => read_option_of _ _ r
      (fun t ht => read_reduction_covered value t (hv.1.2 r hr t (by simpa using ht))
        (shape.reductions r hr t ht)))
  have preparation := read_option_of (Codec.preparation value)
    (readPreparation value n.queries.length) n.preparation
    (fun t ht => read_preparation_covered value t (hv.2 t (by simpa using ht))
      (shape.preparation t ht))
  simp [readNode, node, tuple, Json.getArr_arr, bind, Except.bind, pure, Except.pure,
    ctx, read_poly_covered value n.head hv.1.1.1.1.1.1,
    read_endpoint_covered value n.lower hv.1.1.1.1.1.2,
    read_endpoint_covered value n.upper hv.1.1.1.1.2,
    read_list_of (poly value) (readPoly value) n.queries
      (fun p hp => read_poly_covered value p (hv.1.1.1.2 p hp)),
    read_system n.system shape.rows shape.columns, reductions, preparation, moments,
    read_basis n.basis shape.rankRows shape.rankCols]

end Hex.SignDet.Codec
