/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiteralSupport
public import HexSignDet.Codec
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Node

public section

namespace Hex.RealClosure.Tower
open Lean SignDet

@[simp] theorem Literal.Supported.codec_array {A : Type} (write : A → Json)
    (h : ∀ a, Supported (write a)) (xs : Array A) : Supported (Codec.array write xs) :=
  Supported.array_map write xs (fun a _ => h a)

@[simp] theorem Literal.Supported.codec_list {A : Type} (write : A → Json)
    (h : ∀ a, Supported (write a)) (xs : List A) : Supported (Codec.list write xs) :=
  Supported.list_map write xs (fun a _ => h a)

@[simp] theorem Literal.Supported.codec_option {A : Type} (write : A → Json)
    (h : ∀ a, Supported (write a)) (x : Option A) : Supported (Codec.option write x) := by
  cases x <;> simp [Codec.option, Supported.arr_iff, h]

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable (value : ValueCodec E) (hv : ∀ a, Literal.Supported (value.encode a))

include hv

@[simp] theorem Literal.Supported.poly (p : DensePoly E) :
    Supported (Codec.poly value p) := by
  simp [Codec.poly, hv]

@[simp] theorem Literal.Supported.endpoint (e : Endpoint E) :
    Supported (Codec.endpoint value e) := by
  cases e <;> simp [Codec.endpoint, Supported.arr_iff, hv]

@[simp] theorem Literal.Supported.remainder (s : RemainderStep E) :
    Supported (Codec.remainder value s) := by
  simp [Codec.remainder, Supported.arr_iff, Supported.poly value hv, hv]

@[simp] theorem Literal.Supported.terminal (t : E × DensePoly E) :
    Supported (Codec.terminal value t) := by
  simp [Codec.terminal, Supported.arr_iff, Supported.poly value hv, hv]

@[simp] theorem Literal.Supported.chain (c : SignedRemainderChain E) :
    Supported (Codec.chain value c) := by
  simp [Codec.chain, Supported.arr_iff, Supported.poly value hv,
    Supported.remainder value hv, Supported.terminal value hv]

omit hv in
@[simp] theorem Literal.Supported.matrix (a : Matrix Int n m) :
    Supported (Codec.encodeMatrix a) := by
  simp [Codec.encodeMatrix, Codec.array, Supported.arr_iff]

variable (context : ValueCodec Ctx) (hc : ∀ a, Literal.Supported (context.encode a))

include hc in
@[simp] theorem Literal.Supported.tarski (c : TarskiCertificate E E Ctx) :
    Supported (Codec.tarski value context c) := by
  simp [Codec.tarski, Supported.arr_iff, Supported.poly value hv,
    Supported.endpoint value hv, Supported.chain value hv, hc]

@[simp] theorem Literal.Supported.reductionStep (s : ReductionStep E) :
    Supported (Codec.reductionStep value s) := by
  simp [Codec.reductionStep, Supported.arr_iff, Supported.poly value hv,
    Supported.remainder value hv]

@[simp] theorem Literal.Supported.reduction (r : Reduction E) :
    Supported (Codec.reduction value r) := by
  simp [Codec.reduction, Supported.arr_iff, Supported.reductionStep value hv,
    Supported.poly value hv]

@[simp] theorem Literal.Supported.preparation (r : QueryReduction E) :
    Supported (Codec.preparation value r) := by
  simp [Codec.preparation, Supported.reductionStep value hv]

omit hv in
@[simp] theorem Literal.Supported.system (s : System n) :
    Supported (Codec.system s) := by
  simp [Codec.system, Supported.arr_iff, Supported.matrix]

omit hv in
@[simp] theorem Literal.Supported.basis (b : Matrix.RankCert Int n m) :
    Supported (Codec.basis b) := by
  simp [Codec.basis, Supported.arr_iff, Supported.matrix]

include hc in
@[simp] theorem Literal.Supported.node (n : Node E Ctx) :
    Supported (Codec.node value context n) := by
  simp [Codec.node, Supported.arr_iff, Supported.poly value hv,
    Supported.endpoint value hv, Supported.tarski value hv context hc,
    Supported.reduction value hv, Supported.preparation value hv, hc]

include hc in
@[simp] theorem Literal.Supported.entry (e : Dag.Entry E Ctx) :
    Supported (Codec.entry value context e) := by
  simp [Codec.entry, Supported.arr_iff, Supported.node value hv context hc]

include hc in
@[simp] theorem Literal.Supported.graph (d : Dag E Ctx) :
    Supported (Codec.graph value context d) := by
  simp [Codec.graph, Supported.arr_iff, Supported.entry value hv context hc]

end Hex.RealClosure.Tower
