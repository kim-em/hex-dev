/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealFormula
import Lean.Data.Json

/-! Versioned, exact fixtures for tree/list decoding, evaluation and DAG sharing. -/

namespace Hex.RealFormula.Emit

open Lean

private def obj := Json.mkObj
private def arr (xs : List Json) : Json := .arr xs.toArray
private def cmp : Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
private def quant : Quantifier → String
  | .existsReal => "exists" | .forallReal => "forall"
private def rat (q : Rat) : Json := arr [toJson q.num, toJson q.den]
private def terms (ts : MvPoly.Kernel.PolyList Int) : Json :=
  arr (ts.map fun t => arr [toJson t.1, toJson t.2])

private def body : Kernel.Body → Json
  | .atom p c => obj [("op", toJson "atom"), ("terms", terms p), ("cmp", toJson (cmp c))]
  | .tt => obj [("op", toJson "true")]
  | .ff => obj [("op", toJson "false")]
  | .not p => obj [("op", toJson "not"), ("arg", body p)]
  | .and p q => obj [("op", toJson "and"), ("left", body p), ("right", body q)]
  | .or p q => obj [("op", toJson "or"), ("left", body p), ("right", body q)]

private def names (n : Nat) : Json := toJson ((List.range n).map fun i => s!"a{i}")
private def emit (id kind : String) (fields : List (String × Json)) : IO Unit :=
  IO.println (obj ([("schema", toJson "hex-real-formula"), ("version", toJson (1 : Nat)),
    ("library", toJson "HexRealFormula"), ("profile", toJson "ci"),
    ("seed", toJson (0 : Nat)), ("case", toJson id), ("kind", toJson kind)] ++ fields)).compress

private def drops : (n : Nat) → QF n → Json
  | 0, _ => arr []
  | m + 1, p => arr ((List.finRange (m + 1)).map fun i =>
      toJson ((p.drop? i).map fun q => body q.kernelBody))

private def operations {n : Nat} (p : QF n) : Json := obj [
  ("nodes", toJson p.nodeCount), ("polynomials", toJson p.polys.length),
  ("support", toJson (p.support.map (·.val))),
  ("degrees", toJson ((List.finRange n).map p.degree)),
  ("nnf", body p.nnf.kernelBody), ("lift", body p.lift.kernelBody),
  ("drops", drops n p)]

private def emitRename {n m : Nat} (id : String) (p : QF n) (σ : Fin n → Fin m) : IO Unit :=
  emit id "rename" [("arity", toJson n), ("freeOrder", names n),
    ("body", body p.kernelBody), ("targetArity", toJson m),
    ("map", toJson ((List.finRange n).map fun i => (σ i).val)),
    ("result", body (p.rename σ).kernelBody)]

private def emitQF (id : String) (p : Kernel.QF) (samples : List (List Rat)) : IO Unit := do
  let decoded : Option (QF p.arity) := QF.ofKernel? p
  let normalized := decoded.map (fun p => body p.kernelBody)
  let values := samples.map fun qs =>
    let q : Fin p.arity → Rat := fun i => qs[i.val]!
    obj [("point", arr (qs.map rat)), ("value", toJson (decoded.map (·.evalRat q))),
      ("kernelValue", toJson (p.validate.map (·.evalRat q)))]
  emit id "qf" [("wireVersion", toJson p.version), ("arity", toJson p.arity),
    ("freeOrder", names p.arity), ("body", body p.body),
    ("normalized", toJson normalized), ("samples", arr values),
    ("operations", toJson (decoded.map operations))]

private def node : Kernel.Node → Json
  | .atom p c => body (.atom p c)
  | .tt => body .tt | .ff => body .ff
  | .input i => obj [("op", toJson "input"), ("id", toJson i)]
  | .not i => obj [("op", toJson "not"), ("arg", toJson i)]
  | .and i j => obj [("op", toJson "and"), ("left", toJson i), ("right", toJson j)]
  | .or i j => obj [("op", toJson "or"), ("left", toJson i), ("right", toJson j)]

private def emitDag (id : String) (d : Kernel.Dag) (inputs : Array (QF d.arity)) : IO Unit := do
  let decoded := d.decode inputs
  emit id "dag" [("wireVersion", toJson d.version), ("arity", toJson d.arity),
    ("freeOrder", names d.arity), ("nodes", .arr (d.nodes.map node)),
    ("inputs", .arr (inputs.map fun p => body p.kernelBody)), ("root", toJson d.root),
    ("decoded", toJson (decoded.map fun p => body p.kernelBody)),
    ("dagNodes", toJson d.nodes.size), ("treeNodes", toJson (decoded.map (·.nodeCount)))]

private def emitPrenex {n : Nat} (id : String) (p : Prenex n)
    (boundNames : List String) : IO Unit := do
  let k := p.toKernel
  emit id "prenex" [("arity", toJson n), ("freeOrder", names n),
    ("prefix", toJson (k.prefix.map quant)), ("binderNames", toJson boundNames),
    ("matrixArity", toJson k.matrix.arity), ("body", body k.matrix.body),
    ("roundTrip", toJson (Prenex.ofKernel? k == some p))]

private def run : IO Unit := do
  emitQF "arity-zero" ⟨1, 0, .atom [([], -3)] .lt⟩ [[]]
  emitQF "unused-variables" ⟨1, 3, .atom [([0, 0, 0], 7)] .ge⟩ [[0, 2, -9]]
  emitQF "duplicates-cancel" ⟨1, 2, .atom [([2, 0], 3), ([2, 0], -3), ([0, 0], 0)] .eq⟩
    [[1/2, -2/3], [0, 0]]
  emitQF "unsorted-terms" ⟨1, 2, .atom [([2, 0], 1), ([0, 0], -2), ([0, 1], 3)] .le⟩
    [[1/2, -1/3], [2, 1]]
  for c in [Cmp.eq, .ne, .lt, .le, .gt, .ge] do
    emitQF ("comparison-" ++ cmp c) ⟨1, 1, .atom [([1], 1)] c⟩ [[-1/2], [0], [1/2]]
  emitQF "boolean-boundaries" ⟨1, 1, .or (.and (.atom [([1], 1)] .gt)
      (.atom [([1], 2), ([0], -1)] .le)) (.not (.atom [([1], 1)] .ne))⟩
    [[-1/2], [0], [1/4], [1/2], [3/4]]
  emitQF "negative-denominator" ⟨1, 1, .atom [([1], -3), ([0], -2)] .lt⟩ [[1/(-2)], [-1], [0]]
  emitQF "malformed-zero-term" ⟨1, 1, .atom [([0, 0], 0)] .eq⟩ [[0]]
  emitQF "malformed-unused-branch" ⟨1, 1, .or .tt (.atom [([], 0)] .eq)⟩ [[0]]
  emitQF "unknown-wire-version" ⟨2, 0, .tt⟩ [[]]
  emitRename "rename-nonadjacent" (.atom ⟨MvPoly.X 0 ^ 2 - MvPoly.X 2, .lt⟩ : QF 3)
    (fun i => (#[2, 1, 0] : Array (Fin 3))[i.val]!)
  emitRename "rename-zero-arity" (QF.tt : QF 0) (Fin.elim0 : Fin 0 → Fin 0)
  emitRename "rename-collision" (.atom ⟨MvPoly.X 0 - MvPoly.X 1, .eq⟩ : QF 2)
    (fun _ => (0 : Fin 1))
  emitDag "sharing" ⟨1, 1, #[.input 0, .not 0, .and 0 1, .or 2 2], 3⟩
    #[.atom ⟨MvPoly.X 0, .lt⟩]
  emitDag "empty-dag" ⟨1, 0, #[], 0⟩ #[]
  emitDag "self-reference" ⟨1, 0, #[.not 0], 0⟩ #[]
  emitDag "bad-unreachable-input" ⟨1, 0, #[.tt, .input 1], 0⟩ #[.tt]
  emitDag "bad-unreachable-atom" ⟨1, 1, #[.tt, .atom [([], 0)] .eq], 0⟩ #[]
  emitPrenex "alternation" (Prenex.quant .forallReal (.quant .existsReal
    (.matrix (.atom ⟨MvPoly.X 0 - MvPoly.X 1, .eq⟩))) : Prenex 0) ["x", "y"]
  emitPrenex "shadowed-binder-names" (Prenex.quant .existsReal (.quant .forallReal
    (.matrix (.atom ⟨MvPoly.X 0 - MvPoly.X 1 + MvPoly.X 2, .ge⟩))) : Prenex 1) ["x", "x"]
  emitPrenex "empty-prefix" (Prenex.matrix .tt : Prenex 0) []

end Hex.RealFormula.Emit

def main : IO Unit := Hex.RealFormula.Emit.run
