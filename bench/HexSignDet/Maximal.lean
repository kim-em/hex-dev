/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Input
import HexPolyFast.Interpolation
import HexPolyFast.Karatsuba
import Lean.Data.Json

namespace Hex.SignDetBench
open Hex.SignDet Hex.DensePoly

/-- Every ternary word is realized once at a distinct integer root. Word
count/shape checks are sanity checks on `words`; root distinctness comes from
the consecutive integer points. Degree and direct evaluation check the complete
root/sign oracle independently of interpolation and Tarski replay. -/
def buildMaximal (s : Nat) : Except String Input := do
  let conditions := (words [-1, 0, 1] s).toArray
  if conditions.size != 3^s || !decide conditions.toList.Nodup ||
      conditions.any (fun word => word.length != s || word.any (fun v => v < -1 || 1 < v)) then
    throw "invalid ternary word inventory"
  let points : Array Rat := (Array.range conditions.size).map fun (i : Nat) => (i : Rat)
  let some plan := InterpPlan.build? (karatsubaPlan 2) points |
    throw "interpolation plan failed"
  let some built := plan.evalPlan.cachedNode | throw "point product is missing"
  let p := built.1
  let qs ← (List.range s).mapM fun j => do
    let some q := plan.interpolate? (conditions.map fun word => ((word[j]! : Int) : Rat)) |
      throw s!"query interpolation failed at coordinate {j}"
    pure q
  if p.natDegree != 3^s then throw "point product has the wrong degree"
  for i in [:conditions.size] do
    if p.eval points[i]! != 0 then throw s!"head does not vanish at root {i}"
    for j in [:s] do
      if (qs.getD j 0).eval points[i]! != ((conditions[i]![j]! : Int) : Rat) then
        throw s!"wrong query value at root {i}, coordinate {j}"
  let some domain := Sturm.prepare Sturm.orderSign p .negInf .posInf |
    throw "invalid maximal root domain"
  let .ok reduced := buildPrepared (10377 : Nat) domain qs |
    throw "reduced table construction failed"
  let .ok direct := buildPrepared (10377 : Nat) domain qs false |
    throw "unreduced table construction failed"
  let .ok full := referencePrepared (10377 : Nat) domain qs |
    throw "full reference construction failed"
  let expected := conditions.toList.map fun word => (word, (1 : Int))
  if entries reduced.val.node.system != expected then throw "wrong reduced complete table"
  if entries direct.val.node.system != expected then throw "wrong unreduced complete table"
  if entries full.system != expected then throw "wrong full reference complete table"
  if full.size != 3^s then throw "wrong reference column count"
  if !full.check Sturm.orderSign 10377 p .negInf .posInf qs then
    throw "full reference replay failed"
  let graph := Dag.encode reduced.val
  if !graph.check Sturm.orderSign 10377 p .negInf .posInf qs then throw "graph replay failed"
  return ⟨p, qs, some domain, some reduced.val, some graph⟩

private def intBits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1
private def ratBits (q : Rat) : Nat := max (intBits q.num) (q.den.log2 + 1)
private def polyBits (p : DensePoly Rat) : Nat := p.toArray.foldl (fun n q => max n (ratBits q)) 0

/-- Inspect maximal support using fixed small inputs. Sizes and stored bits
are observations of the actual certificates, not peak allocation/bit counts or
a complexity measurement. Every line is flushed before the next input starts. -/
def inspectMaximal : IO UInt32 := do
  for s in #[1, 2, 3] do
    let input ← match buildMaximal s with
      | .ok input => pure input
      | .error message => throw (IO.userError s!"maximal input {s}: {message}")
    let some tree := input.tree | throw (IO.userError "missing maximal tree")
    let some graph := input.graph | throw (IO.userError "missing maximal graph")
    let ns := nodes tree
    let moments := ns.foldl (fun n node => n + node.size) 0
    let maxColumns := ns.foldl (fun n node => max n node.size) 0
    let witnessBits := ns.foldl (fun n node => node.moments.toList.foldl (fun n cert =>
      cert.remainders.chain.foldl (fun n p => max n (polyBits p)) n) n) 0
    unless tree.node.system.support.length == 3^s && maxColumns == 3^s do
      throw (IO.userError s!"maximal support inventory failed at {s}")
    IO.println <| (Lean.Json.mkObj [
      ("family", Lean.toJson "maximal-ternary-support"), ("queries", Lean.toJson s),
      ("rootCount", Lean.toJson (3^s)), ("realizedSupport", Lean.toJson tree.node.system.support.length),
      ("headDegree", Lean.toJson input.head.natDegree),
      ("queryDegree", Lean.toJson (input.queries.foldl (fun n p => max n p.natDegree) 0)),
      ("headCoefficientBits", Lean.toJson (polyBits input.head)),
      ("queryCoefficientBits", Lean.toJson (input.queries.foldl (fun n p => max n (polyBits p)) 0)),
      ("remainderCoefficientBits", Lean.toJson witnessBits),
      ("querySlots", Lean.toJson moments), ("maxColumns", Lean.toJson maxColumns),
      ("treeNodes", Lean.toJson ns.length), ("graphNodes", Lean.toJson graph.entries.size),
      ("graphEdges", Lean.toJson (graph.entries.foldl (fun n e => n + if e.children.isSome then 2 else 0) 0)),
      ("inputHash", Lean.toJson (hash input).toNat),
      ("tableHash", Lean.toJson (hash (entries tree.node.system)).toNat)]).compress
    (← IO.getStdout).flush
  return 0

end Hex.SignDetBench
