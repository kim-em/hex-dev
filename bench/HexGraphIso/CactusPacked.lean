/-
Scratch measurement driver for the packed vertex-set search: times
`Nauty.runColored` against the nauty comparator on the cactus corpus,
importing only the search modules so the measurement does not wait on
the theory port. Emits the same JSON lines as `hexgraphiso_cactus`.
-/

import HexGraphIso.Nauty.Search
import HexGraphIso.Families
import HexGraphIso.Random
import Hex.BenchOracle.Nauty

namespace Hex.GraphIsoCactusPacked

open Hex.GraphIso

private def reps : Nat := 5

private structure Inst where
  family : String
  name : String
  packed : (n : Nat) × Colored n 1

private def inst (family name : String) {n : Nat} (G : Graph n)
    (h : 0 < n) : Inst :=
  { family, name, packed := ⟨n, Graph.singleColor G h⟩ }

private def digest {n : Nat} (r : Nauty.RunResult n) : Nat :=
  r.canong.foldl (fun a s => a + s.toNat % 1000003) 0 +
    r.canonlab.foldl (· + ·) 0

private def adjStrings {n : Nat} (G : Colored n 1) : List String :=
  (List.finRange n).map fun i => String.ofList <|
    (List.finRange n).map fun j => if G.graph.adj i j then '1' else '0'

initialize sinkRef : IO.Ref Nat ← IO.mkRef 0

@[noinline] def blackBox (a : Nat) : IO Unit :=
  sinkRef.modify (· ^^^ a)

private def timeMinNs (act : Unit → IO Nat) : IO Nat := do
  let w0 ← IO.monoNanosNow
  blackBox (← act ())
  let w1 ← IO.monoNanosNow
  let effReps := if w1 - w0 > 1000000000 then 1 else reps
  let mut best : Nat := 0
  for _ in [0 : effReps] do
    let t0 ← IO.monoNanosNow
    blackBox (← act ())
    let t1 ← IO.monoNanosNow
    if best == 0 || t1 - t0 < best then
      best := t1 - t0
  return best

private def runInst (i : Inst) : IO Unit := do
  let ⟨n, G⟩ := i.packed
  let fastNs ← timeMinNs fun _ => pure (digest (Nauty.runColored G))
  let colors := List.replicate n 0
  let adj := adjStrings G
  let nautyNs ← timeMinNs fun _ => do
    let r ← Hex.BenchOracle.Nauty.canon n 1 colors adj
    pure (r.lab.foldl (· + ·) 0)
  let r := Nauty.runColored G
  let nr ← Hex.BenchOracle.Nauty.canon n 1 colors adj
  let agree := r.canonlab == nr.lab && r.numnodes == nr.nodes
  IO.println <| "{\"family\": \"" ++ i.family ++ "\", \"name\": \"" ++
    i.name ++ s!"\", \"n\": {n}, \"fast_ns\": {fastNs}" ++
    s!", \"nauty_ns\": {nautyNs}, \"nodes\": {r.numnodes}, \"agree\": {agree}}"
  (← IO.getStdout).flush

private def instances : List Inst := Id.run do
  let mut out : List Inst := []
  for n in [8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 96, 128, 160,
      192, 224, 255] do
    if h : 0 < n then
      out := inst "circulant-12" s!"circulant{n}-1-2"
        (Families.circulant n [1, 2]) h :: out
  for n in [17, 25, 33, 41, 49, 57, 65, 97, 129, 161, 193, 225] do
    if h : 0 < n then
      out := inst "circulant-1248" s!"circulant{n}-1-2-4-8"
        (Families.circulant n [1, 2, 4, 8]) h :: out
  for a in [3, 4, 5, 6, 7, 8, 10, 12, 14, 15] do
    if h : 0 < a * a then
      out := inst "grid" s!"grid{a}x{a}" (Families.grid a a) h :: out
  for d in [3, 4, 5, 6, 7] do
    if h : 0 < 2 ^ d then
      out := inst "hypercube" s!"q{d}" (Families.hypercube d) h :: out
  for m in [5, 6, 7, 8, 9, 12, 15, 17, 20, 22] do
    if h : 0 < Families.choose m 2 then
      out := inst "kneser" s!"kneser{m}-2" (Families.kneser m 2) h :: out
    if h : 0 < Families.choose m 2 then
      out := inst "johnson" s!"johnson{m}-2" (Families.johnson m 2) h :: out
  for q in [13, 17, 29, 37, 41, 53, 61, 73, 89, 113, 149, 181, 229] do
    if h : 0 < q then
      out := inst "paley" s!"paley{q}" (Families.paley q) h :: out
  for m in [5, 9, 13] do
    if h : 0 < m * m then
      out := inst "latin" s!"latin{m}" (Families.latinSquare m) h :: out
  let mut g : Random.Gen := ⟨Random.seed1⟩
  for n in [10, 14, 18, 22, 26, 30, 36, 42, 48, 56, 64, 80, 96, 128,
      160, 192, 224, 255] do
    let (mask, g') := Random.gnpMask g n
    g := g'
    if h : 0 < n then
      out := inst "random" s!"gnp{n}-seed1"
        (Graph.ofRel fun i j =>
          decide (i.val < j.val) &&
            mask.testBit (i.val * (n - 1) - i.val * (i.val - 1) / 2 +
              (j.val - i.val - 1)))
        h :: out
  return out.reverse

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  for i in instances do
    if only.all (fun f => f == i.family || f == i.name) then
      runInst i
  return 0

end Hex.GraphIsoCactusPacked

def main (args : List String) : IO UInt32 := Hex.GraphIsoCactusPacked.main args
