/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso

/-!
Stage-decomposition profiler for the canonicalization pipeline:
`hexgraphiso_profile [stage]` times one pipeline stage in a
data-dependent loop and prints nanoseconds per iteration, for the
paley61, kneser72, and circulant64 instances.

Stages: `run` (transcribed search), `pass1` (producer search),
`produce` (both producer passes), `ckey` (one trusted `checkKey`
replay), `ccanon` (one `checkCanon`),
`canon` (the fast public tier), `canonchecked` (the full
certificate-checked pipeline), `stats` (work counters, no timing). No
argument runs every stage.

Methodology notes (hard-won):
- Never measure with `lake env lean` `#eval`: the interpreter is
  25-30× slower than compiled code, uniformly.
- Loop bodies take data-dependent inputs (two relabelled variants
  indexed by the running accumulator) so the compiler cannot hoist the
  pure call; per-iteration times must replicate across iteration
  counts (checked by the `--check` flag of the cactus sweep, and by
  running a stage at two counts here).
-/

open Hex.GraphIso Hex.GraphIso.Nauty

private def rot (n : Nat) (h : 0 < n) : Label n :=
  ((Perm.ofVector? (Vector.ofFn fun i =>
    ⟨(i.val + 1) % n, Nat.mod_lt _ h⟩)).getD (Perm.id n)).toLabel

/-- One profiling instance: the graph and its rotation relabelling. -/
private structure Inst (n : Nat) where
  name : String
  g0 : Colored n 1
  g1 : Colored n 1

private def mkInst {n : Nat} (name : String) (G : Hex.Graph n) (h : 0 < n) :
    Inst n :=
  let g0 := Families.plain G h
  { name, g0, g1 := g0.relabel (rot n h) }

private def countAutom : CertNode → Nat
  | .leaf | .codePrune => 0
  | .autom _ _ => 1
  | .node cs => cs.foldl (fun a c => a + countAutom c) 0

/-- Time `iters` data-dependent evaluations; ns per iteration. -/
private def timeLoop (iters : Nat) (act : Nat → Nat) : IO Nat := do
  let mut sink := 0
  let t0 ← IO.monoNanosNow
  for _ in [0 : iters] do
    sink := sink + act sink
  let t1 ← IO.monoNanosNow
  if sink == 42424242424242 then IO.eprintln "(unreachable)"
  return (t1 - t0) / iters

private def stageIters : String → Nat
  | "run" => 2000
  | "ckey" | "ccanon" => 200
  | "pass1" | "produce" => 60
  | _ => 40

private def runStage {n : Nat} (inst : Inst n) (stage : String)
    (hn : 0 < n) : IO Unit := do
  let pick (i : Nat) : Colored n 1 := if i % 2 == 0 then inst.g0 else inst.g1
  let iters := stageIters stage
  -- pre-produce fixed certificates for the replay stages
  let certs (G : Colored n 1) : CertNode × Key :=
    (certifyKey? G).getD (.leaf, ⟨[], []⟩)
  let (c0, b0) := certs inst.g0
  let (c1, b1) := certs inst.g1
  let ns ← match stage with
    | "run" => timeLoop iters fun i => (runColored (pick i)).numnodes
    | "pass1" => timeLoop iters fun i =>
        let G := pick i
        (searchNodeAutom { n := n, g := rowsOf G } 100 n 1
          (initialPartition G).1 (initPtn n (n + 2) (initialPartition G).2)
          (initActive (initialPartition G).2)
          (initialPartition G).2.length none
          (AutState.init n)).1.key.codes.length
    | "produce" => timeLoop iters fun i =>
        match produceCand (pick i) none with
        | some (c, _) => c.size
        | none => 0
    | "ckey" => timeLoop iters fun i =>
        if i % 2 == 0 then
          (if checkKey inst.g0 c0 b0 then 1 else 0)
        else
          (if checkKey inst.g1 c1 b1 then 1 else 0)
    | "ccanon" => timeLoop iters fun i =>
        if i % 2 == 0 then
          (match checkCanon inst.g0 c0 b0 (runColored inst.g0).canonlab with
            | some r => (rowsOf r.form).size | none => 0)
        else
          (match checkCanon inst.g1 c1 b1 (runColored inst.g1).canonlab with
            | some r => (rowsOf r.form).size | none => 0)
    | "canonchecked" => timeLoop iters fun i =>
        (rowsOf (canonicalizeChecked (pick i)).form).size
    | "stats" => do
        let r := runColored inst.g0
        IO.println s!"  {inst.name} stats: nauty-nodes={r.numnodes} \
          cert-records={c0.size} autom-records={countAutom c0} \
          key-codes={b0.codes.length}"
        pure 0
    | _ => timeLoop iters fun i =>
        (rowsOf (canonicalize (pick i)).form).size
  unless stage == "stats" do
    IO.println s!"  {inst.name} {stage}: {ns / 1000}us/iter ({iters} iters)"

private def stages : List String :=
  ["run", "pass1", "produce", "ckey", "ccanon", "canon",
   "canonchecked", "stats"]

def main (args : List String) : IO Unit := do
  let todo := match args with
    | [] => stages
    | l => l
  let paley : Inst 61 := mkInst "paley61" (Families.paley 61) (by omega)
  let kneser : Inst 21 := mkInst "kneser72" (Families.kneser 7 2) (by decide)
  let circ : Inst 64 := mkInst "circulant64" (Families.circulant 64 [1, 2])
    (by omega)
  for stage in todo do
    IO.println s!"== {stage}"
    runStage paley stage (by omega)
    runStage kneser stage (by decide)
    runStage circ stage (by omega)
