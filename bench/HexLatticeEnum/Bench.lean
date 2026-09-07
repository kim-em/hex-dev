/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexLatticeEnum
import LeanBench
import Lean.Data.Json

/-!
Exact lattice search benchmarks. Fixed family registrations are latency and
expected-output anchors, not a polynomial complexity claim in rank. The separate
rectangular ladder fixes rank, radius, coefficients and visited tree, varying only
ambient dimension: preparation, reconstruction and replay then take linear work.
Input construction, initial candidates and already-generated certificates are
hoisted. Optimization, tie traversal, certificate packaging and replay have separate
registrations; the tie traversal itself allocates the exhaustive tree.
-/

namespace Hex.LatticeEnumBench
open Hex Hex.LatticeEnum Lean

structure Input where
  family : String
  name : String
  n : Nat
  m : Nat
  basis : Basis n m
  original : Basis n m
  reduced : Bool
  target : Vector Rat m
  radius : Rat
  data : Prepared basis target
  mode : SearchMode
  seed : Point n m
  first : Traversal n m
  run : OptimumRun n m
  certificate : OptimumCertificate n m
  encoded : String

instance : Hashable Input where
  hash i := hash (i.family, i.name, i.basis.rows.rows.toList.map Vector.toList,
    i.target.toList.map toString, toString i.radius)

private def digestPoints (ps : List (Point n m)) : UInt64 :=
  hash (ps.map fun q => (q.coefficients.toList, q.ambient.toList, toString q.distanceSq))

private def digestTree : Tree → UInt64
  | .empty => 0
  | .leaf => 1
  | .node interval children => children.attach.foldl
      (fun h child => mixHash h (mixHash (hash child.val.1) (digestTree child.val.2))) (hash (interval.lo, interval.hi))
termination_by tree => sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem child.property
  have hp : sizeOf child.val = 1 + sizeOf child.val.1 + sizeOf child.val.2 := by
    cases child.val
    rfl
  simp only [Tree.node.sizeOf_spec]
  omega

private def digest (run : Traversal n m) : UInt64 :=
  mixHash (digestPoints run.state.points) (hash (toString run.state.radius,
    run.state.counts.nodes, run.state.counts.answers, run.state.counts.certificateNodes,
    run.pending.length, run.tree.map digestTree,
    run.state.incumbent.map (fun q => digestPoints [q])))

private def digestCertificate (cert : OptimumCertificate n m) : UInt64 :=
  let c := cert.enumeration
  mixHash (digestPoints (cert.candidate :: c.points)) <| mixHash (digestTree c.tree) <|
    hash (c.rows.rows.toList.map Vector.toList, c.forward.rows.toList.map Vector.toList,
      c.reverse.rows.toList.map Vector.toList,
      c.data.mu.rows.toList.map (fun v => v.toList.map toString),
      c.data.orthogonal.rows.toList.map (fun v => v.toList.map toString),
      c.data.norms.toList.map toString, c.data.projection.toList.map toString,
      c.data.residual.toList.map toString)

private def make (family name : String) (rows : Matrix Int n m) (target : Vector Rat m)
    (radius : Rat) (mode : SearchMode := .closest) (reduce : Bool := false) : Option Input := do
  let original ← ofMatrix? rows
  let b := if reduce then (lllPreprocess original).working else original
  let p := prepare b target
  let seed ← if mode == .shortest then shortestSeed b else
    some (point b target (nearestPlane p n (Nat.le_refl n) 0))
  let first := traverse b target p {} mode n (Nat.le_refl n) 0 0
    { radius := seed.distanceSq, incumbent := some seed }
  let incumbent := first.state.incumbent.getD seed
  let ties := traverse b target p {} .ball n (Nat.le_refl n) 0 0
    { radius := incumbent.distanceSq, incumbent := some incumbent, counts := first.state.counts }
  let run : OptimumRun n m := ⟨incumbent, ties, .ties⟩
  let cert := optimumCertificate b p run
  return ⟨family, name, n, m, b, original, reduce, target, radius, p, mode, seed, first, run, cert, encodeOptimumCertificate cert⟩

private def require (input : Option Input) : IO Input :=
  match input with
  | some i => pure i
  | none => throw (IO.userError "invalid lattice benchmark input")

private def fixtures : IO (Array Input) := do
  let mut inputs := #[]
  for n in [2, 4, 6] do
    for r in [1, 2, 4] do
      inputs := inputs.push (← require (make "rank-radius" s!"rank-{n}-radius-{r}"
        (Matrix.identity n) 0 r .shortest))
  for shear in [0, 10, 100] do
    for reduce in [false, true] do
      inputs := inputs.push (← require (make "basis-quality" s!"shear-{shear}-lll-{reduce}"
        (Matrix.ofRows #v[#v[1, shear], #v[0, 1]]) #v[1/2, 1/3] 2 .closest reduce))
  for bits in [8, 64, 256] do
    let h : Rat := (2 ^ bits : Nat)
    inputs := inputs.push (← require (make "coefficient-height" s!"target-bits-{bits}"
      (Matrix.identity 2) #v[h + 1/2, -h + 1/(h+1)] 2))
    let scale : Int := (2 ^ bits : Nat)
    inputs := inputs.push (← require (make "coefficient-height" s!"basis-bits-{bits}"
      (Matrix.ofRows #v[#v[scale, 0], #v[1, scale]]) #v[h/2, h/3] (h*h)))
  for m in [4, 16, 64] do
    inputs := inputs.push (← require (make "rectangular-target" s!"ambient-{m}"
      (Matrix.ofFn fun (i : Fin 2) (j : Fin m) => if i.val == j.val then 1 else 0)
      (Vector.ofFn fun j => if j.val + 1 == m then 1/2 else 0) (9/4)))
  inputs := inputs.push (← require (make "ties-boundary" "a2-shortest"
    (Matrix.ofRows #v[#v[1, -1, 0], #v[0, 1, -1]]) 0 2 .shortest))
  inputs := inputs.push (← require (make "ties-boundary" "cube-64-ties"
    (Matrix.identity 6) (Vector.replicate 6 (1/2)) (3/2)))
  inputs := inputs.push (← require (make "babai-gap" "integer-least-squares"
    (Matrix.ofRows #v[#v[2, 0], #v[1, 2]]) #v[1, 1] 2))
  inputs := inputs.push (← require (make "certificate-replay" "rank-8-shortest"
    (Matrix.identity 8) 0 2 .shortest))
  return inputs

initialize inputs : IO.Ref (Array Input) ← IO.mkRef (← fixtures)

private def collect (f : Input → UInt64) : IO UInt64 := do
  return (← inputs.get).foldl (fun h i => mixHash h (f i)) 0

private def ball (i : Input) : Traversal i.n i.m :=
  traverse i.basis i.target i.data {} .ball i.n (Nat.le_refl _) 0 0 { radius := i.radius }

private def optimum (i : Input) : Traversal i.n i.m :=
  traverse i.basis i.target i.data {} i.mode i.n (Nat.le_refl _) 0 0
    { radius := i.seed.distanceSq, incumbent := some i.seed }

private def ties (i : Input) : Traversal i.n i.m :=
  traverse i.basis i.target i.data {} .ball i.n (Nat.le_refl _) 0 0
    { radius := i.run.incumbent.distanceSq, incumbent := some i.run.incumbent,
      counts := i.first.state.counts }

private def check (i : Input) : Bool :=
  if i.mode == .shortest then checkShortest i.basis.rows i.certificate
  else checkClosest i.basis.rows i.target i.certificate

private def family (name : String) : IO UInt64 := do
  return (← inputs.get).foldl (fun h i => if i.family == name then mixHash h (digest (ball i)) else h) 0

def runRankRadius (_ : Unit) : IO UInt64 := family "rank-radius"
def runBasisQuality (_ : Unit) : IO UInt64 := family "basis-quality"
def runHeight (_ : Unit) : IO UInt64 := family "coefficient-height"
def runRectangular (_ : Unit) : IO UInt64 := family "rectangular-target"
def runTiesBoundary (_ : Unit) : IO UInt64 := family "ties-boundary"
def runBabaiGap (_ : Unit) : IO UInt64 := family "babai-gap"
def runPreparation (_ : Unit) : IO UInt64 := collect fun i =>
  let p := prepare i.basis i.target
  hash (p.mu.rows.toList.map (fun v => v.toList.map toString),
    p.orthogonal.rows.toList.map (fun v => v.toList.map toString),
    p.norms.toList.map toString, p.projection.toList.map toString, p.residual.toList.map toString)
def runBabai (_ : Unit) : IO UInt64 := collect fun i =>
  digestPoints [point i.basis i.target (nearestPlane i.data i.n (Nat.le_refl _) 0)]
def runOptimum (_ : Unit) : IO UInt64 := collect fun i => digest (optimum i)
def runTies (_ : Unit) : IO UInt64 := collect fun i => digest (ties i)
def runCertificate (_ : Unit) : IO UInt64 := collect fun i =>
  digestCertificate (optimumCertificate i.basis i.data i.run)
def runReplay (_ : Unit) : IO UInt64 := collect fun i => hash (check i)
def runEncode (_ : Unit) : IO UInt64 := collect fun i => hash (encodeOptimumCertificate i.certificate)
def runDecode (_ : Unit) : IO UInt64 := collect fun i =>
  match decodeOptimumCertificate {} i.n i.m i.encoded with
  | .ok c => digestCertificate c
  | .error e => panic! s!"native certificate decode failed: {e}"
def runRetarget (_ : Unit) : IO UInt64 := collect fun i =>
  let p := retarget i.data (i.target.map (- ·))
  hash (p.projection.toList.map toString, p.residual.toList.map toString)
def runLLL (_ : Unit) : IO UInt64 := collect fun i =>
  if i.family == "basis-quality" then
    let c := lllPreprocess i.basis
    hash (c.working.rows.rows.toList.map Vector.toList,
      c.forward.rows.toList.map Vector.toList, c.reverse.rows.toList.map Vector.toList)
  else 0

/-- Fixed expected-output anchors; scientific rank scaling is not inferred from these easy inputs. -/
def config : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 5, minTotalSeconds := 0.01 }

setup_fixed_benchmark runRankRadius where { config with expectedHash := some 0x3cd62cbcc3a35203 }
setup_fixed_benchmark runBasisQuality where { config with expectedHash := some 0x637960186336d7f }
setup_fixed_benchmark runHeight where { config with expectedHash := some 0xf3aa667062250c5f }
setup_fixed_benchmark runRectangular where { config with expectedHash := some 0x9689538617f392b0 }
setup_fixed_benchmark runTiesBoundary where { config with expectedHash := some 0x75263638c431a4ea }
setup_fixed_benchmark runBabaiGap where { config with expectedHash := some 0x953a008173b8fd77 }
setup_fixed_benchmark runPreparation where { config with expectedHash := some 0xdb1a7101f7a4fbf3 }
setup_fixed_benchmark runBabai where { config with expectedHash := some 0xef9d5015141ee921 }
setup_fixed_benchmark runOptimum where { config with expectedHash := some 0xcc8e6c51bcee2464 }
setup_fixed_benchmark runTies where { config with expectedHash := some 0x99cbb544fe20a3d9 }
setup_fixed_benchmark runCertificate where { config with expectedHash := some 0x759e11c2c98b4fbd }
setup_fixed_benchmark runReplay where { config with expectedHash := some 0xa00e7ed5162fb860 }
setup_fixed_benchmark runEncode where { config with expectedHash := some 0xd39f1277cb719f90 }
setup_fixed_benchmark runDecode where { config with expectedHash := some 0x759e11c2c98b4fbd }
setup_fixed_benchmark runRetarget where { config with expectedHash := some 0xd8453db9ef75590a }
setup_fixed_benchmark runLLL where { config with expectedHash := some 0xe5be6555adebc8ff }

/-- Rank two with a fixed nine-point ball and a nonzero off-span target component.
The tree and rational bit lengths are fixed while every ambient scan is linear in `m`.
This family-specific model says nothing polynomial about the rank variable. -/
def prepAmbient (m : Nat) : Option Input :=
  make "rectangular-target" s!"ambient-{m}"
    (Matrix.ofFn fun (i : Fin 2) (j : Fin m) => if i.val == j.val then 1 else 0)
    (Vector.ofFn fun j => if j.val + 1 == m then 1/2 else 0) (9/4)

/-- A nonoptimal Babai seed with a fixed off-span residual. -/
def prepGapAmbient (m : Nat) : Option Input :=
  make "babai-gap" s!"ambient-{m}"
    (Matrix.ofFn fun (i : Fin 2) (j : Fin m) =>
      if j.val == 0 then (if i.val == 0 then 2 else 1)
      else if j.val == 1 && i.val == 1 then 2 else 0)
    (Vector.ofFn fun j => if j.val < 2 then 1 else if j.val + 1 == m then 1/2 else 0) (9/4)

/-- Both input rows are longer than their difference, so shortest search improves its seed. -/
def prepShortAmbient (m : Nat) : Option Input :=
  make "ties-boundary" s!"shortest-ambient-{m}"
    (Matrix.ofFn fun (i : Fin 2) (j : Fin m) =>
      if j.val < 2 then (if i.val == j.val then 2 else 1) else 0) 0 5 .shortest

/-- A fixed nontrivial LLL reduction while ambient dimension grows. -/
def prepShearAmbient (m : Nat) : Option Input :=
  make "basis-quality" s!"lll-ambient-{m}"
    (Matrix.ofFn fun (i : Fin 2) (j : Fin m) =>
      if i.val == j.val then 1 else if i.val == 0 && j.val == 1 then 100 else 0)
    (Vector.ofFn fun j => if j.val + 1 == m then 1/2 else 0) (9/4)

def runAmbient (input : Option Input) : UInt64 :=
  match input with
  | some i => digest (ball i)
  | none => panic! "invalid rectangular benchmark input"

/- Rank two, fixed rational bit lengths, thirteen tree nodes and nine leaves.
Every centre has fixed size and every reconstruction scans m ambient entries,
so the traversal and its output checksum take linear work in m. -/
setup_benchmark runAmbient m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientPreparation (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    let p := prepare i.basis i.target
    hash (p.mu.rows.toList.map (fun v => v.toList.map toString),
      p.orthogonal.rows.toList.map (fun v => v.toList.map toString),
      p.norms.toList.map toString, p.projection.toList.map toString, p.residual.toList.map toString)

/- Ambient-dimension cost model: With rank two, Gram formation, row reconstruction, target projection and residual each scan m entries.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientPreparation m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientBabai (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    digestPoints [point i.basis i.target (nearestPlane i.data i.n (Nat.le_refl _) 0)]

/- Ambient-dimension cost model: Two nearest-plane steps have fixed work; direct reconstruction and distance evaluation scan m entries.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientBabai m => m
  with prep := prepGapAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientOptimum (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    digest (optimum i)

/- Ambient-dimension cost model: The rank-two optimum pass visits six nodes and improves the nonoptimal Babai seed; each leaf reconstructs m coordinates.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientOptimum m => m
  with prep := prepGapAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientTies (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    digest (ties i)

/- Ambient-dimension cost model: The optimum tie pass visits four nodes and emits one m-coordinate point.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientTies m => m
  with prep := prepGapAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientCertificate (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    digestCertificate (closestCertificate i.basis i.target)

/- Ambient-dimension cost model: The end-to-end closest certificate producer includes preparation, a six-node improvement pass and a four-node tie pass; all reconstructed vectors and checked data have m coordinates.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientCertificate m => m
  with prep := prepGapAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientReplay (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    hash (check i)

/- Ambient-dimension cost model: Rank-two Gram identities, projection and residual validation scan m coordinates, as does the single reconstructed leaf.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientReplay m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientEncode (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    hash (encodeOptimumCertificate i.certificate)

/- Ambient-dimension cost model: The fixed tree has one point and rank two. The text contains a linear number of bounded-size rational tokens.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientEncode m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientDecode (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    match decodeOptimumCertificate { dimension := 4096 } i.n i.m i.encoded with
      | .ok c => digestCertificate c
      | .error e => panic! e

/- Ambient-dimension cost model: The configured dimension limit admits the whole ladder. Tokenization, parsing and the full digest scan a linear-size certificate.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientDecode m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientRetarget (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    let p := retarget i.data (i.target.map (- ·))
    hash (p.projection.toList.map toString, p.residual.toList.map toString)

/- Ambient-dimension cost model: Two target dot products and residual reconstruction each scan m coordinates; orthogonalization is shared.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientRetarget m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientLLL (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    let c := lllPreprocess i.basis
    hash (c.working.rows.rows.toList.map Vector.toList,
      c.forward.rows.toList.map Vector.toList, c.reverse.rows.toList.map Vector.toList)

/- Ambient-dimension cost model: The sheared rank-two basis requires size reduction and a swap, with a fixed number of operations. Gram preparation, coordinate recovery and exact transform checks scan m entries.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientLLL m => m
  with prep := prepShearAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientInput (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    hash (ofMatrix? i.basis.rows |>.isSome)

/- Ambient-dimension cost model: Independence uses a rank-two Gram matrix: four m-entry dot products followed by fixed-size determinant work.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientInput m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientClosest (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    let a := closest i.basis i.target
    mixHash (digestPoints a.points) (hash (toString a.distanceSq))

/- Ambient-dimension cost model: End-to-end preparation, seed reconstruction and both fixed-size passes, including a strict improvement, scan m coordinates; the one-element output sort is fixed.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientClosest m => m
  with prep := prepGapAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientShortest (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    match shortest i.basis with
      | none => 0
      | some a => mixHash (digestPoints a.points) (hash (toString a.distanceSq))

/- Ambient-dimension cost model: The two input rows have norm squared five, but their difference has norm squared two. Search improves its seed and returns both signs; the tree is fixed and each reconstruction scans m coordinates.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientShortest m => m
  with prep := prepShortAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def runAmbientBudget (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid rectangular benchmark input"
  | some i =>
    match closestWith { nodes := some 4 } i.basis i.target with
      | .complete a _ c => mixHash (digestPoints a.points) (hash c.nodes)
      | .incomplete q ps pending phase c =>
        mixHash (digestPoints (q :: ps)) (hash (pending.length, toString (repr phase), c.nodes))

/- Ambient-dimension cost model: A four-node shared budget finishes the three-node optimum pass and interrupts the tie pass. Preparation and the retained incumbent scan m coordinates; pending state has fixed rank.
Integer and rational arithmetic sizes and the search tree are fixed; the expected work is linear in m.
This is a family-specific model, not a polynomial bound in rank. -/
setup_benchmark runAmbientBudget m => m
  with prep := prepAmbient
  where {
    paramFloor := 64
    paramCeiling := 2048
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-- A ball-only fixture does not precompute optimization passes unrelated to its measured query. -/
structure BallInput where
  n : Nat
  m : Nat
  basis : Basis n m
  target : Vector Rat m
  radius : Rat

instance : Hashable BallInput where
  hash i := hash (i.basis.rows.rows.toList.map Vector.toList, i.target.toList.map toString, toString i.radius)

private def ballInput (rows : Matrix Int n m) (t : Vector Rat m) (r : Rat) : Option BallInput :=
  (ofMatrix? rows).map fun b => ⟨n, m, b, t, r⟩


def prepRank (n : Nat) : Option BallInput := ballInput (Matrix.identity n) 0 1

def runRank (input : Option BallInput) : UInt64 :=
  match input with
  | none => panic! "invalid rank benchmark input"
  | some i => digestPoints (enumerate i.basis i.target i.radius)

/- Rank-radius model at squared radius one: the unit lattice has 2n+1 leaves
and (n+1)^2 visited nodes. Each centre scans n coefficients and each leaf
reconstructs n coordinates from n rows, giving cubic arithmetic work at fixed
bit sizes. This fixed-radius model is not a polynomial general-rank bound. -/
setup_benchmark runRank n => n * n * n
  with prep := prepRank
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 64, 128, 256]
    maxSecondsPerCall := 120
    outerTrials := 3
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def prepRadius (r : Nat) : Option BallInput := ballInput (Matrix.identity 1) 0 (r*r)

def runRadius (input : Option BallInput) : UInt64 :=
  match input with
  | none => panic! "invalid radius benchmark input"
  | some i => digestPoints (enumerate i.basis i.target i.radius)

/- Radius model in rank one: radius r gives 2r+1 leaves. Reconstruction is
linear in r, while merge-sorting the alternating positive/negative traversal
order takes r log r comparisons, with bounded word-size coordinates. -/
setup_benchmark runRadius r => r * (r.log2 + 1)
  with prep := prepRadius
  where {
    paramFloor := 64
    paramCeiling := 4096
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def prepCube (n : Nat) : Option BallInput :=
  ballInput (Matrix.identity n) (Vector.replicate n (1/2)) ((n : Rat)/4)

def runCube (input : Option BallInput) : UInt64 :=
  match input with
  | none => panic! "invalid tie benchmark input"
  | some i => digestPoints (enumerate i.basis i.target i.radius)

/- The half-integral target of the unit lattice has exactly 2^n closest ties,
with a complete binary coefficient tree. Direct leaf reconstruction takes n^2
work, and sorting has the same `n^2 * 2^n` bound because each vector comparison
materializes n entries. This ladder deliberately measures exponential output. -/
setup_benchmark runCube n => (2 ^ n) * n * n
  with prep := prepCube
  where {
    paramFloor := 8
    paramCeiling := 13
    paramSchedule := .custom #[8, 9, 10, 11, 12, 13]
    maxSecondsPerCall := 30
    outerTrials := 3
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }


def prepShear (s : Nat) : Option Input :=
  make "basis-quality" s!"shear-{s}" (Matrix.ofRows #v[#v[1, (s : Int)], #v[0, 1]]) #v[1/2, 1/3] 2

def runShear (input : Option Input) : UInt64 :=
  match input with
  | none => panic! "invalid shear benchmark input"
  | some i => digest (optimum i)

/- For even shear s, Babai gives squared distance s^2/4-s/3+13/36.
The last Gram-Schmidt norm is 1/(s^2+1), so its initial interval contains
Theta(s^2) siblings. The current traversal tightens child bounds when the
incumbent improves, but still visits that finite initial sibling stream.
Fixed rank and word-size arithmetic therefore give quadratic work in s. -/
setup_benchmark runShear s => s * s
  with prep := prepShear
  where {
    paramFloor := 8
    paramCeiling := 256
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 10
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-- Exact output checks and work counts outside the timed registrations. -/
def validate : IO Unit := do
  for i in ← inputs.get do
    unless check i do throw (IO.userError s!"certificate failed: {i.name}")
    let ball := ball i
    unless ball.pending.isEmpty && i.first.pending.isEmpty && i.run.traversal.pending.isEmpty do
      throw (IO.userError s!"incomplete benchmark: {i.name}")
    let original := enumerationCertificate i.basis i.target i.radius
    unless original.points == sortPoints ball.state.points do
      throw (IO.userError s!"ball mismatch: {i.name}")
    IO.println s!"{i.family}/{i.name}: n={i.n} m={i.m} radius={i.radius} nodes={ball.state.counts.nodes} answers={ball.state.counts.answers} optimumNodes={i.first.state.counts.nodes} tieNodes={i.run.traversal.state.counts.nodes-i.first.state.counts.nodes} seedSq={i.seed.distanceSq} optimumSq={i.run.incumbent.distanceSq}"

/-- Exact comparator requests. External tools compare minima and membership, not tie choices. -/
private def measure (work : IO UInt64) : IO Nat := do
  let start ← IO.monoNanosNow
  LeanBench.blackBox (← work)
  return (← IO.monoNanosNow) - start

/-- Per-case phase timings; the IO read prevents pure-work hoisting out of the measured callback. -/
private def compareTimes (input : Input) : IO (Nat × Nat × Nat × Nat) := do
  let ref ← IO.mkRef input
  let lll := do
    let i ← ref.get
    return hash ((lllPreprocess i.original).working.rows.rows.toList.map Vector.toList)
  let prep := do
    let i ← ref.get
    let p := prepare i.basis i.target
    return hash (p.mu.rows.toList.map (fun v => v.toList.map toString),
      p.orthogonal.rows.toList.map (fun v => v.toList.map toString),
      p.norms.toList.map toString, p.projection.toList.map toString, p.residual.toList.map toString)
  let seed := do
    let i ← ref.get
    return digestPoints [if i.mode == .shortest then (shortestSeed i.basis).getD i.seed else
      point i.basis i.target (nearestPlane i.data i.n (Nat.le_refl _) 0)]
  let search := do
    let i ← ref.get
    return digest (optimum i)
  let mut reductions := #[]
  let mut preparation := #[]
  let mut seeds := #[]
  let mut searches := #[]
  for iteration in [:6] do
    let reduction ← if input.reduced then measure lll else pure 0
    let a ← measure prep
    let b ← measure seed
    let c ← measure search
    if iteration > 0 then
      reductions := reductions.push reduction
      preparation := preparation.push a
      seeds := seeds.push b
      searches := searches.push c
  return (reductions.qsort (· < ·) |>.getD 2 0, preparation.qsort (· < ·) |>.getD 2 0,
    seeds.qsort (· < ·) |>.getD 2 0, searches.qsort (· < ·) |>.getD 2 0)

def emitComparisons : IO Unit := do
  for i in ← inputs.get do
    if i.n == i.m then
      let (lll, prep, seed, search) ← compareTimes i
      IO.println (Json.mkObj [
        ("hex_lll_ns", toJson lll), ("hex_preprocessed", toJson i.reduced),
        ("original_basis", toJson (i.original.rows.rows.toList.map Vector.toList)),
        ("hex_prepare_ns", toJson prep), ("hex_seed_ns", toJson seed), ("hex_search_ns", toJson search),
        ("name", toJson i.name), ("operation", toJson (if i.mode == .shortest then "shortest" else "closest")),
        ("basis", toJson (i.basis.rows.rows.toList.map Vector.toList)),
        ("target", toJson (i.target.toList.map toString)),
        ("distanceSq", toJson (toString i.run.incumbent.distanceSq))]).compress

/-- Profile the fixed coefficient-height controls with the same timed-region
protocol as parametric registrations. Fixture construction remains outside. -/
def profileHeight : IO Unit := do
  let loop := fun (count : Nat) => do
    let start ← IO.monoNanosNow
    let mut result : UInt64 := 0
    for _ in [:count] do
      result := mixHash result (← runHeight ())
    LeanBench.blackBox result
    return ((← IO.monoNanosNow) - start, some result)
  let (timed, sidecar) ← LeanBench.withSidecarIfEnabled loop "warm-loop"
  try
    let _ ← timed 2048
  finally
    if let some handle := sidecar then handle.flush

end Hex.LatticeEnumBench

def main (args : List String) : IO UInt32 := do
  match args with
  | ["sizes"] => Hex.LatticeEnumBench.validate; return 0
  | ["comparisons"] => Hex.LatticeEnumBench.emitComparisons; return 0
  | ["profile-height"] => Hex.LatticeEnumBench.profileHeight; return 0
  | _ => LeanBench.Cli.dispatch args
