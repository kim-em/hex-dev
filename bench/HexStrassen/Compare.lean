/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp

/-!
Local measurement for the periodic-reduction Strassen base kernel. It compares
`mulImpl` with `barrettBaseMul` directly, compares default and periodic
`mulStrassen` at shipped and matched cutoffs, and sweeps candidate reduction
windows on long rectangular leaves.

This is not a CI timing gate. It emits the JSON consumed by
`scripts/plots/strassen-base-kernel-comparison.py` on stdout; progress and live
checksums go to stderr. CI builds this executable but does not run it.
-/

open Hex Hex.Matrix

abbrev tinyPrime : Nat := 5
abbrev smallPrime : Nat := 65537
abbrev upperPrime : Nat := 2147483647

instance : ZMod64.Bounds tinyPrime := ⟨by decide, by decide⟩
instance : ZMod64.Bounds smallPrime := ⟨by decide, by decide⟩
instance : ZMod64.Bounds upperPrime := ⟨by decide, by decide⟩

def tinyCtx : Hex.BarrettCtx tinyPrime := Hex.BarrettCtx.ofModulus (by decide) (by decide)
def smallCtx : Hex.BarrettCtx smallPrime := Hex.BarrettCtx.ofModulus (by decide) (by decide)
def upperCtx : Hex.BarrettCtx upperPrime := Hex.BarrettCtx.ofModulus (by decide) (by decide)

@[noinline]
def cmpMat (p n m salt : Nat) [ZMod64.Bounds p] : Matrix (ZMod64 p) n m :=
  Matrix.ofFn fun i j =>
    ZMod64.ofNat p ((i.val * 2654435761 + j.val * 40503 + salt * 97 + 1) % p)

def cmpChecksum (p : Nat) [ZMod64.Bounds p] {n k : Nat} (M : Matrix (ZMod64 p) n k) : Nat :=
  (List.finRange n).foldl
    (fun acc i => (List.finRange k).foldl (fun a j => (a + M[(i, j)].toNat) % p) acc) 0

@[noinline]
def cmpForce {α : Type} (x : α) : IO α :=
  pure x

structure Timed where
  nanos : Nat
  checksum : Nat

def updateBest (best sample : Nat) : Nat :=
  if best = 0 || sample < best then sample else best

@[noinline]
def cmpLeafProduct {p n m k : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (periodic : Bool) (a : Matrix (ZMod64 p) n m) (b : Matrix (ZMod64 p) m k) :
    Matrix (ZMod64 p) n k :=
  if periodic then barrettBaseMul ctx a b else Matrix.mulImpl a b

def timeLeaf {p n m k : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (periodic : Bool) (a : Matrix (ZMod64 p) n m) (b : Matrix (ZMod64 p) m k) : IO Timed := do
  let t0 ← IO.monoNanosNow
  let c ← cmpForce (cmpLeafProduct ctx periodic a b)
  let t1 ← IO.monoNanosNow
  return { nanos := t1 - t0, checksum := cmpChecksum p c }

def cmpLeafBest {p : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (n m k iters : Nat) : IO (Nat × Nat × Nat) := do
  let warmA ← cmpForce (cmpMat p n m 5)
  let warmB ← cmpForce (cmpMat p m k 12)
  let _ ← cmpForce (cmpLeafProduct ctx false warmA warmB)
  let _ ← cmpForce (cmpLeafProduct ctx true warmA warmB)
  let mut defaultBest := 0
  let mut periodicBest := 0
  let mut sink := 0
  for iter in [0:iters] do
    let salt := 1000 + iter * 13
    let a ← cmpForce (cmpMat p n m salt)
    let b ← cmpForce (cmpMat p m k (salt + 7))
    let (d, q) ← if iter % 2 = 0 then do
        let d ← timeLeaf ctx false a b
        let q ← timeLeaf ctx true a b
        pure (d, q)
      else do
        let q ← timeLeaf ctx true a b
        let d ← timeLeaf ctx false a b
        pure (d, q)
    unless d.checksum = q.checksum do
      throw <| IO.userError s!"leaf checksum mismatch at {n}x{m}x{k}"
    defaultBest := updateBest defaultBest d.nanos
    periodicBest := updateBest periodicBest q.nanos
    sink := sink + d.checksum
  IO.eprintln s!"  leaf {n}x{m}x{k}: checksum={sink % 1000000007}"
  return (defaultBest, periodicBest, sink % 1000000007)

def cmpConfig {p : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p) (which : Nat) :
    Matrix.StrassenConfig (ZMod64 p) :=
  let defCut := (strassenDefault (R := ZMod64 p)).cutoff
  let perCut := (strassenBarrett ctx).cutoff
  match which with
  | 0 => strassenDefault
  | 1 => strassenBarrett ctx
  | 2 => { strassenBarrett ctx with cutoff := defCut }
  | _ => { (strassenDefault : Matrix.StrassenConfig (ZMod64 p)) with cutoff := perCut }

def configName : Nat → String
  | 0 => "default_ns"
  | 1 => "periodic_ns"
  | 2 => "periodic_at_default_cutoff_ns"
  | _ => "default_at_periodic_cutoff_ns"

@[noinline]
def cmpFullProduct {p n m k : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (which : Nat) (a : Matrix (ZMod64 p) n m) (b : Matrix (ZMod64 p) m k) :
    Matrix (ZMod64 p) n k :=
  mulStrassen (cmpConfig ctx which) a b

def timeFull {p n m k : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p) (which : Nat)
    (a : Matrix (ZMod64 p) n m) (b : Matrix (ZMod64 p) m k) : IO Timed := do
  let t0 ← IO.monoNanosNow
  let c ← cmpForce (cmpFullProduct ctx which a b)
  let t1 ← IO.monoNanosNow
  return { nanos := t1 - t0, checksum := cmpChecksum p c }

def cmpFullBest {p : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (n m k iters : Nat) : IO (Array Nat × Nat) := do
  let warmA ← cmpForce (cmpMat p n m 5)
  let warmB ← cmpForce (cmpMat p m k 12)
  for which in [0:4] do
    let _ ← cmpForce (cmpFullProduct ctx which warmA warmB)
  let mut best := #[0, 0, 0, 0]
  let mut sink := 0
  for iter in [0:iters] do
    let salt := 1000 + iter * 13
    let a ← cmpForce (cmpMat p n m salt)
    let b ← cmpForce (cmpMat p m k (salt + 7))
    let mut checksums := #[0, 0, 0, 0]
    for offset in [0:4] do
      let which := (offset + iter) % 4
      let sample ← timeFull ctx which a b
      best := best.set! which (updateBest best[which]! sample.nanos)
      checksums := checksums.set! which sample.checksum
    unless checksums.all (· = checksums[0]!) do
      throw <| IO.userError s!"full checksum mismatch at {n}x{m}x{k}"
    sink := sink + checksums[0]!
  IO.eprintln s!"  full {n}x{m}x{k}: checksum={sink % 1000000007}"
  return (best, sink % 1000000007)

/-! Benchmark-only parameterized copy of the executable periodic loop. It lets
the measurement compare window policies without changing the proved production
definition. Every measured result is checksum-checked against the other windows
and the production leaf comparison above. -/

def cmpDotLoop {p m : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p) (window : Nat)
    (u v : Vector (ZMod64 p) m) : Nat → UInt64 → UInt64 → Nat → UInt64
  | i, lo, hi, count =>
    if h : i < m then
      let q := u[i].toUInt64 * v[i].toUInt64
      let lo' := lo + q
      let hi' := hi + (if lo' < lo then 1 else 0)
      if count + 1 = window then
        cmpDotLoop ctx window u v (i + 1)
          (BarrettCtx.accReduce ctx.toUInt64Ctx (BarrettCtx.radixResidue ctx.toUInt64Ctx)
            lo' hi') 0 0
      else
        cmpDotLoop ctx window u v (i + 1) lo' hi' (count + 1)
    else
      BarrettCtx.accReduce ctx.toUInt64Ctx (BarrettCtx.radixResidue ctx.toUInt64Ctx) lo hi
  termination_by i => m - i
  decreasing_by all_goals omega

def cmpDotWindow {p m : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p) (window : Nat)
    (u v : Vector (ZMod64 p) m) : ZMod64 p :=
  if m < window then
    ZMod64.ofNat p (delayedDotRun ctx u v 0 0 0).toNat
  else
    ZMod64.ofNat p (cmpDotLoop ctx window u v 0 0 0 0).toNat

def cmpWindowBaseMul {p n m k : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (window : Nat) (a : Matrix (ZMod64 p) n m) (b : Matrix (ZMod64 p) m k) :
    Matrix (ZMod64 p) n k :=
  let bRows := (Matrix.transpose b).rows
  Matrix.ofRows (Vector.ofFn fun i =>
    let ai := Matrix.getRow a i
    Vector.ofFn fun j => cmpDotWindow ctx window ai bRows[j])

@[noinline]
def cmpWindowProduct {p n m k : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (window : Nat) (a : Matrix (ZMod64 p) n m) (b : Matrix (ZMod64 p) m k) :
    Matrix (ZMod64 p) n k :=
  cmpWindowBaseMul ctx window a b

def windowCandidates : Array Nat := #[256, 4096, 4294967296]

def timeWindow {p n m k : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p) (window : Nat)
    (a : Matrix (ZMod64 p) n m) (b : Matrix (ZMod64 p) m k) : IO Timed := do
  let t0 ← IO.monoNanosNow
  let c ← cmpForce (cmpWindowProduct ctx window a b)
  let t1 ← IO.monoNanosNow
  return { nanos := t1 - t0, checksum := cmpChecksum p c }

def cmpWindowBest {p : Nat} [ZMod64.Bounds p] (ctx : Hex.BarrettCtx p)
    (n m k iters : Nat) : IO (Array Nat × Nat) := do
  let warmA ← cmpForce (cmpMat p n m 5)
  let warmB ← cmpForce (cmpMat p m k 12)
  for window in windowCandidates do
    let _ ← cmpForce (cmpWindowProduct ctx window warmA warmB)
  let mut best := windowCandidates.map (fun _ => 0)
  let mut sink := 0
  for iter in [0:iters] do
    let salt := 2000 + iter * 17
    let a ← cmpForce (cmpMat p n m salt)
    let b ← cmpForce (cmpMat p m k (salt + 9))
    let reference ← cmpForce (Matrix.mulImpl a b)
    let referenceChecksum := cmpChecksum p reference
    let mut checksums := windowCandidates.map (fun _ => 0)
    for offset in [0:windowCandidates.size] do
      let which := (offset + iter) % windowCandidates.size
      let sample ← timeWindow ctx windowCandidates[which]! a b
      best := best.set! which (updateBest best[which]! sample.nanos)
      checksums := checksums.set! which sample.checksum
    unless checksums.all (· = referenceChecksum) do
      throw <| IO.userError s!"window checksum mismatch at {n}x{m}x{k}"
    sink := sink + referenceChecksum
  IO.eprintln s!"  window {n}x{m}x{k}: checksum={sink % 1000000007}"
  return (best, sink % 1000000007)

def measureModulus {p : Nat} [ZMod64.Bounds p] (label : String) (ctx : Hex.BarrettCtx p) :
    IO (Array String) := do
  IO.eprintln s!"modulus={label} p={p} window={BarrettCtx.barrettWindow}"
  let mut rows : Array String := #[]
  let leafShapes := #[(64, 64, 64), (128, 128, 128), (32, 256, 48),
    (4, 12289, 8), (3, 20481, 8)]
  for (n, m, k) in leafShapes do
    let (d, q, checksum) ← cmpLeafBest ctx n m k 9
    rows := rows.push
      ("    {" ++
        "\"kind\": \"leaf\", \"modulus\": \"" ++ label ++ "\", " ++
        "\"prime\": " ++ toString p ++ ", " ++
        "\"n\": " ++ toString n ++ ", \"m\": " ++ toString m ++
        ", \"k\": " ++ toString k ++ ", " ++
        "\"window_flushes\": " ++ toString (m / BarrettCtx.barrettWindow) ++ ", " ++
        "\"default_ns\": " ++ toString d ++ ", \"periodic_ns\": " ++ toString q ++
        ", \"checksum\": " ++ toString checksum ++ "}")
  let fullShapes := #[(96, 96, 96), (112, 112, 112), (120, 120, 120),
    (104, 112, 120)]
  for (n, m, k) in fullShapes do
    let (times, checksum) ← cmpFullBest ctx n m k 7
    rows := rows.push
      ("    {" ++
        "\"kind\": \"full\", \"modulus\": \"" ++ label ++ "\", " ++
        "\"prime\": " ++ toString p ++ ", " ++
        "\"n\": " ++ toString n ++ ", \"m\": " ++ toString m ++
        ", \"k\": " ++ toString k ++ ", " ++
        "\"default_ns\": " ++ toString times[0]! ++
        ", \"periodic_ns\": " ++ toString times[1]! ++
        ", \"periodic_at_default_cutoff_ns\": " ++ toString times[2]! ++
        ", \"default_at_periodic_cutoff_ns\": " ++ toString times[3]! ++
        ", \"checksum\": " ++ toString checksum ++ "}")
  return rows

def measureWindows : IO (Array String) := do
  let mut rows : Array String := #[]
  for (n, m, k) in #[(4, 12289, 8), (3, 20481, 8)] do
    let (times, checksum) ← cmpWindowBest upperCtx n m k 9
    for which in [0:windowCandidates.size] do
      rows := rows.push
        ("    {" ++
          "\"kind\": \"window\", \"modulus\": \"upper\", " ++
          "\"prime\": " ++ toString upperPrime ++ ", " ++
          "\"n\": " ++ toString n ++ ", \"m\": " ++ toString m ++
          ", \"k\": " ++ toString k ++ ", " ++
          "\"window_terms\": " ++ toString windowCandidates[which]! ++
          ", \"window_flushes\": " ++ toString (m / windowCandidates[which]!) ++
          ", \"wall_ns\": " ++ toString times[which]! ++
          ", \"checksum\": " ++ toString checksum ++ "}")
  return rows

def commandText (cmd : String) (args : Array String) : IO String := do
  try
    let result ← IO.Process.output { cmd, args }
    let value := result.stdout.trimAscii.toString
    return if value.isEmpty then "unknown" else value
  catch _ =>
    return "unknown"

def main : IO Unit := do
  let gitDescribe ← commandText "git" #["describe", "--always", "--dirty"]
  let host ← commandText "hostname" #[]
  let tiny ← measureModulus "tiny" tinyCtx
  let small ← measureModulus "small" smallCtx
  let upper ← measureModulus "upper" upperCtx
  let windows ← measureWindows
  let rows := tiny ++ small ++ upper ++ windows
  IO.println "{"
  IO.println "  \"schema_version\": 3,"
  IO.println "  \"generated_by\": \"lake exe hexstrassen_compare\","
  IO.println ("  \"git_describe\": \"" ++ gitDescribe ++ "\",")
  IO.println ("  \"lean_version\": \"" ++ Lean.versionString ++ "\",")
  IO.println ("  \"host\": \"" ++ host ++ "\",")
  IO.println "  \"metric\": \"best_of_iters_wall_nanos\","
  IO.println "  \"timed_region\": \"matrix multiplication only; fixture generation and checksums excluded\","
  IO.println ("  \"window_terms\": " ++ toString BarrettCtx.barrettWindow ++ ",")
  IO.println ("  \"default_cutoff\": " ++
    toString (strassenDefault (R := ZMod64 tinyPrime)).cutoff ++ ",")
  IO.println ("  \"periodic_cutoff\": " ++ toString (strassenBarrett tinyCtx).cutoff ++ ",")
  IO.println "  \"results\": ["
  IO.println (String.intercalate ",\n" rows.toList)
  IO.println "  ]"
  IO.println "}"
