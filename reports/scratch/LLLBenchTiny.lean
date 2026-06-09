import HexLLL.Basic

open Hex

namespace LLLBenchTinyScratch

def lcgStep (x : Nat) : Nat :=
  (1103515245 * x + 12345) % 2147483648

def lcgIterate (seed : Nat) : Nat → Nat
  | 0 => seed
  | k + 1 => lcgIterate (lcgStep seed) k

/-- Small entries in [-3, 3] to keep Isabelle LLL within reach. -/
def tinyEntry (raw : Nat) : Int :=
  Int.ofNat (raw % 7) - 3

def tinyBasis (n seed : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if j.val < i.val then
      0
    else if i = j then
      Int.ofNat (n - i.val + 1)
    else
      tinyEntry (lcgIterate seed (i.val * n + j.val + 1))

end LLLBenchTinyScratch

open LLLBenchTinyScratch

private def encodeMatrix {n m : Nat} (M : Matrix Int n m) : String :=
  let rows := M.toArray.toList.map fun row =>
    "[" ++ String.intercalate "," (row.toArray.toList.map toString) ++ "]"
  "[" ++ String.intercalate "," rows ++ "]"

private def matrixChecksum {n m : Nat} (M : Matrix Int n m) : UInt64 :=
  M.toArray.foldl (init := (0 : UInt64)) fun acc row =>
    row.toArray.foldl (init := acc) fun a c => mixHash a (hash c)

private theorem hδLow : (1 / 4 : Rat) < 3 / 4 := by grind
private theorem hδHigh : (3 / 4 : Rat) ≤ 1 := by grind

private def runOne (n : Nat) (reps : Nat) (hn : 1 ≤ n) : IO Unit := do
  let basis : Matrix Int n n := tinyBasis n 8
  let _ := matrixChecksum basis
  let t0 ← IO.monoNanosNow
  let mut chk : UInt64 := 0
  for _ in [0:reps] do
    let reduced := Hex.lllNative basis (3 / 4) hδLow hδHigh hn
    chk := chk ^^^ matrixChecksum reduced
  let t1 ← IO.monoNanosNow
  let nanos := (t1 - t0) / reps
  let basisJson := encodeMatrix basis
  let line := "{" ++
    s!"\"n\":{n},\"reps\":{reps},\"lean_nanos\":{nanos},\"checksum\":{chk},\"basis\":{basisJson}"
    ++ "}"
  IO.println line

def main : IO Unit := do
  runOne 3  200 (by decide)
  runOne 4  200 (by decide)
  runOne 5  200 (by decide)
  runOne 6  100 (by decide)
  runOne 7  50  (by decide)
  runOne 8  30  (by decide)
  runOne 10 20  (by decide)
  runOne 12 10  (by decide)
  runOne 15 5   (by decide)
