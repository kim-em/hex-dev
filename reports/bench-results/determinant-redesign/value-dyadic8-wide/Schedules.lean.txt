/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDet.Basic
import HexModularMatrix.Fixtures
import HexCharPoly.Berkowitz
import Init.Data.Dyadic
import Lean

namespace Determinant.Schedules

open Hex

@[inline] def entry [OfNat R 0] (A : Matrix R n n) (i j : Nat) : R :=
  if hi : i < n then
    if hj : j < n then A[(i, j)] else 0
  else 0

/-- Eager Bird recurrence on the same flat row-major matrix representation as the
existing controls. This experimental producer has no new soundness claim. -/
def bird [Lean.Grind.CommRing R] (A : Matrix R n n) : R := Id.run do
  if n == 0 then return 1
  let mut F := A
  for _ in [:n - 1] do
    let diag := Vector.ofFn fun i : Fin n =>
      (List.range (n - i.val - 1)).foldl
        (fun s k => s + entry F (i.val + k + 1) (i.val + k + 1)) 0
    let next := Matrix.ofFn fun i j =>
      (List.range (n - i.val - 1)).foldl
        (fun s k => s + entry F i.val (i.val + k + 1) *
          entry A (i.val + k + 1) j.val) (-diag[i] * A[(i, j)])
    F := next
  let d := entry F 0 0
  return if (n - 1) % 2 == 0 then d else -d

/-- Consume only the signed final Berkowitz coefficient, without converting
the whole vector into a dense polynomial. The existing schedule is unchanged. -/
def berkowitz [Lean.Grind.CommRing R] (A : Matrix R n n) : R :=
  let d := A.berkowitz[n]
  if n % 2 == 0 then d else -d

def dense (n bits : Nat) (salt : Nat := 10219) : Matrix Int n n :=
  ModularMatrixFixtures.dense n bits salt

def variant (A : Matrix Int n n) (kind : String) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if kind == "singular" && i.val == 1 then entry A 0 j.val
    else if kind == "swap" && i.val == 0 && j.val == 0 then 0
    else A[(i, j)]

/-- IO references bound both ends of the clock: the input is read after
start, and the computed value is stored before stop. These barriers prevent
pure computation from floating out of the timed region. Formatting and external
answer comparison are outside this clock. Every arithmetic schedule uses the same prepared input. -/
@[noinline] def timed {A R : Type} (label : String) (input : IO.Ref A)
    (compute : A → R) (format : R → String) : IO Unit := do
  let start ← IO.monoNanosNow
  let a ← input.get
  let saved ← IO.mkRef (compute a)
  let elapsed ← IO.monoNanosNow
  let result ← saved.get
  IO.println <| (Lean.Json.mkObj [("arm", Lean.toJson label),
    ("elapsed_ns", Lean.toJson (elapsed - start)),
    ("value", Lean.toJson (format result))]).compress

end Determinant.Schedules
