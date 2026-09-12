/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRowReduce
import HexPolyFp.PrimeField
import HexRationalFn
import Lean.Data.Json
import Hex.Conformance.Emit

namespace Hex.RowReduceFixtures

open Lean

structure Case (F : Type) where
  name : String
  n : Nat
  m : Nat
  A : Matrix F n m
  b : Vector F n
  rank : Nat
  particular : Option (Vector F m)
  basis : Array (Array F)
  separator : Vector F n

private def mat [OfNat F 0] (n m : Nat) (a : Array (Array F)) : Matrix F n m :=
  Matrix.ofFn fun i j => (a[i.val]?.getD #[])[j.val]?.getD 0

private def vec [OfNat F 0] (n : Nat) (a : Array F) : Vector F n :=
  Vector.ofFn fun i => a[i.val]?.getD 0

private def consistent [OfNat F 0] (name : String) (n m rank : Nat)
    (a : Array (Array F)) (b x : Array F) (basis : Array (Array F)) : Case F :=
  ⟨name, n, m, mat n m a, vec n b, rank, some (vec m x), basis, vec n #[]⟩

private def inconsistent [OfNat F 0] (name : String) (n m rank : Nat)
    (a : Array (Array F)) (b y : Array F) : Case F :=
  ⟨name, n, m, mat n m a, vec n b, rank, none, #[], vec n y⟩

/-- Exact boundary answers, valid in characteristic two as well as zero. -/
def cases [Lean.Grind.Field F] (a : F) : Array (Case F) := #[
  consistent "empty" 0 0 0 #[] #[] #[] #[],
  consistent "no-equations" 0 3 0 #[] #[] #[0, 0, 0]
    #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]],
  consistent "no-variables" 3 0 0 #[#[], #[], #[]] #[0, 0, 0] #[] #[],
  inconsistent "no-variables-inconsistent" 3 0 0 #[#[], #[], #[]] #[0, 1, 0] #[0, 1, 0],
  consistent "singular" 2 2 1 #[#[1, 0], #[0, 0]] #[a, 0] #[a, 0] #[#[0], #[1]],
  inconsistent "singular-inconsistent" 2 2 1 #[#[1, 0], #[0, 0]] #[a, 1] #[0, 1],
  inconsistent "rectangular-inconsistent" 2 3 1 #[#[1, 0, 0], #[1, 0, 0]]
    #[0, 1] #[-1, 1],
  consistent "leading-free" 1 3 1 #[#[0, 1, 1]] #[a] #[0, a, 0]
    #[#[1, 0], #[0, -1], #[0, 1]],
  consistent "tall" 3 2 2 #[#[1, 0], #[0, 1], #[1, 1]] #[a, 1, a + 1]
    #[a, 1] #[#[], #[]],
  consistent "wide" 2 4 2 #[#[1, 0, 1, 0], #[0, 1, 0, 1]] #[a, 1]
    #[a, 1, 0, 0] #[#[-1, 0], #[0, -1], #[1, 0], #[0, 1]],
  consistent "row-swap" 2 2 2 #[#[0, 1], #[1, a]] #[1, 0] #[-a, 1] #[#[], #[]],
  consistent "nonconstant-pivot" 2 2 2 #[#[a, 1], #[0, a⁻¹]] #[a + 1, a⁻¹]
    #[1, 1] #[#[], #[]]]

/-- Check canonical answers as well as all returned product identities. -/
def check [Lean.Grind.Field F] [DecidableEq F] (c : Case F) : Bool := Id.run do
  if Matrix.rowReduce_rank c.A != c.rank then return false
  match Matrix.solve c.A c.b, c.particular with
  | .ok (x, N), some expected =>
    if x != expected || N.rows.toArray.map (·.toArray) != c.basis then return false
    if c.A * x != c.b then return false
  | .error y, none =>
    if y != c.separator || Matrix.vecMul y c.A != 0 || y.dotProduct c.b == 0 then
      return false
  | _, _ => return false
  if (Matrix.solve? c.A c.b).isSome != c.particular.isSome then return false
  if h : c.m = c.n then
    let A : Matrix F c.n c.n := h ▸ c.A
    match Matrix.inverse? A with
    | none => if c.rank == c.n then return false
    | some B =>
      if A * B != Matrix.identity c.n || B * A != Matrix.identity c.n then return false
  return true

def ratJson (q : Rat) : Json := toJson #[toJson q.num, toJson q.den]
def fnJson (f : RationalFn Rat) : Json :=
  toJson #[toJson (f.num.toArray.map ratJson), toJson (f.den.toArray.map ratJson)]

private def vectorJson (enc : F → Json) (v : Vector F n) : Json :=
  toJson (v.toArray.map enc)
private def matrixJson (enc : F → Json) (A : Matrix F n m) : Json :=
  toJson (A.rows.toArray.map (vectorJson enc))

def emit [Lean.Grind.Field F] [DecidableEq F] (carrier : String) (modulus : Nat)
    (enc : F → Json) (c : Case F) : IO Unit := do
  let name := carrier ++ "/" ++ toString modulus ++ "/" ++ c.name
  let input := Json.mkObj [("kind", toJson "fieldmatrix"), ("lib", toJson "HexRowReduce"),
    ("case", toJson name), ("carrier", toJson carrier), ("modulus", toJson modulus),
    ("n", toJson c.n), ("m", toJson c.m), ("rows", matrixJson enc c.A),
    ("b", vectorJson enc c.b)]
  match (← IO.getEnv "HEX_FIXTURE_OUTPUT") with
  | none => IO.println input.compress
  | some path =>
    let handle ← IO.FS.Handle.mk path IO.FS.Mode.append
    handle.putStrLn input.compress
  let result := match Matrix.solve c.A c.b with
    | .error y => Json.mkObj [("error", vectorJson enc y)]
    | .ok (x, N) => Json.mkObj [("particular", vectorJson enc x), ("basis", matrixJson enc N)]
  Hex.Conformance.Emit.emitResult "HexRowReduce" name "field-solve" result.compress
  if h : c.m = c.n then
    let A : Matrix F c.n c.n := h ▸ c.A
    let result := match Matrix.inverse? A with
      | none => Json.null
      | some B => matrixJson enc B
    Hex.Conformance.Emit.emitResult "HexRowReduce" name "field-inverse" result.compress

scoped instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
scoped instance : ZMod64.PrimeModulus 2 := ZMod64.primeModulusOfPrime (by decide)
scoped instance : ZMod64.Bounds 101 := ⟨by decide, by decide⟩
scoped instance : ZMod64.PrimeModulus 101 := ZMod64.primeModulusOfPrime (by decide)

def rationalFunction : RationalFn Rat := RationalFn.X / (RationalFn.X + 1)

def emitAll : IO Unit := do
  for c in cases (1/2 : Rat) do emit "Rat" 0 ratJson c
  for c in cases (1 : ZMod64 2) do emit "ZMod64" 2 (fun x => toJson x.toNat) c
  for c in cases (3 : ZMod64 101) do emit "ZMod64" 101 (fun x => toJson x.toNat) c
  for c in cases rationalFunction do emit "RationalFn" 0 fnJson c

end Hex.RowReduceFixtures
