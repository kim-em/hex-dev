/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDet
import HexMvPoly.KernelResidue.Denote
import HexArith.Nat.Prime
import Lean.Data.Json

namespace Hex.PolyDet.PackedBench
open Lean Hex.Matrix Hex.MvPoly.Kernel Hex.Kronecker Hex.PolyDet.Packed

structure Input where
  n : Nat
  k : Nat
  rows : List (List (PolyList Int))
  p : Nat := 0
  missing : Bool := false
  deriving FromJson

structure Prepared where
  ps : List (Product (PolyList Int))
  quotients : Option (List (List (PolyList Int)))
  listCheck : Unit → Bool
  packedCheck : MulMode → List (Nat × Nat) → Bool
  witnessTerms : Nat
  deriving Inhabited

def budget : Budget := {}

def witnessTerms (w : DetWitness (PolyList C)) : Nat :=
  match w with
  | .triangular _ ts d => d.length + support ts.flatten
  | .singular v => support v

/-- Coefficient admission is independent of the producer's observed support.
Support limits are enforced by the same budgeted producer as the frontend. -/
def initialDecline (a : Input) : Option String := Id.run do
  let supp := a.rows.flatten.foldl (fun s p => max s p.length) 1
  let bits := a.rows.flatten.foldl (fun b p => p.foldl
    (fun b (_, z) => max b (if z == 0 then 0 else z.natAbs.log2 + 1)) b) 1
  let count := 2 * a.n * (bits + supp.log2 + a.n.log2 + 2)
  if count > 4096 then return some s!"coefficient bits budget exhausted (count {count}, limit 4096)"
  return none

def producerBudget : DetWitness.Budget := ⟨100000, 65536⟩

def residueWitness (p k n : Nat) (rows : List (List (PolyList Nat))) :
    Option (Except DetWitness.Error (DetWitness (PolyList Nat))) := do
  if hb : 0 < p ∧ p < 2^31 then
    letI : ZMod64.Bounds p := ⟨hb.1, hb.2⟩
    if hp : Hex.Nat.Prime p then
      letI : ZMod64.PrimeModulus p := ⟨hp⟩
      letI : Div (MvPoly k (ZMod64 p) Mono.grevlex) := MvPoly.instDiv
      let decode := fun a : PolyList Nat => MvPoly.ofTerms (cmp := Mono.grevlex)
        (a.map fun (m,c) => (Hex.MvPoly.Kernel.mono k m, (c : ZMod64 p)))
      let quotePoly := fun f => Hex.MvPoly.Kernel.ofResidues p (Hex.PolyDet.toList f)
      let check := fun rs w => checkDetPolyList (opsMod p k) n
        (rs.map (List.map quotePoly)) (w.map quotePoly)
      return (Hex.PolyDet.produce producerBudget n check (rows.map (List.map decode))).map
        (fun w => w.map quotePoly)
    else none
  else none

def prepare (a : Input) : Except String Prepared := do
  if a.p == 0 then do
    let decode := Hex.MvPoly.Kernel.denote (n := a.k) (cmp := Mono.grevlex)
    let w ← (Hex.PolyDet.produce producerBudget a.n (Hex.PolyDet.check a.n)
      (a.rows.map (List.map decode))).mapError DetWitness.Error.message
    let w := w.map Hex.PolyDet.toList
    let ps := products (Hex.PolyDet.ops a.k) a.n a.rows w
    return { ps, quotients := none, witnessTerms := witnessTerms w
             listCheck := fun _ => checkDetPolyList (Hex.PolyDet.ops a.k) a.n a.rows w
             packedCheck := fun mode widths => checkDetPolyPacked mode a.k a.n a.rows w widths }
  else
    let rows := a.rows.map (List.map (fun p => p.map (fun (e,c) => (e, c.toNat))))
    let some result := residueWitness a.p a.k a.n rows | throw "residue witness unavailable"
    let w ← result.mapError DetWitness.Error.message
    let ps := (products (opsMod a.p a.k) a.n rows w).map (Product.map lift)
    let qs ← if a.missing then pure none else
      match prepareQuotients { certificateTerms := 65536 - witnessTerms w } a.p ps with
      | .ok qs => pure (some qs)
      | .error .unavailable => pure none
      | .error e => throw (reprStr e)
    return { ps, quotients := qs, witnessTerms := witnessTerms w
             listCheck := fun _ => checkDetPolyList (opsMod a.p a.k) a.n rows w
             packedCheck := fun mode widths => checkDetPolyPackedMod mode a.p a.k a.n rows w qs.get! widths }

def reportJson (s : Selection) : Json := Json.mkObj
  [("packed", toJson s.packed), ("route", toJson s.route), ("reason", toJson s.reason),
   ("quotient_support", toJson s.quotientSupport),
   ("products", toJson (s.reports.map fun r => Json.mkObj
     [("row", toJson r.row), ("degrees", toJson r.size.degrees),
      ("digits", toJson r.size.digits), ("packedBits", toJson r.size.packedBits),
      ("key", toJson [r.key.packedBits, r.key.leftSupport, r.key.rightSize, r.key.resultSupport, r.key.inner])]))]

@[noinline] def force (f : Unit → α) : IO α := pure (f ())

def measure (f : Unit → α) : IO (α × Nat) := do
  let ref ← IO.mkRef f
  let start ← IO.monoNanosNow
  let value ← force (← ref.get)
  let stop ← IO.monoNanosNow
  return (value, stop - start)

def run (a : Input) (timing : Bool) : IO Json := do
  if let some reason := initialDecline a then
    return Json.mkObj [("classification", toJson "overall-decline"), ("reason", toJson reason)]
  let (prepared, producerNs) ← measure fun _ => prepare a
  let .ok p := prepared |
    return Json.mkObj
      [("classification", toJson (match prepared with
        | .error e => if e.startsWith "intermediate budget" || e.startsWith "certificate budget"
          then "overall-decline" else "producer-failure"
        | _ => "producer-failure")),
     ("reason", toJson (match prepared with | .error e => e | _ => "unavailable")),
     ("producer_ns", toJson producerNs)]
  let choose := fun arm => select budget arm a.k p.ps (if a.p == 0 then none else some a.p) p.quotients
  let (selected, preflightNs) ← measure fun _ => choose .packed
  let s ← match selected with | .ok s => pure s | .error e => throw (IO.userError e)
  let mut fields := [("classification", toJson (if s.packed then "eligible" else "packed-decline")),
    ("selection", reportJson s), ("witness_terms", toJson p.witnessTerms),
    ("producer_ns", toJson producerNs), ("preflight_ns", toJson preflightNs)]
  if timing then
    let mut samples := []
    for trial in [:6] do
      for packed in (if trial % 2 == 0 then [false,true] else [true,false]) do
        if packed && !s.packed then continue
        let (ok, ns) ← measure (if packed then fun _ => p.packedCheck .plain s.widths else p.listCheck)
        if !ok then throw (IO.userError "selected compiled checker rejected the witness")
        samples := samples ++ [Json.mkObj [("trial", toJson trial), ("arm", toJson (if packed then "packed" else "term-list")), ("ns", toJson ns)]]
    fields := fields ++ [("samples", toJson samples)]
    let (qs, quotientNs) ← measure fun _ => if a.p == 0 || a.missing then .ok [] else prepareQuotients {} a.p p.ps
    match qs with | .error (.indivisible _ _) => throw (IO.userError "indivisible quotient") | _ => pure ()
    fields := fields ++ [("quotient_ns", toJson quotientNs)]
    if s.packed then
      let (packed, packingNs) ← measure fun _ => (p.ps.zip s.reports).map fun (a,r) =>
        (a, r.size, packMatrix r.size [a.left], packMatrix r.size a.right, packMatrix r.size [a.result],
          packMatrix r.size [(p.quotients.getD []).getD a.row []])
      let (_, multiplicationNs) ← measure fun _ => packed.map fun (product,s,l,b,c,q) =>
        if a.p == 0 then checkRows .plain s product.inner (Hex.Matrix.Packed.columns product.width b) l c
        else checkRowsMod .plain s product.inner a.p (Hex.Matrix.Packed.columns product.width b) l c q
      fields := fields ++ [("packing_ns", toJson packingNs), ("multiplication_ns", toJson multiplicationNs)]
  return Json.mkObj fields

end Hex.PolyDet.PackedBench

def main (args : List String) : IO UInt32 := do
  let some file := args.head? | throw (IO.userError "input JSON file required")
  let data ← IO.FS.readFile file
  let a ← match Lean.Json.parse data >>= Lean.fromJson? with
    | .ok a => pure a | .error e => throw (IO.userError e)
  let result ← Hex.PolyDet.PackedBench.run a (args.contains "--time")
  IO.println result.compress
  return 0
