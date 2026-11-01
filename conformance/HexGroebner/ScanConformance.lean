/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.NativeScan

open Hex.Groebner.Native
open Hex.Groebner.Native.Scan

namespace Hex.Groebner.ScanConformance

def packed (width : Nat) (values : Array Nat) : ByteArray :=
  values.foldl (fun bytes value =>
    (List.range width).foldl (fun b i => b.push (UInt8.ofNat (value / 256^i))) bytes) ByteArray.empty

def row (columns coefficients : Array Nat) (sugar : Nat) : Scan.Pivot :=
  ⟨packed 4 columns, packed 1 coefficients, sugar⟩

def pivots : Array Scan.Pivot := #[row #[0,1,5] #[1,2,3] 9, row #[2,4] #[1,6] 11]
def slots : ByteArray := packed 4 #[1,0,2,0,0,0]
def initial : Scan.State := { dense := packed 1 #[3,4,2,0,0,0], column := 0, last := 2, chargedUntil := 0 }

def run (quantum : Nat) (provenance : Bool) (native : Bool := false) : Option Scan.Result := Id.run do
  let mut state := initial
  let mut events : Array (Nat × UInt64) := #[]
  let mut work := 0
  let mut reductions := 0
  let mut traces := 0
  for _ in [:100] do
    let result := (if native then transition else portable) 7 slots pivots state quantum (1000-work) (100-traces) provenance
    state := result.state
    events := events ++ result.events
    work := work+result.work
    reductions := reductions+result.reductions
    traces := traces+result.traceNodes
    if result.status == 1 then return some { state, events, work, reductions, traceNodes := traces, status := 1 }
    if result.status != 0 then return none
  return none

def equal (a b : Scan.Result) : Bool :=
  a.state.dense.data == b.state.dense.data && a.state.column == b.state.column &&
  a.state.last == b.state.last && a.state.chargedUntil == b.state.chargedUntil &&
  a.state.leading == b.state.leading && a.state.pending == b.state.pending &&
  a.state.entry == b.state.entry && a.state.sugar == b.state.sugar &&
  a.state.factor == b.state.factor && a.events == b.events && a.work == b.work &&
  a.reductions == b.reductions && a.traceNodes == b.traceNodes && a.status == b.status

#guard match run 4096 true with
  | some result => result.state.dense.data == #[0,5,0,0,2,5] &&
    result.state.leading == 2 && result.state.sugar == 11 && result.work == 11 &&
    result.events == #[(0,3),(1,2)] && result.reductions == 2
  | none => false

#guard (List.range 16).all fun k =>
  match run (k+1) true, run 4096 true with
  | some a,some b => equal a b
  | _,_ => false

#guard (portable 7 slots pivots initial 4097 1000 100 true).status == 4
#guard (portable 7 slots pivots initial 4096 0 100 true).status == 2
#guard (portable 7 slots pivots initial 4096 1000 0 true).status == 3
#guard match run 1 false with
  | some result => result.events.isEmpty && result.traceNodes == 0 && result.reductions == 2
  | none => false

#guard (List.range 32).all fun k =>
  match run (k+1) true true, run 4096 true false with
  | some a,some b => equal a b
  | _,_ => false

#guard (List.range 20).all fun q => (List.range 25).all fun work =>
  (List.range 4).all fun traces =>
    equal (transition 7 slots pivots initial q work traces true)
      (portable 7 slots pivots initial q work traces true)

private def fuzz : Bool := Id.run do
  for p in [2,3,251,256,257,65521,65536,65537,65538,2147483646,2147483647] do
    let w := Hex.Groebner.Native.width p
    for seed in [:12] do
      let mut rows : Array Scan.Pivot := #[]
      let mut indices := Array.replicate 31 0
      for (first,i) in (#[0,2,5,7]).zipIdx do
        let support := (Array.range (31-first)).map (·+first)
        let values := support.map fun j => if j == first then 1 else
          ((seed+1)*12345+(i+1)*69069+j*17)%(p-1)+1
        rows := rows.push ⟨packed 4 support,packed w values,2^90+(i+1)*17⟩
        indices := indices.set! first (i+1)
      let slots := packed 4 indices
      let input : Scan.State := { dense := packed w ((Array.range 31).map fun i =>
        ((seed+1)*69069+(i+1)*12345)%p),column := 0,last := 30,chargedUntil := 0 }
      for q in [0,1,2,7,31,64,4096] do
        for work in [0,1,31,32,64,127,4096,2^90] do
          for trace in [0,1,3,4,2^90] do
            for provenance in [false,true] do
              if !equal (transition p.toUInt64 slots rows input q work trace provenance)
                  (portable p.toUInt64 slots rows input q work trace provenance) then return false
  return true

#guard fuzz

private def aliases : Bool := Id.run do
  let p := 65537
  let w := 4
  let slots := packed 4 #[1,0,2,0,0,0]
  let rows : Array Scan.Pivot := #[⟨packed 4 #[0,2,5],packed w #[1,p-1,p-2],11⟩,
    ⟨packed 4 #[2,3],packed w #[1,p-3],2^90⟩]
  let input : Scan.State := { dense := slots,column := 0,last := 5,chargedUntil := 0 }
  if !equal (transition p.toUInt64 slots rows input 4096 1000 100 true)
      (portable p.toUInt64 slots rows input 4096 1000 100 true) then return false
  let dense := packed w (Array.replicate 9 1)
  let rows : Array Scan.Pivot := #[⟨packed 4 (Array.range 9),dense,5⟩]
  let slots := packed 4 #[1,0,0,0,0,0,0,0,0]
  let input : Scan.State := { dense,column := 0,last := 8,chargedUntil := 0 }
  return equal (transition p.toUInt64 slots rows input 4096 1000 100 true)
    (portable p.toUInt64 slots rows input 4096 1000 100 true)

#guard aliases

private def malformed : Bool := Id.run do
  let mut cases : Array (UInt64 × ByteArray × Array Scan.Pivot × Scan.State) := #[]
  cases := cases.push (1,slots,pivots,initial)
  cases := cases.push (2147483648,slots,pivots,initial)
  cases := cases.push (7,slots.extract 0 5,pivots,initial)
  cases := cases.push (7,slots,pivots,{ initial with column := 7 })
  cases := cases.push (7,slots,pivots,{ initial with column := 2^90 })
  cases := cases.push (7,slots,pivots,{ initial with last := 6 })
  cases := cases.push (7,slots,pivots,{ initial with pending := 3 })
  cases := cases.push (7,slots,pivots,{ initial with pending := 1,entry := 4 })
  cases := cases.push (7,slots,pivots,{ initial with factor := 7 })
  cases := cases.push (7,slots,pivots,{ initial with dense := packed 1 #[7,0,0,0,0,0] })
  cases := cases.push (7,packed 4 #[3,0,0,0,0,0],pivots,initial)
  for bad in [row #[0,0,5] #[1,2,3] 0,row #[0,6] #[1,2] 0,
      row #[0,1] #[2,3] 0,row #[0,1] #[1,7] 0,
      row #[0,1] #[1,0] 0,⟨packed 1 #[0,1],packed 1 #[1],0⟩] do
    cases := cases.push (7,slots,#[bad],initial)
  for (p,s,r,input) in cases do
    for quantum in [0,1,2,3,8,4096,4097,2^90] do
      if !equal (transition p s r input quantum 1000 100 true)
          (portable p s r input quantum 1000 100 true) then return false
  return true

#guard malformed

def runtimeChecks : Bool := fuzz && aliases && malformed &&
  (List.range 20).all fun q => (List.range 25).all fun work =>
  (List.range 4).all fun traces =>
    equal (transition 7 slots pivots initial q work traces true)
      (portable 7 slots pivots initial q work traces true)

def runtimeWideChecks : Bool := Id.run do
  for p in [3,251,257,32003,65521,65537,2147483647] do
    let w := Hex.Groebner.Native.width p
    let support := Array.range 16
    let values := (Array.range 16).map fun i => if i == 0 then 1 else (i*7919)%(p-1)+1
    let slots := packed 4 (#[1] ++ Array.replicate 30 0)
    for bad in [1:16] do
      for kind in [:5] do
        let columns := if kind == 0 then support.set! bad support[bad-1]! else
          if kind == 1 then support.set! bad 4294967295 else support
        let coefficients := if kind == 2 then values.set! bad 0 else
          if kind == 3 then values.set! bad p else values
        let dense := if kind == 4 then (Array.replicate 31 1).set! bad p else Array.replicate 31 1
        let pivots : Array Scan.Pivot := #[⟨packed 4 columns, packed w coefficients, 2^90⟩]
        let initial : Scan.State := { dense := packed w dense, column := 0, last := 15, chargedUntil := 0 }
        for quantum in [1,2,7,8,9,16,17,32,4096] do
          for provenance in [false,true] do
            if !equal (transition p.toUInt64 slots pivots initial quantum 100000 100 provenance)
                (portable p.toUInt64 slots pivots initial quantum 100000 100 provenance) then return false
  -- Valid strided vectors exercise gather/scatter independently of malformed fallback.
  for p in [3,251,257,32003,65521,65537,65538,2147483646,2147483647] do
    let w := Hex.Groebner.Native.width p
    for stride in [2,3] do
      let support := (Array.range 16).map (·*stride)
      let columns := 15*stride+1
      let slots := packed 4 (#[1] ++ Array.replicate (columns-1) 0)
      let values := (Array.range 16).map fun i => if i == 0 then 1 else (i*7919)%(p-1)+1
      let pivots : Array Scan.Pivot := #[⟨packed 4 support,packed w values,2^90⟩]
      let initial : Scan.State := {
        dense := packed w (Array.replicate columns (p-1))
        column := 0
        last := columns-1
        chargedUntil := 0 }
      for quantum in [1,7,8,9,16,17,32,4096] do
        for provenance in [false,true] do
          if !equal (transition p.toUInt64 slots pivots initial quantum 100000 100 provenance)
              (portable p.toUInt64 slots pivots initial quantum 100000 100 provenance) then return false
  -- Strided gathers require a full four-byte read, even for narrow scalars.
  for p in [3,251,257,32003,65521,65537] do
    let w := Hex.Groebner.Native.width p
    for stride in [1,2,3] do
      for padding in [:4] do
        let support := (Array.range 16).map (·*stride)
        let columns := 15*stride+1+padding
        let slots := packed 4 (#[1] ++ Array.replicate (columns-1) 0)
        let values := (Array.range 16).map fun i => if i == 0 then 1 else (i*7919)%(p-1)+1
        let pivots : Array Scan.Pivot := #[⟨packed 4 support,packed w values,2^90⟩]
        let initial : Scan.State := {dense:=packed w (Array.replicate columns (p-1)),column:=0,last:=columns-1,chargedUntil:=0}
        for quantum in [7,8,9,16,17,31,32,4096] do
          if !equal (transition p.toUInt64 slots pivots initial quantum 100000 100 true)
              (portable p.toUInt64 slots pivots initial quantum 100000 100 true) then return false
    let dense := packed w (Array.replicate 16 1)
    let pivots : Array Scan.Pivot := #[⟨packed 4 (Array.range 16),dense,5⟩]
    let slots := packed 4 (#[1] ++ Array.replicate 15 0)
    let initial : Scan.State := {dense,column:=0,last:=15,chargedUntil:=0}
    if !equal (transition p.toUInt64 slots pivots initial 4096 10000 100 true)
        (portable p.toUInt64 slots pivots initial 4096 10000 100 true) then return false
  return true

#guard runtimeWideChecks

set_option maxRecDepth 8192 in
/-- The transparent scan model replays independently of the native implementation. -/
theorem scan_literal :
    (transition 7 slots pivots initial 4096 1000 100 true).state.dense.data =
      #[0, 5, 0, 0, 2, 5] := by decide +kernel

/-- info: 'Hex.Groebner.ScanConformance.scan_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scan_literal

end Hex.Groebner.ScanConformance
