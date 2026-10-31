/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.NativeGather
import HexGroebner.ScanConformance

open Hex.Groebner.Native

open Hex.Groebner.ScanConformance

namespace Hex.Groebner.GatherConformance

private def gatherEqual (a b : Gather.Result) : Bool :=
  a.state.dense.data == b.state.dense.data && a.state.columns.data == b.state.columns.data &&
  a.state.coefficients.data == b.state.coefficients.data && a.state.cursor == b.state.cursor &&
  a.entries == b.entries && a.bytes == b.bytes && a.work == b.work && a.status == b.status

private def checked : Bool := Id.run do
  for p in [2,3,251,256,257,65521,65536,65537,2147483647] do
    let w := width p
    for seed in [:8] do
      let dense := packed w ((Array.range 31).map fun i =>
        if (i+seed)%3 == 0 then 0 else ((i+1)*69069+(seed+1)*12345)%p)
      let state : Gather.State := ⟨dense,{}, {},0⟩
      for factor in [1,p-1,p/2] do
        for quantum in [0,1,3,31,32,4096,4097] do
          for entries in [0,1,30,31,2^90] do
            for bytes in [0,4+w,30*(4+w),31*(4+w),2^90] do
              for work in [0,1,30,31,2^90] do
                if !gatherEqual (Gather.gather p.toUInt64 state 31 quantum entries bytes work factor.toUInt64)
                    (Gather.portable p.toUInt64 state 31 quantum entries bytes work factor.toUInt64) then return false
  return true

#guard checked

private def aliases : Bool := Id.run do
  let dense := packed 4 #[0,2,0,7,0,11,0]
  for state in [(⟨dense,dense,packed 4 (Array.replicate 7 1),0⟩ : Gather.State),
      ⟨dense,{}, {},0⟩,⟨dense,packed 4 #[0],packed 4 #[1],1⟩,
      ⟨dense,dense,dense,0⟩] do
    if !gatherEqual (Gather.gather 65537 state 7 4096 100 1000 100 3)
        (Gather.portable 65537 state 7 4096 100 1000 100 3) then return false
  let dense := packed 4 ((Array.replicate 31 1).set! 30 0)
  for state in [(⟨dense,dense,dense,1⟩ : Gather.State),
      ⟨dense,packed 4 (Array.replicate 31 0),dense,1⟩] do
    if !gatherEqual (Gather.gather 65537 state 31 4096 100 1000 100 3)
        (Gather.portable 65537 state 31 4096 100 1000 100 3) then return false
  return true

#guard aliases

def gatherRuntimeChecks : Bool := checked && aliases

private def malformed : Bool := Id.run do
  let dense := packed 1 #[1,0,2,0]
  for p in [0,1,2,7,2147483648] do
    for state in [(⟨dense,{}, {},0⟩ : Gather.State),⟨dense,{}, {},5⟩,
        ⟨dense,{}, {},2^90⟩,⟨dense,packed 1 #[1],{},0⟩,
        ⟨dense,packed 4 #[0],{},0⟩] do
      for stop in [0,3,4,5,2^90] do
        for q in [0,1,4,4096,4097,2^90] do
          for factor in [0,1,2,7,2147483647] do
            if !gatherEqual (Gather.gather p.toUInt64 state stop q 100 100 100 factor.toUInt64)
                (Gather.portable p.toUInt64 state stop q 100 100 100 factor.toUInt64) then return false
  return true

#guard malformed

def gatherMalformedChecks : Bool := malformed

set_option maxRecDepth 8192 in
/-- Exact row extraction also has an ordinary-kernel replay. -/
theorem gather_literal :
    (Gather.gather 7 ⟨packed 1 #[0, 2, 0, 3], {}, {}, 0⟩ 4 4096 4 20 4 2).state.coefficients.data =
      #[4, 6] := by
  unfold Gather.gather Gather.portable
  cases System.Platform.numBits_eq with
  | inl h => simp only [USize.size, h]; decide +kernel
  | inr h => simp only [USize.size, h]; decide +kernel

/-- info: 'Hex.Groebner.GatherConformance.gather_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gather_literal

end Hex.Groebner.GatherConformance
