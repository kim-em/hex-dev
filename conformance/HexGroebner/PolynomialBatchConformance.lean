/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Polynomial

namespace Hex.Groebner.PolynomialBatchConformance
open Computation

/-- The scalar multiplication loop preceding support batching. -/
private def reference (limits : Limits) (p : Polynomial) (monomial : Nat) :
    Computation Polynomial := do
  if (← get).table.degree monomial == 0 then return p
  allocate limits p.support.size
  let mut support := ByteArray.emptyWithCapacity p.support.size
  for i in [:p.size] do
    let id ← combine limits .product (p.monomial i) monomial
    support := Packed.push .u32 support id.toUInt64
  return { p with support }

private def sameTable (a b : MonomialTable) : Bool :=
  a.arity == b.arity && a.width == b.width && a.count == b.count &&
    a.exponents == b.exponents && a.metadata == b.metadata && a.workspace == b.workspace &&
    a.index.heads == b.index.heads && a.index.links == b.index.links &&
    a.hashBits == b.hashBits && a.work == b.work

private def check (context : Context) (limits : Limits) (workspace : Workspace)
    (p : Polynomial) (monomial : Nat) : Bool :=
  let (actual,s) := (p.multiply context limits monomial).run workspace
  let (expected,t) := (reference limits p monomial).run workspace
  let result := match actual,expected with
    | .ok x,.ok y => x.support == y.support && x.coefficients == y.coefficients
    | .error x,.error y => x == y
    | _,_ => false
  result && sameTable s.table t.table && s.statistics == t.statistics

/-- Compare all returned bytes and workspace counters with the original scalar
loop, including successful lookups, insertions, allowance prefixes and overflow. -/
def checks (seed : Nat) (full := true) : Bool := Id.run do
  let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  for arity in (if full then [1,3,21] else [1,3]) do
    let context : Context := ⟨field,arity,.grevlex⟩
    for n in (if full then [0,1,2,63,64,65,129] else [1,2,65]) do
      for step in ([1,257,65537] : List Nat) do
        let mut table : MonomialTable := { arity,hashBits := if seed%3 == 0 then 0 else 64 }
        for id in [:n+4] do
          let next := table.internOwned (Array.replicate arity (id*step).toUInt64)
            1000 10000000 1000000000
          let .ok _ := next.result | return false
          table := next.table
        let statistics : Statistics := { work := 17, allocatedBytes := 11, pairs := 7, rounds := 3, matrixCalls := 2 }
        let workspace : Workspace := ⟨table,statistics⟩
        let mut p : Polynomial := {}
        for i in [:n] do
          p := ⟨Packed.push .u32 p.support (n-1-i).toUInt64,
            Packed.push field.width p.coefficients (1+seed%6).toUInt64⟩
        for monomial in [0,1,3,n+3] do
          for native in [false,true] do
            let limits : Limits := { work := 1000000000, packedBytes := 1000000000, monomials := 1000000, nativeMonomials := native }
            let total := ((reference limits p monomial).run workspace).2.statistics.work
            for work in [0,16,17,18,19,total-1,total,total+1,2^90] do
              if !check context { limits with work } workspace p monomial then return false
            for packedBytes in [0,11+table.bytes+p.support.size-1,
                11+table.bytes+p.support.size,11+table.bytes+p.support.size+1,2^90] do
              if !check context { limits with packedBytes } workspace p monomial then return false
            for monomials in [0,table.count,table.count+1,2^90] do
              if !check context { limits with monomials } workspace p monomial then return false
            if n ≤ 2 then
              for work in [:total+1] do
                if !check context { limits with work } workspace p monomial then return false
  let mut table : MonomialTable := { arity := 1 }
  for exponent in ([0,4294967295] : List UInt64) do
    let next := table.internOwned #[exponent] 100 1000000
    let .ok _ := next.result | return false
    table := next.table
  let p : Polynomial := ⟨Packed.push .u32 {} 1,Packed.push field.width {} 1⟩
  for work in [:12] do
    if !check ⟨field,1,.grevlex⟩ { work } ⟨table,{}⟩ p 1 then return false
  return true

#guard checks 0 false

end Hex.Groebner.PolynomialBatchConformance
