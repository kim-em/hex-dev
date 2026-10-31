/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Runtime
public import HexMvPoly.Basic

public section

/-! Canonical packed prime-field polynomials. Only interchange decodes exponent
vectors. Arithmetic combines sorted supports directly; it never uses tree maps
or boxed coefficient arrays as the computational polynomial representation. -/

namespace Hex.Groebner
namespace Polynomial
open Computation

/-- Payload bytes occupied by a polynomial in the selected coefficient encoding. -/
def bytes (context : Context) (p : Polynomial) : Nat := p.size * (4 + context.field.width.bytes)

private def append (field : PrimeField) (p : Polynomial) (id : Nat) (c : UInt64) : Polynomial :=
  { support := Packed.push .u32 p.support id.toUInt64
    coefficients := Packed.push field.width p.coefficients c }

/-- Normalize raw input, preserving canonical coefficients and every exponent.
Duplicate monomials are summed, zero terms removed, and supports sorted once. -/
def normalize (context : Context) (limits : Limits) (index : Nat)
    (raw : RawPolynomial) : Computation Polynomial := do
  spend limits (raw.size * (context.variables + 1))
  let mut coefficients : Std.HashMap Nat UInt64 := {}
  for term in [:raw.size] do
    let t := raw[term]!
    if t.exponents.size != context.variables then throw (.arity index term)
    if t.coefficient ≥ context.field.modulus then throw (.coefficient index term)
    if t.coefficient != 0 then
      let mut exponents := Array.emptyWithCapacity context.variables
      for e in t.exponents do
        if e > 4294967295 then throw (.representation .exponent)
        exponents := exponents.push e.toUInt64
      let id ← intern limits exponents
      let sum := coefficients[id]?.getD 0 + t.coefficient
      let sum := if sum ≥ context.field.modulus then sum - context.field.modulus else sum
      coefficients := if sum == 0 then coefficients.erase id else coefficients.insert id sum
  let ids ← sort context limits (coefficients.toArray.map Prod.fst)
  allocate limits (ids.size * (4 + context.field.width.bytes))
  let mut p : Polynomial := {}
  for id in ids do p := append context.field p id coefficients[id]!
  return p

/-- Scale canonical coefficients without changing the ordered support. -/
def scale (context : Context) (limits : Limits) (p : Polynomial) (factor : UInt64) :
    Computation Polynomial := do
  if factor == 1 || p.size == 0 then return p
  if factor == 0 then return {}
  spend limits p.size
  allocate limits p.coefficients.size
  let ctx := context.field.barrett
  let mut coefficients := ByteArray.emptyWithCapacity p.coefficients.size
  for i in [:p.size] do
    coefficients := Packed.push context.field.width coefficients (ctx.mulMod (p.coefficient context.field i) factor)
  return { p with coefficients }

/-- Divide by the leading coefficient once per polynomial. -/
def monic (context : Context) (limits : Limits) (p : Polynomial) : Computation Polynomial := do
  if p.size == 0 || p.coefficient context.field 0 == 1 then return p
  let factor ← inverse context.field limits (p.coefficient context.field 0)
  scale context limits p factor

/-- Multiply by an interned monomial, preserving the selected mathematical order. -/
def multiply (_context : Context) (limits : Limits) (p : Polynomial) (monomial : Nat) :
    Computation Polynomial := do
  if (← get).table.degree monomial == 0 then return p
  allocate limits p.support.size
  let mut support := ByteArray.emptyWithCapacity p.support.size
  for i in [:p.size] do
    let id ← combine limits .product (p.monomial i) monomial
    support := Packed.push .u32 support id.toUInt64
  return { p with support }

/-- Linear subtraction of canonical supports, with exact modular coefficients. -/
def subtract (context : Context) (limits : Limits) (p q : Polynomial) : Computation Polynomial := do
  let table := (← get).table
  spend limits ((p.size + q.size) * (context.variables + 1))
  allocate limits ((p.size + q.size) * (4 + context.field.width.bytes))
  let mut result : Polynomial := {}
  let mut i := 0
  let mut j := 0
  for _ in [:p.size + q.size] do
    if i ≥ p.size && j ≥ q.size then break
    let order := if i ≥ p.size then .lt else if j ≥ q.size then .gt else
      table.compare context.order (p.monomial i) (q.monomial j)
    match order with
    | .gt =>
      result := append context.field result (p.monomial i) (p.coefficient context.field i)
      i := i + 1
    | .lt =>
      result := append context.field result (q.monomial j) (context.field.modulus - q.coefficient context.field j)
      j := j + 1
    | .eq =>
      let a := p.coefficient context.field i
      let b := q.coefficient context.field j
      let c := if a ≥ b then a - b else a + context.field.modulus - b
      if c != 0 then result := append context.field result (p.monomial i) c
      i := i + 1
      j := j + 1
  return result

/-- S-polynomial of two nonzero monic polynomials, using their actual LCM. -/
def sPolynomial (context : Context) (limits : Limits) (f g : Polynomial) : Computation Polynomial := do
  let lcm ← combine limits .lcm (f.monomial 0) (g.monomial 0)
  let a ← combine limits .quotient lcm (f.monomial 0)
  let b ← combine limits .quotient lcm (g.monomial 0)
  let f ← multiply context limits f a
  let g ← multiply context limits g b
  subtract context limits f g

/-- Decode canonical interchange terms; no coefficient or exponent is reduced
or reinterpreted during conversion. -/
def toRaw (field : PrimeField) (table : MonomialTable) (p : Polynomial) : RawPolynomial :=
  (Array.range p.size).map fun i =>
    ⟨table.exponentsAt (p.monomial i), p.coefficient field i⟩

/-- Convert a polynomial to the existing lawful `Hex.MvPoly` interchange API.
The fixed-arity check is explicit; hot loops never call this conversion. -/
def toMvPoly (order : TermOrder) (p : Nat) [ZMod64.Bounds p] (n : Nat)
    (raw : RawPolynomial) : Option (MvPoly n (ZMod64 p) (order.cmp n)) := do
  let terms ← raw.toList.mapM fun term => do
    if h : term.exponents.size = n then
      if term.coefficient.toNat ≥ p then none else
        some (⟨term.exponents, h⟩, ZMod64.ofNat p term.coefficient.toNat)
    else none
  return MvPoly.ofTerms terms

/-- Convert `Hex.MvPoly` terms into raw input without changing their coefficients. -/
def ofMvPoly (order : TermOrder) (p : Nat) [ZMod64.Bounds p] (n : Nat)
    (f : MvPoly n (ZMod64 p) (order.cmp n)) : RawPolynomial :=
  f.termsList.toArray.map fun (m, c) => ⟨m.toArray, c.val⟩

end Polynomial
end Hex.Groebner
