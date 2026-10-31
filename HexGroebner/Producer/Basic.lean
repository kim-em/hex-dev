/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.F4
public import HexGroebner.CertificateBasisReplay

public section

namespace Hex.Groebner.Producer

structure Derivation where
  nodes : Array Certificate.Node := #[]
  allocatedTerms : Nat := 0
  termLimit : Nat := 1000000
  exponentBits : Nat := 64
  maxExponentBits : Nat := 0

inductive Error where
  | compute (error : ComputeError)
  | exhausted (resource : F4Resource)
  | representation (error : MonomialError)
  | matrix (error : MatrixError)
  | certificate (resource : Certificate.Resource)

structure Execution where
  workspace : Workspace
  derivation : Derivation

abbrev Work := ExceptT Error (StateM Execution)

def lift (operation : Computation α) : Work α := do
  let state ← get
  let (result,workspace) := operation.run state.workspace
  set { state with workspace }
  match result with
  | .ok value => return value
  | .error error => throw (.compute error)

/-- Reserve cumulative certificate term slots before allocating factors or
canonical conversion rows. Counts survive failed atomic F4 stages. -/
def reserveTerms (amount : Nat) : Work Unit := do
  let state ← get
  let count := state.derivation.allocatedTerms+amount
  if count > state.derivation.termLimit then throw (.certificate .allocatedTerms)
  set { state with derivation.allocatedTerms := count }

def reserveExponent (limits : Limits) (value : Nat) : Work Unit := do
  let bits := if value == 0 then 0 else value.log2+1
  lift (Computation.spend limits (bits/64+1))
  let data := (← get).derivation
  if bits > data.exponentBits then throw (.certificate .exponentBits)
  modify fun s => { s with derivation.maxExponentBits := max data.maxExponentBits bits }

/-- Append a node; factor payload is reserved by its constructor before allocation. -/
def emit (limits : Limits) (nodeLimit : Nat) (node : Certificate.Node) : Work Nat := do
  let data := (← get).derivation
  lift (Computation.spend limits 1)
  if data.nodes.size ≥ nodeLimit then throw (.matrix (.exhausted .traceNodes))
  lift (Computation.allocate limits 64)
  let index := data.nodes.size
  modify fun s => { s with derivation.nodes := data.nodes.push node }
  return index

def monomial (context : Context) (limits : Limits) (nodeLimit id root : Nat)
    (coefficient : UInt64 := 1) : Work Nat := do
  lift (Computation.spend limits (context.variables+1))
  lift (Computation.allocate limits (128+context.variables*32))
  reserveTerms 1
  let table := (← lift get).table
  for i in [:context.variables] do reserveExponent limits (table.exponent id i).toNat
  emit limits nodeLimit (.multiply [(table.exponentsAt id |>.toList,coefficient.toNat)] root)

structure Element where
  value : BasisElement
  root : Nat
  deriving Inhabited

def plain (elements : Array Element) : Array BasisElement := elements.map (·.value)

def sPolynomial (context : Context) (limits : Limits) (nodeLimit : Nat)
    (a b : Element) : Work Element := do
  let f := a.value.polynomial
  let g := b.value.polynomial
  let lcm ← lift (Computation.combine limits .lcm (f.monomial 0) (g.monomial 0))
  let x ← lift (Computation.combine limits .quotient lcm (f.monomial 0))
  let y ← lift (Computation.combine limits .quotient lcm (g.monomial 0))
  let left ← monomial context limits nodeLimit x a.root
  let right ← monomial context limits nodeLimit y b.root
  let negative ← emit limits nodeLimit (.scale (context.field.modulus.toNat-1) right)
  let root ← emit limits nodeLimit (.add left negative)
  let value ← lift (f.sPolynomial context limits g)
  return ⟨⟨value,max a.value.sugar b.value.sugar⟩,root⟩

end Hex.Groebner.Producer
