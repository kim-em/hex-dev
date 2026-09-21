/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Policy
import Lean.Data.Json
namespace Refinement
open Hex Algebraic Policy Lean

/-- Checked persistent split of the lower defining polynomial, keeping the
same selected root. This experiment has finite rational endpoints. -/
def validSplit (keep discard : QPoly) : Bool :=
  keep*discard == reducible.polynomial &&
  valid ⟨keep,interval⟩ && rootCount discard interval == 0 &&
  (DensePoly.gcd keep discard).natDegree == 0

/-- The upper defining coefficient has a genuinely different raw literal
before and after the lower split, while denoting the same sqrt(2). -/
def top (mode : Nat) : Extension (Elem (base mode)) :=
  let e := base mode
  let alpha := pack e (DensePoly.monomial 1 1 + sqrt2)
  ⟨DensePoly.ofCoeffs #[-alpha,0,1], DensePoly.isZero, mode != 0⟩

def observeTop (mode : Nat) (a : Elem (top mode)) : Array (Array Rat) :=
  let r := (DensePoly.divMod (raw (top mode) a) (top mode).polynomial).2
  r.toArray.map (Policy.observe mode)

def lowerMap (a : Elem (base 0)) : Elem (base 2) := pack (base 2) (raw (base 0) a)
def mapPoly (p : DensePoly (Elem (base 0))) : DensePoly (Elem (base 2)) :=
  DensePoly.ofCoeffs (p.toArray.map lowerMap)
def upperMap (a : Elem (top 0)) : Elem (top 2) :=
  pack (top 2) (mapPoly (raw (top 0) a))

/-- Literal context identity includes the lower definition and the transported
upper definition. This serializable binding is intentionally not a hash. -/
structure Binding where
  lower : Array Rat
  upper : Array (Array Rat)
  lowerInterval : Array Rat
  positiveUpper : Bool
  deriving BEq

def binding (mode : Nat) : Binding :=
  ⟨(base mode).polynomial.toArray,
   (top mode).polynomial.toArray.map fun a => (raw (base mode) a).toArray,
   #[1,3/2],true⟩

structure Ticket where
  context : Binding
  operand : Array (Array Rat)

def literal (mode : Nat) (a : Elem (top mode)) : Array (Array Rat) :=
  (raw (top mode) a).toArray.map fun c => (raw (base mode) c).toArray

def accepts (mode : Nat) (a : Elem (top mode)) (ticket : Ticket) : Bool :=
  ticket.context == binding mode && ticket.operand == literal mode a

def jsonValue (a : Array (Array Rat)) : Json :=
  toJson (a.map fun c => c.map toString)

def checks : IO Unit := do
  unless validSplit sqrt2 sqrt3 && !validSplit sqrt3 sqrt2 do
    throw (IO.userError "split selected the wrong root")
  -- Transport the dependent upper polynomial, rather than reusing its old coefficients.
  unless (mapPoly (top 0).polynomial-(top 2).polynomial).isZero do
    throw (IO.userError "dependent defining polynomial changed denotation")
  unless (binding 0).upper != (binding 2).upper do
    throw (IO.userError "dependent defining coefficient did not change literal")
  let beta := pack (top 0) (DensePoly.monomial 1 1)
  let dependent := pack (top 0) (DensePoly.C (pack (base 0) (DensePoly.monomial 1 1 + sqrt2)))
  let live := #[beta,dependent,beta+dependent,beta*dependent,(beta+dependent)⁻¹]
  for a in live do
    let ticket : Ticket := ⟨binding 0,literal 0 a⟩
    let mapped := upperMap a
    unless observeTop 0 a == observeTop 2 mapped do
      throw (IO.userError "live value changed under transport")
    unless accepts 0 a ticket && !accepts 2 mapped ticket &&
        accepts 2 mapped ⟨binding 2,literal 2 mapped⟩ do
      throw (IO.userError "old ticket was accepted in a new context")
    IO.println (Json.mkObj [("before",jsonValue (observeTop 0 a)),
      ("after",jsonValue (observeTop 2 mapped)),
      ("oldStillValid",toJson (accepts 0 a ticket)),
      ("staleRejected",toJson (!accepts 2 mapped ticket))]).compress
  let a := live.getD 2 0
  let b := live.getD 3 0
  unless observeTop 2 (upperMap (a+b)) == observeTop 2 (upperMap a+upperMap b) &&
      observeTop 2 (upperMap (a*b)) == observeTop 2 (upperMap a*upperMap b) &&
      observeTop 2 (upperMap a⁻¹) == observeTop 2 (upperMap a)⁻¹ do
    throw (IO.userError "transport does not commute with arithmetic")
  -- A stale certificate for an unchanged literal still fails its full-context binding.
  let one : Elem (top 0) := 1
  unless !accepts 2 (upperMap one) ⟨binding 0,literal 0 one⟩ do
    throw (IO.userError "unchanged operand allowed stale context")
end Refinement

def main : IO Unit := Refinement.checks
