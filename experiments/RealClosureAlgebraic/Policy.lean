/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Algebraic
namespace Policy
open Hex Algebraic

/-- Experimental algorithm parameters, not a coefficient-operation interface.
`zeroRem` is valid only for the fixture's selected root. -/
structure Extension (R : Type) [Zero R] [DecidableEq R] where
  polynomial : DensePoly R
  zeroRem : DensePoly R → Bool
  retain : Bool

/-- The type enforces literal nonzero storage. Semantic zero correctness is
validated for the fixtures, not asserted as a theorem or a field instance. -/
structure Elem {R : Type} [Zero R] [DecidableEq R] (e : Extension R) where
  value : Option {q : DensePoly R // q.isZero = false}


section
variable {R : Type} [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R] [Div R] [Inv R] [Neg R] [NatCast R]
variable (e : Extension R)
instance : DecidableEq (Elem e) := fun a b =>
  if h : a.value = b.value then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse (fun hab => h (congrArg Elem.value hab))
instance : Zero (Elem e) := ⟨⟨none⟩⟩
def raw (a : Elem e) : DensePoly R := match a.value with | none => 0 | some q => q.val

def pack (q : DensePoly R) : Elem e :=
  let r := (DensePoly.divMod q e.polynomial).2
  if e.zeroRem r then ⟨none⟩ else
    let stored := if e.retain then r else q
    if h : stored.isZero = false then ⟨some ⟨stored,h⟩⟩ else ⟨none⟩

instance : One (Elem e) := ⟨pack e 1⟩
instance : NatCast (Elem e) := ⟨fun n => pack e (DensePoly.C (n : R))⟩
instance : Add (Elem e) := ⟨fun a b => pack e (raw e a+raw e b)⟩
instance : Sub (Elem e) := ⟨fun a b => pack e (raw e a-raw e b)⟩
instance : Neg (Elem e) := ⟨fun a => pack e (-raw e a)⟩
instance : Mul (Elem e) := ⟨fun a b => pack e (raw e a*raw e b)⟩
instance : Inv (Elem e) := ⟨fun a =>
  if raw e a == 0 then 0 else
    let g := DensePoly.monicize (DensePoly.gcd e.polynomial (raw e a))
    let h := (DensePoly.divMod e.polynomial g).1
    let eg := DensePoly.xgcd (raw e a) h
    pack e (DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left)⟩
instance : Div (Elem e) := ⟨fun a b => a*b⁻¹⟩
end

/-- Modes 0/1 retain the reducible descriptor; 2/3 use the minimal polynomial.
Only mode 3 exploits its known irreducibility. -/
def base (mode : Nat) : Extension Rat :=
  let policy := mode%4
  let p := if policy < 2 then reducible.polynomial else sqrt2
  ⟨p, (fun r =>
    let result := if policy == 3 then r.isZero else
      if r.isZero then true else if r.natDegree == 0 then false else
        let g := DensePoly.gcd p r
        g.natDegree > 0 && rootCount g interval == 1
    if mode >= 4 then dbg_trace "zero,0"; result else result), policy != 0⟩

def upper (mode : Nat) : Extension (Elem (base mode)) :=
  let e := base mode
  let alpha := pack e (DensePoly.monomial 1 1)
  ⟨DensePoly.ofCoeffs #[-alpha,0,1],
    (fun r => if mode >= 4 then dbg_trace "zero,1"; r.isZero else r.isZero), mode%4 != 0⟩

/-- Shared raw input: all modes denote the same a+b*sqrt(2). -/
def coefficient (mode i salt : Nat) : Elem (base mode) :=
  pack (base mode) (DensePoly.ofCoeffs #[(((i+salt)%5+1 : Nat) : Rat),(((i+salt)%3+1 : Nat) : Rat)] +
    DensePoly.scale ((i%2+1 : Nat) : Rat) sqrt2)

def input (mode n salt : Nat) : DensePoly (Elem (base mode)) :=
  DensePoly.ofCoeffs ((List.range n).toArray.map fun i => coefficient mode i salt)

def nestedInput (mode n salt : Nat) : DensePoly (Elem (upper mode)) :=
  DensePoly.ofCoeffs ((List.range n).toArray.map fun i =>
    pack (upper mode) (DensePoly.ofCoeffs #[coefficient mode i salt, coefficient mode (i+1) (salt+1)]))

def observe (mode : Nat) (a : Elem (base mode)) : Array Rat :=
  (canonical (raw (base mode) a)).toArray

def observeNested (mode : Nat) (a : Elem (upper mode)) : Array (Array Rat) :=
  let r := (DensePoly.divMod (raw (upper mode) a) (upper mode).polynomial).2
  r.toArray.map (observe mode)

/-- Maximum stored degrees at the two levels, including zero as degree zero. -/
def degrees (mode : Nat) (a : Elem (upper mode)) : Nat × Nat :=
  let p := raw (upper mode) a
  (p.natDegree, p.toArray.foldl (fun n c => max n (raw (base mode) c).natDegree) 0)
end Policy
