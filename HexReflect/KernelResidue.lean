/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Kernel
public import HexMvPoly.KernelResidue

@[expose] public section

namespace Hex.Reflect.Kernel

open Hex.MvPoly.Kernel

/-- Integer constants replay through the shared natural-residue operations. -/
def constantMod (p k : Nat) : Int → PolyList Nat
  | .ofNat n => smulMod p n (oneMod p k)
  | .negSucc n => negMod p (smulMod p (n + 1) (oneMod p k))

/-- A formal variable, including the trivial residue ring. -/
def atomMod (p k i : Nat) : PolyList Nat :=
  if Nat.blt 1 p then [(unitExp k i, 1)] else []

/-- Structural exponentiation using the shared residue multiplication. -/
def powerMod (p k : Nat) (a : PolyList Nat) : Nat → PolyList Nat
  | 0 => oneMod p k
  | n + 1 => mulMod p (powerMod p k a n) a

/-- Replay ring syntax with natural residues; exponents are never reduced. -/
def ringListMod (p k : Nat) : RingExpr → PolyList Nat
  | .num z | .intCast z => constantMod p k z
  | .natCast z => constantMod p k (Int.ofNat z)
  | .var i => atomMod p k i
  | .add a b => addMod p (ringListMod p k a) (ringListMod p k b)
  | .sub a b => subMod p (ringListMod p k a) (ringListMod p k b)
  | .mul a b => mulMod p (ringListMod p k a) (ringListMod p k b)
  | .neg a => negMod p (ringListMod p k a)
  | .pow a n => powerMod p k (ringListMod p k a) n

theorem canonical_constantMod (p k : Nat) (z : Int) : CanonicalMod p k (constantMod p k z) := by
  cases z with
  | ofNat n => exact smulMod_canonical p n (oneMod_canonical p k)
  | negSucc n => exact negMod_canonical p (smulMod_canonical p (n + 1) (oneMod_canonical p k))

theorem canonical_atomMod (p k i : Nat) : CanonicalMod p k (atomMod p k i) := by
  unfold atomMod
  split <;> simp_all [CanonicalMod, Canonical, length_unitExp, Nat.blt_eq]

theorem canonical_powerMod (p k : Nat) (a : PolyList Nat) (n : Nat)
    (ha : CanonicalMod p k a) : CanonicalMod p k (powerMod p k a n) := by
  induction n with
  | zero => exact oneMod_canonical p k
  | succ n ih => exact mulMod_canonical p ih ha

theorem canonical_ringListMod (p k : Nat) (e : RingExpr) :
    CanonicalMod p k (ringListMod p k e) := by
  induction e with
  | num z | intCast z => exact canonical_constantMod p k z
  | natCast z => exact canonical_constantMod p k (Int.ofNat z)
  | var i => exact canonical_atomMod p k i
  | add a b ha hb => exact addMod_canonical p ha hb
  | sub a b ha hb => exact subMod_canonical p ha hb
  | mul a b ha hb => exact mulMod_canonical p ha hb
  | neg a ha => exact negMod_canonical p ha
  | pow a n ha => exact canonical_powerMod p k _ n ha

end Hex.Reflect.Kernel
