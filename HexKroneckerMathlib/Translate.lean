/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.ExprSound
public import HexReflect.Kernel
public import HexMvPolyMathlib.Aeval

public section

namespace HexKroneckerMathlib

open Hex.Kronecker
open scoped HexMvPolyMathlib
attribute [local instance 2000] Ring.toGrindRing

/-- Preserve the retained ring tree, including subtraction and powers. -/
@[expose] def fromGrindImpl : Lean.Grind.CommRing.Expr → Expr
  | .num z | .intCast z => .int z
  | .natCast n => .int n
  | .var i => .atom i
  | .add a b => .add (fromGrindImpl a) (fromGrindImpl b)
  | .sub a b => .sub (fromGrindImpl a) (fromGrindImpl b)
  | .mul a b => .mul (fromGrindImpl a) (fromGrindImpl b)
  | .neg a => .neg (fromGrindImpl a)
  | .pow a n => .pow (fromGrindImpl a) n

/-- Primitive recursor form used when replaying the reflected syntax in the kernel. -/
@[expose] noncomputable def fromGrind (e : Lean.Grind.CommRing.Expr) : Expr :=
  Lean.Grind.CommRing.Expr.rec Expr.int (fun n => .int (Int.ofNat n)) Expr.int Expr.atom
    (fun _ a => .neg a) (fun _ _ a b => .add a b)
    (fun _ _ a b => .sub a b) (fun _ _ a b => .mul a b) (fun _ n a => .pow a n) e

@[csimp] theorem fromGrind_eq_impl : fromGrind = fromGrindImpl := by
  funext e
  induction e <;> simp_all [fromGrind, fromGrindImpl]

/-- Validate every variable against the sealed atom table. -/
@[expose] def fromGrind? (k : Nat) (e : Lean.Grind.CommRing.Expr) : Option Expr :=
  let t := fromGrind e
  if t.wellFormed k then some t else none

theorem fromGrind_wellFormed {k : Nat} {e : Lean.Grind.CommRing.Expr} {t : Expr}
    (h : fromGrind? k e = some t) : t.WellFormed k := by
  unfold fromGrind? at h
  dsimp only at h
  split at h
  · cases Option.some.inj h
    assumption
  · contradiction

theorem fromGrind_denote {R : Type u} [CommRing R]
    (ctx : Lean.RArray R) (e : Lean.Grind.CommRing.Expr) :
    (fromGrind e).denote ctx.get = e.denote ctx := by
  induction e <;> simp_all [fromGrind, Expr.denote,
    Lean.Grind.CommRing.Expr.denote, Lean.Grind.CommRing.Var.denote,
    Lean.Grind.CommRing.denoteInt_eq]

/-- Transport an identity of translated trees back to the retained syntax. -/
theorem denote_transport {R : Type u} [CommRing R] (ctx : Lean.RArray R)
    (l r : Lean.Grind.CommRing.Expr)
    (h : (fromGrind l).denote ctx.get = (fromGrind r).denote ctx.get) :
    l.denote ctx = r.denote ctx := by
  simpa only [fromGrind_denote] using h

end HexKroneckerMathlib
