/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.TarskiInterpret
public import HexRealRootsMathlib.TarskiSum
public import HexRealRoots.Map
public import Mathlib.FieldTheory.IsRealClosed.Basic

public section

namespace HexRealRootsMathlib.Tarski

open Hex HexPolyMathlib.Interpret

/-- Every accepted shared query certificate gives the sum of signs at the
distinct roots in its open interval. Coefficient representations need only
reflect zero and preserve the actual operations; endpoint representations
may differ from coefficients. This includes infinite endpoints, constant
heads, zero queries and common factors, with no producer-success premise. -/
theorem check_rootSum
    {D : Type u} {E : Type v} {Ctx : Type w} {R : Type u₁}
    [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    [DecidableEq E] [DecidableEq Ctx]
    [Field R] [DecidableEq R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (f : D → R) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hnat : ∀ n : Nat, f (n : D) = (n : R))
    (sign : D → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (point : E → R) (ends : EndpointSigns D E)
    (hcompare : ∀ a b, ends.compare a b = (SignType.sign (point a - point b) : Int))
    (heval : ∀ p a, ends.evalSign p a = (SignType.sign ((interpret f hz p).eval (point a)) : Int))
    (context : Ctx) (p q : DensePoly D) (a b : Endpoint E) (value : Int)
    (certificate : TarskiCertificate D E Ctx)
    (checked : TarskiCertificate.check sign ends context p q a b value certificate = true) :
    value = rootSum (interpret f hz p) (interpret f hz q) (a.map point) (b.map point) := by
  sorry

end HexRealRootsMathlib.Tarski
