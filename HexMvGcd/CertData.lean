/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Instances
public import HexModArith.Modulus
public import HexPolyFp.Field

@[expose] public section

/-!
Certificate data for multivariate gcd replay. The coefficient ring is a fixed
parameter of every recursive certificate. Optional leaves are parameterized
separately, so the integer evidence inside a rational lift cannot contain
another rational lift or replace the integer arithmetic.
-/

namespace Hex.MvPoly

universe u v w

namespace Cert

/-- Optional leaf data at each arity and monomial order. -/
abbrev Leaves := (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
  [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type v

mutual
  /-- Recursive coprimality evidence over one fixed coefficient ring. -/
  inductive Coprime (R : Type u) [Lean.Grind.CommRing R] (E : Leaves.{v}) :
      (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (max u v)
    | unit {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : Coprime R E n cmp
    | base {cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (u v : R) : Coprime R E 0 cmp
    | bezout {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (u v : MvPoly n R cmp) : Coprime R E n cmp
    | leaf {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (data : E n cmp) : Coprime R E n cmp
    | split {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
        [IsMonomialOrder cmp'] (P : ZMod64.Prime)
        (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
        (a : Fin n → @ZMod64 P.m P.bounds)
        (α β : @FpPoly P.m P.bounds)
        (left right : Content R E n cmp') (rest : Coprime R E n cmp') :
        Coprime R E (n + 1) cmp
    | splitBezout {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
        [IsMonomialOrder cmp'] (u v : MvPoly (n + 1) R cmp)
        (r : MvPoly n R cmp')
        (left right : Content R E n cmp') (rest : Coprime R E n cmp') :
        Coprime R E (n + 1) cmp
  /-- A gcd, exact cofactors, and their coprimality evidence. -/
  inductive Gcd (R : Type u) [Lean.Grind.CommRing R] (E : Leaves.{v}) :
      (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (max u v)
    | mk {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (gcd cofL cofR : MvPoly n R cmp) (coprime : Coprime R E n cmp) : Gcd R E n cmp
  /-- A coefficient gcd and the checked fold producing it. -/
  inductive Content (R : Type u) [Lean.Grind.CommRing R] (E : Leaves.{v}) :
      (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (max u v)
    | mk {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (value : MvPoly n R cmp) (steps : Steps R E n cmp) : Content R E n cmp
  /-- Strictly positive list of gcd certificates in a content fold. -/
  inductive Steps (R : Type u) [Lean.Grind.CommRing R] (E : Leaves.{v}) :
      (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (max u v)
    | nil {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : Steps R E n cmp
    | cons {n cmp} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (head : Gcd R E n cmp) (tail : Steps R E n cmp) : Steps R E n cmp
end

/-- Ordinary certificates have no optional leaves. -/
abbrev NoLeaves : Leaves := fun _ _ _ _ => Empty

end Cert

/-- Ordinary integer evidence replayed with canonical integer arithmetic. -/
abbrev IntCoprimeCert (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] := Cert.Coprime Int Cert.NoLeaves n cmp

/-- Rational scales and ordinary integer-model evidence. No coefficient
operations or embeddings are certificate data. -/
structure RatLiftCert (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  scaleL : Rat
  scaleR : Rat
  left : MvPoly n Int cmp
  right : MvPoly n Int cmp
  cert : IntCoprimeCert n cmp

/-- Identification of a coefficient ring with the canonical rational ring.
The laws refer to the same ring parameter as the surrounding certificate;
this representation witness supplies no replacement arithmetic for replay. -/
structure RatModel (R : Type u) [Lean.Grind.CommRing R] where
  toRat : R → Rat
  fromRat : Rat → R
  left_inv : ∀ x, fromRat (toRat x) = x
  right_inv : ∀ x, toRat (fromRat x) = x
  map_zero : toRat 0 = 0
  map_one : toRat 1 = 1
  map_add : ∀ x y, toRat (x + y) = toRat x + toRat y
  map_mul : ∀ x y, toRat (x * y) = toRat x * toRat y

/-- A rational representation reflects equality. -/
theorem RatModel.injective {R : Type u} [Lean.Grind.CommRing R] (model : RatModel R) :
    Function.Injective model.toRat := by
  intro x y h
  simpa only [model.left_inv] using congrArg model.fromRat h

/-- Integer certificates cannot contain a rational-representation leaf. -/
theorem RatModel.not_int (model : RatModel Int) : False := by
  have htwo : model.toRat (2 : Int) = 2 := by
    change model.toRat (1 + 1) = 2
    rw [model.map_add, model.map_one]
    decide +kernel
  have hhalf := model.right_inv (1 / 2)
  have heq : 2 * model.fromRat (1 / 2) = (1 : Int) := by
    apply model.injective
    rw [model.map_mul, htwo, hhalf, model.map_one]
    decide +kernel
  omega

/-- The canonical rational coefficient representation. -/
def RatModel.rat : RatModel Rat where
  toRat := id
  fromRat := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

/-- A rational lift is available only in a coefficient ring identified with
`Rat`; its models and recursive replay are always canonical integers. -/
structure RatLeaf (R : Type u) [Lean.Grind.CommRing R]
    (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  model : RatModel R
  data : RatLiftCert n cmp

/-- Public coprimality evidence with canonical rational lift leaves. -/
abbrev CoprimeCert (n : Nat) (R : Type u) [Lean.Grind.CommRing R]
    (cmp : Mono n → Mono n → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  Cert.Coprime R (RatLeaf R) n cmp

/-- Public gcd certificate. -/
abbrev GcdCert (n : Nat) (R : Type u) [Lean.Grind.CommRing R]
    (cmp : Mono n → Mono n → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  Cert.Gcd R (RatLeaf R) n cmp

/-- Public coefficient-content certificate. -/
abbrev ContentCert (n : Nat) (R : Type u) [Lean.Grind.CommRing R]
    (cmp : Mono n → Mono n → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  Cert.Content R (RatLeaf R) n cmp

/-- Public list of gcd steps. -/
abbrev GcdCerts (n : Nat) (R : Type u) [Lean.Grind.CommRing R]
    (cmp : Mono n → Mono n → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  Cert.Steps R (RatLeaf R) n cmp

namespace CoprimeCert
export Cert.Coprime (unit base bezout split splitBezout)

/-- Canonical `Int → Rat` lifting from ordinary integer evidence. -/
def ratLift {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (scaleL scaleR : Rat) (left right : MvPoly n Int cmp)
    (cert : IntCoprimeCert n cmp) : CoprimeCert n Rat cmp :=
  .leaf ⟨RatModel.rat, ⟨scaleL, scaleR, left, right, cert⟩⟩
end CoprimeCert

namespace GcdCert
export Cert.Gcd (mk)
end GcdCert

namespace Cert.Steps

variable {n : Nat} {R : Type u} [Lean.Grind.CommRing R] {E : Cert.Leaves.{v}}
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

@[reducible] def toList : Cert.Steps R E n cmp → List (Cert.Gcd R E n cmp)
  | .nil => []
  | .cons head tail => head :: toList tail

@[reducible] def ofList : List (Cert.Gcd R E n cmp) → Cert.Steps R E n cmp
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

end Cert.Steps

namespace Cert.Gcd

variable {n : Nat} {R : Type u} [Lean.Grind.CommRing R] {E : Cert.Leaves.{v}}
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

@[reducible] def gcd : Cert.Gcd R E n cmp → MvPoly n R cmp
  | .mk gcd _ _ _ => gcd

@[reducible] def cofL : Cert.Gcd R E n cmp → MvPoly n R cmp
  | .mk _ cofL _ _ => cofL

@[reducible] def cofR : Cert.Gcd R E n cmp → MvPoly n R cmp
  | .mk _ _ cofR _ => cofR

@[reducible] def coprime : Cert.Gcd R E n cmp → Cert.Coprime R E n cmp
  | .mk _ _ _ coprime => coprime

end Cert.Gcd

namespace Cert.Content

variable {n : Nat} {R : Type u} [Lean.Grind.CommRing R] {E : Cert.Leaves.{v}}
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

@[reducible] def value : Cert.Content R E n cmp → MvPoly n R cmp
  | .mk value _ => value

@[reducible] def steps : Cert.Content R E n cmp → List (Cert.Gcd R E n cmp)
  | .mk _ steps => steps.toList

/-- Public list-based constructor; the strictly-positive internal list is an
implementation detail of Lean's mutual-inductive positivity checker. -/
@[reducible] def ofSteps (value : MvPoly n R cmp) (steps : List (Cert.Gcd R E n cmp)) :
    Cert.Content R E n cmp :=
  .mk value (Cert.Steps.ofList steps)

@[simp] theorem value_ofSteps (value : MvPoly n R cmp)
    (steps : List (Cert.Gcd R E n cmp)) :
    (ofSteps value steps).value = value := by
  rfl

@[simp] theorem steps_ofSteps (value : MvPoly n R cmp)
    (steps : List (Cert.Gcd R E n cmp)) :
    (ofSteps value steps).steps = steps := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      simp only [Cert.Content.steps, Cert.Steps.toList, ih]

end Cert.Content

namespace GcdCerts
export Cert.Steps (nil cons)

variable {n : Nat} {R : Type u} [Lean.Grind.CommRing R]
  {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
@[reducible] def toList (steps : GcdCerts n R cmp) : List (GcdCert n R cmp) :=
  Cert.Steps.toList steps
@[reducible] def ofList (steps : List (GcdCert n R cmp)) : GcdCerts n R cmp :=
  Cert.Steps.ofList steps
end GcdCerts

namespace GcdCert
variable {n : Nat} {R : Type u} [Lean.Grind.CommRing R]
  {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
@[reducible] def gcd (cert : GcdCert n R cmp) : MvPoly n R cmp := Cert.Gcd.gcd cert
@[reducible] def cofL (cert : GcdCert n R cmp) : MvPoly n R cmp := Cert.Gcd.cofL cert
@[reducible] def cofR (cert : GcdCert n R cmp) : MvPoly n R cmp := Cert.Gcd.cofR cert
@[reducible] def coprime (cert : GcdCert n R cmp) : CoprimeCert n R cmp :=
  Cert.Gcd.coprime cert
end GcdCert

namespace ContentCert
export Cert.Content (mk)

variable {n : Nat} {R : Type u} [Lean.Grind.CommRing R]
  {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
@[reducible] def value (cert : ContentCert n R cmp) : MvPoly n R cmp :=
  Cert.Content.value cert
@[reducible] def steps (cert : ContentCert n R cmp) : List (GcdCert n R cmp) :=
  Cert.Content.steps cert
/-- Build a coefficient-content certificate from a list of gcd steps. -/
@[reducible] def ofSteps (value : MvPoly n R cmp) (steps : List (GcdCert n R cmp)) :
    ContentCert n R cmp := Cert.Content.ofSteps value steps
@[simp] theorem value_ofSteps (value : MvPoly n R cmp) (steps : List (GcdCert n R cmp)) :
    (ofSteps value steps).value = value := Cert.Content.value_ofSteps value steps
@[simp] theorem steps_ofSteps (value : MvPoly n R cmp) (steps : List (GcdCert n R cmp)) :
    (ofSteps value steps).steps = steps := Cert.Content.steps_ofSteps value steps
end ContentCert

namespace Cert

variable {R : Type u} [Lean.Grind.CommRing R] {E : Leaves.{v}}

/-- Extraction of ordinary evidence at one arity. -/
structure StripOps (R : Type u) [Lean.Grind.CommRing R] (E : Leaves.{v}) (n : Nat) where
  coprime : {cmp : Mono n → Mono n → Ordering} →
    [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] →
    Coprime R E n cmp → Option (Coprime R NoLeaves n cmp)

/-- Extract ordinary evidence from a gcd using a supplied coprimality extractor. -/
def stripGcdWith {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (strip : Coprime R E n cmp → Option (Coprime R NoLeaves n cmp))
    (cert : Gcd R E n cmp) : Option (Gcd R NoLeaves n cmp) := do
  return .mk cert.gcd cert.cofL cert.cofR (← strip cert.coprime)

/-- Extract ordinary evidence from all gcd steps of a content fold. -/
def stripContentWith {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (strip : Coprime R E n cmp → Option (Coprime R NoLeaves n cmp))
    (cert : Content R E n cmp) : Option (Content R NoLeaves n cmp) := do
  return Content.ofSteps cert.value (← cert.steps.mapM (stripGcdWith strip))

/-- Extract ordinary certificates by arity, rejecting a leaf at any depth. -/
def stripOps : (n : Nat) → StripOps R E n
  | 0 => { coprime := fun cert =>
      match cert with
      | .unit => some .unit
      | .base u v => some (.base u v)
      | .bezout u v => some (.bezout u v)
      | .leaf _ => none }
  | n + 1 =>
      let lower := stripOps n
      { coprime := fun cert => by
          cases cert with
          | unit => exact some .unit
          | bezout u v => exact some (.bezout u v)
          | leaf _ => exact none
          | split i cmp' P φ a α β left right rest => exact do
              return .split i cmp' P φ a α β (← stripContentWith lower.coprime left)
                (← stripContentWith lower.coprime right) (← lower.coprime rest)
          | splitBezout i cmp' u v r left right rest => exact do
              return .splitBezout i cmp' u v r (← stripContentWith lower.coprime left)
                (← stripContentWith lower.coprime right) (← lower.coprime rest) }

/-- Remove optional leaves before using an integer certificate in rational replay. -/
def stripCoprime? {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (cert : Coprime R E n cmp) :
    Option (Coprime R NoLeaves n cmp) := (stripOps n).coprime cert

end Cert

end Hex.MvPoly
