/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseCodec
public import HexPoly.Interpret

public section

namespace Hex.RealClosure.BaseContext

/-- A polynomial whose coefficients belong to one entire immutable base context. -/
structure Polynomial {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (context : Context registry K sign) where
  stored : DensePoly K

namespace Polynomial

variable {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
variable {sign : K → Int} {context : Context registry K sign}

@[ext] theorem ext {p q : Polynomial context} (h : p.stored = q.stored) : p = q := by
  cases p; cases q; cases h; rfl

instance : Zero (Polynomial context) := ⟨⟨0⟩⟩
instance : One (Polynomial context) := ⟨⟨1⟩⟩
instance : Add (Polynomial context) := ⟨fun p q => ⟨p.stored + q.stored⟩⟩
instance : Neg (Polynomial context) := ⟨fun p => ⟨-p.stored⟩⟩
instance : Sub (Polynomial context) := ⟨fun p q => ⟨p.stored - q.stored⟩⟩
instance : Mul (Polynomial context) := ⟨fun p q => ⟨p.stored * q.stored⟩⟩

/-- Construct a polynomial from coefficients of this context. -/
@[expose] def ofCoeffs (coefficients : Array (Element context)) : Polynomial context :=
  ⟨DensePoly.ofCoeffs (coefficients.map Element.stored)⟩

@[expose] def coeff (p : Polynomial context) (i : Nat) : Element context :=
  ⟨p.stored.coeff i⟩

@[expose] def eval (p : Polynomial context) (a : Element context) : Element context :=
  ⟨p.stored.eval a.stored⟩

theorem C_zero_iff (a : K) : RationalFn.C a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [← RationalFn.C_zero] at h
    have hc := congrArg (fun f : RationalFn K => f.num.coeff 0) h
    simpa [RationalFn.C, RationalFn.ofPoly, DensePoly.coeff_C] using hc
  · intro h
    subst a
    exact RationalFn.C_zero

private theorem C_sub (a b : K) :
    RationalFn.C (a - b) = RationalFn.C a - RationalFn.C b := by
  have h := RationalFn.C_add (a - b) b
  have hab : a - b + b = a := by grind
  rw [hab] at h
  grind

/-- Include every coefficient in the new infinitesimal child. Zero reflection
retains the stored array length without a trailing-zero scan. -/
@[expose] def embed (p : Polynomial context) : Polynomial (.infinitesimal context) :=
  ⟨DensePoly.Interpret.map RationalFn.C C_zero_iff p.stored⟩

theorem embed_coeff (p : Polynomial context) (i : Nat) :
    p.embed.coeff i = (p.coeff i).embed :=
  Element.ext (DensePoly.Interpret.map_coeff RationalFn.C C_zero_iff p.stored i)

theorem embed_eval (p : Polynomial context) (a : Element context) :
    p.embed.eval a.embed = (p.eval a).embed :=
  Element.ext (DensePoly.Interpret.map_eval RationalFn.C C_zero_iff
    RationalFn.C_add RationalFn.C_mul p.stored a.stored).symm

theorem embed_zero : (0 : Polynomial context).embed = 0 :=
  ext (DensePoly.Interpret.map_zero_poly RationalFn.C C_zero_iff)

theorem embed_one : (1 : Polynomial context).embed = 1 :=
  ext (DensePoly.Interpret.map_one RationalFn.C C_zero_iff RationalFn.C_one)

theorem embed_add (p q : Polynomial context) : (p + q).embed = p.embed + q.embed :=
  ext (DensePoly.Interpret.map_add RationalFn.C C_zero_iff RationalFn.C_add p.stored q.stored)

theorem embed_sub (p q : Polynomial context) : (p - q).embed = p.embed - q.embed :=
  ext (DensePoly.Interpret.map_sub RationalFn.C C_zero_iff C_sub p.stored q.stored)

theorem embed_neg (p : Polynomial context) : (-p).embed = -p.embed :=
  ext (DensePoly.Interpret.map_neg RationalFn.C C_zero_iff C_sub p.stored)

theorem embed_mul (p q : Polynomial context) : (p * q).embed = p.embed * q.embed :=
  ext (DensePoly.Interpret.map_mul RationalFn.C C_zero_iff RationalFn.C_add
    RationalFn.C_mul p.stored q.stored)

theorem embed_size (p : Polynomial context) : p.embed.stored.size = p.stored.size :=
  DensePoly.Interpret.map_size RationalFn.C C_zero_iff p.stored

theorem embed_degree (p : Polynomial context) : p.embed.stored.natDegree = p.stored.natDegree :=
  DensePoly.Interpret.map_degree RationalFn.C C_zero_iff p.stored

/-- Serialized coefficients have one literal context binding. -/
structure Serialized where
  binding : Signature
  coefficients : List Syntax
  deriving Repr

@[expose] def write (p : Polynomial context) : Serialized :=
  ⟨context.signature, p.stored.toArray.toList.map context.write⟩

/-- Check the binding and every coefficient before constructing a canonical polynomial. -/
@[expose] def read (context : Context registry K sign) (raw : Serialized) :
    Option (Polynomial context) := do
  if raw.binding ≠ context.signature then none
  else
    let coefficients ← raw.coefficients.mapM context.read
    return ⟨DensePoly.ofCoeffs coefficients.toArray⟩

private theorem read_coefficients (coefficients : List K) :
    (coefficients.map context.write).mapM context.read = some coefficients := by
  induction coefficients with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, Context.read_write, ih]

theorem read_write (p : Polynomial context) : read context p.write = some p := by
  simp only [read, write, ne_eq, not_true_eq_false, ↓reduceIte, read_coefficients]
  change some (⟨DensePoly.ofCoeffs p.stored.toArray.toList.toArray⟩ : Polynomial context) = some p
  rw [Array.toArray_toList, DensePoly.ofCoeffs_toArray]

theorem read_stale (raw : Serialized) (h : raw.binding ≠ context.signature) :
    read context raw = none := by
  simp [read, h]

section Constant

variable {approx : K → Rat → OrderedFn.Oracle.Bounds}
variable (parent : RealContext registry K approx sign) (key : ConstantKey)
variable (present : (registry key).isSome = true)
variable (sp : ∀ f : RationalFn K,
  Acc (OrderedFn.Next (OrderedFn.Real.attempt (parent.source key present) f)) 0)
variable (ap : ∀ (f : RationalFn K) (δ : Rat),
  Acc (OrderedFn.Next (OrderedFn.Real.approxAttempt (parent.source key present) f
    (OrderedFn.Real.requestWidth δ))) 0)

/-- Include all coefficients in the new registered real level. -/
@[expose] def embedConstant (p : Polynomial (.real parent)) :
    Polynomial (.real (parent.constant key present sp ap)) :=
  ⟨DensePoly.Interpret.map RationalFn.C C_zero_iff p.stored⟩

theorem embedConstant_coeff (p : Polynomial (.real parent)) (i : Nat) :
    (p.embedConstant parent key present sp ap).coeff i =
      Element.embedConstant parent key present sp ap (p.coeff i) :=
  Element.ext (DensePoly.Interpret.map_coeff RationalFn.C C_zero_iff p.stored i)

theorem embedConstant_eval (p : Polynomial (.real parent)) (a : Element (.real parent)) :
    (p.embedConstant parent key present sp ap).eval
      (Element.embedConstant parent key present sp ap a) =
        Element.embedConstant parent key present sp ap (p.eval a) :=
  Element.ext (DensePoly.Interpret.map_eval RationalFn.C C_zero_iff
    RationalFn.C_add RationalFn.C_mul p.stored a.stored).symm

theorem embedConstant_zero :
    (0 : Polynomial (.real parent)).embedConstant parent key present sp ap = 0 :=
  ext (DensePoly.Interpret.map_zero_poly RationalFn.C C_zero_iff)

theorem embedConstant_one :
    (1 : Polynomial (.real parent)).embedConstant parent key present sp ap = 1 :=
  ext (DensePoly.Interpret.map_one RationalFn.C C_zero_iff RationalFn.C_one)

theorem embedConstant_add (p q : Polynomial (.real parent)) :
    (p + q).embedConstant parent key present sp ap =
      p.embedConstant parent key present sp ap + q.embedConstant parent key present sp ap :=
  ext (DensePoly.Interpret.map_add RationalFn.C C_zero_iff RationalFn.C_add p.stored q.stored)

theorem embedConstant_sub (p q : Polynomial (.real parent)) :
    (p - q).embedConstant parent key present sp ap =
      p.embedConstant parent key present sp ap - q.embedConstant parent key present sp ap :=
  ext (DensePoly.Interpret.map_sub RationalFn.C C_zero_iff C_sub p.stored q.stored)

theorem embedConstant_neg (p : Polynomial (.real parent)) :
    (-p).embedConstant parent key present sp ap =
      -(p.embedConstant parent key present sp ap) :=
  ext (DensePoly.Interpret.map_neg RationalFn.C C_zero_iff C_sub p.stored)

theorem embedConstant_mul (p q : Polynomial (.real parent)) :
    (p * q).embedConstant parent key present sp ap =
      p.embedConstant parent key present sp ap * q.embedConstant parent key present sp ap :=
  ext (DensePoly.Interpret.map_mul RationalFn.C C_zero_iff RationalFn.C_add
    RationalFn.C_mul p.stored q.stored)

theorem embedConstant_size (p : Polynomial (.real parent)) :
    (p.embedConstant parent key present sp ap).stored.size = p.stored.size :=
  DensePoly.Interpret.map_size RationalFn.C C_zero_iff p.stored

theorem embedConstant_degree (p : Polynomial (.real parent)) :
    (p.embedConstant parent key present sp ap).stored.natDegree = p.stored.natDegree :=
  DensePoly.Interpret.map_degree RationalFn.C C_zero_iff p.stored

end Constant

end Polynomial
end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Polynomial.embed_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Polynomial.embed_eval
/-- info: 'Hex.RealClosure.BaseContext.Polynomial.embedConstant_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Polynomial.embedConstant_eval
/-- info: 'Hex.RealClosure.BaseContext.Polynomial.read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Polynomial.read_write
/-- info: 'Hex.RealClosure.BaseContext.Polynomial.read_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Polynomial.read_stale
