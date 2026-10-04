/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts

public section

namespace Hex.RealClosure.Algebraic.InProcessProbe

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Read one intermediate value only when its retained sign is supplied or
the ordinary constant path applies. No nonconstant missing branch is entered.
This is a partial evidence reader, not a replacement arithmetic instance. -/
@[expose] def readValue? (reduce : DensePoly E → DensePoly E)
    (_hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E) :
    Option (Element context) :=
  let kept := reduce p
  match SignFact.find facts kept with
  | some f =>
    if hn : f.val = 0 then some 0
    else some (Element.restore kept f.val f.property hn)
  | none =>
    if hc : kept.size ≤ 1 then
      let s := coeffSign (kept.coeff 0)
      if hn : s = 0 then some 0
      else some (Element.restore kept s (context.signPoly_const kept hc) hn)
    else none

theorem readValue_sound (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly E) (a : Element context)
    (h : readValue? reduce hr facts p = some a) : a = Element.ofPoly p := by
  have packed : Element.pack reduce hr facts p = a := by
    cases hf : SignFact.find facts (reduce p) with
    | some f =>
      by_cases hz : f.val = 0 <;>
        simpa only [readValue?, Element.pack, hf, hz, ↓reduceDIte, Option.some.injEq] using h
    | none =>
      by_cases hc : (reduce p).size ≤ 1
      · by_cases hz : coeffSign ((reduce p).coeff 0) = 0 <;>
          simpa only [readValue?, Element.pack, hf, hc, hz, ↓reduceDIte, Option.some.injEq] using h
      · simp [readValue?, hf, hc] at h
  exact packed.symm.trans (Element.pack_eq reduce hr facts p)

theorem readValue_missing (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E)
    (hc : ¬ (reduce p).size ≤ 1) (hf : SignFact.find facts (reduce p) = none) :
    readValue? reduce hr facts p = none := by
  simp [readValue?, hc, hf]

/-- The actual Horner steps, with finite evidence read before constructing
each intermediate value. The coefficient operations themselves stay total. -/
@[expose] def readCoefficients? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (cs : List (Element context)) (x : Element context) : Option (Element context) :=
  cs.foldrM (fun c acc => do
    let product ← readValue? reduce hr facts (acc.polynomial * x.polynomial)
    readValue? reduce hr facts (product.polynomial + c.polynomial)) 0

theorem readCoefficients_sound (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (cs : List (Element context)) (x a : Element context)
    (h : readCoefficients? reduce hr facts cs x = some a) :
    a = DensePoly.evalCoeffList cs x := by
  induction cs generalizing a with
  | nil => exact (Option.some.inj h).symm
  | cons c cs ih =>
    simp only [readCoefficients?, List.foldrM_cons] at h
    change (do
      let acc ← readCoefficients? reduce hr facts cs x
      let product ← readValue? reduce hr facts (acc.polynomial * x.polynomial)
      readValue? reduce hr facts (product.polynomial + c.polynomial)) = some a at h
    cases ht : readCoefficients? reduce hr facts cs x with
    | none => simp [ht] at h
    | some acc =>
      simp only [ht, bind, Option.bind] at h
      cases hp : readValue? reduce hr facts (acc.polynomial * x.polynomial) with
      | none => simp [hp] at h
      | some product =>
        simp only [hp] at h
        have ht' := ih acc ht
        have hp' := readValue_sound reduce hr facts _ product hp
        have ha := readValue_sound reduce hr facts _ a h
        change product = acc * x at hp'
        change a = product + c at ha
        simpa only [DensePoly.evalCoeffList, hp', ht'] using ha

@[expose] def readEval? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly (Element context)) (x : Element context) : Option (Element context) :=
  readCoefficients? reduce hr facts p.toArray.toList x

theorem readEval_sound (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly (Element context)) (x a : Element context)
    (h : readEval? reduce hr facts p x = some a) : a = p.eval x := by
  exact readCoefficients_sound reduce hr facts p.toList x a h

@[expose] def readValueProof? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E) :
    Option {a : Element context // a = Element.ofPoly p} :=
  match h : readValue? reduce hr facts p with
  | none => none
  | some a => some ⟨a, readValue_sound reduce hr facts p a h⟩

@[expose] def readEvalProof? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly (Element context)) (x : Element context) :
    Option {a : Element context // a = p.eval x} :=
  match h : readEval? reduce hr facts p x with
  | none => none
  | some a => some ⟨a, readEval_sound reduce hr facts p x a h⟩

/-- Read the actual endpoint comparison without searching for a missing sign. -/
@[expose] def readLess? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (a b : Hex.Endpoint (Element context)) :
    Option {ok : Bool // ok = a.lt (Hex.EndpointSigns.ofSign Element.sign) b} :=
  match a, b with
  | .negInf, .finite _ | .negInf, .posInf | .finite _, .posInf => some ⟨true, rfl⟩
  | .negInf, .negInf | .finite _, .negInf | .posInf, .negInf |
      .posInf, .finite _ | .posInf, .posInf => some ⟨false, rfl⟩
  | .finite x, .finite y => do
    let value ← readValueProof? reduce hr facts (x.polynomial - y.polynomial)
    pure ⟨decide (value.val.sign < 0), by
      have same : value.val = x - y := value.property
      rw [same]
      rfl⟩

/-- Read the finite endpoint's Horner value; infinities need no evaluation. -/
@[expose] def readNonvanishing? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly (Element context)) (a : Hex.Endpoint (Element context)) :
    Option {ok : Bool // ok = a.nonvanishing (Hex.EndpointSigns.ofSign Element.sign) p} :=
  match a with
  | .negInf | .posInf => some ⟨true, rfl⟩
  | .finite x => do
    let value ← readEvalProof? reduce hr facts p x
    pure ⟨value.val.sign != 0, by rw [value.property]; rfl⟩

/-- Check the existing endpoint predicate in process. The ordinary result is
retained in the erased proof; absent evidence returns `none` immediately. -/
@[expose] def readEndpoints? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly (Element context)) (a b : Hex.Endpoint (Element context)) :
    Option {ok : Bool // ok = Hex.TarskiCertificate.checkEndpoints
      (Hex.EndpointSigns.ofSign Element.sign) p a b} :=
  if hp : p.isZero = true then
    some ⟨false, by simp [Hex.TarskiCertificate.checkEndpoints, hp]⟩
  else do
    let ordered ← readLess? reduce hr facts a b
    if hl : ordered.val = false then
      pure ⟨false, by simp [Hex.TarskiCertificate.checkEndpoints, ← ordered.property, hl]⟩
    else
      let left ← readNonvanishing? reduce hr facts p a
      if ha : left.val = false then
        pure ⟨false, by simp [Hex.TarskiCertificate.checkEndpoints, ← left.property, ha]⟩
      else
        let right ← readNonvanishing? reduce hr facts p b
        pure ⟨right.val, by
          have ordered_true := (Bool.eq_false_or_eq_true ordered.val).resolve_right hl
          have left_true := (Bool.eq_false_or_eq_true left.val).resolve_right ha
          have nonzero := Bool.eq_false_iff.mpr hp
          simp [Hex.TarskiCertificate.checkEndpoints, ← ordered.property,
            ← left.property, ← right.property, ordered_true, left_true, nonzero]⟩

end Hex.RealClosure.Algebraic.InProcessProbe

/-- info: 'Hex.RealClosure.Algebraic.InProcessProbe.readEval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.InProcessProbe.readEval_sound
