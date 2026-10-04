/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts
public import HexRealClosure.AlgebraicCodec
public import HexSignDet.Codec.Bytes
public import HexSignDet.Codec.Coefficients

public section

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Decode exact stored coefficients from previously proved signs. Zero needs
no fact. Nonzero literals need their exact polynomial and claimed sign in the
fixed context; missing facts reject without invoking this context's sign
producer. The supplied predecessor codec controls lower-level decoding. This
partial codec need not roundtrip values absent from the finite facts. -/
@[expose] def Element.signCodec (value : ValueCodec E) (facts : List (SignFact context)) :
    ValueCodec (Element context) where
  encode := (Element.codec value).encode
  decode j := do
    let fields ← j.getArr?
    match fields.toList with
    | [] => return 0
    | [p, s] =>
      let polynomial ← Codec.readPoly value p
      let claimed ← Codec.Json.decode (α := Int) s
      match SignFact.read facts polynomial claimed with
      | some a => return a
      | none => throw "stored sign fact missing or mismatched"
    | _ => throw "wrong stored value field count"

/-- Membership supplies literal lookup coverage; duplicate keys have the same
sign because every fact proves the sign of the same polynomial. -/
theorem SignFact.find_of_mem (facts : List (SignFact context)) (f : SignFact context)
    (hf : f ∈ facts) : SignFact.find facts f.polynomial = some ⟨f.sign, f.checked⟩ := by
  induction facts with
  | nil => simp at hf
  | cons g gs ih =>
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · simp [SignFact.find]
    · by_cases hg : g.polynomial = f.polynomial
      · have hs : g.sign = f.sign := (hg ▸ g.checked).symm.trans f.checked
        simp [SignFact.find, hg, hs]
      · simpa [SignFact.find, hg] using ih hf

/-- A stored nonzero fact can be restored using list membership alone. -/
theorem SignFact.read_of_mem (facts : List (SignFact context)) (f : SignFact context)
    (hf : f ∈ facts) (hn : f.sign ≠ 0) :
    SignFact.read facts f.polynomial f.sign =
      some (Element.restore f.polynomial f.sign f.checked hn) := by
  simp [SignFact.read, SignFact.find_of_mem facts f hf, hn]

/-- A nonzero stored element is covered whenever its exact key occurs in the
facts. The sign follows from the stored and supplied proofs. -/
theorem SignFact.read_of_key (facts : List (SignFact context)) (a : Element context)
    (ha : a ≠ 0) (f : SignFact context) (hf : f ∈ facts)
    (hp : f.polynomial = a.polynomial) :
    SignFact.read facts a.polynomial a.sign = some a := by
  cases hs : a.stored with
  | none => exact (ha (Element.ext (hs.trans Element.stored_zero.symm))).elim
  | some p =>
    have hp' : f.polynomial = p.polynomial := by
      simpa only [Element.polynomial, hs] using hp
    have hc := f.checked
    rw [hp'] at hc
    have hsign : f.sign = p.sign := hc.symm.trans p.checked
    have hn : f.sign ≠ 0 := by simpa only [hsign] using p.nonzero
    have hrestore : Element.restore f.polynomial f.sign f.checked hn = a := by
      apply Element.ext
      rw [Element.stored_restore, hs]
      congr 1
      rcases f with ⟨q, s, checked⟩
      rcases p with ⟨r, t, checked', nonzero⟩
      dsimp only at hp' hsign ⊢
      subst r
      subst t
      rfl
    have hr := SignFact.read_of_mem facts f hf hn
    rw [hrestore] at hr
    simpa only [Element.polynomial, Element.sign, hs, hp', hsign] using hr

/-- The encoder preserves the existing wire format exactly. -/
theorem Element.signCodec_encode (value : ValueCodec E) (facts : List (SignFact context))
    (a : Element context) :
    (Element.signCodec value facts).encode a = (Element.codec value).encode a := rfl

/-- Every accepted literal is the same value accepted by the independent
native decoder, without a completeness claim for the finite fact list. -/
theorem Element.signCodec_sound (value : ValueCodec E) (facts : List (SignFact context))
    (j : Codec.Json) (a : Element context)
    (h : (Element.signCodec value facts).decode j = .ok a) :
    (Element.codec value).decode j = .ok a := by
  unfold Element.signCodec at h
  unfold Element.codec
  dsimp only at h ⊢
  cases hf : j.getArr? with
  | error e => simp [hf, bind, Except.bind] at h
  | ok fields =>
    simp only [hf, bind, Except.bind] at h ⊢
    split at h
    · rename_i hs
      simpa only [hs] using h
    · rename_i p s hs
      simp only [hs]
      cases hp : Codec.readPoly value p with
      | error e => simp [hp] at h
      | ok polynomial =>
        simp only [hp] at h ⊢
        cases hc : Codec.Json.decode (α := Int) s with
        | error e => simp [hc] at h
        | ok claimed =>
          simp only [hc] at h ⊢
          cases hr : SignFact.read facts polynomial claimed with
          | none => simp [hr] at h
          | some b =>
            simp only [hr, pure, Except.pure, Except.ok.injEq] at h
            subst b
            rw [SignFact.read_sound facts polynomial claimed a hr]
            rfl
    · simp at h

/-- Refinement composes across extension levels: a successful strict read
agrees with the native decoder built over any refining predecessor reader. -/
theorem Element.signCodec_refines (strict complete : ValueCodec E)
    (h : strict.Refines complete) (facts : List (SignFact context)) :
    (Element.signCodec strict facts).Refines (Element.codec complete) := by
  intro j a ha
  exact Element.codec_refines strict complete h j a
    (Element.signCodec_sound strict facts j a ha)

/-- Exact roundtrip on a value whose nonzero literal is covered by the finite
facts. Canonical zero requires no fact; no global coverage premise is hidden. -/
theorem Element.signCodec_roundtrip (value : ValueCodec E)
    (facts : List (SignFact context)) (a : Element context)
    (hv : ∀ x ∈ a.polynomial.toArray, value.decode (value.encode x) = .ok x)
    (covered : a = 0 ∨ SignFact.read facts a.polynomial a.sign = some a) :
    (Element.signCodec value facts).decode ((Element.signCodec value facts).encode a) = .ok a := by
  cases hs : a.stored with
  | none =>
    have ha : a = 0 := Element.ext (hs.trans Element.stored_zero.symm)
    subst a
    simp [Element.signCodec, Element.codec, Element.stored_zero, Codec.Json.getArr_arr,
      bind, Except.bind, pure, Except.pure]
  | some p =>
    have hr : SignFact.read facts p.polynomial p.sign = some a := by
      rcases covered with ha | hr
      · simp [ha, Element.stored_zero] at hs
      · simpa only [Element.polynomial, Element.sign, hs] using hr
    have hp : ∀ x ∈ p.polynomial.toArray, value.decode (value.encode x) = .ok x := by
      simpa only [Element.polynomial, hs] using hv
    simp [Element.signCodec, Element.codec, hs, Codec.Json.getArr_arr,
      Codec.read_poly_of value p.polynomial hp, hr, bind, Except.bind, pure, Except.pure]

/-- Literal child sign requests in first-occurrence order. Repeated keys are
shared; equal values stored as different polynomials remain different keys. -/
@[expose] def Element.signKeys (coefficients : List (Element context)) : List (DensePoly E) :=
  (coefficients.map Element.polynomial).eraseDups

/-- All predecessor coefficients stored by those algebraic literals. This
does not collect the additional signs needed by arithmetic during replay. -/
@[expose] def Element.predecessors (coefficients : List (Element context)) : List E :=
  coefficients.flatMap (fun a => Codec.Coefficients.poly a.polynomial)

/-- Finite proved child keys and finite predecessor coverage establish a
roundtrip for every requested literal, without a global decoder law. -/
theorem Element.signCodec_covers (value : ValueCodec E) (facts : List (SignFact context))
    (coefficients : List (Element context))
    (hv : value.Covers (Element.predecessors coefficients))
    (keys : ∀ p ∈ Element.signKeys coefficients, ∃ f ∈ facts, f.polynomial = p) :
    (Element.signCodec value facts).Covers coefficients := by
  simp only [Element.predecessors, ValueCodec.covers_flatMap] at hv
  intro a ha
  apply Element.signCodec_roundtrip
  · intro x hx
    exact hv a ha x (by simpa [Codec.Coefficients.poly] using hx)
  · by_cases hz : a = 0
    · exact Or.inl hz
    · have mem : a.polynomial ∈ Element.signKeys coefficients := by
        simpa only [Element.signKeys, List.mem_eraseDups] using
          (List.mem_map.mpr ⟨a, ha, rfl⟩ : a.polynomial ∈ coefficients.map Element.polynomial)
      obtain ⟨f, hf, hp⟩ := keys a.polynomial mem
      exact Or.inr (SignFact.read_of_key facts a hz f hf hp)

/-- The actual byte printer/parser preserves covered values under its existing
lexical policy. Finite sign facts do not need to cover every possible element. -/
theorem Element.signCodec_bytes (value : ValueCodec E)
    (facts : List (SignFact context)) (a : Element context)
    (hv : ∀ x ∈ a.polynomial.toArray, value.decode (value.encode x) = .ok x)
    (covered : a = 0 ∨ SignFact.read facts a.polynomial a.sign = some a)
    (limits : Codec.Limits)
    (bound : Codec.checkBytes limits ((Element.signCodec value facts).encodeBytes a) = .ok ()) :
    (Element.signCodec value facts).decodeBytes
      ((Element.signCodec value facts).encodeBytes a) limits = .ok a := by
  exact (Element.signCodec value facts).decode_encode_of a
    (Element.signCodec_roundtrip value facts a hv covered) limits bound

end Hex.RealClosure.Algebraic
