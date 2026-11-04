/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.CellFormula

public section

namespace Hex.RCF.RealCoefficients.Decision

open Hex.RealFormula HexPolyTheory.Interpret HexRealRootsTheory

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Read root signs from their checked rows and sector signs at the listed
ordinary point. The specialization is supplied independently of its semantics. -/
@[expose] def cellSign (sign : E → Int) (point : Dyadic → E)
    (polynomial : RealFormula.Poly n → DensePoly E) (cert : IsolationReplay E Ctx)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly n → Int)
    (cell : Cell cert.isolations.intervals.size) (atom : RealFormula.Poly n) : Option Sign :=
  match cell with
  | .open cut => some <| Sign.ofInt <| sign <|
      (polynomial atom).eval (point (cert.isolations.openPoint cut))
  | .root i => some <| Sign.ofInt (rootValue i atom)

private theorem sign_cast_sign (y : ℝ) :
    SignType.sign (((SignType.sign y : Int) : ℝ)) = SignType.sign y := by
  cases h : SignType.sign y <;> simp

/-- Checked complete isolations and atom queries determine signs throughout
every cell. Source specialization and atom-root coverage are explicit
mathematical inputs, so the cell argument does not depend on a field presentation. -/
theorem cellSign_spec
    (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hnat : ∀ n : Nat, f (n : E) = (n : ℝ))
    (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (point : Dyadic → E) (hpoint : ∀ d, f (point d) = HexRealRootsTheory.Dyadic.toReal d)
    (formula : QF n) (valuation : ℝ → Fin n → ℝ)
    (polynomial : RealFormula.Poly n → DensePoly E)
    (atom_eval : ∀ atom x, (interpret f hz (polynomial atom)).eval x = atom.eval (valuation x))
    (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (hisolation : cert.check sign point context head = true)
    (atom_roots : ∀ atom ∈ formula.polys,
      interpret f hz (polynomial atom) = 0 ∨
        ∀ y, (interpret f hz (polynomial atom)).IsRoot y → (interpret f hz head).IsRoot y)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly n → Int)
    (evidence : Fin cert.isolations.intervals.size → RealFormula.Poly n →
      TarskiCertificate E E Ctx)
    (hquery : ∀ i atom, atom ∈ formula.polys →
      Sturm.check sign context head (polynomial atom)
        (.finite (point cert.isolations.intervals[i].lower))
        (.finite (point cert.isolations.intervals[i].upper))
        (rootValue i atom) (evidence i atom) = true) :
    ∃ roots : Fin cert.isolations.intervals.size → ℝ,
      StrictMono roots ∧
      ∀ cell x, Cell.Region roots cell x → ∀ atom ∈ formula.polys, ∃ observed,
        cellSign sign point polynomial cert rootValue cell atom = some observed ∧
        SignType.sign (((observed.toInt : Int) : ℝ)) = SignType.sign (atom.eval (valuation x)) := by
  obtain ⟨roots, hroots, hmono, hcomplete, hsample⟩ :=
    cert.check_roots f hz h1 ha hs hm hnat sign hsign point hpoint context head hisolation
  refine ⟨roots, hmono, ?_⟩
  intro cell x hx atom hatom
  cases cell with
  | «open» cut =>
      let observed := sign ((polynomial atom).eval (point (cert.isolations.openPoint cut)))
      refine ⟨Sign.ofInt observed, rfl, ?_⟩
      rw [Sign.ofInt_spec]
      have meaning := cert.open_sign f hz ha hm sign hsign point hpoint head (polynomial atom)
        roots hmono hcomplete cut (hsample cut) (atom_roots atom hatom) x hx
      change observed = (SignType.sign ((interpret f hz (polynomial atom)).eval x) : Int) at meaning
      rw [meaning, atom_eval]
      exact sign_cast_sign _
  | root i =>
      have same : x = roots i := hx
      subst x
      refine ⟨Sign.ofInt (rootValue i atom), rfl, ?_⟩
      rw [Sign.ofInt_spec]
      have meaning := cert.check_sign f hz h1 ha hs hm hnat sign hsign point hpoint context head
        hisolation i (polynomial atom) (rootValue i atom) (evidence i atom) (hquery i atom hatom)
        (roots i) (hroots i).1 (hroots i).2.1 (hroots i).2.2
      rw [meaning, atom_eval]
      exact sign_cast_sign _

end Hex.RCF.RealCoefficients.Decision
