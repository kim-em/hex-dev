/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldCarrier
public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.Radical
public import HexRCF.RealCoefficients.Formula
public import HexRCF.RealCoefficients.CellFormula
public import HexRCF.RealCoefficients.Decision

public section

/-! Cell signs over a literal fixed real number field. -/

namespace Hex.RCF.RealCoefficients.FieldDecision

open Hex.RealFormula HexPolyTheory.Interpret HexRealRootsTheory

variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]
variable {Ctx : Type u} [DecidableEq Ctx]

/-- Rational dyadic samples in the existing reduced-coordinate field. -/
@[expose] def point (d : Dyadic) : PolyQuot p root := PolyQuot.ofRat d.toRat

/-- A checked table supplies the coefficient sign operation; root signs come
from separate Tarski queries and open signs from the listed sample. -/
@[expose] def cellSign (sign : PolyQuot p root → Int)
    (values : Fin n → PolyQuot p root)
    (cert : IsolationReplay (PolyQuot p root) Ctx)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (cell : Cell cert.isolations.intervals.size)
    (atom : RealFormula.Poly (n + 1)) : Option Sign :=
  match cell with
  | .open cut =>
      some <| Sign.ofInt <| sign <|
        (FieldSpecialize.literalPolynomial values atom).eval
          (point (cert.isolations.openPoint cut))
  | .root i => some <| Sign.ofInt (rootValue i atom)

/-- Every accepted atom sign agrees with its source formula at every point of
its cell. A copied root query cannot inherit another cell's sign. -/
theorem cellSign_spec (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (sign : PolyQuot p root → Int)
    (hsign : ∀ a, sign a = (SignType.sign (Field.value rep a) : Int))
    (values : Fin n → PolyQuot p root)
    (formula : QF (n + 1)) (context : Ctx)
    (radical : RadicalCert (PolyQuot p root) Ctx)
    (hradical : radical.check context (FieldCarrier.product values formula) = true)
    (cert : IsolationReplay (PolyQuot p root) Ctx)
    (hisolation : cert.check sign point context radical.core = true)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (evidence : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) →
      TarskiCertificate (PolyQuot p root) (PolyQuot p root) Ctx)
    (hquery : ∀ i atom, atom ∈ formula.polys →
      Sturm.check sign context radical.core
        (FieldSpecialize.literalPolynomial values atom)
        (.finite (point cert.isolations.intervals[i].lower))
        (.finite (point cert.isolations.intervals[i].upper))
        (rootValue i atom) (evidence i atom) = true) :
    ∃ roots : Fin cert.isolations.intervals.size → ℝ,
      StrictMono roots ∧
      (∀ cell x, Cell.Region roots cell x →
        ∀ atom ∈ formula.polys, ∃ observed,
          cellSign sign values cert rootValue cell atom = some observed ∧
          SignType.sign (((observed.toInt : Int) : ℝ)) =
            SignType.sign (atom.eval
              (append (fun j => Field.value rep (values j)) x))) := by
  let f : PolyQuot p root → ℝ := Field.value rep
  have hpoint : ∀ d : Dyadic, f (point d : PolyQuot p root) =
      HexRealRootsTheory.Dyadic.toReal d := by
    intro d
    simpa [f, point, HexRealRootsTheory.toReal_eq_cast_toRat] using
      FieldSpecialize.value_ofRat rep hrep hr d.toRat
  have covered : ∀ atom ∈ formula.polys,
      interpret f (Field.value_eq_zero rep hrep hr)
        (FieldSpecialize.literalPolynomial values atom) = 0 ∨
      ∀ y, (interpret f (Field.value_eq_zero rep hrep hr)
        (FieldSpecialize.literalPolynomial values atom)).IsRoot y →
        (interpret f (Field.value_eq_zero rep hrep hr) radical.core).IsRoot y := by
    intro atom hatom
    rcases FieldCarrier.atom_roots rep hrep hr values formula atom hatom with hz | hcover
    · exact Or.inl hz
    · right
      intro y hy
      exact (radical.roots f (Field.value_eq_zero rep hrep hr)
        (Field.value_one rep hrep hr) (Field.value_add rep hrep hr)
        (Field.value_sub rep hrep hr) (Field.value_mul rep hrep hr)
        context (FieldCarrier.product values formula) hradical y).mpr (hcover y hy)
  have result := Decision.cellSign_spec f (Field.value_eq_zero rep hrep hr)
    (Field.value_one rep hrep hr) (Field.value_add rep hrep hr)
    (Field.value_sub rep hrep hr) (Field.value_mul rep hrep hr)
    (Field.value_natCast rep hrep hr) sign hsign point hpoint
    formula (fun x => append (fun j => f (values j)) x)
    (FieldSpecialize.literalPolynomial values)
    (FieldCarrier.atom_eval rep hrep hr values) context radical.core cert hisolation
    covered rootValue evidence hquery
  have same : Decision.cellSign sign point (FieldSpecialize.literalPolynomial values)
      cert rootValue = cellSign sign values cert rootValue := by
    funext cell atom
    cases cell <;> rfl
  simpa only [same, f] using result

/-- The checked fixed-field cells decide a universal source formula. -/
theorem forall_cells (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (sign : PolyQuot p root → Int)
    (hsign : ∀ a, sign a = (SignType.sign (Field.value rep a) : Int))
    (values : Fin n → PolyQuot p root)
    (formula : QF (n + 1)) (context : Ctx)
    (radical : RadicalCert (PolyQuot p root) Ctx)
    (hradical : radical.check context (FieldCarrier.product values formula) = true)
    (cert : IsolationReplay (PolyQuot p root) Ctx)
    (hisolation : cert.check sign point context radical.core = true)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (evidence : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) →
      TarskiCertificate (PolyQuot p root) (PolyQuot p root) Ctx)
    (hquery : ∀ i atom, atom ∈ formula.polys →
      Sturm.check sign context radical.core
        (FieldSpecialize.literalPolynomial values atom)
        (.finite (point cert.isolations.intervals[i].lower))
        (.finite (point cert.isolations.intervals[i].upper))
        (rootValue i atom) (evidence i atom) = true) :
    OptionFold.allArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (cellSign sign values cert rootValue cell)) = some true ↔
      ∀ x, formula.toProp (append (fun j => Field.value rep (values j)) x) := by
  obtain ⟨roots, hmono, hlookup⟩ :=
    cellSign_spec rep hrep hr sign hsign values formula context radical hradical
      cert hisolation rootValue evidence hquery
  exact RealCoefficients.forall_formula roots hmono formula
    (fun x => append (fun j => Field.value rep (values j)) x)
    (cellSign sign values cert rootValue) hlookup

/-- The checked fixed-field cells decide an existential source formula. -/
theorem exists_cells (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (sign : PolyQuot p root → Int)
    (hsign : ∀ a, sign a = (SignType.sign (Field.value rep a) : Int))
    (values : Fin n → PolyQuot p root)
    (formula : QF (n + 1)) (context : Ctx)
    (radical : RadicalCert (PolyQuot p root) Ctx)
    (hradical : radical.check context (FieldCarrier.product values formula) = true)
    (cert : IsolationReplay (PolyQuot p root) Ctx)
    (hisolation : cert.check sign point context radical.core = true)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (evidence : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) →
      TarskiCertificate (PolyQuot p root) (PolyQuot p root) Ctx)
    (hquery : ∀ i atom, atom ∈ formula.polys →
      Sturm.check sign context radical.core
        (FieldSpecialize.literalPolynomial values atom)
        (.finite (point cert.isolations.intervals[i].lower))
        (.finite (point cert.isolations.intervals[i].upper))
        (rootValue i atom) (evidence i atom) = true) :
    OptionFold.anyArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (cellSign sign values cert rootValue cell)) = some true ↔
      ∃ x, formula.toProp (append (fun j => Field.value rep (values j)) x) := by
  obtain ⟨roots, hmono, hlookup⟩ :=
    cellSign_spec rep hrep hr sign hsign values formula context radical hradical
      cert hisolation rootValue evidence hquery
  exact RealCoefficients.exists_formula roots hmono formula
    (fun x => append (fun j => Field.value rep (values j)) x)
    (cellSign sign values cert rootValue) hlookup

end Hex.RCF.RealCoefficients.FieldDecision
