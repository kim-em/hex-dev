/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.CarrierRadical
public import HexRCF.RealCoefficients.IsolationsAlgebraic
public import HexRCF.RealCoefficients.CellFormula
public import HexRCF.RealCoefficients.OpenFormula

public section

/-! Signs supplied by the checked algebraic-coefficient cell decomposition. -/

namespace Hex.RCF.RealCoefficients

open Hex.RealFormula HexPolyMathlib.Interpret HexRealRootsMathlib

variable {Ctx : Type u} [DecidableEq Ctx]

/-- Open cells evaluate an atom at their dyadic sample. Root cells use a
recorded query value that must be checked against the same head and interval. -/
@[expose] def cellSign (values : Fin n → RealAlgebraicNumber)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (cell : Cell cert.isolations.intervals.size) (p : RealFormula.Poly (n + 1)) : Option Sign :=
  match cell with
  | .open cut =>
      some <| Sign.ofInt <| RealAlgebraicNumber.sign <|
        (Specialize.polynomial values p).eval
          (RealAlgebraicNumber.ofRat (cert.isolations.openPoint cut).toRat)
  | .root i => some <| Sign.ofInt (rootValue i p)

/-- Every recorded atom sign agrees with the real source polynomial at every
point of its cell. The isolation, radical and root-query checks are independent
Boolean premises, so a copied or stale query cannot inherit another cell's
result. -/
theorem cellSign_spec (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (radical : RadicalCert RealAlgebraicNumber Ctx)
    (hradical : radical.check context (Specialize.product values formula) = true)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (hisolation : cert.check RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context radical.core = true)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (evidence : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) →
      TarskiCertificate RealAlgebraicNumber RealAlgebraicNumber Ctx)
    (hquery : ∀ i p, p ∈ formula.polys →
      Sturm.check RealAlgebraicNumber.sign context radical.core
        (Specialize.polynomial values p)
        (.finite (RealAlgebraicNumber.ofRat cert.isolations.intervals[i].lower.toRat))
        (.finite (RealAlgebraicNumber.ofRat cert.isolations.intervals[i].upper.toRat))
        (rootValue i p) (evidence i p) = true) :
    ∃ root : Fin cert.isolations.intervals.size → ℝ,
      StrictMono root ∧
      (∀ cell x, Cell.Region root cell x →
        ∀ p ∈ formula.polys, ∃ sign,
          cellSign values cert rootValue cell p = some sign ∧
          SignType.sign (((sign.toInt : Int) : ℝ)) =
            SignType.sign (p.eval (append (fun j => (values j).toReal) x))) := by
  obtain ⟨root, hroot, hmono, hcomplete, hsample⟩ :=
    cert.roots_algebraic context radical.core hisolation
  refine ⟨root, hmono, ?_⟩
  intro cell x hx p hp
  cases cell with
  | «open» cut =>
      let q := Specialize.polynomial values p
      let observed := RealAlgebraicNumber.sign
        (q.eval (RealAlgebraicNumber.ofRat (cert.isolations.openPoint cut).toRat))
      refine ⟨Sign.ofInt observed, rfl, ?_⟩
      rw [Sign.ofInt_spec]
      have hs := cert.open_sign RealAlgebraicNumber.toReal RadicalCert.zero_iff
        RealAlgebraicNumber.add_toReal RealAlgebraicNumber.mul_toReal
        RealAlgebraicNumber.sign IsolationReplay.algebraic_sign
        (fun d => RealAlgebraicNumber.ofRat d.toRat) IsolationReplay.dyadic_point
        radical.core q root hmono hcomplete cut (hsample cut)
        (Specialize.atom_roots_of_radical values formula context radical
          hradical p hp) x hx
      change observed = (SignType.sign ((interpret RealAlgebraicNumber.toReal
        RadicalCert.zero_iff q).eval x) : Int) at hs
      rw [hs, Specialize.atom_eval values p x]
      exact sign_cast_sign _
  | root i =>
      have hxi : x = root i := hx
      subst x
      refine ⟨Sign.ofInt (rootValue i p), rfl, ?_⟩
      rw [Sign.ofInt_spec]
      have hs := cert.check_sign RealAlgebraicNumber.toReal RadicalCert.zero_iff
        RealAlgebraicNumber.one_toReal RealAlgebraicNumber.add_toReal
        RealAlgebraicNumber.sub_toReal RealAlgebraicNumber.mul_toReal
        (fun n => by
          change (RealAlgebraicNumber.ofRat (n : Rat)).toReal = (n : ℝ)
          simp)
        RealAlgebraicNumber.sign IsolationReplay.algebraic_sign
        (fun d => RealAlgebraicNumber.ofRat d.toRat) IsolationReplay.dyadic_point
        context radical.core hisolation i (Specialize.polynomial values p)
        (rootValue i p) (evidence i p) (hquery i p hp)
        (root i) (hroot i).1 (hroot i).2.1 (hroot i).2.2
      rw [hs, Specialize.atom_eval values p (root i)]
      exact sign_cast_sign _

/-- A successful strict fold proves the source universal statement. -/
theorem forall_cells (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (radical : RadicalCert RealAlgebraicNumber Ctx)
    (hradical : radical.check context (Specialize.product values formula) = true)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (hisolation : cert.check RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context radical.core = true)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (evidence : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) →
      TarskiCertificate RealAlgebraicNumber RealAlgebraicNumber Ctx)
    (hquery : ∀ i p, p ∈ formula.polys →
      Sturm.check RealAlgebraicNumber.sign context radical.core
        (Specialize.polynomial values p)
        (.finite (RealAlgebraicNumber.ofRat cert.isolations.intervals[i].lower.toRat))
        (.finite (RealAlgebraicNumber.ofRat cert.isolations.intervals[i].upper.toRat))
        (rootValue i p) (evidence i p) = true) :
    OptionFold.allArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (cellSign values cert rootValue cell)) = some true ↔
      ∀ x, formula.toProp (append (fun j => (values j).toReal) x) := by
  obtain ⟨root, hmono, hlookup⟩ :=
    cellSign_spec values formula context radical hradical cert hisolation
      rootValue evidence hquery
  exact forall_formula root hmono formula
    (fun x => append (fun j => (values j).toReal) x)
    (cellSign values cert rootValue) hlookup

/-- A successful strict fold proves the source existential statement. -/
theorem exists_cells (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (radical : RadicalCert RealAlgebraicNumber Ctx)
    (hradical : radical.check context (Specialize.product values formula) = true)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (hisolation : cert.check RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context radical.core = true)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) → Int)
    (evidence : Fin cert.isolations.intervals.size → RealFormula.Poly (n + 1) →
      TarskiCertificate RealAlgebraicNumber RealAlgebraicNumber Ctx)
    (hquery : ∀ i p, p ∈ formula.polys →
      Sturm.check RealAlgebraicNumber.sign context radical.core
        (Specialize.polynomial values p)
        (.finite (RealAlgebraicNumber.ofRat cert.isolations.intervals[i].lower.toRat))
        (.finite (RealAlgebraicNumber.ofRat cert.isolations.intervals[i].upper.toRat))
        (rootValue i p) (evidence i p) = true) :
    OptionFold.anyArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (cellSign values cert rootValue cell)) = some true ↔
      ∃ x, formula.toProp (append (fun j => (values j).toReal) x) := by
  obtain ⟨root, hmono, hlookup⟩ :=
    cellSign_spec values formula context radical hradical cert hisolation
      rootValue evidence hquery
  exact exists_formula root hmono formula
    (fun x => append (fun j => (values j).toReal) x)
    (cellSign values cert rootValue) hlookup

end Hex.RCF.RealCoefficients
