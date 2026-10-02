/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldRootSigns

public section

/-! Assemble checked literal root queries with fixed-field cell decisions. -/

namespace Hex.RCF.RealCoefficients.FieldReplay

open Hex Hex.RealFormula

variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]
variable {Ctx : Type u} [DecidableEq Ctx]

@[expose] def intervals (cert : IsolationReplay (PolyQuot p root) Ctx) :
    Vector DyadicInterval cert.isolations.intervals.size :=
  cert.isolations.intervals.toVector

/-- A checked finite root-sign table supplies every atom query required by
the universal cell theorem, with the certificate's original interval. -/
theorem forall_formula (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (sign : PolyQuot p root → Int)
    (hsign : ∀ a, sign a = (SignType.sign (Field.value rep a) : Int))
    (values : Fin n → PolyQuot p root) (formula : QF (n + 1))
    (context : Ctx) (radical : RadicalCert (PolyQuot p root) Ctx)
    (hradical : radical.check context (FieldCarrier.product values formula) = true)
    (cert : IsolationReplay (PolyQuot p root) Ctx)
    (hisolation : cert.check sign FieldDecision.point context radical.core = true)
    (rootSigns : FieldRootSigns.Table (PolyQuot p root) Ctx (n + 1)
      cert.isolations.intervals.size)
    (hroots : rootSigns.check sign FieldDecision.point context radical.core
      (intervals cert) (FieldSpecialize.literalPolynomial values) formula = true) :
    OptionFold.allArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns
        (FieldDecision.cellSign sign values cert (rootSigns.value cert.total) cell)) = some true ↔
      ∀ x, formula.toProp (append (fun j => Field.value rep (values j)) x) := by
  apply FieldDecision.forall_cells rep hrep hr sign hsign values formula context
    radical hradical cert hisolation (rootSigns.value cert.total)
    (rootSigns.evidence cert.total)
  intro i atom hatom
  have hquery := rootSigns.query_checked sign FieldDecision.point context radical.core
    (intervals cert) (FieldSpecialize.literalPolynomial values) formula hroots
    i atom hatom cert.total
  have hinter : (intervals cert)[i] = cert.isolations.intervals[i] := by
    simp [intervals]
  simpa only [hinter] using hquery

/-- The same checked table supplies the existential cell theorem. -/
theorem exists_formula (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (sign : PolyQuot p root → Int)
    (hsign : ∀ a, sign a = (SignType.sign (Field.value rep a) : Int))
    (values : Fin n → PolyQuot p root) (formula : QF (n + 1))
    (context : Ctx) (radical : RadicalCert (PolyQuot p root) Ctx)
    (hradical : radical.check context (FieldCarrier.product values formula) = true)
    (cert : IsolationReplay (PolyQuot p root) Ctx)
    (hisolation : cert.check sign FieldDecision.point context radical.core = true)
    (rootSigns : FieldRootSigns.Table (PolyQuot p root) Ctx (n + 1)
      cert.isolations.intervals.size)
    (hroots : rootSigns.check sign FieldDecision.point context radical.core
      (intervals cert) (FieldSpecialize.literalPolynomial values) formula = true) :
    OptionFold.anyArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns
        (FieldDecision.cellSign sign values cert (rootSigns.value cert.total) cell)) = some true ↔
      ∃ x, formula.toProp (append (fun j => Field.value rep (values j)) x) := by
  apply FieldDecision.exists_cells rep hrep hr sign hsign values formula context
    radical hradical cert hisolation (rootSigns.value cert.total)
    (rootSigns.evidence cert.total)
  intro i atom hatom
  have hquery := rootSigns.query_checked sign FieldDecision.point context radical.core
    (intervals cert) (FieldSpecialize.literalPolynomial values) formula hroots
    i atom hatom cert.total
  have hinter : (intervals cert)[i] = cert.isolations.intervals[i] := by
    simp [intervals]
  simpa only [hinter] using hquery

end Hex.RCF.RealCoefficients.FieldReplay
