/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SignMatrixCheck
public import HexRCF.Carrier
public import HexRCF.CommonRoot
public import Mathlib.Topology.Instances.Sign

public section

/-!
# Semantics of certified sign matrices for RCF cells

The Mathlib-free checker and replay live in `HexRCF.SignMatrixCheck`. This file
proves that its exact dyadic signs and cached common-root decisions agree with
polynomial signs over the semantic cells cut out by a checked square-free
carrier, and connects Boolean formula replay to reflected propositions.
-/

namespace Hex.RCF

open HexRealRootsMathlib Polynomial

namespace Sign

/-- Collapsing an integer preserves its mathematical sign. -/
theorem ofInt_spec (value : Int) :
    SignType.sign (((Sign.ofInt value).toInt : Int) : ℝ) =
      SignType.sign ((value : Int) : ℝ) := by
  by_cases hneg : value < 0
  · have hcast : ((value : Int) : ℝ) < 0 := by exact_mod_cast hneg
    have hsign : SignType.sign ((value : Int) : ℝ) = -1 :=
      sign_eq_neg_one_iff.mpr hcast
    rw [hsign]
    simp [ofInt, hneg, toInt]
  by_cases hpos : 0 < value
  · have hcast : (0 : ℝ) < (value : Int) := by exact_mod_cast hpos
    have hsign : SignType.sign ((value : Int) : ℝ) = 1 :=
      sign_eq_one_iff.mpr hcast
    rw [hsign]
    simp [ofInt, hneg, hpos, toInt]
  · have hzero : value = 0 := by omega
    subst value
    simp [ofInt, toInt]

end Sign

end Hex.RCF

namespace Polynomial

/-- The sign of a continuous polynomial evaluation is constant on a
preconnected set containing no root of the polynomial. -/
theorem sign_eq_of_noRoot {p : Polynomial ℝ} {s : Set ℝ}
    (hs : IsPreconnected s) (hnz : ∀ z ∈ s, ¬p.IsRoot z)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (p.eval x) = SignType.sign (p.eval y) := by
  have hcont : ContinuousOn (SignType.sign ∘ fun z => p.eval z) s := by
    refine (continuousOn_of_forall_continuousAt fun q hq => ?_).comp
      p.continuousOn (Set.mapsTo_image (fun z => p.eval z) s)
    obtain ⟨z, hz, rfl⟩ := hq
    exact continuousAt_sign_of_ne_zero (fun hzero => hnz z hz hzero)
  exact (hs.image _ hcont).subsingleton
    (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy)

end Polynomial

namespace Hex.RCF

open HexRealRootsMathlib Polynomial

/-- Exact dyadic Horner evaluation computes the sign of the corresponding
real-polynomial evaluation. -/
theorem evalSign_spec (p : ZPoly) (x : Dyadic) :
    SignType.sign (((evalSign p x).toInt : Int) : ℝ) =
      SignType.sign ((toPolyℝ p).eval (Dyadic.toReal x)) := by
  rw [evalSign, Sign.ofInt_spec, ← toReal_evalDyadic]
  exact sign_dyadicSign _

/-- A polynomial whose executable degree is not positive is constant after
casting, including the zero polynomial. -/
theorem eval_eq_at_zero (p : ZPoly)
    (hdegree : ¬0 < p.degree?.getD 0) (x : ℝ) :
    (toPolyℝ p).eval x = (toPolyℝ p).eval 0 := by
  have hnat : (toPolyℝ p).natDegree = 0 := by
    rw [natDegree_toPolyℝ]
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hnat,
    Polynomial.eval_C, Polynomial.eval_C]

/-- Sign constancy on an open carrier cell from root containment. -/
theorem sign_eval_eq_open {carrier : ZPoly} {replay : SturmReplay}
    (hreplay : replay.check carrier = true) {isolations : IsolationCert}
    (hstrict : isolations.checkStrict replay = true) {atom : ZPoly}
    (hroot : ∀ z, (toPolyℝ atom).IsRoot z →
      (toPolyℝ carrier).IsRoot z)
    (cut : Fin (isolations.intervals.size + 1)) {x : ℝ}
    (hx : Cell.Sem (isolations.rootModel hreplay hstrict) (.open cut) x) :
    SignType.sign ((toPolyℝ atom).eval
      (Dyadic.toReal (isolations.openPoint cut))) =
      SignType.sign ((toPolyℝ atom).eval x) := by
  let model := isolations.rootModel hreplay hstrict
  apply Polynomial.sign_eq_of_noRoot (Cell.isPreconnected_open model cut)
  · intro z hz hatom
    exact Cell.open_not_root model hz (hroot z hatom)
  · exact Cell.openPoint_mem isolations hreplay hstrict cut
  · exact hx

/-- The exact dyadic sign is valid at every point of an open carrier cell. -/
theorem evalSign_open_spec {carrier : ZPoly} {replay : SturmReplay}
    (hreplay : replay.check carrier = true) {isolations : IsolationCert}
    (hstrict : isolations.checkStrict replay = true) {atom : ZPoly}
    (hroot : ∀ z, (toPolyℝ atom).IsRoot z →
      (toPolyℝ carrier).IsRoot z)
    (cut : Fin (isolations.intervals.size + 1)) {x : ℝ}
    (hx : Cell.Sem (isolations.rootModel hreplay hstrict) (.open cut) x) :
    SignType.sign (((evalSign atom (isolations.openPoint cut)).toInt : Int) : ℝ) =
      SignType.sign ((toPolyℝ atom).eval x) :=
  (evalSign_spec atom (isolations.openPoint cut)).trans
    (sign_eval_eq_open hreplay hstrict hroot cut hx)

/-- Every nonconstant sentence atom has its exact sampled sign throughout an
open cell of an accepted carrier decomposition. -/
theorem evalSign_open_of_atom {sentence : Sentence} {carrier : CarrierCert}
    (hcarrier : carrier.check sentence = true)
    {isolations : IsolationCert}
    (hstrict : isolations.checkStrict carrier.replay = true)
    {atom : ZPoly} (hatom : atom ∈ sentence.polys)
    (cut : Fin (isolations.intervals.size + 1)) {x : ℝ}
    (hx : Cell.Sem
      (isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict)
      (.open cut) x) :
    SignType.sign (((evalSign atom (isolations.openPoint cut)).toInt : Int) : ℝ) =
      SignType.sign ((toPolyℝ atom).eval x) := by
  apply evalSign_open_spec (CarrierCert.replay_of_check hcarrier) hstrict
  · intro z hroot
    exact (CarrierCert.isRoot_iff_atom hcarrier z).2 ⟨atom, hatom, hroot⟩
  · exact hx

/-- A nonzero atom has the same sign at carrier root `i` as on the open cell
immediately to its left. -/
theorem sign_eval_eq_leftRoot {carrier atom : ZPoly} {cert : IsolationCert}
    (model : RootModel carrier cert)
    (hroot : ∀ z, (toPolyℝ atom).IsRoot z →
      (toPolyℝ carrier).IsRoot z)
    (i : Fin cert.intervals.size)
    (hnonzero : ¬(toPolyℝ atom).IsRoot (model.root i))
    {sample : ℝ} (hsample : Cell.Sem model (.open i.castSucc) sample) :
    SignType.sign ((toPolyℝ atom).eval sample) =
      SignType.sign ((toPolyℝ atom).eval (model.root i)) := by
  apply Polynomial.sign_eq_of_noRoot (model.isPreconnected_leftSpan i) _
      (model.leftOpen_mem_leftSpan i hsample) (model.root_mem_leftSpan i)
  intro z hz hzroot
  exact hnonzero (by
    rw [← model.root_unique_leftSpan i (hroot z hzroot) hz]
    exact hzroot)

/-- Exact left-open sample sign at a carrier root where the atom does not
vanish. -/
theorem evalSign_leftRoot {carrier atom : ZPoly} {replay : SturmReplay}
    {isolations : IsolationCert} (hreplay : replay.check carrier = true)
    (hstrict : isolations.checkStrict replay = true)
    (hroot : ∀ z, (toPolyℝ atom).IsRoot z →
      (toPolyℝ carrier).IsRoot z)
    (i : Fin isolations.intervals.size)
    (hnonzero : ¬(toPolyℝ atom).IsRoot
      ((isolations.rootModel hreplay hstrict).root i)) :
    SignType.sign
      (((evalSign atom (isolations.openPoint i.castSucc)).toInt : Int) : ℝ) =
      SignType.sign ((toPolyℝ atom).eval
        ((isolations.rootModel hreplay hstrict).root i)) := by
  rw [evalSign_spec]
  exact sign_eval_eq_leftRoot (isolations.rootModel hreplay hstrict)
    hroot i hnonzero (Cell.openPoint_mem isolations hreplay hstrict i.castSucc)

/-- A false cached common-root query certifies the exact nonzero root-cell
sign using the canonical left open sample. -/
theorem evalSign_commonLeft
    {sentence : Sentence} {carrier : CarrierCert}
    (hcarrier : carrier.check sentence = true)
    {isolations : IsolationCert}
    (hstrict : isolations.checkStrict carrier.replay = true)
    {atom : ZPoly} (hatom : atom ∈ sentence.polys)
    {common : CommonRootCert}
    (hcommon : common.check atom carrier.carrier = true)
    (i : Fin isolations.intervals.size)
    (hnonroot : common.hasRoot isolations.intervals[i] = false) :
    SignType.sign
      (((evalSign atom (isolations.openPoint i.castSucc)).toInt : Int) : ℝ) =
      SignType.sign ((toPolyℝ atom).eval
        ((isolations.rootModel (CarrierCert.replay_of_check hcarrier)
          hstrict).root i)) := by
  let hreplay := CarrierCert.replay_of_check hcarrier
  let model := isolations.rootModel hreplay hstrict
  have hroot : ∀ z, (toPolyℝ atom).IsRoot z →
      (toPolyℝ carrier.carrier).IsRoot z := by
    intro z hz
    exact (carrier.isRoot_iff_atom hcarrier z).2 ⟨atom, hatom, hz⟩
  have hnonzero : ¬(toPolyℝ atom).IsRoot (model.root i) := by
    intro hz
    have hyes : common.hasRoot isolations.intervals[i] = true :=
      (common.hasRoot_model_iff hreplay hstrict hcommon i).2 hz
    rw [hnonroot] at hyes
    contradiction
  exact evalSign_leftRoot hreplay hstrict hroot i hnonzero

/-- Exact evaluation cannot report zero at a certified nonroot. -/
theorem evalSign_ne_zero (p : ZPoly) (x : Dyadic)
    (hroot : ¬(toPolyℝ p).IsRoot (Dyadic.toReal x)) :
    evalSign p x ≠ .zero := by
  intro hzero
  have hsign := evalSign_spec p x
  rw [hzero] at hsign
  have heval : (toPolyℝ p).eval (Dyadic.toReal x) = 0 := by
    apply sign_eq_zero_iff.mp
    simpa [Sign.toInt] using hsign.symm
  exact hroot heval

/-- The shared open-cell lookup is total and exact for every formula atom of a
checked carrier, including constants. -/
theorem openCellSign_spec {sentence : Sentence} {carrier : CarrierCert}
    (hcarrier : carrier.check sentence = true)
    {isolations : IsolationCert}
    (hstrict : isolations.checkStrict carrier.replay = true)
    {p : ZPoly} (hp : p ∈ sentence.formula.polys)
    (cut : Fin (isolations.intervals.size + 1)) {x : ℝ}
    (hx : Cell.Sem
      (isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict)
      (.open cut) x) :
    ∃ sign, openCellSign? p isolations cut = some sign ∧
      SignType.sign (((sign.toInt : Int) : ℝ)) =
        SignType.sign ((toPolyℝ p).eval x) := by
  by_cases hdegree : 0 < p.degree?.getD 0
  · have hpmem : p ∈ sentence.polys := by
      simp only [Sentence.polys, List.mem_filter, decide_eq_true_eq]
      exact ⟨hp, hdegree⟩
    let hreplay := CarrierCert.replay_of_check hcarrier
    let model := isolations.rootModel hreplay hstrict
    have hroot : ∀ z, (toPolyℝ p).IsRoot z →
        (toPolyℝ carrier.carrier).IsRoot z := by
      intro z hz
      exact (carrier.isRoot_iff_atom hcarrier z).2 ⟨p, hpmem, hz⟩
    have hsample : Cell.Sem model (.open cut)
        (Dyadic.toReal (isolations.openPoint cut)) :=
      Cell.openPoint_mem isolations hreplay hstrict cut
    have hnotroot : ¬(toPolyℝ p).IsRoot
        (Dyadic.toReal (isolations.openPoint cut)) := by
      intro hpRoot
      exact Cell.open_not_root model hsample (hroot _ hpRoot)
    have hnonzero : evalSign p (isolations.openPoint cut) ≠ .zero :=
      evalSign_ne_zero p _ hnotroot
    refine ⟨evalSign p (isolations.openPoint cut), ?_, ?_⟩
    · simp [openCellSign?, hdegree, openSign?_eq_some hnonzero]
    · exact evalSign_open_of_atom hcarrier hstrict hpmem cut hx
  · refine ⟨evalSign p 0, by simp [openCellSign?, hdegree], ?_⟩
    rw [eval_eq_at_zero p hdegree x]
    simpa using evalSign_spec p 0

namespace SignMatrixCert

/-- A checked sign-matrix package returns a total exact sign for every atom on
every semantic carrier cell when given the checker-derived package order. -/
theorem signWith?_spec {sentence : Sentence} {carrier : CarrierCert}
    {cert : SignMatrixCert} {isolations : IsolationCert}
    (hcarrier : carrier.check sentence = true)
    (hstrict : isolations.checkStrict carrier.replay = true)
    (hmatrix : cert.check sentence carrier = true)
    {commonPolys : List ZPoly}
    (hpolys : commonPolys = dedupPolys sentence.polys)
    {p : ZPoly} (hp : p ∈ sentence.formula.polys)
    (cell : Cell isolations.intervals.size) :
    ∃ sign, cert.signWith? commonPolys isolations cell p = some sign ∧
      ∀ x, Cell.Sem
        (isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict)
        cell x →
        SignType.sign (((sign.toInt : Int) : ℝ)) =
          SignType.sign ((toPolyℝ p).eval x) := by
  subst commonPolys
  by_cases hdegree : 0 < p.degree?.getD 0
  · have hpmem : p ∈ sentence.polys := by
      simp only [Sentence.polys, List.mem_filter, decide_eq_true_eq]
      exact ⟨hp, hdegree⟩
    have hreplay := CarrierCert.replay_of_check hcarrier
    let model := isolations.rootModel hreplay hstrict
    have hroot : ∀ z, (toPolyℝ p).IsRoot z →
        (toPolyℝ carrier.carrier).IsRoot z := by
      intro z hz
      exact (carrier.isRoot_iff_atom hcarrier z).2 ⟨p, hpmem, hz⟩
    cases cell with
    | «open» cut =>
        have hsample : Cell.Sem model (.open cut)
            (Dyadic.toReal (isolations.openPoint cut)) :=
          Cell.openPoint_mem isolations hreplay hstrict cut
        obtain ⟨sign, hsign, _⟩ :=
          openCellSign_spec hcarrier hstrict hp cut hsample
        refine ⟨sign, by simpa [signWith?] using hsign, ?_⟩
        intro x hx
        obtain ⟨other, hother, hsound⟩ :=
          openCellSign_spec hcarrier hstrict hp cut hx
        rw [hsign] at hother
        cases Option.some.inj hother
        exact hsound
    | root i =>
        obtain ⟨common, hfind, hcommon⟩ :=
          cert.findCommon?_of_check hmatrix hpmem
        have hfind' : Hex.RCF.findCommon? p (dedupPolys sentence.polys)
            cert.commonRoots = some common := by
          simpa [findCommon?] using hfind
        by_cases hhas : common.hasRoot isolations.intervals[i] = true
        · refine ⟨.zero, ?_, ?_⟩
          · have hhas' : common.hasRoot isolations.intervals[↑i] = true := by
              simpa using hhas
            simp only [signWith?, if_pos hdegree]
            rw [hfind']
            change rootSign? p common isolations i = some .zero
            unfold rootSign?
            rw [hhas']
          · intro x hx
            have hxroot : x = model.root i := by simpa [Cell.Sem] using hx
            rw [hxroot]
            have hpRoot : (toPolyℝ p).IsRoot (model.root i) :=
              (common.hasRoot_model_iff hreplay hstrict hcommon i).1 hhas
            simp only [Polynomial.IsRoot] at hpRoot
            rw [hpRoot]
            simp [Sign.toInt]
        · have hhasFalse : common.hasRoot isolations.intervals[i] = false :=
            Bool.eq_false_of_not_eq_true hhas
          have hhasFalse' : common.hasRoot isolations.intervals[↑i] = false := by
            simpa using hhasFalse
          have hsample : Cell.Sem model (.open i.castSucc)
              (Dyadic.toReal (isolations.openPoint i.castSucc)) :=
            Cell.openPoint_mem isolations hreplay hstrict i.castSucc
          have hnotroot : ¬(toPolyℝ p).IsRoot
              (Dyadic.toReal (isolations.openPoint i.castSucc)) := by
            intro hpRoot
            exact Cell.open_not_root model hsample (hroot _ hpRoot)
          have hnonzero : evalSign p (isolations.openPoint i.castSucc) ≠ .zero :=
            evalSign_ne_zero p _ hnotroot
          refine ⟨evalSign p (isolations.openPoint i.castSucc), ?_, ?_⟩
          · simp only [signWith?, if_pos hdegree]
            rw [hfind']
            change rootSign? p common isolations i =
              some (evalSign p (isolations.openPoint i.castSucc))
            unfold rootSign?
            rw [hhasFalse', openSign?_eq_some hnonzero]
          · intro x hx
            have hxroot : x = model.root i := by simpa [Cell.Sem] using hx
            rw [hxroot]
            exact evalSign_commonLeft hcarrier hstrict hpmem
              hcommon i hhasFalse
  · cases cell with
    | «open» cut =>
        refine ⟨evalSign p 0, by simp [signWith?, openCellSign?, hdegree], ?_⟩
        intro x _hx
        rw [eval_eq_at_zero p hdegree x]
        simpa using evalSign_spec p 0
    | root i =>
        refine ⟨evalSign p 0, by simp [signWith?, hdegree], ?_⟩
        intro x _hx
        rw [eval_eq_at_zero p hdegree x]
        simpa using evalSign_spec p 0

/-- Public atom-sign lookup is total and exact under the combined checker. -/
theorem sign?_spec {sentence : Sentence} {carrier : CarrierCert}
    {cert : SignMatrixCert} {isolations : IsolationCert}
    (hcarrier : carrier.check sentence = true)
    (hstrict : isolations.checkStrict carrier.replay = true)
    (hmatrix : cert.check sentence carrier = true)
    {p : ZPoly} (hp : p ∈ sentence.formula.polys)
    (cell : Cell isolations.intervals.size) :
    ∃ sign, cert.sign? sentence isolations cell p = some sign ∧
      ∀ x, Cell.Sem
        (isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict)
        cell x →
        SignType.sign (((sign.toInt : Int) : ℝ)) =
          SignType.sign ((toPolyℝ p).eval x) := by
  exact cert.signWith?_spec hcarrier hstrict hmatrix rfl hp cell

end SignMatrixCert

namespace Cmp

/-- Comparison evaluation depends only on the mathematical sign. -/
theorem evalSign_iff {cmp : Cmp} {sign : Sign} {value : ℝ}
    (hsign : SignType.sign (((sign.toInt : Int) : ℝ)) = SignType.sign value) :
    cmp.evalSign sign = true ↔ cmp.toProp value 0 := by
  cases sign with
  | neg =>
      have hv : SignType.sign value = -1 := by
        simpa [Sign.toInt] using hsign.symm
      have hvneg : value < 0 := sign_eq_neg_one_iff.mp hv
      have hvnotge : ¬0 ≤ value := not_le.mpr hvneg
      cases cmp <;> simp [evalSign, toProp, hvneg, hvneg.le,
        hvneg.ne, hvnotge]
  | zero =>
      have hv : SignType.sign value = 0 := by
        simpa [Sign.toInt] using hsign.symm
      have hvzero : value = 0 := sign_eq_zero_iff.mp hv
      subst value
      cases cmp <;> simp [evalSign, toProp]
  | pos =>
      have hv : SignType.sign value = 1 := by
        simpa [Sign.toInt] using hsign.symm
      have hvpos : 0 < value := sign_eq_one_iff.mp hv
      have hvnotle : ¬value ≤ 0 := not_le.mpr hvpos
      cases cmp <;> simp [evalSign, toProp, hvpos, hvpos.le,
        hvpos.ne', hvnotle]

end Cmp

/-- Relate the reflected atom semantics to real-cast polynomial evaluation. -/
theorem Atom.toProp_iff_eval (a : Atom) (x : ℝ) :
    a.toProp x ↔ a.cmp.toProp ((toPolyℝ a.p).eval x) 0 := by
  unfold Atom.toProp
  rw [Polynomial.aeval_def, ← Polynomial.eval_map]
  rfl

namespace Formula

/-- Formula evaluation returns a Boolean whose truth is exactly the semantic
formula, provided every referenced polynomial lookup carries its exact sign.
The existential result also supplies the false direction required by negation
and implication. -/
theorem evalSigns_spec {formula : Formula} {signOf : ZPoly → Option Sign}
    {x : ℝ}
    (hlookup : ∀ p ∈ formula.polys, ∃ sign,
      signOf p = some sign ∧
      SignType.sign (((sign.toInt : Int) : ℝ)) =
        SignType.sign ((toPolyℝ p).eval x)) :
    ∃ value, formula.evalSigns signOf = some value ∧
      (value = true ↔ formula.toProp x) := by
  induction formula with
  | atom a =>
      obtain ⟨sign, hsign, hsound⟩ := hlookup a.p (by simp [Formula.polys])
      refine ⟨a.cmp.evalSign sign, by simp [evalSigns, hsign], ?_⟩
      rw [Formula.toProp, a.toProp_iff_eval]
      exact Cmp.evalSign_iff hsound
  | tt => exact ⟨true, rfl, by simp [Formula.toProp]⟩
  | ff => exact ⟨false, rfl, by simp [Formula.toProp]⟩
  | not φ ih =>
      obtain ⟨value, hvalue, hsound⟩ := ih (by
        intro p hp
        exact hlookup p (by simpa [Formula.polys] using hp))
      refine ⟨!value, by simp [evalSigns, hvalue], ?_⟩
      cases value <;>
        simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
          eq_self, Formula.toProp, false_iff, true_iff,
          not_false_eq_true, not_true_eq_false]
  | and φ ψ ihφ ihψ =>
      obtain ⟨left, hleft, hleftSound⟩ := ihφ (by
        intro p hp
        exact hlookup p (by simp [Formula.polys, hp]))
      obtain ⟨right, hright, hrightSound⟩ := ihψ (by
        intro p hp
        exact hlookup p (by simp [Formula.polys, hp]))
      refine ⟨left && right, by simp [evalSigns, hleft, hright], ?_⟩
      cases left <;> cases right <;>
        simp_all only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
          eq_self, Formula.toProp, false_iff, true_iff] <;> simp
  | or φ ψ ihφ ihψ =>
      obtain ⟨left, hleft, hleftSound⟩ := ihφ (by
        intro p hp
        exact hlookup p (by simp [Formula.polys, hp]))
      obtain ⟨right, hright, hrightSound⟩ := ihψ (by
        intro p hp
        exact hlookup p (by simp [Formula.polys, hp]))
      refine ⟨left || right, by simp [evalSigns, hleft, hright], ?_⟩
      cases left <;> cases right <;>
        simp_all only [Bool.false_or, Bool.true_or, Bool.false_eq_true,
          eq_self, Formula.toProp, false_iff, true_iff] <;> simp
  | imp φ ψ ihφ ihψ =>
      obtain ⟨left, hleft, hleftSound⟩ := ihφ (by
        intro p hp
        exact hlookup p (by simp [Formula.polys, hp]))
      obtain ⟨right, hright, hrightSound⟩ := ihψ (by
        intro p hp
        exact hlookup p (by simp [Formula.polys, hp]))
      refine ⟨!left || right, by simp [evalSigns, hleft, hright], ?_⟩
      cases left <;> cases right <;>
        simp_all only [Bool.not_false, Bool.not_true, Bool.false_or,
          Bool.true_or, Bool.false_eq_true, eq_self, Formula.toProp,
          false_iff, true_iff] <;> simp

/-- Successful true formula evaluation is equivalent to the reflected
semantics at the point. -/
theorem evalSigns_eq_true_iff {formula : Formula}
    {signOf : ZPoly → Option Sign} {x : ℝ}
    (hlookup : ∀ p ∈ formula.polys, ∃ sign,
      signOf p = some sign ∧
      SignType.sign (((sign.toInt : Int) : ℝ)) =
        SignType.sign ((toPolyℝ p).eval x)) :
    formula.evalSigns signOf = some true ↔ formula.toProp x := by
  obtain ⟨value, hvalue, hsound⟩ := evalSigns_spec hlookup
  constructor
  · intro htrue
    exact hsound.mp (Option.some.inj (hvalue.symm.trans htrue))
  · intro hprop
    have : value = true := hsound.mpr hprop
    simpa [this] using hvalue

/-- Constant-only formula evaluation is exact at every real point, including
formulas containing the zero polynomial. -/
theorem evalConstants_eq_true_iff {formula : Formula}
    (hconstant : ∀ p ∈ formula.polys, ¬0 < p.degree?.getD 0) (x : ℝ) :
    formula.evalConstants? = some true ↔ formula.toProp x := by
  apply evalSigns_eq_true_iff
  intro p hp
  refine ⟨Hex.RCF.evalSign p 0, rfl, ?_⟩
  rw [eval_eq_at_zero p (hconstant p hp) x]
  simpa using Hex.RCF.evalSign_spec p 0

end Formula

namespace SignMatrixCert

/-- A checked package computes one Boolean valid uniformly throughout each
semantic carrier cell. -/
theorem evalCell_spec {sentence : Sentence} {carrier : CarrierCert}
    {cert : SignMatrixCert} {isolations : IsolationCert}
    (hcarrier : carrier.check sentence = true)
    (hstrict : isolations.checkStrict carrier.replay = true)
    (hmatrix : cert.check sentence carrier = true)
    (cell : Cell isolations.intervals.size) :
    ∃ value, cert.evalCell? sentence isolations cell = some value ∧
      ∀ x, Cell.Sem
        (isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict)
        cell x →
        (value = true ↔ sentence.formula.toProp x) := by
  let model := isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict
  let commonPolys := dedupPolys sentence.polys
  obtain ⟨sample, hsample⟩ := Cell.exists_point model cell
  obtain ⟨entries, hentries⟩ := buildSigns?_total
      (signOf := cert.signWith? commonPolys isolations cell)
      (ps := dedupPolys sentence.formula.polys) (by
    intro p hp
    have hpFormula : p ∈ sentence.formula.polys := mem_dedupPolys.mp hp
    obtain ⟨sign, hsign, _hsound⟩ :=
      cert.signWith?_spec hcarrier hstrict hmatrix rfl hpFormula cell
    exact ⟨sign, hsign⟩)
  obtain ⟨value, hvalue, _hsampleSound⟩ := Formula.evalSigns_spec
    (x := sample) (by
      intro p hp
      obtain ⟨sign, hsign, hsound⟩ :=
        cert.signWith?_spec hcarrier hstrict hmatrix rfl hp cell
      have hfind := findSign?_of_build hentries (mem_dedupPolys.mpr hp)
      rw [hsign] at hfind
      exact ⟨sign, hfind, hsound sample hsample⟩)
  refine ⟨value, by simp [evalCell?, commonPolys, hentries, hvalue], ?_⟩
  intro x hx
  have hformula := Formula.evalSigns_eq_true_iff
    (formula := sentence.formula)
    (signOf := fun p => findSign? p entries) (x := x) (by
      intro p hp
      obtain ⟨sign, hsign, hsound⟩ :=
        cert.signWith?_spec hcarrier hstrict hmatrix rfl hp cell
      have hfind := findSign?_of_build hentries (mem_dedupPolys.mpr hp)
      rw [hsign] at hfind
      exact ⟨sign, hfind, hsound x hx⟩)
  rw [← hformula, hvalue]
  simp

/-- The computed true value is exactly the reflected formula semantics at
every point of the checked cell. -/
theorem evalCell_eq_true_iff {sentence : Sentence} {carrier : CarrierCert}
    {cert : SignMatrixCert} {isolations : IsolationCert}
    (hcarrier : carrier.check sentence = true)
    (hstrict : isolations.checkStrict carrier.replay = true)
    (hmatrix : cert.check sentence carrier = true)
    {cell : Cell isolations.intervals.size} {x : ℝ}
    (hx : Cell.Sem
      (isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict)
      cell x) :
    cert.evalCell? sentence isolations cell = some true ↔
      sentence.formula.toProp x := by
  obtain ⟨value, hvalue, hsound⟩ :=
    cert.evalCell_spec hcarrier hstrict hmatrix cell
  constructor
  · intro htrue
    have : value = true := Option.some.inj (hvalue.symm.trans htrue)
    exact (hsound x hx).1 this
  · intro hprop
    have : value = true := (hsound x hx).2 hprop
    simpa [this] using hvalue

end SignMatrixCert

end Hex.RCF
