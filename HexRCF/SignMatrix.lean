/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Carrier
public import HexRCF.CommonRoot
public import Mathlib.Topology.Instances.Sign

public section

/-!
# Certified sign matrices for RCF cells

This file computes exact polynomial signs on the semantic cells cut out by a
checked square-free carrier.  Open-cell signs come from exact dyadic Horner
evaluation and preconnected root-free sign constancy. Root-cell zero tests use
the cached common-root packages; nonzero root signs are transferred from an
adjacent open cell. Formula evaluation is option-valued so missing or
misaligned certificate data fails closed.
-/

namespace Hex.RCF

open HexRealRootsMathlib Polynomial

/-- The three possible signs stored by an RCF sign matrix. -/
inductive Sign where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

namespace Sign

/-- Canonical integer representative used to connect signs to Mathlib's
`SignType.sign`. -/
@[expose]
def toInt : Sign → Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- Collapse an arbitrary integer to its three-way sign. -/
@[expose]
def ofInt (value : Int) : Sign :=
  if value < 0 then .neg else if 0 < value then .pos else .zero

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

/-- The sign of a continuous polynomial evaluation is constant on a
preconnected set containing no root of the polynomial. -/
theorem sign_eval_eq_of_noRoot {p : Polynomial ℝ} {s : Set ℝ}
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

/-- Exact executable sign of an integer polynomial at a dyadic point. -/
@[expose]
def evalSign (p : ZPoly) (x : Dyadic) : Sign :=
  Sign.ofInt (Hex.dyadicSign (p.evalDyadic x))

/-- Exact dyadic Horner evaluation computes the sign of the corresponding
real-polynomial evaluation. -/
theorem evalSign_spec (p : ZPoly) (x : Dyadic) :
    SignType.sign (((evalSign p x).toInt : Int) : ℝ) =
      SignType.sign ((toPolyℝ p).eval (Dyadic.toReal x)) := by
  rw [evalSign, Sign.ofInt_spec, ← toReal_evalDyadic]
  exact sign_dyadicSign _

/-- A polynomial whose executable degree is not positive is constant after
casting, including the zero polynomial. -/
theorem eval_eq_eval_zero_of_degree_nonpos (p : ZPoly)
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
  apply sign_eval_eq_of_noRoot (Cell.isPreconnected_open model cut)
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
  apply sign_eval_eq_of_noRoot (model.isPreconnected_leftSpan i) _
      (model.leftOpen_mem_leftSpan i hsample) (model.root_mem_leftSpan i)
  intro z hz hzroot
  exact hnonzero (by
    rw [← model.root_eq_of_mem_leftSpan i (hroot z hzroot) hz]
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
theorem evalSign_ne_zero_of_not_root (p : ZPoly) (x : Dyadic)
    (hroot : ¬(toPolyℝ p).IsRoot (Dyadic.toReal x)) :
    evalSign p x ≠ .zero := by
  intro hzero
  have hsign := evalSign_spec p x
  rw [hzero] at hsign
  have heval : (toPolyℝ p).eval (Dyadic.toReal x) = 0 := by
    apply sign_eq_zero_iff.mp
    simpa [Sign.toInt] using hsign.symm
  exact hroot heval

/-- Coefficient-equality membership test for literal polynomials. This avoids
the derived array equality that does not kernel-reduce through modules. -/
@[expose]
def containsPoly (p : ZPoly) : List ZPoly → Bool
  | [] => false
  | q :: qs => DensePoly.beqCoeffs p q || containsPoly p qs

theorem containsPoly_iff {p : ZPoly} {ps : List ZPoly} :
    containsPoly p ps = true ↔ p ∈ ps := by
  induction ps with
  | nil => simp [containsPoly]
  | cons q qs ih =>
      simp [containsPoly, Bool.or_eq_true, DensePoly.beqCoeffs_iff_eq, ih]

/-- The coefficient-equality membership test is false exactly on
nonmembership. -/
theorem containsPoly_eq_false_iff {p : ZPoly} {ps : List ZPoly} :
    containsPoly p ps = false ↔ p ∉ ps := by
  rw [Bool.eq_false_iff]
  exact not_congr containsPoly_iff

/-- First-occurrence-preserving duplicate removal with an explicit seen set. -/
@[expose]
def dedupPolysAux (seen : List ZPoly) : List ZPoly → List ZPoly
  | [] => []
  | p :: ps =>
      if containsPoly p seen then dedupPolysAux seen ps
      else p :: dedupPolysAux (p :: seen) ps

/-- Deterministic first-occurrence-preserving duplicate removal using only
coefficient equality. -/
@[expose]
def dedupPolys (ps : List ZPoly) : List ZPoly := dedupPolysAux [] ps

theorem mem_dedupPolysAux {p : ZPoly} {seen ps : List ZPoly} :
    p ∈ dedupPolysAux seen ps ↔ p ∈ ps ∧ p ∉ seen := by
  classical
  induction ps generalizing seen p with
  | nil => simp [dedupPolysAux]
  | cons q qs ih =>
      simp only [dedupPolysAux]
      split <;> rename_i hq
      · have hqmem : q ∈ seen := containsPoly_iff.mp hq
        simp only [ih, List.mem_cons]
        by_cases hpq : p = q
        · subst p
          simp [hqmem]
        · simp [hpq]
      · have hqmem : q ∉ seen :=
          containsPoly_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hq)
        simp only [List.mem_cons, ih]
        by_cases hpq : p = q
        · subst p
          simp [hqmem]
        · simp [hpq]

theorem mem_dedupPolys {p : ZPoly} {ps : List ZPoly} :
    p ∈ dedupPolys ps ↔ p ∈ ps := by
  simp [dedupPolys, mem_dedupPolysAux]

theorem dedupPolysAux_nodup (seen ps : List ZPoly) :
    (dedupPolysAux seen ps).Nodup := by
  induction ps generalizing seen with
  | nil => simp [dedupPolysAux]
  | cons p ps ih =>
      simp only [dedupPolysAux]
      split
      · exact ih seen
      · apply List.nodup_cons.mpr
        exact ⟨by simp [mem_dedupPolysAux], ih (p :: seen)⟩

theorem dedupPolys_nodup (ps : List ZPoly) : (dedupPolys ps).Nodup :=
  dedupPolysAux_nodup [] ps

/-- Pair a recomputed polynomial order with common-root packages and validate
every package. Length mismatches and malformed packages are rejected. -/
@[expose]
def checkCommon (carrier : ZPoly) :
    List ZPoly → List CommonRootCert → Bool
  | [], [] => true
  | p :: ps, common :: commons =>
      common.check p carrier && checkCommon carrier ps commons
  | _, _ => false

/-- Positional lookup in an aligned common-root package list. -/
@[expose]
def findCommon? (p : ZPoly) :
    List ZPoly → List CommonRootCert → Option CommonRootCert
  | q :: qs, common :: commons =>
      if DensePoly.beqCoeffs p q then some common
      else findCommon? p qs commons
  | _, _ => none

/-- Checked alignment makes positional lookup total and validates the package
against the requested external polynomial. -/
theorem findCommon?_of_check {carrier p : ZPoly} {ps : List ZPoly}
    {commons : List CommonRootCert} (hcheck : checkCommon carrier ps commons = true)
    (hmem : p ∈ ps) :
    ∃ common, findCommon? p ps commons = some common ∧
      common.check p carrier = true := by
  induction ps generalizing commons with
  | nil => simp at hmem
  | cons q qs ih =>
      cases commons with
      | nil => simp [checkCommon] at hcheck
      | cons common commons =>
          simp only [checkCommon, Bool.and_eq_true] at hcheck
          rcases hcheck with ⟨hhead, htail⟩
          by_cases hpq : p = q
          · subst q
            exact ⟨common, by simp [findCommon?, DensePoly.beqCoeffs_iff_eq], hhead⟩
          · have htailMem : p ∈ qs := by
              simpa [hpq] using hmem
            obtain ⟨found, hfind, hfound⟩ := ih htail htailMem
            refine ⟨found, ?_, hfound⟩
            simp [findCommon?, DensePoly.beqCoeffs_iff_eq, hpq, hfind]

/-- Common-root data carried by the sign-matrix layer.  No signs or formula
truth values are trusted fields: both are recomputed exactly. -/
structure SignMatrixCert where
  commonRoots : List CommonRootCert

/-- Exact sign on an open cell, rejecting the impossible zero result for a
nonconstant atom of a valid carrier decomposition. -/
@[expose]
def openSign? (p : ZPoly) (isolations : IsolationCert)
    (cut : Fin (isolations.intervals.size + 1)) : Option Sign :=
  match evalSign p (isolations.openPoint cut) with
  | .zero => none
  | sign => some sign

/-- Exact sign on a root cell from the cached common-root zero test, or from
the canonical left open sample when the atom does not vanish. -/
@[expose]
def rootSign? (p : ZPoly) (common : CommonRootCert)
    (isolations : IsolationCert) (i : Fin isolations.intervals.size) :
    Option Sign :=
  match common.hasRoot isolations.intervals[i] with
  | true => some .zero
  | false => openSign? p isolations i.castSucc

theorem openSign?_eq_some {p : ZPoly} {isolations : IsolationCert}
    {cut : Fin (isolations.intervals.size + 1)}
    (hnonzero : evalSign p (isolations.openPoint cut) ≠ .zero) :
    openSign? p isolations cut =
      some (evalSign p (isolations.openPoint cut)) := by
  cases hsign : evalSign p (isolations.openPoint cut) <;>
    simp_all [openSign?]

/-- Exact sign on an open cell, with constant polynomials evaluated once at
zero and nonconstant polynomials guarded against an impossible zero sample. -/
@[expose]
def openCellSign? (p : ZPoly) (isolations : IsolationCert)
    (cut : Fin (isolations.intervals.size + 1)) : Option Sign :=
  if 0 < p.degree?.getD 0 then openSign? p isolations cut
  else some (evalSign p 0)

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
      evalSign_ne_zero_of_not_root p _ hnotroot
    refine ⟨evalSign p (isolations.openPoint cut), ?_, ?_⟩
    · simp [openCellSign?, hdegree, openSign?_eq_some hnonzero]
    · exact evalSign_open_of_atom hcarrier hstrict hpmem cut hx
  · refine ⟨evalSign p 0, by simp [openCellSign?, hdegree], ?_⟩
    rw [eval_eq_eval_zero_of_degree_nonpos p hdegree x]
    simpa using evalSign_spec p 0

/-- One cached sign associated with its literal polynomial. -/
structure SignEntry where
  poly : ZPoly
  sign : Sign

/-- Coefficient-equality lookup in a cached sign row. -/
@[expose]
def findSign? (p : ZPoly) : List SignEntry → Option Sign
  | [] => none
  | entry :: entries =>
      if DensePoly.beqCoeffs p entry.poly then some entry.sign
      else findSign? p entries

/-- Materialize a sign row once for each polynomial in a recomputed distinct
order. Any missing sign fails the whole row. -/
@[expose]
def buildSigns? (signOf : ZPoly → Option Sign) :
    List ZPoly → Option (List SignEntry)
  | [] => some []
  | p :: ps => do
      let sign ← signOf p
      let entries ← buildSigns? signOf ps
      pure (⟨p, sign⟩ :: entries)

/-- A row built from an option-valued environment returns exactly that
environment on every polynomial included in the row order. -/
theorem findSign?_of_build {signOf : ZPoly → Option Sign} {ps : List ZPoly}
    {entries : List SignEntry} (hbuild : buildSigns? signOf ps = some entries)
    {p : ZPoly} (hmem : p ∈ ps) : findSign? p entries = signOf p := by
  induction ps generalizing entries with
  | nil => simp at hmem
  | cons q qs ih =>
      cases hq : signOf q with
      | none => simp [buildSigns?, hq] at hbuild
      | some sign =>
          cases hrest : buildSigns? signOf qs with
          | none => simp [buildSigns?, hq, hrest] at hbuild
          | some rest =>
              have hentries : entries = ⟨q, sign⟩ :: rest := by
                simpa [buildSigns?, hq, hrest] using hbuild.symm
              subst entries
              by_cases hpq : p = q
              · subst q
                simp [findSign?, DensePoly.beqCoeffs_iff_eq, hq]
              · have htail : p ∈ qs := by simpa [hpq] using hmem
                simp [findSign?, DensePoly.beqCoeffs_iff_eq, hpq,
                  ih hrest htail]

/-- A total option-valued environment builds a complete cached row. -/
theorem buildSigns?_total {signOf : ZPoly → Option Sign} {ps : List ZPoly}
    (htotal : ∀ p ∈ ps, ∃ sign, signOf p = some sign) :
    ∃ entries, buildSigns? signOf ps = some entries := by
  induction ps with
  | nil => exact ⟨[], rfl⟩
  | cons p ps ih =>
      obtain ⟨sign, hsign⟩ := htotal p (by simp)
      obtain ⟨entries, hentries⟩ := ih (by
        intro q hq
        exact htotal q (by simp [hq]))
      exact ⟨⟨p, sign⟩ :: entries, by simp [buildSigns?, hsign, hentries]⟩

namespace SignMatrixCert

/-- Recompute the distinct nonconstant atom order and validate exact package
alignment against the checked carrier. -/
@[expose]
def check (sentence : Sentence) (carrier : CarrierCert)
    (cert : SignMatrixCert) : Bool :=
  checkCommon carrier.carrier (dedupPolys sentence.polys) cert.commonRoots

/-- Look up the package associated with one nonconstant atom. -/
@[expose]
def findCommon? (sentence : Sentence) (cert : SignMatrixCert)
    (p : ZPoly) : Option CommonRootCert :=
  Hex.RCF.findCommon? p (dedupPolys sentence.polys) cert.commonRoots

/-- Every recomputed nonconstant atom has a checked package after successful
alignment. -/
theorem findCommon?_of_check {sentence : Sentence} {carrier : CarrierCert}
    {cert : SignMatrixCert} (hcheck : cert.check sentence carrier = true)
    {p : ZPoly} (hmem : p ∈ sentence.polys) :
    ∃ common, cert.findCommon? sentence p = some common ∧
      common.check p carrier.carrier = true := by
  apply Hex.RCF.findCommon?_of_check hcheck
  exact mem_dedupPolys.mpr hmem

/-- Recompute one atom sign on one carrier cell using a precomputed distinct
nonconstant order. Constants use evaluation at zero and consume no
common-root package. -/
@[expose]
def signWith? (cert : SignMatrixCert) (commonPolys : List ZPoly)
    (isolations : IsolationCert) (cell : Cell isolations.intervals.size)
    (p : ZPoly) : Option Sign :=
  match cell with
  | .open cut => openCellSign? p isolations cut
  | .root i =>
      if 0 < p.degree?.getD 0 then do
        let common ← Hex.RCF.findCommon? p commonPolys cert.commonRoots
        rootSign? p common isolations i
      else some (evalSign p 0)

/-- Public atom-sign lookup, recomputing the deterministic package order. -/
@[expose]
def sign? (cert : SignMatrixCert) (sentence : Sentence)
    (isolations : IsolationCert) (cell : Cell isolations.intervals.size)
    (p : ZPoly) : Option Sign :=
  cert.signWith? (dedupPolys sentence.polys) isolations cell p

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
            evalSign_ne_zero_of_not_root p _ hnotroot
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
        rw [eval_eq_eval_zero_of_degree_nonpos p hdegree x]
        simpa using evalSign_spec p 0
    | root i =>
        refine ⟨evalSign p 0, by simp [signWith?, hdegree], ?_⟩
        intro x _hx
        rw [eval_eq_eval_zero_of_degree_nonpos p hdegree x]
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

/-- Evaluate a comparison from the sign of its left-hand side. -/
@[expose]
def evalSign (cmp : Cmp) (sign : Sign) : Bool :=
  match cmp with
  | .lt => sign == .neg
  | .le => sign != .pos
  | .eq => sign == .zero
  | .ge => sign != .neg
  | .gt => sign == .pos
  | .ne => sign != .zero

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

/-- Bridge the reflected atom semantics to real-cast polynomial evaluation. -/
theorem Atom.toProp_iff_eval (a : Atom) (x : ℝ) :
    a.toProp x ↔ a.cmp.toProp ((toPolyℝ a.p).eval x) 0 := by
  unfold Atom.toProp
  rw [Polynomial.aeval_def, ← Polynomial.eval_map]
  rfl

namespace Formula

/-- Evaluate a formula from an option-valued polynomial-sign environment.
Every Boolean branch evaluates both children, so any missing sign fails closed.
-/
@[expose]
def evalSigns (signOf : ZPoly → Option Sign) : Formula → Option Bool
  | .atom a => do
      let sign ← signOf a.p
      pure (a.cmp.evalSign sign)
  | .tt => some true
  | .ff => some false
  | .not φ => do
      let value ← φ.evalSigns signOf
      pure (!value)
  | .and φ ψ => do
      let left ← φ.evalSigns signOf
      let right ← ψ.evalSigns signOf
      pure (left && right)
  | .or φ ψ => do
      let left ← φ.evalSigns signOf
      let right ← ψ.evalSigns signOf
      pure (left || right)
  | .imp φ ψ => do
      let left ← φ.evalSigns signOf
      let right ← ψ.evalSigns signOf
      pure (!left || right)

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

/-- Evaluate a formula whose atoms are all constant, without constructing a
carrier decomposition. -/
@[expose]
def evalConstants? (formula : Formula) : Option Bool :=
  formula.evalSigns fun p => some (Hex.RCF.evalSign p 0)

/-- Constant-only formula evaluation is exact at every real point, including
formulas containing the zero polynomial. -/
theorem evalConstants_eq_true_iff {formula : Formula}
    (hconstant : ∀ p ∈ formula.polys, ¬0 < p.degree?.getD 0) (x : ℝ) :
    formula.evalConstants? = some true ↔ formula.toProp x := by
  apply evalSigns_eq_true_iff
  intro p hp
  refine ⟨Hex.RCF.evalSign p 0, rfl, ?_⟩
  rw [eval_eq_eval_zero_of_degree_nonpos p (hconstant p hp) x]
  simpa using Hex.RCF.evalSign_spec p 0

end Formula

namespace SignMatrixCert

/-- Recompute the formula truth value on one carrier cell after materializing
one exact sign per distinct polynomial. Repeated atom occurrences reuse the
cached row entry. -/
@[expose]
def evalCell? (cert : SignMatrixCert) (sentence : Sentence)
    (isolations : IsolationCert) (cell : Cell isolations.intervals.size) :
    Option Bool := do
  let commonPolys := dedupPolys sentence.polys
  let entries ← buildSigns? (cert.signWith? commonPolys isolations cell)
    (dedupPolys sentence.formula.polys)
  sentence.formula.evalSigns (findSign? · entries)

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
