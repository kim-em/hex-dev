/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import Init.Data.List.Lemmas
public import HexRCF.CarrierCheck
public import HexRCF.CellsCheck
public import HexRCF.CommonRootCheck

public section

/-!
# Executable sign-matrix replay

This module computes exact polynomial signs from dyadic samples and checked
common-root packages, caches one sign per distinct polynomial, and evaluates
reflected formulas on carrier cells. It contains only exact data and Boolean
or option-valued replay. The interpretation over real roots and semantic cells
lives in `HexRCF.SignMatrix`.
-/

namespace Hex.RCF

/-- The three possible signs stored by an RCF sign matrix. -/
inductive Sign where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

namespace Sign

/-- Canonical integer representative of a stored sign. -/
@[expose]
def toInt : Sign → Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- Collapse an arbitrary integer to its three-way sign. -/
@[expose]
def ofInt (value : Int) : Sign :=
  if value < 0 then .neg else if 0 < value then .pos else .zero

end Sign

/-- Exact executable sign of an integer polynomial at a dyadic point. -/
@[expose]
def evalSign (p : ZPoly) (x : Dyadic) : Sign :=
  Sign.ofInt (Hex.dyadicSign (p.evalDyadic x))

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
      · have hqmem : q ∉ seen := by
          apply containsPoly_eq_false_iff.mp
          cases h : containsPoly q seen <;> simp_all
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

/-- Common-root data carried by the sign-matrix layer. No signs or formula
truth values are trusted fields: both are recomputed exactly. -/
structure SignMatrixCert where
  commonRoots : List CommonRootCert

/-- Exact sign on an open cell, rejecting zero for a nonconstant atom of a
valid carrier decomposition. -/
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
nonconstant order. Constants use evaluation at zero and consume no common-root
package. -/
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

end Cmp

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

/-- Evaluate a formula whose atoms are all constant, without constructing a
carrier decomposition. -/
@[expose]
def evalConstants? (formula : Formula) : Option Bool :=
  formula.evalSigns fun p => some (Hex.RCF.evalSign p 0)

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

end SignMatrixCert

end Hex.RCF
