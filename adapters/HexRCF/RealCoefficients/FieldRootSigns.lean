/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealFormula
public import HexRCF.RealCoefficients.IsolationCheck

public section

/-! Finite literal root-sign queries for the atoms of one source formula. -/

namespace Hex.RCF.RealCoefficients.FieldRootSigns

open Hex Hex.RealFormula

structure Entry (E : Type u) (Ctx : Type v) (n roots : Nat)
    [Zero E] [DecidableEq E] where
  atom : RealFormula.Poly n
  evidence : Vector (TarskiCertificate E E Ctx) roots

structure Table (E : Type u) (Ctx : Type v) (n roots : Nat)
    [Zero E] [DecidableEq E] where
  entries : List (Entry E Ctx n roots)

namespace Table

variable {E : Type u} {Ctx : Type v} {n roots : Nat}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
variable [NatCast E] [DecidableEq Ctx]

@[expose] def sameAtom (atom : RealFormula.Poly n) (row : Entry E Ctx n roots) : Bool :=
  if row.atom = atom then true else false

/-- An unlisted atom receives the caller's fallback certificate. The checker
rejects this case for every atom used in the formula. -/
@[expose] def evidence (table : Table E Ctx n roots)
    (fallback : TarskiCertificate E E Ctx) (i : Fin roots)
    (atom : RealFormula.Poly n) : TarskiCertificate E E Ctx :=
  ((table.entries.find? (sameAtom atom)).map
    (fun row => row.evidence[i])).getD fallback

@[expose] def value (table : Table E Ctx n roots)
    (fallback : TarskiCertificate E E Ctx) (i : Fin roots)
    (atom : RealFormula.Poly n) : Int :=
  (table.evidence fallback i atom).value

/-- Traverse the actual formula atoms and every root. Missing rows reject
before the supplied query validator is called. -/
@[expose] def checkWith (table : Table E Ctx n roots) (formula : QF n)
    (accept : RealFormula.Poly n → Fin roots → TarskiCertificate E E Ctx → Bool) : Bool :=
  formula.polys.all fun atom =>
    match table.entries.find? (sameAtom atom) with
    | none => false
    | some row => (List.finRange roots).all fun i => accept atom i row.evidence[i]

omit [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx] in
/-- Acceptance supplies a checked query for each actual atom at each root.
The fallback cannot be used to accept an absent row. -/
theorem query_checkedWith (table : Table E Ctx n roots) (formula : QF n)
    (accept : RealFormula.Poly n → Fin roots → TarskiCertificate E E Ctx → Bool)
    (h : table.checkWith formula accept = true)
    (i : Fin roots) (atom : RealFormula.Poly n) (ha : atom ∈ formula.polys)
    (fallback : TarskiCertificate E E Ctx) :
    accept atom i (table.evidence fallback i atom) = true := by
  have hrow := List.all_eq_true.mp h atom ha
  cases hfind : table.entries.find? (sameAtom atom) with
  | none => simp [hfind] at hrow
  | some row =>
      simp only [hfind] at hrow
      have hi := List.all_eq_true.mp hrow i (List.mem_finRange i)
      simpa only [evidence, hfind, Option.map_some, Option.getD_some] using hi

/-- Bind the complete ordered row inventory and validate every retained row,
including repeated atoms. Unused or corrupt duplicate rows cannot hide behind
a previous matching row. -/
@[expose] def checkRows {E : Type u} {Ctx : Type v} {n roots : Nat}
    [Zero E] [DecidableEq E] (table : Table E Ctx n roots) (formula : QF n)
    (accept : RealFormula.Poly n → Fin roots → TarskiCertificate E E Ctx → Bool) : Bool :=
  Decidable.decide (table.entries.map (fun row => row.atom) = formula.polys) &&
    table.entries.all fun row => (List.finRange roots).all fun i => accept row.atom i row.evidence[i]

/-- Complete checked rows supply the existing source-atom lookup interface. -/
theorem checkRows_checked {E : Type u} {Ctx : Type v} {n roots : Nat}
    [Zero E] [DecidableEq E] (table : Table E Ctx n roots) (formula : QF n)
    (accept : RealFormula.Poly n → Fin roots → TarskiCertificate E E Ctx → Bool)
    (accepted : table.checkRows formula accept = true) : table.checkWith formula accept = true := by
  simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at accepted
  unfold checkWith
  apply List.all_eq_true.mpr
  intro atom member
  cases found : table.entries.find? (sameAtom atom) with
  | none =>
      have listed : atom ∈ table.entries.map (fun row => row.atom) := by
        rw [accepted.1]
        exact member
      obtain ⟨row, rowMember, equality⟩ := List.mem_map.mp listed
      have absent := List.find?_eq_none.mp found row rowMember
      simp [sameAtom, equality] at absent
  | some row =>
      have matched : row.atom = atom := by
        simpa [sameAtom] using List.find?_some found
      simpa only [matched] using
        List.all_eq_true.mp accepted.2 row (List.mem_of_find?_eq_some found)

/-- Check every actual atom on every isolated root against its own original
polynomial and exact dyadic interval. Missing rows fail closed. -/
@[expose] def check (table : Table E Ctx n roots) (sign : E → Int)
    (point : Dyadic → E) (context : Ctx) (head : DensePoly E)
    (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n) : Bool :=
  table.checkWith formula fun atom i cert =>
    let interval := intervals[i]
    Sturm.check sign context head (query atom)
      (.finite (point interval.lower)) (.finite (point interval.upper)) cert.value cert

/-- A successful full check supplies the exact query required for any source
atom at any root; copied rows still fail the shared binding checker. -/
theorem query_checked (table : Table E Ctx n roots) (sign : E → Int)
    (point : Dyadic → E) (context : Ctx) (head : DensePoly E)
    (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (h : table.check sign point context head intervals query formula = true)
    (i : Fin roots) (atom : RealFormula.Poly n) (ha : atom ∈ formula.polys)
    (fallback : TarskiCertificate E E Ctx) :
    Sturm.check sign context head (query atom)
      (.finite (point intervals[i].lower)) (.finite (point intervals[i].upper))
      (table.value fallback i atom) (table.evidence fallback i atom) = true :=
  table.query_checkedWith formula _ h i atom ha fallback

/-- Produce every atom row using an explicit signed-remainder normalizer.
Each atom's remainder chain is shared across its root intervals. No coefficient
inverse or field instance is needed. The complete retained inventory is checked. -/
@[expose] def buildWith [Neg E] (sign : E → Int) (point : Dyadic → E)
    (normalize : DensePoly E → E × DensePoly E)
    (context : Ctx) (head : DensePoly E)
    (cert : IsolationReplay E Ctx) (query : RealFormula.Poly n → DensePoly E)
    (formula : QF n) : Option (Table E Ctx n cert.isolations.intervals.size) :=
  let entries := formula.polys.map fun atom =>
    let q := query atom
    let remainders := SignedRemainderChain.build sign normalize head q
    (⟨atom, Vector.ofFn fun i =>
      let interval := cert.isolations.intervals[i]
      TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) context head q
        (.finite (point interval.lower)) (.finite (point interval.upper))
        cert.total.squarefree remainders⟩ : Entry E Ctx n cert.isolations.intervals.size)
  let table : Table E Ctx n cert.isolations.intervals.size := ⟨entries⟩
  if table.checkRows formula (fun atom i evidence =>
      let interval := cert.isolations.intervals[i]
      Sturm.check sign context head (query atom)
        (.finite (point interval.lower)) (.finite (point interval.upper)) evidence.value evidence) then
    some table
  else none

/-- Produce one literal query per formula atom and root cell. Successful
construction returns only a table accepted by the same checker used in replay. -/
@[expose] def build [Neg E] [Inv E] (sign : E → Int) (point : Dyadic → E)
    (context : Ctx) (head : DensePoly E)
    (cert : IsolationReplay E Ctx) (query : RealFormula.Poly n → DensePoly E)
    (formula : QF n) :
    Option (Table E Ctx n cert.isolations.intervals.size) :=
  let entries := formula.polys.map fun atom =>
    (⟨atom, Vector.ofFn fun i =>
      cert.queryAt sign point context head (query atom) i⟩ :
      Entry E Ctx n cert.isolations.intervals.size)
  let table : Table E Ctx n cert.isolations.intervals.size := ⟨entries⟩
  if table.check sign point context head cert.isolations.intervals.toVector query formula then
    some table
  else none

theorem build_checked [Neg E] [Inv E] (sign : E → Int) (point : Dyadic → E)
    (context : Ctx) (head : DensePoly E)
    (cert : IsolationReplay E Ctx) (query : RealFormula.Poly n → DensePoly E)
    (formula : QF n) (table : Table E Ctx n cert.isolations.intervals.size)
    (h : build sign point context head cert query formula = some table) :
    table.check sign point context head cert.isolations.intervals.toVector query formula = true := by
  unfold build at h
  dsimp only at h
  split at h
  · next hc =>
      cases Option.some.inj h
      exact hc
  · simp at h

end Table

end Hex.RCF.RealCoefficients.FieldRootSigns
