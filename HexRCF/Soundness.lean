/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Certificate
public import HexRCF.SignMatrix

public section

/-! Soundness of quantified RCF certificate replay. -/

namespace Hex.RCF

open HexRealRootsMathlib

namespace OptionFold

/-- A strict universal fold returns `none` exactly when an input evaluates to `none`. -/
theorem all_eq_none_iff {f : α → Option Bool} {xs : List α} :
    all f xs = none ↔ ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp [all]
  | cons x xs ih =>
      constructor
      · intro hnone
        cases hx : f x with
        | none => exact ⟨x, by simp, hx⟩
        | some head =>
            have htail : all f xs = none := by
              cases h : all f xs with
              | none => rfl
              | some tail => simp [all, hx, h] at hnone
            obtain ⟨y, hy, hfy⟩ := ih.mp htail
            exact ⟨y, by simp [hy], hfy⟩
      · rintro ⟨y, hy, hfy⟩
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · simp [all, hfy]
        · have htail := ih.mpr ⟨y, hy, hfy⟩
          cases hx : f x <;> simp [all, hx, htail]

/-- A strict existential fold returns `none` exactly when an input evaluates to `none`. -/
theorem any_eq_none_iff {f : α → Option Bool} {xs : List α} :
    any f xs = none ↔ ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp [any]
  | cons x xs ih =>
      constructor
      · intro hnone
        cases hx : f x with
        | none => exact ⟨x, by simp, hx⟩
        | some head =>
            have htail : any f xs = none := by
              cases h : any f xs with
              | none => rfl
              | some tail => simp [any, hx, h] at hnone
            obtain ⟨y, hy, hfy⟩ := ih.mp htail
            exact ⟨y, by simp [hy], hfy⟩
      · rintro ⟨y, hy, hfy⟩
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · simp [any, hfy]
        · have htail := ih.mpr ⟨y, hy, hfy⟩
          cases hx : f x <;> simp [any, hx, htail]

/-- A total strict universal fold is true exactly when every input is true. -/
theorem all_spec {f : α → Option Bool} {xs : List α}
    (htotal : ∀ x ∈ xs, ∃ value, f x = some value) :
    ∃ value, all f xs = some value ∧
      (value = true ↔ ∀ x ∈ xs, f x = some true) := by
  induction xs with
  | nil => exact ⟨true, by simp [all]⟩
  | cons x xs ih =>
      obtain ⟨head, hhead⟩ := htotal x (by simp)
      obtain ⟨tail, htail, htailSpec⟩ := ih (by
        intro y hy
        exact htotal y (by simp [hy]))
      refine ⟨head && tail, by simp [all, hhead, htail], ?_⟩
      cases head <;> cases tail <;> simp_all

/-- A total strict existential fold is true exactly when some input is true. -/
theorem any_spec {f : α → Option Bool} {xs : List α}
    (htotal : ∀ x ∈ xs, ∃ value, f x = some value) :
    ∃ value, any f xs = some value ∧
      (value = true ↔ ∃ x ∈ xs, f x = some true) := by
  induction xs with
  | nil => exact ⟨false, by simp [any]⟩
  | cons x xs ih =>
      obtain ⟨head, hhead⟩ := htotal x (by simp)
      obtain ⟨tail, htail, htailSpec⟩ := ih (by
        intro y hy
        exact htotal y (by simp [hy]))
      refine ⟨head || tail, by simp [any, hhead, htail], ?_⟩
      cases head <;> cases tail <;> simp_all

/-- A strict universal array fold returns `none` exactly when an entry evaluates to `none`. -/
theorem allArray_none {xs : Array α} {f : α → Option Bool} :
    allArray xs f = none ↔ ∃ x ∈ xs, f x = none := by
  simpa [allArray] using all_eq_none_iff (xs := xs.toList) (f := f)

/-- A strict existential array fold returns `none` exactly when an entry evaluates to `none`. -/
theorem anyArray_none {xs : Array α} {f : α → Option Bool} :
    anyArray xs f = none ↔ ∃ x ∈ xs, f x = none := by
  simpa [anyArray] using any_eq_none_iff (xs := xs.toList) (f := f)

/-- A filtered universal array fold returns `none` exactly at a relevant undefined entry. -/
theorem allWhereArray_none {xs : Array α}
    {relevant : α → Bool} {f : α → Option Bool} :
    allWhereArray xs relevant f = none ↔
      ∃ x ∈ xs, relevant x = true ∧ f x = none := by
  rw [allWhereArray, all_eq_none_iff]
  simp only [List.mem_filter]
  aesop

/-- A filtered existential array fold returns `none` exactly at a relevant undefined entry. -/
theorem anyWhereArray_none {xs : Array α}
    {relevant : α → Bool} {f : α → Option Bool} :
    anyWhereArray xs relevant f = none ↔
      ∃ x ∈ xs, relevant x = true ∧ f x = none := by
  rw [anyWhereArray, any_eq_none_iff]
  simp only [List.mem_filter]
  aesop

/-- A total strict universal array fold is true exactly when every entry is true. -/
theorem allArray_spec {xs : Array α} {f : α → Option Bool}
    (htotal : ∀ x ∈ xs, ∃ value, f x = some value) :
    ∃ value, allArray xs f = some value ∧
      (value = true ↔ ∀ x ∈ xs, f x = some true) := by
  simpa [allArray] using
    all_spec (xs := xs.toList) (f := f) (by
      intro x hx
      exact htotal x (by simpa using hx))

/-- A total strict existential array fold is true exactly when some entry is true. -/
theorem anyArray_spec {xs : Array α} {f : α → Option Bool}
    (htotal : ∀ x ∈ xs, ∃ value, f x = some value) :
    ∃ value, anyArray xs f = some value ∧
      (value = true ↔ ∃ x ∈ xs, f x = some true) := by
  simpa [anyArray] using
    any_spec (xs := xs.toList) (f := f) (by
      intro x hx
      exact htotal x (by simpa using hx))

/-- A total filtered universal fold is true exactly when every relevant entry is true. -/
theorem allWhereArray_spec {xs : Array α} {relevant : α → Bool}
    {f : α → Option Bool}
    (htotal : ∀ x ∈ xs, relevant x = true → ∃ value, f x = some value) :
    ∃ value, allWhereArray xs relevant f = some value ∧
      (value = true ↔
        ∀ x ∈ xs, relevant x = true → f x = some true) := by
  obtain ⟨value, hvalue, hspec⟩ := all_spec
    (xs := xs.toList.filter relevant) (f := f) (by
      intro x hx
      simp only [List.mem_filter] at hx
      exact htotal x (by simpa using hx.1) hx.2)
  refine ⟨value, by simpa [allWhereArray] using hvalue, ?_⟩
  rw [hspec]
  simp only [List.mem_filter]
  aesop

/-- A total filtered existential fold is true exactly when some relevant entry is true. -/
theorem anyWhereArray_spec {xs : Array α} {relevant : α → Bool}
    {f : α → Option Bool}
    (htotal : ∀ x ∈ xs, relevant x = true → ∃ value, f x = some value) :
    ∃ value, anyWhereArray xs relevant f = some value ∧
      (value = true ↔
        ∃ x ∈ xs, relevant x = true ∧ f x = some true) := by
  obtain ⟨value, hvalue, hspec⟩ := any_spec
    (xs := xs.toList.filter relevant) (f := f) (by
      intro x hx
      simp only [List.mem_filter] at hx
      exact htotal x (by simpa using hx.1) hx.2)
  refine ⟨value, by simpa [anyWhereArray] using hvalue, ?_⟩
  rw [hspec]
  simp only [List.mem_filter]
  aesop

end OptionFold

namespace CellFold

open OptionFold

/--
Universal folding over all cells is equivalent to universal quantification over the real line.
-/
theorem forall_spec {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (eval : Cell cert.intervals.size → Option Bool)
    (P : ℝ → Prop)
    (hcell : ∀ c, ∃ value, eval c = some value ∧
      ∀ x, Cell.Sem M c x → (value = true ↔ P x)) :
    ∃ value, allArray (Cell.all cert.intervals.size) eval = some value ∧
      (value = true ↔ ∀ x, P x) := by
  obtain ⟨value, hvalue, hfold⟩ := allArray_spec
    (xs := Cell.all cert.intervals.size) (f := eval) (by
      intro c _
      obtain ⟨v, hv, _⟩ := hcell c
      exact ⟨v, hv⟩)
  refine ⟨value, hvalue, ?_⟩
  constructor
  · intro hv x
    obtain ⟨c, hcx⟩ := Cell.exists_mem M x
    have heval := (hfold.mp hv) c (Cell.mem_all c)
    obtain ⟨v, hev, hsound⟩ := hcell c
    have hvtrue : v = true := by
      rw [hev] at heval
      exact Option.some.inj heval
    exact (hsound x hcx).mp hvtrue
  · intro hP
    apply hfold.mpr
    intro c _
    obtain ⟨v, hev, hsound⟩ := hcell c
    obtain ⟨x, hx⟩ := Cell.exists_point M c
    have hvtrue : v = true := (hsound x hx).mpr (hP x)
    simpa [hvtrue] using hev

/--
Existential folding over all cells is equivalent to existential quantification over the real line.
-/
theorem exists_spec {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (eval : Cell cert.intervals.size → Option Bool)
    (P : ℝ → Prop)
    (hcell : ∀ c, ∃ value, eval c = some value ∧
      ∀ x, Cell.Sem M c x → (value = true ↔ P x)) :
    ∃ value, anyArray (Cell.all cert.intervals.size) eval = some value ∧
      (value = true ↔ ∃ x, P x) := by
  obtain ⟨value, hvalue, hfold⟩ := anyArray_spec
    (xs := Cell.all cert.intervals.size) (f := eval) (by
      intro c _
      obtain ⟨v, hv, _⟩ := hcell c
      exact ⟨v, hv⟩)
  refine ⟨value, hvalue, ?_⟩
  constructor
  · intro hv
    obtain ⟨c, _, heval⟩ := hfold.mp hv
    obtain ⟨v, hev, hsound⟩ := hcell c
    obtain ⟨x, hx⟩ := Cell.exists_point M c
    have hvtrue : v = true := by
      rw [hev] at heval
      exact Option.some.inj heval
    exact ⟨x, (hsound x hx).mp hvtrue⟩
  · rintro ⟨x, hPx⟩
    obtain ⟨c, hcx⟩ := Cell.exists_mem M x
    apply hfold.mpr
    refine ⟨c, Cell.mem_all c, ?_⟩
    obtain ⟨v, hev, hsound⟩ := hcell c
    have hvtrue : v = true := (hsound x hcx).mpr hPx
    simpa [hvtrue] using hev

/--
Universal folding over relevant cells is equivalent to quantification over the specified domain.
-/
theorem forallWhere_spec {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (eval : Cell cert.intervals.size → Option Bool)
    (relevant : Cell cert.intervals.size → Bool) (D P : ℝ → Prop)
    (hcell : ∀ c, ∃ value, eval c = some value ∧
      ∀ x, Cell.Sem M c x → (value = true ↔ P x))
    (hrelevant : ∀ c, relevant c = true ↔
      ∃ x, Cell.Sem M c x ∧ D x) :
    ∃ value,
      allWhereArray (Cell.all cert.intervals.size) relevant eval = some value ∧
      (value = true ↔ ∀ x, D x → P x) := by
  obtain ⟨value, hvalue, hfold⟩ := allWhereArray_spec
    (xs := Cell.all cert.intervals.size) (f := eval) (relevant := relevant) (by
      intro c _ _
      obtain ⟨v, hv, _⟩ := hcell c
      exact ⟨v, hv⟩)
  refine ⟨value, hvalue, ?_⟩
  constructor
  · intro hv x hDx
    obtain ⟨c, hcx⟩ := Cell.exists_mem M x
    have hrel : relevant c = true := (hrelevant c).mpr ⟨x, hcx, hDx⟩
    have heval := (hfold.mp hv) c (Cell.mem_all c) hrel
    obtain ⟨v, hev, hsound⟩ := hcell c
    have hvtrue : v = true := by
      rw [hev] at heval
      exact Option.some.inj heval
    exact (hsound x hcx).mp hvtrue
  · intro hP
    apply hfold.mpr
    intro c _ hrel
    obtain ⟨x, hcx, hDx⟩ := (hrelevant c).mp hrel
    obtain ⟨v, hev, hsound⟩ := hcell c
    have hvtrue : v = true := (hsound x hcx).mpr (hP x hDx)
    simpa [hvtrue] using hev

/--
Existential folding over relevant cells is equivalent to quantification over the specified domain.
-/
theorem existsWhere_spec {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (eval : Cell cert.intervals.size → Option Bool)
    (relevant : Cell cert.intervals.size → Bool) (D P : ℝ → Prop)
    (hcell : ∀ c, ∃ value, eval c = some value ∧
      ∀ x, Cell.Sem M c x → (value = true ↔ P x))
    (hrelevant : ∀ c, relevant c = true ↔
      ∃ x, Cell.Sem M c x ∧ D x) :
    ∃ value,
      anyWhereArray (Cell.all cert.intervals.size) relevant eval = some value ∧
      (value = true ↔ ∃ x, D x ∧ P x) := by
  obtain ⟨value, hvalue, hfold⟩ := anyWhereArray_spec
    (xs := Cell.all cert.intervals.size) (f := eval) (relevant := relevant) (by
      intro c _ _
      obtain ⟨v, hv, _⟩ := hcell c
      exact ⟨v, hv⟩)
  refine ⟨value, hvalue, ?_⟩
  constructor
  · intro hv
    obtain ⟨c, _, hrel, heval⟩ := hfold.mp hv
    obtain ⟨x, hcx, hDx⟩ := (hrelevant c).mp hrel
    obtain ⟨v, hev, hsound⟩ := hcell c
    have hvtrue : v = true := by
      rw [hev] at heval
      exact Option.some.inj heval
    exact ⟨x, hDx, (hsound x hcx).mp hvtrue⟩
  · rintro ⟨x, hDx, hPx⟩
    obtain ⟨c, hcx⟩ := Cell.exists_mem M x
    apply hfold.mpr
    refine ⟨c, Cell.mem_all c, (hrelevant c).mpr ⟨x, hcx, hDx⟩, ?_⟩
    obtain ⟨v, hev, hsound⟩ := hcell c
    have hvtrue : v = true := (hsound x hcx).mpr hPx
    simpa [hvtrue] using hev

/-- Universal folding over cells that meet `(a, b]` computes the bounded universal proposition. -/
theorem forallIoc_spec {carrier : ZPoly} {replay : SturmReplay}
    (hreplay : replay.check carrier = true) {cert : IsolationCert}
    (hstrict : cert.checkStrict replay = true)
    (a b : Dyadic) (cmps : IocCmps cert.intervals.size)
    (hcmps : IocCmps.check carrier replay cert a b cmps = true)
    (eval : Cell cert.intervals.size → Option Bool) (P : ℝ → Prop)
    (hcell : ∀ c, ∃ value, eval c = some value ∧
      ∀ x, Cell.Sem (cert.rootModel hreplay hstrict) c x →
        (value = true ↔ P x)) :
    ∃ value,
      allWhereArray (Cell.all cert.intervals.size)
        (Cell.meetsIocOn a b cmps) eval = some value ∧
      (value = true ↔ ∀ x, x ∈ Set.Ioc (Dyadic.toReal a) (Dyadic.toReal b) → P x) := by
  apply forallWhere_spec (cert.rootModel hreplay hstrict) eval
    (Cell.meetsIocOn a b cmps)
    (fun x => x ∈ Set.Ioc (Dyadic.toReal a) (Dyadic.toReal b)) P hcell
  exact fun c => Cell.meetsIocOn_iff_of_check cmps a b hreplay hstrict hcmps c

/--
Existential folding over cells that meet `(a, b]` computes the bounded existential proposition.
-/
theorem existsIoc_spec {carrier : ZPoly} {replay : SturmReplay}
    (hreplay : replay.check carrier = true) {cert : IsolationCert}
    (hstrict : cert.checkStrict replay = true)
    (a b : Dyadic) (cmps : IocCmps cert.intervals.size)
    (hcmps : IocCmps.check carrier replay cert a b cmps = true)
    (eval : Cell cert.intervals.size → Option Bool) (P : ℝ → Prop)
    (hcell : ∀ c, ∃ value, eval c = some value ∧
      ∀ x, Cell.Sem (cert.rootModel hreplay hstrict) c x →
        (value = true ↔ P x)) :
    ∃ value,
      anyWhereArray (Cell.all cert.intervals.size)
        (Cell.meetsIocOn a b cmps) eval = some value ∧
      (value = true ↔ ∃ x, x ∈ Set.Ioc (Dyadic.toReal a) (Dyadic.toReal b) ∧ P x) := by
  apply existsWhere_spec (cert.rootModel hreplay hstrict) eval
    (Cell.meetsIocOn a b cmps)
    (fun x => x ∈ Set.Ioc (Dyadic.toReal a) (Dyadic.toReal b)) P hcell
  exact fun c => Cell.meetsIocOn_iff_of_check cmps a b hreplay hstrict hcmps c

end CellFold

/-- An accepted certificate has three-valued replay result `some true`. -/
theorem Certificate.replay_true {s : Sentence}
    {cert : Certificate} (h : cert.check s = true) :
    cert.replay? s = some true := by
  simpa [Certificate.check] using h

/-- Constant-only sentence replay is exact at every real point. -/
theorem Sentence.evalConstants_of_empty {s : Sentence}
    (hempty : s.polys.isEmpty = true) (x : ℝ) :
    s.formula.evalConstants? = some true ↔ s.formula.toProp x := by
  apply Formula.evalConstants_eq_true_iff
  intro p hp hdegree
  have hmem : p ∈ s.polys := by
    simp only [Sentence.polys, List.mem_filter, decide_eq_true_eq]
    exact ⟨hp, hdegree⟩
  cases hpolys : s.polys with
  | nil => simp [hpolys] at hmem
  | cons q qs => simp [hpolys] at hempty

/-- The empty bounded-domain branch is sound independently of its body. -/
theorem Certificate.emptyIoc_sound {s : Sentence}
    (h : Certificate.emptyIoc.replay? s = some true) : s.toProp := by
  cases s with
  | forallReal formula => simp [Certificate.replay?] at h
  | existsReal formula => simp [Certificate.replay?] at h
  | forallIoc a b formula =>
      simp only [Certificate.replay?] at h
      split at h
      · simp at h
      · rename_i hab
        intro x hx
        have hreal : ¬Dyadic.toReal a < Dyadic.toReal b := by
          simpa [toReal_lt_toReal_iff] using hab
        exact (hreal (lt_of_lt_of_le hx.1 hx.2)).elim
  | existsIoc a b formula =>
      simp only [Certificate.replay?] at h
      split at h <;> simp_all

/-- A successfully replayed constants-only branch proves the sentence. -/
theorem Certificate.constants_sound {s : Sentence}
    (h : Certificate.constants.replay? s = some true) : s.toProp := by
  cases s with
  | forallReal formula =>
      simp only [Certificate.replay?, Sentence.replayConstants?] at h
      split at h
      · rename_i hempty
        intro x
        exact (Sentence.evalConstants_of_empty hempty x).mp h
      · simp at h
  | existsReal formula =>
      simp only [Certificate.replay?, Sentence.replayConstants?] at h
      split at h
      · rename_i hempty
        exact ⟨0, (Sentence.evalConstants_of_empty hempty 0).mp h⟩
      · simp at h
  | forallIoc a b formula =>
      simp only [Certificate.replay?, Sentence.replayConstants?] at h
      split at h
      · rename_i hempty
        split at h
        · intro x _
          exact (Sentence.evalConstants_of_empty hempty x).mp h
        · simp at h
      · simp at h
  | existsIoc a b formula =>
      simp only [Certificate.replay?, Sentence.replayConstants?] at h
      split at h
      · rename_i hempty
        split at h
        · rename_i hab
          obtain ⟨x, hax, hxb⟩ := exists_between (toReal_lt_toReal hab)
          exact ⟨x, ⟨hax, hxb.le⟩,
            (Sentence.evalConstants_of_empty hempty x).mp h⟩
        · simp at h
      · simp at h

/-- The matrix-free open-cell evaluator is exact under the carrier and strict
isolation checks. -/
theorem Sentence.evalOpen_eq_true_iff {s : Sentence} {carrier : CarrierCert}
    (hcarrier : carrier.check s = true) {isolations : IsolationCert}
    (hstrict : isolations.checkStrict carrier.replay = true)
    (cut : Fin (isolations.intervals.size + 1)) {x : ℝ}
    (hx : Cell.Sem
      (isolations.rootModel (CarrierCert.replay_of_check hcarrier) hstrict)
      (.open cut) x) :
    s.evalOpen? isolations cut = some true ↔ s.formula.toProp x := by
  unfold Sentence.evalOpen?
  apply Formula.evalSigns_eq_true_iff
  intro p hp
  exact openCellSign_spec hcarrier hstrict hp cut hx

/-- A checked empty isolation set gives the single-cell decomposition. -/
theorem Certificate.noRoots_sound {s : Sentence} {data : DecompCert}
    (h : (Certificate.noRoots data).replay? s = some true) : s.toProp := by
  simp only [Certificate.replay?, Sentence.replayNoRoots?] at h
  split at h
  · rename_i hvalid
    simp only [Bool.and_eq_true] at hvalid
    obtain ⟨⟨hcarrier, hstrict⟩, hempty⟩ := hvalid
    have hsize : data.isolations.intervals.size = 0 := by
      simpa [Array.isEmpty] using hempty
    let cut : Fin (data.isolations.intervals.size + 1) :=
      Fin.last data.isolations.intervals.size
    have formulaAt (x : ℝ)
        (hvalue : s.evalOpen? data.isolations cut = some true) :
        s.formula.toProp x := by
      have hx : Cell.Sem
          (data.isolations.rootModel
            (CarrierCert.replay_of_check hcarrier) hstrict)
          (.open cut) x := by
        simp [Cell.Sem, hsize]
      exact (Sentence.evalOpen_eq_true_iff hcarrier hstrict cut hx).mp hvalue
    cases s with
    | forallReal formula =>
        intro x
        exact formulaAt x h
    | existsReal formula =>
        exact ⟨0, formulaAt 0 h⟩
    | forallIoc a b formula =>
        change (if a < b then
          Sentence.evalOpen? (.forallIoc a b formula) data.isolations
            (Fin.last data.isolations.intervals.size)
          else none) = some true at h
        split at h
        · intro x _
          exact formulaAt x h
        · simp at h
    | existsIoc a b formula =>
        change (if a < b then
          Sentence.evalOpen? (.existsIoc a b formula) data.isolations
            (Fin.last data.isolations.intervals.size)
          else none) = some true at h
        split at h
        · rename_i hab
          obtain ⟨x, hax, hxb⟩ := exists_between (toReal_lt_toReal hab)
          exact ⟨x, ⟨hax, hxb.le⟩, formulaAt x h⟩
        · simp at h
  · simp at h

/-- A checked positive-root decomposition proves the quantified sentence. -/
theorem Certificate.cells_sound {s : Sentence} {data : CellsCert}
    (h : (Certificate.cells data).replay? s = some true) : s.toProp := by
  simp only [Certificate.replay?, Sentence.replayCells?] at h
  split at h
  · rename_i hvalid
    simp only [Bool.and_eq_true] at hvalid
    obtain ⟨⟨⟨hcarrier, hstrict⟩, _hpositive⟩, hmatrix⟩ := hvalid
    cases s with
    | forallReal formula =>
        cases hopt : data.iocCmps with
        | none =>
            simp only [hopt] at h
            change OptionFold.allArray (Cell.all data.isolations.intervals.size)
              (data.signs.evalCell? (.forallReal formula) data.isolations) =
              some true at h
            obtain ⟨value, hvalue, hspec⟩ := CellFold.forall_spec
              (data.isolations.rootModel
                (CarrierCert.replay_of_check hcarrier) hstrict)
              (data.signs.evalCell? (.forallReal formula) data.isolations)
              formula.toProp
              (fun c => data.signs.evalCell_spec hcarrier hstrict hmatrix c)
            have htrue : value = true := by
              rw [hvalue] at h
              exact Option.some.inj h
            exact hspec.mp htrue
        | some cmps => simp [hopt] at h
    | existsReal formula =>
        cases hopt : data.iocCmps with
        | none =>
            simp only [hopt] at h
            change OptionFold.anyArray (Cell.all data.isolations.intervals.size)
              (data.signs.evalCell? (.existsReal formula) data.isolations) =
              some true at h
            obtain ⟨value, hvalue, hspec⟩ := CellFold.exists_spec
              (data.isolations.rootModel
                (CarrierCert.replay_of_check hcarrier) hstrict)
              (data.signs.evalCell? (.existsReal formula) data.isolations)
              formula.toProp
              (fun c => data.signs.evalCell_spec hcarrier hstrict hmatrix c)
            have htrue : value = true := by
              rw [hvalue] at h
              exact Option.some.inj h
            exact hspec.mp htrue
        | some cmps => simp [hopt] at h
    | forallIoc a b formula =>
        cases hopt : data.iocCmps with
        | none => simp [hopt] at h
        | some cmps =>
            simp only [hopt] at h
            change (if a < b &&
                cmps.check data.carrier.carrier data.carrier.replay
                  data.isolations a b then
              OptionFold.allWhereArray
                (Cell.all data.isolations.intervals.size)
                (Cell.meetsIocOn a b cmps)
                (data.signs.evalCell? (.forallIoc a b formula) data.isolations)
              else none) = some true at h
            split at h
            · rename_i hguard
              simp only [Bool.and_eq_true] at hguard
              obtain ⟨_hab, hcmps⟩ := hguard
              obtain ⟨value, hvalue, hspec⟩ := CellFold.forallIoc_spec
                (CarrierCert.replay_of_check hcarrier) hstrict a b cmps hcmps
                (data.signs.evalCell? (.forallIoc a b formula) data.isolations)
                formula.toProp
                (fun c => data.signs.evalCell_spec hcarrier hstrict hmatrix c)
              have htrue : value = true := by
                rw [hvalue] at h
                exact Option.some.inj h
              exact hspec.mp htrue
            · simp at h
    | existsIoc a b formula =>
        cases hopt : data.iocCmps with
        | none => simp [hopt] at h
        | some cmps =>
            simp only [hopt] at h
            change (if a < b &&
                cmps.check data.carrier.carrier data.carrier.replay
                  data.isolations a b then
              OptionFold.anyWhereArray
                (Cell.all data.isolations.intervals.size)
                (Cell.meetsIocOn a b cmps)
                (data.signs.evalCell? (.existsIoc a b formula) data.isolations)
              else none) = some true at h
            split at h
            · rename_i hguard
              simp only [Bool.and_eq_true] at hguard
              obtain ⟨_hab, hcmps⟩ := hguard
              obtain ⟨value, hvalue, hspec⟩ := CellFold.existsIoc_spec
                (CarrierCert.replay_of_check hcarrier) hstrict a b cmps hcmps
                (data.signs.evalCell? (.existsIoc a b formula) data.isolations)
                formula.toProp
                (fun c => data.signs.evalCell_spec hcarrier hstrict hmatrix c)
              have htrue : value = true := by
                rw [hvalue] at h
                exact Option.some.inj h
              exact hspec.mp htrue
            · simp at h
  · simp at h

/-- The public Boolean certificate checker is sound. -/
theorem check_sound (s : Sentence) (cert : Certificate) :
    cert.check s = true → s.toProp := by
  intro h
  have hreplay := Certificate.replay_true h
  cases cert with
  | emptyIoc => exact Certificate.emptyIoc_sound hreplay
  | constants => exact Certificate.constants_sound hreplay
  | noRoots data => exact Certificate.noRoots_sound hreplay
  | cells data => exact Certificate.cells_sound hreplay

end Hex.RCF
