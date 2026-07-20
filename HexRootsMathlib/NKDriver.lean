/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.IsolateAll
public import HexRootsMathlib.NKCertify

public section

/-!
# End-to-end soundness of NK-only isolation

This module connects the semantic `.nk` loop kernel to `isolateAll?` and the
initial Cauchy component.  It proves coverage, unique indexed assignment, and
the unique simple-root contract for every emitted atom.
-/

namespace HexRootsMathlib

noncomputable section

/-- An option-valued list map that succeeds preserves length and maps
corresponding entries. -/
private theorem list_mapM_some_get {α β : Type*} {f : α → Option β}
    {xs : List α} {ys : List β} (hmap : xs.mapM f = some ys) :
    xs.length = ys.length ∧
      ∀ (i : Nat) (hi : i < xs.length) (hj : i < ys.length),
        f xs[i] = some ys[i] := by
  induction xs generalizing ys with
  | nil =>
      simp at hmap
      subst ys
      simp
  | cons x xs ih =>
      cases hfx : f x with
      | none => simp [hfx] at hmap
      | some y =>
          cases htail : xs.mapM f with
          | none => simp [hfx, htail] at hmap
          | some ys' =>
              have heq : some (y :: ys') = some ys := by
                simpa [hfx, htail] using hmap
              have hys : ys = y :: ys' := by
                exact (Option.some.inj heq).symm
              subst ys
              obtain ⟨hlen, hget⟩ := ih htail
              constructor
              · simp [hlen]
              · intro i hi hj
                cases i with
                | zero => simpa using hfx
                | succ i =>
                    simp only [List.getElem_cons_succ]
                    exact hget i (by simpa using hi) (by simpa using hj)

/-- An option-valued array map that succeeds preserves size and maps
corresponding entries. -/
private theorem array_mapM_some_get {α β : Type*} {f : α → Option β}
    {xs : Array α} {ys : Array β} (hmap : xs.mapM f = some ys) :
    xs.size = ys.size ∧
      ∀ (i : Nat) (hi : i < xs.size) (hj : i < ys.size),
        f xs[i] = some ys[i] := by
  have hlist : xs.toList.mapM f = some ys.toList := by
    calc
      xs.toList.mapM f = Array.toList <$> xs.mapM f :=
        Array.toList_mapM.symm
      _ = some ys.toList := by rw [hmap]; rfl
  obtain ⟨hlen, hget⟩ := list_mapM_some_get hlist
  constructor
  · simpa using hlen
  · intro i hi hj
    simpa only [← Array.getElem_toList] using hget i (by simpa using hi)
      (by simpa using hj)

/-- Every successful NK-only loop result is an NK atom. -/
theorem isolateLoop_nk_atoms {p : Hex.ZPoly} {target : Int} {fuel : Nat}
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hloop : Hex.isolateLoop p target .nk fuel work = some rs) :
    ∀ r ∈ rs.toList, ∃ iso : Hex.DyadicRootIsolation p,
      r = .atom iso ∧ Hex.nkWitness p iso.square := by
  induction fuel generalizing work rs with
  | zero => simp [Hex.isolateLoop] at hloop
  | succ fuel ih =>
      rw [Hex.isolateLoop] at hloop
      split at hloop
      · have hrs : rs = #[] := Option.some.inj hloop.symm
        subst rs
        simp
      · let tried := Hex.IsolationLoop.attempts p .nk work
        change (if (Hex.IsolationLoop.normalized p target tried ||
              Hex.IsolationLoop.allAtoms tried) &&
            (Hex.IsolationLoop.allReady target tried &&
              Hex.IsolationLoop.disjoint tried) then
          some (Hex.IsolationLoop.outputs tried)
        else Hex.isolateLoop p target .nk fuel
          (Hex.IsolationLoop.next p target tried)) = some rs at hloop
        split at hloop
        · have hrs : rs = Hex.IsolationLoop.outputs tried :=
            Option.some.inj hloop.symm
          subst rs
          intro r hr
          have hr' := Array.mem_toList_iff.mp hr
          obtain ⟨t, ht, htr⟩ := Array.mem_filterMap.mp hr'
          rcases t with ⟨c, o⟩
          cases o with
          | none => simp at htr
          | some r' =>
              simp only at htr
              cases Option.some.inj htr
              change (c, some r) ∈
                (Hex.IsolationLoop.attempts p .nk work) at ht
              rw [Hex.IsolationLoop.attempts] at ht
              obtain ⟨d, hd, hdc⟩ := Array.mem_map.mp ht
              have hcert : Hex.Component.certify? p .nk d = some r := by
                exact congrArg Prod.snd hdc
              obtain ⟨iso, hir, hnk, -⟩ := certify_nk_unique hcert
              exact ⟨iso, hir, hnk⟩
        · exact ih hloop

/-- `isolateAll?` is the shared loop with its executable fuel calculation. -/
private theorem isolateAll_nk_loop {p : Hex.ZPoly} {target : Int}
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work .nk = some rs) :
    ∃ fuel, Hex.isolateLoop p target .nk fuel work = some rs := by
  refine ⟨Hex.fuelFor p target
    (work.foldl (fun m c => min m c.prec)
      ((work[0]?.map (·.prec)).getD 0)), ?_⟩
  simpa [Hex.isolateAll?] using hrun

/-- Successful NK-only `isolateAll?` execution preserves every root covered
by its starting worklist. -/
theorem isolateAll_nk_covers {p : Hex.ZPoly} {target : Int}
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work .nk = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs := by
  obtain ⟨fuel, hloop⟩ := isolateAll_nk_loop hrun
  exact isolateLoop_nk_covers hloop hzroot hz

/-- Every successful NK-only `isolateAll?` result is an NK atom. -/
theorem isolateAll_nk_atoms {p : Hex.ZPoly} {target : Int}
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work .nk = some rs) :
    ∀ r ∈ rs.toList, ∃ iso : Hex.DyadicRootIsolation p,
      r = .atom iso ∧ Hex.nkWitness p iso.square := by
  obtain ⟨fuel, hloop⟩ := isolateAll_nk_loop hrun
  exact isolateLoop_nk_atoms hloop

/-- Successful NK-only `isolateAll?` results meet the target and have
pairwise-disjoint closed circumscribed discs. -/
theorem isolateAll_nk_ready_disjoint {p : Hex.ZPoly} {target : Int}
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work .nk = some rs) :
    (∀ r ∈ rs.toList, target ≤ r.square.prec) ∧
      ∀ {i j : Nat}, (hi : i < rs.size) → (hj : j < rs.size) → i ≠ j →
        Disjoint (DyadicSquare.closedDisc rs[i].square)
          (DyadicSquare.closedDisc rs[j].square) := by
  obtain ⟨fuel, hloop⟩ := isolateAll_nk_loop hrun
  exact ⟨(isolateLoop_ready_disjoint hloop).1,
    fun hi hj hij => isolateLoop_disjoint_of_ne hloop hi hj hij⟩

/-- Starting from the Cauchy component, successful NK-only isolation covers
every complex root. -/
theorem isolateAll_nk_cauchy_covers (p : Hex.ZPoly)
    (hdegree : 0 < p.degree?.getD 0) {target : Int}
    {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target #[Hex.Component.cauchy p hdegree] .nk =
      some rs) {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z) :
    z ∈ Results.region rs := by
  apply isolateAll_nk_covers hrun hzroot
  exact ⟨Hex.Component.cauchy p hdegree, by simp,
    Component.isRoot_mem_cauchy p hdegree hzroot⟩

/-- Each emitted NK atom contains one interior simple root, unique in its
closed square. -/
theorem isolateAll_nk_simple {p : Hex.ZPoly} {target : Int}
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work .nk = some rs)
    {i : Nat} (hi : i < rs.size) :
    ∃ (iso : Hex.DyadicRootIsolation p), rs[i] = .atom iso ∧
      ∃ z, (toPolyℂ p).eval z = 0 ∧
        z ∈ DyadicSquare.openSquare iso.square ∧
        (toPolyℂ p).derivative.eval z ≠ 0 ∧
        ∀ w, (toPolyℂ p).eval w = 0 →
          w ∈ DyadicSquare.closedSquare iso.square → w = z := by
  obtain ⟨iso, hiso, hnk⟩ := isolateAll_nk_atoms hrun rs[i]
    (Array.getElem_mem_toList hi)
  exact ⟨iso, hiso, NKData.sound hnk⟩

/-- In the positive-degree branch, successful `isolate` execution is a
successful Cauchy-started `isolateAll?` run whose result indices correspond
exactly to the returned NK atoms. -/
theorem isolate_nk_run (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (hdegree : 0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms) :
    ∃ rs : Array (Hex.Certified p),
      Hex.isolateAll? p (max atomPrec (Hex.separationDepth p : Int))
        #[Hex.Component.cauchy p hdegree] .nk = some rs ∧
      rs.size = atoms.size ∧
      ∀ (i : Nat) (hi : i < rs.size) (hj : i < atoms.size),
        rs[i] = .atom atoms[i] ∧ Hex.nkWitness p atoms[i].square := by
  have hrun' := hrun
  rw [Hex.isolate, dif_pos hdegree] at hrun'
  let target := max atomPrec (Hex.separationDepth p : Int)
  cases hall : Hex.isolateAll? p target
      #[Hex.Component.cauchy p hdegree] .nk with
  | none => simp [target, hall] at hrun'
  | some rs =>
      have hmap : rs.mapM Hex.Certified.asAtom? = some atoms := by
        simpa only [target, hall, Option.bind_eq_bind, Option.bind_some]
          using hrun'
      obtain ⟨hsize, hget⟩ := array_mapM_some_get hmap
      refine ⟨rs, ?_, hsize, ?_⟩
      · rfl
      · intro i hi hj
        have hm := hget i hi hj
        cases hri : rs[i] with
        | atom iso =>
            rw [hri] at hm
            have hiso : iso = atoms[i] := by
              exact Option.some.inj hm
            obtain ⟨iso', heq, hnk⟩ := isolateAll_nk_atoms hall rs[i]
              (Array.getElem_mem_toList hi)
            have heq' : iso = iso' := by simpa only [hri, Hex.Certified.atom.injEq] using heq
            cases heq'
            cases hiso
            exact ⟨rfl, hnk⟩
        | cluster cl =>
            rw [hri] at hm
            simp [Hex.Certified.asAtom?] at hm

/-- Every atom returned by positive-degree NK-only isolation meets the
requested precision and contains a unique interior simple root. -/
theorem isolate_nk_simple (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (hdegree : 0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms)
    {i : Nat} (hi : i < atoms.size) :
    atomPrec ≤ atoms[i].square.prec ∧
      Hex.nkWitness p atoms[i].square ∧
      ∃ z, (toPolyℂ p).eval z = 0 ∧
        z ∈ DyadicSquare.openSquare atoms[i].square ∧
        (toPolyℂ p).derivative.eval z ≠ 0 ∧
        ∀ w, (toPolyℂ p).eval w = 0 →
          w ∈ DyadicSquare.closedSquare atoms[i].square → w = z := by
  obtain ⟨rs, hall, hsize, hrel⟩ :=
    isolate_nk_run p h atomPrec hdegree hrun
  have hi' : i < rs.size := by simpa [hsize] using hi
  obtain ⟨hri, hnk⟩ := hrel i hi' hi
  have hready := (isolateAll_nk_ready_disjoint hall).1 rs[i]
    (Array.getElem_mem_toList hi')
  rw [hri] at hready
  exact ⟨(le_max_left atomPrec (Hex.separationDepth p : Int)).trans hready,
    hnk, NKData.sound hnk⟩

/-- Distinct atoms returned by positive-degree NK-only isolation have
disjoint closed circumscribed discs. -/
theorem isolate_nk_disjoint (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (hdegree : 0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms)
    {i j : Nat} (hi : i < atoms.size) (hj : j < atoms.size) (hij : i ≠ j) :
    Disjoint (DyadicSquare.closedDisc atoms[i].square)
      (DyadicSquare.closedDisc atoms[j].square) := by
  obtain ⟨rs, hall, hsize, hrel⟩ :=
    isolate_nk_run p h atomPrec hdegree hrun
  have hi' : i < rs.size := by simpa [hsize] using hi
  have hj' : j < rs.size := by simpa [hsize] using hj
  obtain ⟨hri, -⟩ := hrel i hi' hi
  obtain ⟨hrj, -⟩ := hrel j hj' hj
  have hdisj := (isolateAll_nk_ready_disjoint hall).2 hi' hj' hij
  simpa only [hri, hrj, Hex.Certified.square] using hdisj

/-- Every complex root belongs to exactly one atom returned by successful
positive-degree NK-only isolation. -/
theorem isolate_nk_covers_once_of_pos (p : Hex.ZPoly)
    (h : Hex.HasOnlySimpleRoots p) (atomPrec : Int)
    (hdegree : 0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z) :
    ∃! i : Fin atoms.size,
      z ∈ DyadicSquare.closedSquare atoms[i].square := by
  obtain ⟨rs, hall, hsize, hrel⟩ :=
    isolate_nk_run p h atomPrec hdegree hrun
  have hcovered := isolateAll_nk_cauchy_covers p hdegree hall hzroot
  obtain ⟨r, hr, hzr⟩ := hcovered
  obtain ⟨i, hiList, hir⟩ := List.getElem_of_mem hr
  have hi : i < rs.size := by simpa using hiList
  have hir' : rs[i] = r := by
    rw [← hir]
    exact (Array.getElem_toList hi).symm
  obtain ⟨hri, hnk⟩ := hrel i hi (by simpa [← hsize] using hi)
  have hzri : z ∈ Certified.region rs[i] := by simpa only [hir'] using hzr
  have hzsq : z ∈ DyadicSquare.closedSquare atoms[i].square := by
    rw [hri] at hzri
    simpa only [Certified.region, DyadicRootIsolation.region, if_pos hnk]
      using hzri
  let fi : Fin atoms.size := ⟨i, by simpa [← hsize] using hi⟩
  refine ⟨fi, hzsq, ?_⟩
  intro j hzj
  apply Fin.ext
  by_contra hij
  have hdisj := isolate_nk_disjoint p h atomPrec hdegree hrun
    fi.isLt j.isLt (Ne.symm hij)
  exact (Set.disjoint_left.mp hdisj)
    (DyadicSquare.closedSquare_subset_closedDisc atoms[fi].square hzsq)
    (DyadicSquare.closedSquare_subset_closedDisc atoms[j].square hzj)

/-- A nonzero executable polynomial has a nonzero complex cast. -/
theorem toPolyℂ_ne_zero (p : Hex.ZPoly) (hp : p.size ≠ 0) :
    toPolyℂ p ≠ 0 := by
  intro hzero
  have hsize : 0 < p.size := Nat.pos_of_ne_zero hp
  have hcoeff := congrArg
    (fun q : Polynomial ℂ => q.coeff (p.size - 1)) hzero
  rw [coeff_toPolyℂ, Polynomial.coeff_zero] at hcoeff
  apply Hex.DensePoly.coeff_last_ne_zero_of_pos_size p hsize
  exact_mod_cast hcoeff

/-- A nonzero executable polynomial whose natural degree is not positive has
no complex root. -/
theorem not_isRoot_of_degree_not_pos (p : Hex.ZPoly) (hp : p.size ≠ 0)
    (hdegree : ¬0 < p.degree?.getD 0) (z : ℂ) :
    ¬(toPolyℂ p).IsRoot z := by
  intro hz
  have hpos : 0 < (toPolyℂ p).natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_root (toPolyℂ_ne_zero p hp) hz)
  apply hdegree
  simpa only [natDegree_toPolyℂ] using hpos

/-- A successful non-positive-degree `isolate` call is exactly the nonzero
constant branch and returns the empty atom array. -/
theorem isolate_nk_nonpositive (p : Hex.ZPoly)
    (h : Hex.HasOnlySimpleRoots p) (atomPrec : Int)
    (hdegree : ¬0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms) :
    p.size ≠ 0 ∧ atoms = #[] := by
  have hrun' := hrun
  rw [Hex.isolate, dif_neg hdegree] at hrun'
  by_cases hp : p.size = 0
  · simp [hp] at hrun'
  · have hatoms : atoms = #[] := by
      simpa only [hp, ↓reduceIte, Option.some.injEq] using hrun'.symm
    exact ⟨hp, hatoms⟩

/-- Every successful NK-only `isolate` call assigns each complex root to
exactly one returned atom, including the vacuous nonzero-constant branch. -/
theorem isolate_nk_covers_once (p : Hex.ZPoly)
    (h : Hex.HasOnlySimpleRoots p) (atomPrec : Int)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z) :
    ∃! i : Fin atoms.size,
      z ∈ DyadicSquare.closedSquare atoms[i].square := by
  by_cases hdegree : 0 < p.degree?.getD 0
  · exact isolate_nk_covers_once_of_pos p h atomPrec hdegree hrun hzroot
  · obtain ⟨hp, -⟩ := isolate_nk_nonpositive p h atomPrec hdegree hrun
    exact (not_isRoot_of_degree_not_pos p hp hdegree z hzroot).elim

/-- Any two differently indexed atoms returned by successful NK-only
`isolate` execution have disjoint closed circumscribed discs. -/
theorem isolate_nk_pairwise (p : Hex.ZPoly)
    (h : Hex.HasOnlySimpleRoots p) (atomPrec : Int)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms)
    {i j : Nat} (hi : i < atoms.size) (hj : j < atoms.size) (hij : i ≠ j) :
    Disjoint (DyadicSquare.closedDisc atoms[i].square)
      (DyadicSquare.closedDisc atoms[j].square) := by
  by_cases hdegree : 0 < p.degree?.getD 0
  · exact isolate_nk_disjoint p h atomPrec hdegree hrun hi hj hij
  · obtain ⟨-, hatoms⟩ := isolate_nk_nonpositive p h atomPrec hdegree hrun
    subst atoms
    simp at hi

/-- Every returned atom of successful NK-only isolation meets the requested
precision and has the unique interior simple-root contract. -/
theorem isolate_nk_atom_sound (p : Hex.ZPoly)
    (h : Hex.HasOnlySimpleRoots p) (atomPrec : Int)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec .nk = some atoms)
    {i : Nat} (hi : i < atoms.size) :
    atomPrec ≤ atoms[i].square.prec ∧
      Hex.nkWitness p atoms[i].square ∧
      ∃ z, (toPolyℂ p).eval z = 0 ∧
        z ∈ DyadicSquare.openSquare atoms[i].square ∧
        (toPolyℂ p).derivative.eval z ≠ 0 ∧
        ∀ w, (toPolyℂ p).eval w = 0 →
          w ∈ DyadicSquare.closedSquare atoms[i].square → w = z := by
  by_cases hdegree : 0 < p.degree?.getD 0
  · exact isolate_nk_simple p h atomPrec hdegree hrun hi
  · obtain ⟨-, hatoms⟩ := isolate_nk_nonpositive p h atomPrec hdegree hrun
    subst atoms
    simp at hi

end

end HexRootsMathlib
