/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Driver
public import HexRootsMathlib.NKDriver
public import HexRootsMathlib.SimpleRoot

public section

/-!
# Exact atom enumeration

Successful `Hex.isolate` calls enumerate the complex roots exactly, for every
atom strategy and including the executable zero and constant branches.
-/

open Complex Polynomial Set

namespace HexRootsMathlib

noncomputable section

namespace DyadicRootIsolation

/-- The unique complex root selected by an atom certificate. -/
@[expose] noncomputable def root {p : Hex.ZPoly}
    (iso : Hex.DyadicRootIsolation p) : ℂ :=
  (sound iso).choose

/-- The selected value is an interior simple root, unique in the atom's
selected closed region. -/
theorem root_spec {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) :
    (toPolyℂ p).eval (root iso) = 0 ∧
      root iso ∈ openRegion iso ∧
      (toPolyℂ p).derivative.eval (root iso) ≠ 0 ∧
      ∀ w, (toPolyℂ p).eval w = 0 → w ∈ region iso → w = root iso :=
  (sound iso).choose_spec

theorem isRoot {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) :
    (toPolyℂ p).IsRoot (root iso) :=
  (root_spec iso).1

/-- The selected root lies in the atom's stored circumscribed disc. -/
theorem root_mem_closedDisc {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) :
    root iso ∈ DyadicSquare.closedDisc iso.square := by
  apply Certified.region_subset_closedDisc (.atom iso)
  exact openRegion_subset_region iso (root_spec iso).2.1

/-- The raw and separation-refined semantic-root interpretations agree. -/
theorem root_refined {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p)
    (h : (Hex.mahlerPrec p : Int) ≤ iso.square.prec) :
    root iso = RefinedIsolation.root ⟨iso, h⟩ := rfl

end DyadicRootIsolation

/-- An option-valued list map that succeeds preserves length and corresponding
entries. -/
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
              have hys : ys = y :: ys' := (Option.some.inj heq).symm
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

/-- An option-valued array map that succeeds preserves size and corresponding
entries. -/
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
  refine ⟨by simpa using hlen, ?_⟩
  intro i hi hj
  simpa only [← Array.getElem_toList] using hget i (by simpa using hi)
    (by simpa using hj)

/-- In the positive-degree branch, successful isolation is a successful
Cauchy-started general driver run whose results correspond indexwise to the
returned atoms. -/
theorem isolate_run (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (strategy : Hex.AtomStrategy)
    (hdegree : 0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms) :
    ∃ rs : Array (Hex.Certified p),
      Hex.isolateAll? p (max atomPrec (Hex.separationDepth p : Int))
        #[Hex.Component.cauchy p hdegree] strategy = some rs ∧
      rs.size = atoms.size ∧
      ∀ (i : Nat) (hi : i < rs.size) (hj : i < atoms.size),
        rs[i] = .atom atoms[i] := by
  have hrun' := hrun
  rw [Hex.isolate, dif_pos hdegree] at hrun'
  let target := max atomPrec (Hex.separationDepth p : Int)
  cases hall : Hex.isolateAll? p target
      #[Hex.Component.cauchy p hdegree] strategy with
  | none => simp [target, hall] at hrun'
  | some rs =>
      have hmap : rs.mapM Hex.Certified.asAtom? = some atoms := by
        simpa only [target, hall, Option.bind_eq_bind, Option.bind_some]
          using hrun'
      obtain ⟨hsize, hget⟩ := array_mapM_some_get hmap
      refine ⟨rs, rfl, hsize, ?_⟩
      intro i hi hj
      have hm := hget i hi hj
      cases hri : rs[i] with
      | atom iso =>
          rw [hri] at hm
          have hiso : iso = atoms[i] := Option.some.inj hm
          simp [hiso]
      | cluster cl =>
          rw [hri] at hm
          simp [Hex.Certified.asAtom?] at hm

/-- Every root belongs to one of the atoms returned by successful
positive-degree isolation. -/
theorem isolate_root_mem_of_pos (p : Hex.ZPoly)
    (h : Hex.HasOnlySimpleRoots p) (atomPrec : Int)
    (strategy : Hex.AtomStrategy) (hdegree : 0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z) :
    ∃ iso ∈ atoms.toList, DyadicRootIsolation.root iso = z := by
  obtain ⟨rs, hall, hsize, hrel⟩ :=
    isolate_run p h atomPrec strategy hdegree hrun
  obtain ⟨r, hr, hzr⟩ :=
    isolateAll_cauchy_covers p hdegree hall hzroot
  obtain ⟨i, hiList, hir⟩ := List.getElem_of_mem hr
  have hi : i < rs.size := by simpa using hiList
  have hj : i < atoms.size := by simpa [← hsize] using hi
  have hir' : rs[i] = r := by
    rw [← hir]
    exact (Array.getElem_toList hi).symm
  have hri := hrel i hi hj
  have hzri : z ∈ Certified.region rs[i] := by
    simpa only [hir'] using hzr
  rw [hri] at hzri
  refine ⟨atoms[i], Array.getElem_mem_toList hj, ?_⟩
  exact ((DyadicRootIsolation.root_spec atoms[i]).2.2.2 z hzroot hzri).symm

/-- A successful non-positive-degree call is the nonzero constant branch and
returns no atoms, independently of strategy. -/
theorem isolate_nonpositive (p : Hex.ZPoly)
    (h : Hex.HasOnlySimpleRoots p) (atomPrec : Int)
    (strategy : Hex.AtomStrategy) (hdegree : ¬0 < p.degree?.getD 0)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms) :
    p.size ≠ 0 ∧ atoms = #[] := by
  have hrun' := hrun
  rw [Hex.isolate, dif_neg hdegree] at hrun'
  by_cases hp : p.size = 0
  · simp [hp] at hrun'
  · have hatoms : atoms = #[] := by
      simpa only [hp, ↓reduceIte, Option.some.injEq] using hrun'.symm
    exact ⟨hp, hatoms⟩

/-- Every returned atom meets the full driver target, not only the requested
atom precision. -/
theorem isolate_prec (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (strategy : Hex.AtomStrategy)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms) :
    ∀ iso ∈ atoms.toList,
      max atomPrec (Hex.separationDepth p : Int) ≤ iso.square.prec := by
  by_cases hdegree : 0 < p.degree?.getD 0
  · obtain ⟨rs, hall, hsize, hrel⟩ :=
      isolate_run p h atomPrec strategy hdegree hrun
    intro iso hiso
    obtain ⟨i, hiList, hir⟩ := List.getElem_of_mem hiso
    have hi : i < atoms.size := by simpa using hiList
    have hi' : i < rs.size := by simpa [hsize] using hi
    have hri := hrel i hi' hi
    have hready := (isolateAll_sound hall).1 rs[i]
      (Array.getElem_mem_toList hi')
    rw [hri] at hready
    rw [← hir]
    exact hready.1
  · obtain ⟨-, hatoms⟩ :=
      isolate_nonpositive p h atomPrec strategy hdegree hrun
    subst atoms
    simp

/-- Every successful isolation result can be wrapped as a
`RefinedIsolation`: the driver's separation target dominates `mahlerPrec`. -/
theorem isolate_refined (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (strategy : Hex.AtomStrategy)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms) :
    ∀ iso ∈ atoms.toList, (Hex.mahlerPrec p : Int) ≤ iso.square.prec := by
  have hsepNat : Hex.mahlerPrec p ≤ Hex.separationDepth p := by
    rw [Hex.separationDepth]
    omega
  have hsep : (Hex.mahlerPrec p : Int) ≤
      (Hex.separationDepth p : Int) := by exact_mod_cast hsepNat
  intro iso hiso
  exact hsep.trans <| (le_max_right atomPrec
    (Hex.separationDepth p : Int)).trans <| isolate_prec p h atomPrec
      strategy hrun iso hiso

/-- Distinct output indices select distinct semantic roots. -/
theorem isolate_roots_ne (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (strategy : Hex.AtomStrategy)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms)
    {i j : Nat} (hi : i < atoms.size) (hj : j < atoms.size) (hij : i ≠ j) :
    DyadicRootIsolation.root atoms[i] ≠
      DyadicRootIsolation.root atoms[j] := by
  by_cases hdegree : 0 < p.degree?.getD 0
  · obtain ⟨rs, hall, hsize, hrel⟩ :=
      isolate_run p h atomPrec strategy hdegree hrun
    have hi' : i < rs.size := by simpa [hsize] using hi
    have hj' : j < rs.size := by simpa [hsize] using hj
    have hri := hrel i hi' hi
    have hrj := hrel j hj' hj
    have hdisj := (isolateAll_sound hall).2 hi' hj' hij
    have hmemi : DyadicRootIsolation.root atoms[i] ∈
        DyadicSquare.closedDisc rs[i].square := by
      rw [hri]
      exact DyadicRootIsolation.root_mem_closedDisc atoms[i]
    have hmemj : DyadicRootIsolation.root atoms[j] ∈
        DyadicSquare.closedDisc rs[j].square := by
      rw [hrj]
      exact DyadicRootIsolation.root_mem_closedDisc atoms[j]
    intro heq
    rw [heq] at hmemi
    exact (Set.disjoint_left.mp hdisj) hmemi hmemj
  · obtain ⟨-, hatoms⟩ :=
      isolate_nonpositive p h atomPrec strategy hdegree hrun
    subst atoms
    simp at hi

/-- The number of returned atoms is the polynomial's complex natural degree.
Together with `isolate_roots_ne`, this records that the exact enumeration has
no duplicate representatives. -/
theorem isolate_count (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (strategy : Hex.AtomStrategy)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms) :
    atoms.size = (toPolyℂ p).natDegree := by
  classical
  by_cases hdegree : 0 < p.degree?.getD 0
  · obtain ⟨rs, hall, hsize, hrel⟩ :=
      isolate_run p h atomPrec strategy hdegree hrun
    calc
      atoms.size = rs.size := hsize.symm
      _ = ∑ _i : Fin rs.size, 1 := by simp
      _ = ∑ i : Fin rs.size, Certified.count rs[i] := by
        apply Finset.sum_congr rfl
        intro i _
        change 1 = Certified.count rs[i.val]
        rw [hrel i.val i.isLt (by omega)]
        rfl
      _ = (toPolyℂ p).natDegree := isolateAll_count p hdegree hall
  · obtain ⟨-, hatoms⟩ :=
      isolate_nonpositive p h atomPrec strategy hdegree hrun
    subst atoms
    rw [Array.size_empty, natDegree_toPolyℂ]
    exact Nat.eq_zero_of_not_pos hdegree |>.symm

/-- Successful isolation enumerates exactly the distinct complex roots and
meets the requested precision, for every strategy and every executable edge
case. -/
theorem isolate_sound (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (atomPrec : Int) (strategy : Hex.AtomStrategy)
    {atoms : Array (Hex.DyadicRootIsolation p)}
    (hrun : Hex.isolate p h atomPrec strategy = some atoms) :
    (atoms.toList.map DyadicRootIsolation.root).toFinset =
        (toPolyℂ p).roots.toFinset ∧
      ∀ iso ∈ atoms.toList, atomPrec ≤ iso.square.prec := by
  classical
  by_cases hdegree : 0 < p.degree?.getD 0
  · have hq : toPolyℂ p ≠ 0 := by
      intro hzero
      have hnat : (toPolyℂ p).natDegree = 0 := by rw [hzero]; simp
      rw [natDegree_toPolyℂ] at hnat
      omega
    constructor
    · ext z
      constructor
      · intro hz
        rw [List.mem_toFinset] at hz
        obtain ⟨iso, hiso, rfl⟩ := List.mem_map.mp hz
        exact Multiset.mem_toFinset.mpr <|
          (mem_roots hq).mpr (DyadicRootIsolation.isRoot iso)
      · intro hz
        have hzroot : (toPolyℂ p).IsRoot z :=
          (mem_roots hq).mp (Multiset.mem_toFinset.mp hz)
        obtain ⟨iso, hiso, hroot⟩ :=
          isolate_root_mem_of_pos p h atomPrec strategy hdegree hrun hzroot
        rw [List.mem_toFinset]
        exact List.mem_map.mpr ⟨iso, hiso, hroot⟩
    · intro iso hiso
      exact (le_max_left atomPrec (Hex.separationDepth p : Int)).trans <|
        isolate_prec p h atomPrec strategy hrun iso hiso
  · obtain ⟨hp, hatoms⟩ :=
      isolate_nonpositive p h atomPrec strategy hdegree hrun
    have hroots : (toPolyℂ p).roots = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro z hz
      exact not_isRoot_of_degree_not_pos p hp hdegree z <|
        (mem_roots (toPolyℂ_ne_zero p hp)).mp hz
    subst atoms
    simp [hroots]

end

end HexRootsMathlib

namespace Hex.DyadicRootIsolation

/-- Field-notation alias for an atom's semantic root. -/
noncomputable abbrev root {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) : ℂ :=
  HexRootsMathlib.DyadicRootIsolation.root iso

end Hex.DyadicRootIsolation
