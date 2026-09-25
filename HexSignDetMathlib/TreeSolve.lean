/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.NodeSolve
public import HexSignDetMathlib.TreeChecks

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]

/-- Finite interpretation of the actual prepared query for every valid moment
row. This premise mentions neither a solved system nor an accepted output;
the root-sum bridge must establish it from coefficient and root semantics. -/
@[expose] def QueryValues (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (reduced : Bool) (preparation : Option (QueryReduction E))
    (xs : List (List Int)) : Prop :=
  let operands := QueryReduction.operands qs (nodePreparation reduced domain qs preparation)
  ∀ es, es.length = qs.length → es.all (· ≤ 2) = true →
    (Sturm.certifyPrepared context domain
      (queryPoly operands es (nodeReduction reduced domain operands es))).value =
      (xs.map (entry es)).sum

/-- Query-value obligations along the producer's actual balanced slices.
Observations retain multiplicity and are restricted at exactly the same split.
No support, count, solver-success or replay-acceptance premise is included. -/
@[expose] def QueryModel (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (reduced : Bool) (preparation : Option (QueryReduction E))
    (xs : List (List Int)) : Prop :=
  QueryValues context domain qs reduced preparation xs ∧
    if qs.length ≤ 1 then True else
      QueryModel context domain (qs.take (qs.length / 2)) reduced
        (preparation.map fun r => r.slice 0 (qs.length / 2)) (xs.map (List.take (qs.length / 2))) ∧
      QueryModel context domain (qs.drop (qs.length / 2)) reduced
        (preparation.map fun r => r.slice (qs.length / 2) (qs.length - qs.length / 2))
        (xs.map (List.drop (qs.length / 2)))
termination_by qs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

/-- Finite invariant returned by construction, with complete retained support
and exact counts. It does not interpret the observations as real roots. -/
structure Node.Counted (n : Node E Ctx) (arity : Nat) (xs : List (List Int)) : Prop where
  checked : n.system.check arity = true
  basis : n.basis = Matrix.rankCert n.system.retainedMatrix
  values : n.system.values = SignDet.moments n.system.rows xs
  cover : ∀ x ∈ xs, x ∈ n.system.support
  counts : SignDet.counts n.system.columns xs = n.system.counts

/-- Exact finite counts and complete support at every retained node, with
observations restricted along the same balanced slices as the producer. -/
@[expose] def Replay.Counted (arity : Nat) (xs : List (List Int)) : Replay E Ctx → Prop
  | .leaf n => n.Counted arity xs
  | .split n l r =>
    n.Counted arity xs ∧
    l.Counted (min (arity / 2) arity) (xs.map (List.take (arity / 2))) ∧
    r.Counted (arity - arity / 2) (xs.map (List.drop (arity / 2)))

omit [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] in
/-- Project the root invariant while retaining the recursive guarantees. -/
theorem Replay.Counted.node {t : Replay E Ctx} {arity : Nat} {xs : List (List Int)}
    (h : t.Counted arity xs) : t.node.Counted arity xs := by
  cases t with
  | leaf n => exact h
  | split n l r => exact h.1

/-- Assemble a counted node from a complete candidate system. Query values
are interpreted before solving; neither the inverse nor the final equation
is used to infer coverage of omitted columns. -/
theorem buildNode_counted (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int))
    (reduced : Bool) (inverse : Option (Int × Matrix Int rows.length rows.length))
    (preparation : Option (QueryReduction E)) (xs : List (List Int))
    (hv : QueryValues context domain qs reduced preparation xs)
    (s : System rows.length) (hrows : s.rows.toList = rows) (hcols : s.columns.toList = columns)
    (hc : s.check qs.length = true) (hvalues : s.values = moments s.rows xs)
    (cover : ∀ x ∈ xs, x ∈ columns)
    (hinv : ∀ d a, inverse = some (d, a) → d = s.denominator ∧ a = s.inverse) :
    ∃ n, buildNode context domain qs rows columns reduced inverse preparation = .ok n ∧
      n.Counted qs.length xs := by
  have valid {r : Nat} (u : System r) (hu : u.check qs.length = true) (i : Fin r) :
      u.rows[i].length = qs.length ∧ u.rows[i].all (· ≤ 2) = true := by
    simp only [System.check, Bool.and_eq_true] at hu
    have hh := List.all_eq_true.mp hu.1.1.1.1.1 _ (List.getElem_mem (l := u.rows.toList) (n := i.val) (by simp))
    simpa only [Bool.and_eq_true, decide_eq_true_eq, Vector.getElem_toList,
      Fin.getElem_fin] using hh
  obtain ⟨n, hn, _⟩ := buildNode_complete context domain qs rows columns reduced inverse
    preparation s hrows hcols hc hinv (by
      dsimp only
      intro i
      rw [hvalues]
      simp only [moments, Fin.getElem_fin, Vector.getElem_ofFn]
      exact hv _ (valid s hc i).1 (valid s hc i).2)
  have spec := buildNode_spec context domain qs rows columns reduced inverse preparation hn
  have hs := spec.2.2.2.2.2.2.2.1
  have evidence := buildNode_evidence context domain qs rows columns reduced inverse preparation hn
  have values : n.system.values = SignDet.moments n.system.rows xs := by
    apply Vector.ext
    intro i hi
    let j : Fin n.size := ⟨i, hi⟩
    simp only [moments, Fin.getElem_fin, Vector.getElem_ofFn]
    change n.system.values[j] = (xs.map (entry n.system.rows[j])).sum
    rw [(evidence.2 j).2.2, (evidence.2 j).2.1, (evidence.2 j).1, evidence.1]
    exact hv _ (valid n.system hs j).1 (valid n.system hs j).2
  have covers : ∀ x ∈ xs, x ∈ n.system.columns.toList := by
    rw [spec.2.2.2.2.2.2.1]
    exact cover
  exact ⟨n, hn, ⟨hs, spec.2.2.2.2.2.2.2.2, values,
    n.system.covers_support hs xs covers values, n.system.counts_eq hs xs covers values⟩⟩

/-- Ordered finite moments depend only on the literal row list, including
when dimensions are transported between child bases and list products. -/
theorem moments_toList {r : Nat} (rows : Vector (List Nat) r) (xs : List (List Int)) :
    (moments rows xs).toList = rows.toList.map (fun es => (xs.map (entry es)).sum) := by
  have he : moments rows xs = rows.map (fun es => (xs.map (entry es)).sum) := by
    ext i hi
    simp [moments]
  rw [he]
  exact Vector.toList_map

private theorem leaf_system (arity : Nat) (ha : arity ≤ 1)
    (xs : List (List Int)) (ho : Observations arity xs) :
    ∃ s : System (leafRows arity).length,
      s.rows.toList = leafRows arity ∧ s.columns.toList = leafColumns arity ∧
      s.check arity = true ∧ s.values = moments s.rows xs ∧
      ∀ x ∈ xs, x ∈ leafColumns arity := by
  cases arity with
  | zero =>
    simp only [leafRows, leafColumns, ↓reduceIte]
    obtain ⟨s, hc, hr, hs, _, hv⟩ := empty_system xs ho
    refine ⟨s, by simp [hr], by simp [hs], hc, by rw [hr, hv], ?_⟩
    intro x hx
    have he : x = [] := List.eq_nil_of_length_eq_zero (ho x hx).1
    simp [he]
  | succ n =>
    have hn : n = 0 := by omega
    subst n
    simp only [leafRows, leafColumns]
    obtain ⟨s, hc, hr, hs, _, hv⟩ := singleton_system xs ho
    refine ⟨s, by simp [hr], by simp [hs], hc, by rw [hr, hv], ?_⟩
    intro x hx
    obtain ⟨hl, hv⟩ := ho x hx
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hl
    rcases hv v (by simp) with h | h | h <;> simp [h]

/-- The actual balanced producer succeeds on finite observations whenever its
prepared query values interpret them. Child completeness constructs the parent
candidate system before solving. Empty observations and empty retained supports
are included; no exponential fallback or assumed successful output is used. -/
theorem buildTreeFrom_complete (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (reduced : Bool) (preparation : Option (QueryReduction E))
    (xs : List (List Int)) (ho : Observations qs.length xs)
    (hv : QueryModel context domain qs reduced preparation xs) :
    ∃ t, buildTreeFrom context domain qs reduced preparation = .ok t ∧
      t.Counted qs.length xs ∧ t.Interprets qs.length xs := by
  rw [QueryModel] at hv
  by_cases small : qs.length ≤ 1
  · obtain ⟨s, hrows, hcols, hc, hvalues, cover⟩ := leaf_system qs.length small xs ho
    obtain ⟨n, hn, counted⟩ := buildNode_counted context domain qs _ _ reduced none preparation
      xs hv.1 s hrows hcols hc hvalues cover (by simp)
    refine ⟨.leaf n, ?_, counted, counted.values⟩
    simp only [buildTreeFrom, small, ↓reduceDIte, hn, bind, Except.bind, pure, Except.pure]
  · have halves := hv.2
    simp only [small, ↓reduceIte] at halves
    obtain ⟨l, hl, lc, li⟩ := buildTreeFrom_complete context domain _ reduced _
      (xs.map (List.take (qs.length / 2))) (by simpa only [List.length_take] using ho.take _) halves.1
    obtain ⟨r, hr, rc, ri⟩ := buildTreeFrom_complete context domain _ reduced _
      (xs.map (List.drop (qs.length / 2))) (by simpa only [List.length_drop] using ho.drop _) halves.2
    have mid : qs.length / 2 ≤ qs.length := Nat.div_le_self _ _
    have hlc : l.node.system.check (qs.length / 2) = true := by
      simpa only [List.length_take, Nat.min_eq_left mid] using lc.node.checked
    have hrc : r.node.system.check (qs.length - qs.length / 2) = true := by
      simpa only [List.length_drop] using rc.node.checked
    have cl : ∀ x ∈ xs, x.take (qs.length / 2) ∈ l.node.system.support := by
      intro x hx
      exact lc.node.cover _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have cr : ∀ x ∈ xs, x.drop (qs.length / 2) ∈ r.node.system.support := by
      intro x hx
      exact rc.node.cover _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    obtain ⟨s, hrows, hcols, hc, hd, hi, _, hvalues⟩ :=
      l.node.parent_system r.node hlc hrc lc.node.basis rc.node.basis xs cl cr
    have hs : s.check qs.length = true := by
      simpa only [Nat.add_sub_of_le mid] using hc
    have values : s.values = moments s.rows xs := by
      apply Vector.toList_inj.mp
      rw [hvalues, moments_toList, moments_toList, hrows,
        (l.node.product_inverse r.node hlc hrc lc.node.basis rc.node.basis).1]
    have cover : ∀ x ∈ xs, x ∈ product l.node.system.support r.node.system.support := by
      intro x hx
      rw [← List.take_append_drop (qs.length / 2) x]
      exact mem_product (cl x hx) (cr x hx)
    obtain ⟨n, hn, counted⟩ := buildNode_counted context domain qs _ _ reduced
      (some (l.node.basis.denom * r.node.basis.denom, parentInverse l.node r.node)) preparation
      xs hv.1 s hrows hcols hs values cover (by
        intro d a he
        cases he
        exact ⟨hd.symm, hi.symm⟩)
    refine ⟨.split n l r, ?_, ⟨counted, ?_, ?_⟩, ?_⟩
    · simp only [buildTreeFrom, small, ↓reduceDIte, hl, hr, hn, bind, Except.bind,
        pure, Except.pure]
    · simpa only [List.length_take] using lc
    · simpa only [List.length_drop] using rc
    · exact ⟨counted.values, by simpa only [List.length_take] using li,
        by simpa only [List.length_drop] using ri⟩
termination_by qs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

/-- Shared root preprocessing uses the same finite query model as recursion.
This establishes tree construction only; root-sum semantics must still supply
that model, and algebraic interpretation supplies independent replay acceptance. -/
theorem buildTree_complete (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (reduced : Bool) (xs : List (List Int))
    (ho : Observations qs.length xs)
    (hv : QueryModel context domain qs reduced (nodePreparation reduced domain qs none) xs) :
    ∃ t, buildTree context domain qs reduced = .ok t ∧
      t.Counted qs.length xs ∧ t.Interprets qs.length xs := by
  exact buildTreeFrom_complete context domain qs reduced _ xs ho hv

variable {K : Type w} [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable [DecidableEq Ctx]

/-- Finite producer completeness composed with independent algebraic replay
acceptance. The sole remaining root-count obligation here is QueryModel;
this theorem neither supplies nor replaces the shared root-sum foundation. -/
theorem buildPrepared_complete (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f (1 : E) = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b) (hm : ∀ a b, f (a * b) = f a * f b)
    (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
    (sign : E → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)
    (hneg : ∀ a, sign a < 0 ↔ f a < 0) (hbound : ∀ a, -1 ≤ sign a ∧ sign a ≤ 1)
    (context : Ctx) (domain : Sturm.PreparedDomain E) (hsign : domain.sign = sign)
    (qs : List (DensePoly E)) (reduced : Bool) (xs : List (List Int))
    (ho : Observations qs.length xs)
    (hv : QueryModel context domain qs reduced (nodePreparation reduced domain qs none) xs) :
    ∃ t, buildPrepared context domain qs reduced = .ok t ∧
      t.val.Counted qs.length xs ∧ t.val.Interprets qs.length xs := by
  obtain ⟨t, ht, counted, interprets⟩ := buildTree_complete context domain qs reduced xs ho hv
  obtain ⟨hc, hchecked⟩ := buildPrepared_eq f hz h1 ha hs hm hn hi sign hpos hneg hbound
    context domain hsign qs reduced ht
  exact ⟨⟨t, hc⟩, hchecked, counted, interprets⟩

end Hex.SignDet
