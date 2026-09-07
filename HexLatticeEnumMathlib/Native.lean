/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Cert
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

/-- Structural validity of an exhaustive coefficient tree, following the executable bounds. -/
inductive Exhaustive (rows : Hex.Matrix Int n m) (t : Vector Rat m) (p : Data n m) (r : Rat) :
    Nat → Vector Int n → Tree → Prop where
  | leaf (z : Vector Int n) (h : distance (Hex.Matrix.vecMul z rows) t ≤ r) :
      Exhaustive rows t p r 0 z .leaf
  | outside (z : Vector Int n) (h : r < distance (Hex.Matrix.vecMul z rows) t) :
      Exhaustive rows t p r 0 z .empty
  | empty (k : Nat) (hk : k < n) (z : Vector Int n)
      (h : (bounds (p.centre z ⟨k, hk⟩) p.norms[k]
        (r - p.residual.normSq - suffix p z (k + 1))).size = 0) :
      Exhaustive rows t p r (k + 1) z .empty
  | node (k : Nat) (hk : k < n) (z : Vector Int n) (interval : Interval)
      (children : List (Int × Tree))
      (hi : interval = bounds (p.centre z ⟨k, hk⟩) p.norms[k]
        (r - p.residual.normSq - suffix p z (k + 1)))
      (hl : checkLabels interval children = true)
      (hc : ∀ a tree, (a, tree) ∈ children → Exhaustive rows t p r k (z.set k a hk) tree) :
      Exhaustive rows t p r (k + 1) z (.node interval children)

/-- Each supplied tree node consumes one replay unit, including empty and leaf nodes. -/
theorem tree_nodes_pos (tree : Tree) : 0 < tree.nodes := by
  cases tree <;> simp [Tree.nodes]

/-- Child node counts add to the exact replay cost of a branching node. -/
theorem tree_nodes_node (interval : Interval) (children : List (Int × Tree)) :
    (Hex.LatticeEnum.Tree.node interval children).nodes = 1 + (children.map fun child => child.2.nodes).sum := by
  rw [Tree.nodes]
  congr 1
  exact congrArg List.sum (List.attach_map_val (l := children) (f := fun child => child.2.nodes))

/-- Every child contributes at least one node to the replay budget. -/
theorem children_nodes (children : List (Int × Tree)) :
    children.length ≤ (children.map fun child => child.2.nodes).sum := by
  induction children with
  | nil => simp
  | cons child children ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := tree_nodes_pos child.2
    omega

/-- Replaying complete children consumes exactly their total node count. -/
theorem replay_children_accept (visit : Int → Tree → Nat → Option (Replay n m))
    (children : List (Int × Tree))
    (hv : ∀ a tree, (a, tree) ∈ children → ∀ fuel, tree.nodes ≤ fuel →
      ∃ result, visit a tree fuel = some result ∧ result.remaining = fuel - tree.nodes)
    (fuel : Nat) (points : List (Point n m))
    (hf : (children.map fun child => child.2.nodes).sum ≤ fuel) :
    ∃ result, replayAux.loop visit children fuel points = some result ∧
      result.remaining = fuel - (children.map fun child => child.2.nodes).sum := by
  induction children generalizing fuel points with
  | nil => exact ⟨⟨points.reverse, fuel⟩, rfl, by simp⟩
  | cons child children ih =>
    rcases child with ⟨a, tree⟩
    simp only [List.map_cons, List.sum_cons] at hf ⊢
    obtain ⟨first, hfirst, hremaining⟩ := hv a tree (by simp) fuel (by omega)
    obtain ⟨result, hr, hrest⟩ := ih
      (fun a tree hmem => hv a tree (by simp [hmem])) first.remaining (first.points.reverse ++ points)
      (by omega)
    refine ⟨result, ?_, ?_⟩
    · simp only [replayAux.loop, hfirst]
      exact hr
    · omega

/-- Every structurally exhaustive tree replays successfully with its exact node allowance. -/
theorem replay_accepts (rows working : Hex.Matrix Int n m) (forward : Hex.Matrix Int n n)
    (hU : forward * rows = working) (p : Data n m) (t : Vector Rat m) (r : Rat)
    (k : Nat) (hk : k ≤ n) (z : Vector Int n) (tree : Tree)
    (h : Exhaustive working t p r k z tree) (fuel : Nat) (hf : tree.nodes ≤ fuel) :
    ∃ result, replayAux rows t r forward p p.residual.normSq k hk z (suffix p z k) tree fuel = some result ∧
      result.remaining = fuel - tree.nodes := by
  induction h generalizing fuel with
  | leaf z hd =>
    cases fuel with
    | zero => have := tree_nodes_pos (Tree.leaf); omega
    | succ fuel =>
      have he : (pointRows rows t (forward.transpose * z)).distanceSq ≤ r := by
        simpa only [pointRows, transport_vector rows working forward hU] using hd
      exact ⟨⟨[pointRows rows t (forward.transpose * z)], fuel⟩,
        by simp only [replayAux, he, ite_true], by simp [Tree.nodes]⟩
  | outside z hd =>
    cases fuel with
    | zero => have := tree_nodes_pos (Tree.empty); omega
    | succ fuel =>
      have he : r < (pointRows rows t (forward.transpose * z)).distanceSq := by
        simpa only [pointRows, transport_vector rows working forward hU] using hd
      exact ⟨⟨[], fuel⟩, by simp only [replayAux, he, ite_true], by simp [Tree.nodes]⟩
  | empty k hk' z hempty =>
    cases fuel with
    | zero => have := tree_nodes_pos (Tree.empty); omega
    | succ fuel =>
      refine ⟨⟨[], fuel⟩, ?_, by simp [Tree.nodes]⟩
      simp only [replayAux, Fin.getElem_fin, hempty, beq_self_eq_true, ite_true]
  | node k hk' z interval children hi hl hc ih =>
    cases fuel with
    | zero => have := tree_nodes_pos (Hex.LatticeEnum.Tree.node interval children); omega
    | succ fuel =>
      have hsum : (children.map fun child => child.2.nodes).sum ≤ fuel := by
        rw [tree_nodes_node] at hf
        omega
      have hlength := children_nodes children
      have hsize : interval.size ≤ fuel := by
        have he := hl
        simp only [checkLabels, Bool.and_eq_true, beq_iff_eq] at he
        have he := he.1
        omega
      let visit := fun (a : Int) (tree : Tree) (fuel : Nat) =>
        replayAux rows t r forward p p.residual.normSq k (by omega) (z.set k a hk')
          (suffix p z (k + 1) + p.norms[k] * ((a : Rat) - p.centre z ⟨k, hk'⟩) *
            ((a : Rat) - p.centre z ⟨k, hk'⟩)) tree fuel
      have hv : ∀ a tree, (a, tree) ∈ children → ∀ fuel, tree.nodes ≤ fuel →
          ∃ result, visit a tree fuel = some result ∧ result.remaining = fuel - tree.nodes := by
        intro a tree hm fuel hf
        have h := ih a tree hm (by omega) fuel hf
        rwa [suffix_step] at h
      obtain ⟨result, hr, hrem⟩ := replay_children_accept visit children hv fuel [] hsum
      refine ⟨result, ?_, ?_⟩
      · rw [replayAux]
        simp only [Fin.getElem_fin]
        simp only [← hi]
        simp only [bne_self_eq_false, show ¬interval.size > fuel from not_lt.mpr hsize,
          decide_false, Bool.false_or, hl, Bool.not_true, Bool.false_eq_true, ite_false]
        exact hr
      · rw [tree_nodes_node]
        omega

/-- Every duplicate-free listing of the exact coefficient interval passes the label checker. -/
theorem checkLabels_complete (interval : Interval) (children : List (Int × Tree))
    (hn : (children.map Prod.fst).Nodup)
    (hm : ∀ a, a ∈ children.map Prod.fst ↔ interval.lo ≤ a ∧ a ≤ interval.hi) :
    checkLabels interval children = true := by
  let expected := (List.range interval.size).map (fun (i : Nat) => interval.lo + (i : Int))
  have he : expected.Nodup := by
    apply List.Nodup.map_on ?_ List.nodup_range
    intro i _ j _ hij
    omega
  have hp : (children.map Prod.fst).Perm expected :=
    (List.perm_ext_iff_of_nodup hn he).mpr (fun a => (hm a).trans (interval_labels interval a).symm)
  have hs : expected.Pairwise (fun a b => a ≤ b) := by
    apply List.pairwise_map.mpr
    exact List.pairwise_le_range.imp (fun h => by omega)
  have hsorted : ((children.map Prod.fst).mergeSort (fun a b => a ≤ b)).Pairwise (fun a b => a ≤ b) := by
    have h := List.pairwise_mergeSort (le := fun a b : Int => a ≤ b)
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (children.map Prod.fst)
    simpa only [decide_eq_true_eq] using h
  have heq := List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba) hsorted hs
    ((List.mergeSort_perm _ _).trans hp)
  simp only [checkLabels, Bool.and_eq_true, beq_iff_eq, Hex.List.sort_eq]
  exact ⟨by simpa [expected] using hp.length_eq, heq⟩

/-- A completed child run preserves the radius and provides an exhaustive subtree. -/
@[expose] def TreeResult (r : Rat) (P : Tree → Prop) (run : Traversal n m) : Prop :=
  run.state.radius = r ∧ (run.pending = [] ↔ run.tree.isSome = true) ∧
    ∀ tree, run.tree = some tree → P tree

/-- The child loop records exactly its consumed labels, with valid subtrees for each one. -/
theorem children_trees (z : Vector Int n) (cost : Rat) (k : Nat) (interval : Interval)
    (visit : Int → SearchState n m → Traversal n m) (P : Int → Tree → Prop) (r : Rat)
    (hv : ∀ a s, s.radius = r → TreeResult r (P a) (visit a s))
    (fuel : Nat) (cursor : Coefficients) (s : SearchState n m) (trees : List (Int × Tree))
    (hs : s.radius = r) (ht : ∀ a tree, (a, tree) ∈ trees → P a tree) :
    TreeResult r (fun tree => ∃ children, tree = .node interval children ∧
      children.map Prod.fst = trees.reverse.map Prod.fst ++ Coefficients.toList.go fuel cursor ∧
      ∀ a tree, (a, tree) ∈ children → P a tree)
      (traverseAux.children z cost true k interval visit fuel cursor s trees) := by
  induction fuel generalizing cursor s trees with
  | zero =>
    refine ⟨hs, by simp [traverseAux.children], ?_⟩
    intro tree he
    simp only [traverseAux.children, ite_true, Option.some.injEq] at he
    subst tree
    exact ⟨trees.reverse, rfl, by simp [Coefficients.toList.go], fun a tree hm => ht a tree (by simpa using hm)⟩
  | succ fuel ih =>
    cases hn : cursor.next? with
    | none =>
      refine ⟨by simpa [traverseAux.children, hn] using hs, by simp [traverseAux.children, hn], ?_⟩
      intro tree he
      simp only [traverseAux.children, hn, ite_true, Option.some.injEq] at he
      subst tree
      exact ⟨trees.reverse, rfl, by simp [Coefficients.toList.go, hn], fun a tree hm => ht a tree (by simpa using hm)⟩
    | some step =>
      rcases step with ⟨a, cursor'⟩
      have hchild := hv a s hs
      by_cases hempty : (visit a s).pending = []
      · obtain ⟨tree, he⟩ := Option.isSome_iff_exists.mp (hchild.2.1.mp hempty)
        have ht' : ∀ b child, (b, child) ∈ (a, tree) :: trees → P b child := by
          intro b child hm
          rcases List.mem_cons.mp hm with heq | hm
          · obtain ⟨hab, hct⟩ := Prod.mk.inj heq
            subst b
            subst child
            exact hchild.2.2 tree he
          · exact ht b child hm
        have htail := ih cursor' (visit a s).state ((a, tree) :: trees) hchild.1 ht'
        simp only [traverseAux.children, hn, hempty, List.isEmpty_nil, ite_true, he, Option.getD_some]
        refine ⟨htail.1, htail.2.1, ?_⟩
        intro result hr
        obtain ⟨children, hc, hl, hv⟩ := htail.2.2 result hr
        refine ⟨children, hc, ?_, hv⟩
        simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, Coefficients.toList.go,
          hn, List.append_assoc, List.singleton_append] using hl
      · have hnempty : (visit a s).pending.isEmpty = false := by simp [hempty]
        simp only [traverseAux.children, hn, hnempty, Bool.false_eq_true, ite_false, TreeResult]
        refine ⟨hchild.1, ?_, by simp⟩
        simp [hempty]

/-- Every completed fixed-radius traversal supplies a structurally exhaustive tree,
while every interrupted traversal retains pending work. -/
theorem traverse_exhaustive (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (budget : Budget)
    (k : Nat) (hk : k ≤ n) (z : Vector Int n) (s : SearchState n m) :
    TreeResult s.radius (Exhaustive b.rows t p.toData s.radius k z)
      (traverseAux b t p budget .ball p.residual.normSq k hk z (suffix p.toData z k) s) := by
  induction k generalizing z s with
  | zero =>
    rw [traverseAux]
    simp only [beq_self_eq_true, Bool.true_and, ite_true]
    split_ifs with hbudget hdist hanswers
    · simp [TreeResult]
    · refine ⟨rfl, by simp, ?_⟩
      intro tree ht
      cases Option.some.inj ht
      exact Exhaustive.outside z hdist
    · simp [TreeResult]
    · refine ⟨rfl, by simp, ?_⟩
      intro tree ht
      cases Option.some.inj ht
      exact Exhaustive.leaf z (le_of_not_gt hdist)
  | succ k ih =>
    rw [traverseAux]
    simp only [beq_self_eq_true, Bool.true_and, ite_true]
    split_ifs with hbudget hempty
    · simp [TreeResult]
    · refine ⟨rfl, by simp, ?_⟩
      intro tree ht
      cases Option.some.inj ht
      apply Exhaustive.empty k (by omega) z
      simpa only [beq_iff_eq, Fin.getElem_fin, Prepared.centre] using hempty
    · let interval := bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
          (s.radius - p.residual.normSq - suffix p.toData z (k + 1))
      let visit := fun a (state : SearchState n m) =>
        traverseAux b t p budget .ball p.residual.normSq k (by omega) (z.set k a (by omega))
          (suffix p.toData z (k + 1) + p.norms[k] *
            ((a : Rat) - p.centre z ⟨k, by omega⟩) * ((a : Rat) - p.centre z ⟨k, by omega⟩)) state
      let state : SearchState n m := { s with counts :=
        { s.counts with nodes := s.counts.nodes + 1, certificateNodes := s.counts.certificateNodes + 1 } }
      have hchildren := children_trees z (suffix p.toData z (k + 1)) k interval visit
        (fun a => Exhaustive b.rows t p.toData s.radius k (z.set k a (by omega))) s.radius
        (fun a state hs => by
          dsimp only [visit]
          have h := ih (by omega) (z.set k a (by omega)) state
          rw [suffix_step] at h
          simpa only [hs, Prepared.centre] using h)
        interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state [] rfl (by simp)
      change TreeResult s.radius _ (traverseAux.children z (suffix p.toData z (k + 1)) true k interval visit
        interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state [])
      refine ⟨hchildren.1, hchildren.2.1, ?_⟩
      intro tree ht
      obtain ⟨children, rfl, hlabels, hvalid⟩ := hchildren.2.2 tree ht
      apply Exhaustive.node k (by omega) z interval children rfl ?_ hvalid
      apply checkLabels_complete
      · rw [hlabels]
        simpa only [List.reverse_nil, List.map_nil, List.nil_append, Coefficients.toList, coefficients] using
          (coefficients_spec interval (p.centre z ⟨k, by omega⟩)).2
      · intro a
        rw [hlabels]
        simp only [List.reverse_nil, List.map_nil, List.nil_append]
        exact mem_coefficients interval (p.centre z ⟨k, by omega⟩) a

/-- Sorted reconstructed point lists with the same members are equal. -/
theorem sorted_points_eq (b : Basis n m) (t : Vector Rat m) (xs ys : List (Point n m))
    (hx : xs.Nodup) (hy : ys.Nodup) (hm : ∀ q, q ∈ xs ↔ q ∈ ys)
    (hr : ∀ q, q ∈ xs → q = point b t q.coefficients)
    (hs : xs.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt))
    (ht : ys.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt)) : xs = ys := by
  apply List.Perm.eq_of_pairwise ?_ hs ht ((List.perm_ext_iff_of_nodup hx hy).mpr hm)
  intro p q hp hq hpq hqp
  have hcompare := Std.OrientedCmp.isLE_antisymm
    (Ordering.isLE_iff_ne_gt.mpr hpq) (Ordering.isLE_iff_ne_gt.mpr hqp)
  have hlist := Std.LawfulEqOrd.eq_of_compare hcompare
  have hv : p.ambient = q.ambient := Vector.toList_inj.mp hlist
  have hpr := hr p hp
  have hqr := hr q ((hm q).mpr hq)
  have hpv := congrArg Point.ambient hpr
  have hqv := congrArg Point.ambient hqr
  have hz : p.coefficients = q.coefficients := vector_injective b (hpv.symm.trans (hv.trans hqv))
  rw [hpr, hqr, hz]

/-- An exhaustive original-basis tree and its complete sorted ball list always pass replay. -/
theorem certificate_accepts (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (r : Rat) (tree : Tree) (htree : Exhaustive b.rows t p.toData r n (Vector.replicate n 0) tree)
    (points : List (Point n m)) (hn : points.Nodup)
    (hm : ∀ q, q ∈ points ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r)
    (hs : points.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt)) :
    checkEnumeration b.rows t r
      ⟨b.rows, Hex.Matrix.identity n, Hex.Matrix.identity n, p.toData, tree, points⟩ = true := by
  have hidentity : Hex.Matrix.identity (R := Int) n * b.rows = b.rows := Hex.Matrix.identity_mul _
  obtain ⟨result, hresult, _⟩ := replay_accepts b.rows b.rows (Hex.Matrix.identity n) hidentity p.toData t r n
    (Nat.le_refl n) (Vector.replicate n 0) tree htree tree.nodes (Nat.le_refl _)
  rw [suffix_rank] at hresult
  have hspec := replay_spec b.rows b.rows (Hex.Matrix.identity n) p.toData t hp hidentity r n
    (Nat.le_refl n) (Vector.replicate n 0) tree tree.nodes result
  rw [suffix_rank] at hspec
  obtain ⟨hnd, hmem⟩ := hspec hresult
  have hmem' : ∀ q, q ∈ sortPoints result.points ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
    intro q
    simp only [sortPoints, Hex.List.sort_eq, List.mem_mergeSort, hmem]
    exact replay_root b b.rows (Hex.Matrix.identity n) (Hex.Matrix.identity n) hidentity hidentity t r _ q
  have heq : sortPoints result.points = points := by
    apply sorted_points_eq b t _ points ?_ hn (fun q => (hmem' q).trans (hm q).symm)
      (fun q hq => ((hmem' q).mp hq).1) (sortPoints_sorted _) hs
    unfold sortPoints
    rw [Hex.List.sort_eq]
    exact (List.mergeSort_perm _ _).symm.nodup hnd
  have hsame : Hex.Matrix.sameLatticeCert b.rows b.rows (Hex.Matrix.identity n) (Hex.Matrix.identity n) = true := by
    simp only [Hex.Matrix.sameLatticeCert, Bool.and_eq_true, Hex.Matrix.mulEqCert_iff, hidentity, and_self]
  have hd : p.toData.check b.rows t = true := (Data.check_iff _ _ _).mpr hp
  simp only [checkEnumeration, checkEnumerationWith, hsame, hd, Bool.true_and, replay, hresult, heq,
    decide_true]

/-- Certificates produced by native unbudgeted enumeration are accepted unconditionally. -/
theorem enumerationCertificate_check (b : Basis n m) (t : Vector Rat m) (r : Rat) :
    checkEnumeration b.rows t r (enumerationCertificate b t r) = true := by
  let p := prepare b t
  let run := traverse b t p {} .ball n (Nat.le_refl n) 0 0 { radius := r }
  have hball := ball_complete b t r
  have htree := traverse_exhaustive b t p {} n (Nat.le_refl n) 0 { radius := r }
  rw [suffix_rank] at htree
  obtain ⟨tree, he⟩ := Option.isSome_iff_exists.mp hball.2.1
  have hvalid := htree.2.2 tree he
  have hz : (Vector.replicate n (0 : Int)) = 0 := by ext i hi; simp
  rw [← hz] at hvalid
  have hcheck := certificate_accepts b t p (prepare_valid b t) r tree hvalid
    (enumerate b t r) (enumerate_nodup b t r) (enumerate_point_spec b t r) (enumerate_sorted b t r)
  simpa only [enumerationCertificate, he, Option.getD_some, enumerate] using hcheck

/-- The tie phase of optimization uses the same exhaustive fixed-radius tree producer. -/
theorem optimize_tree (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (budget : Budget)
    (mode : SearchMode) (seed : Point n m)
    (hphase : (optimize budget b t p mode seed).phase = .ties) (tree : Tree)
    (ht : (optimize budget b t p mode seed).traversal.tree = some tree) :
    Exhaustive b.rows t p.toData (optimize budget b t p mode seed).incumbent.distanceSq n 0 tree := by
  dsimp only [optimize] at hphase ht ⊢
  split_ifs at hphase ht ⊢ with hpending
  have h := traverse_exhaustive b t p budget n (Nat.le_refl n) 0
    { radius := ((traverse b t p budget mode n (Nat.le_refl n) 0 0
        { radius := seed.distanceSq, incumbent := some seed }).state.incumbent.getD seed).distanceSq,
      incumbent := some ((traverse b t p budget mode n (Nat.le_refl n) 0 0
        { radius := seed.distanceSq, incumbent := some seed }).state.incumbent.getD seed),
      counts := (traverse b t p budget mode n (Nat.le_refl n) 0 0
        { radius := seed.distanceSq, incumbent := some seed }).state.counts }
  rw [suffix_rank] at h
  exact h.2.2 tree ht

/-- Optimization's native tie-ball certificate is accepted without repeating the search. -/
theorem optimumCertificate_check (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (mode : SearchMode) (hmode : mode ≠ .ball) (seed : Point n m)
    (hseed : seed = point b t seed.coefficients) (heligible : Eligible mode seed) :
    let run := optimize {} b t p mode seed
    checkEnumeration b.rows t run.incumbent.distanceSq (optimumCertificate b p run).enumeration = true := by
  let run := optimize {} b t p mode seed
  obtain ⟨_, hphase, hball⟩ := optimize_spec b t p hp mode hmode seed hseed heligible
  obtain ⟨tree, ht⟩ := Option.isSome_iff_exists.mp hball.2.1
  have hvalid := optimize_tree b t p {} mode seed hphase tree ht
  have hz : (Vector.replicate n (0 : Int)) = 0 := by ext i hi; simp
  rw [← hz] at hvalid
  obtain ⟨fresh, hf, hn, hm⟩ := hball.2.2.2
  have hcheck := certificate_accepts b t p hp run.incumbent.distanceSq tree hvalid
    (sortPoints run.traversal.state.points) (by
      unfold sortPoints
      rw [Hex.List.sort_eq]
      apply (List.mergeSort_perm _ _).symm.nodup
      rw [hf]
      simpa using hn) (by
      intro q
      simp only [sortPoints, Hex.List.sort_eq, List.mem_mergeSort]
      rw [hf]
      simpa using hm q) (sortPoints_sorted _)
  simpa only [optimumCertificate, ht, Option.getD_some] using hcheck

/-- Every native closest-vector certificate passes its global-optimality checker. -/
theorem closestCertificate_check (b : Basis n m) (t : Vector Rat m) :
    checkClosest b.rows t (closestCertificate b t) = true := by
  let p := prepare b t
  let seed := babai b t
  let run := optimize {} b t p .closest seed
  obtain ⟨ho, _, hb⟩ := optimize_spec b t p (prepare_valid b t) .closest (by decide) seed rfl (Or.inl rfl)
  have hc := optimumCertificate_check b t p (prepare_valid b t) .closest (by decide) seed rfl (Or.inl rfl)
  change checkClosest b.rows t (optimumCertificate b p run) = true
  simp only [checkClosest, checkClosestWith, Bool.and_eq_true]
  refine ⟨⟨?_, hc⟩, ?_⟩
  · exact (decide_eq_true_eq).mpr ho.1
  · obtain ⟨fresh, hf, _, hm⟩ := hb.2.2.2
    simp only [optimumCertificate, List.all_eq_true, sortPoints, Hex.List.sort_eq, List.mem_mergeSort]
    intro q hq
    rw [hf] at hq
    have hq := (hm q).mp (by simpa using hq)
    apply beq_iff_eq.mpr
    exact le_antisymm hq.2 (ho.2.2 q hq.1 (Or.inl rfl))

/-- Every native positive-rank shortest-vector certificate passes its global-optimality checker. -/
theorem shortestCertificate_check (b : Basis n m) (cert : OptimumCertificate n m)
    (hcert : shortestCertificate b = some cert) : checkShortest b.rows cert = true := by
  obtain ⟨seed, hs, hc⟩ := Option.map_eq_some_iff.mp hcert
  subst cert
  obtain ⟨hseed, heligible, _⟩ := shortestSeed_spec b seed hs
  let p := prepare b 0
  let run := optimize {} b 0 p .shortest seed
  obtain ⟨ho, _, hb⟩ := optimize_spec b 0 p (prepare_valid b 0) .shortest (by decide)
    seed hseed (Or.inr heligible)
  have hc := optimumCertificate_check b 0 p (prepare_valid b 0) .shortest (by decide)
    seed hseed (Or.inr heligible)
  have hz : (Vector.replicate m (0 : Int)) = 0 := by ext i hi; simp
  have ht : (Vector.replicate m (0 : Rat)) = 0 := by ext i hi; simp
  change checkShortest b.rows (optimumCertificate b p run) = true
  simp only [checkShortest, checkShortestWith, hz, ht, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, hc⟩, ?_⟩
  · apply decide_eq_true_eq.mpr
    simpa [Eligible, optimumCertificate, run] using ho.2.1
  · exact decide_eq_true_eq.mpr ho.1
  · obtain ⟨fresh, hf, _, hm⟩ := hb.2.2.2
    simp only [optimumCertificate, List.all_eq_true, sortPoints, Hex.List.sort_eq, List.mem_mergeSort,
      Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    intro q hq
    by_cases hn : q.ambient = 0
    · exact Or.inl hn
    · rw [hf] at hq
      have hq := (hm q).mp (by simpa using hq)
      exact Or.inr (le_antisymm hq.2 (ho.2.2 q hq.1 (Or.inr hn)))

end HexLatticeEnumMathlib
