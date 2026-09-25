/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Induction
public import HexSignDet.Table
public import HexSignDetMathlib.QueryReduction
public import HexSturmMathlib.Soundness

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [Field K] [DecidableEq K] [LinearOrder K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)

/-- Signs in the original query order at one point. -/
@[expose] noncomputable def signsAt (qs : List (DensePoly E)) (x : K) : List Int :=
  qs.map fun q => (SignType.sign ((interpret f hz q).eval x) : Int)

/-- One observation per distinct root, retaining repeated sign conditions. -/
@[expose] noncomputable def rootObservations (p : DensePoly E) (qs : List (DensePoly E))
    (a b : Endpoint E) : List (List Int) :=
  (Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).toList.map (signsAt f hz qs)

/-- Root observations have the exact arity and ternary coordinates required
by finite support induction. No sign-table result is assumed. -/
theorem rootObservations_valid (p : DensePoly E) (qs : List (DensePoly E))
    (a b : Endpoint E) : Observations qs.length (rootObservations f hz p qs a b) := by
  rintro s hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  refine ⟨by simp [signsAt], ?_⟩
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  generalize SignType.sign ((interpret f hz q).eval x) = t
  cases t <;> simp

@[simp] theorem rootObservations_take (p : DensePoly E) (qs : List (DensePoly E))
    (a b : Endpoint E) (k : Nat) :
    rootObservations f hz p (qs.take k) a b =
      (rootObservations f hz p qs a b).map (List.take k) := by
  simp [rootObservations, signsAt, List.map_map, Function.comp_def]

@[simp] theorem rootObservations_drop (p : DensePoly E) (qs : List (DensePoly E))
    (a b : Endpoint E) (k : Nat) :
    rootObservations f hz p (qs.drop k) a b =
      (rootObservations f hz p qs a b).map (List.drop k) := by
  simp [rootObservations, signsAt, List.map_map, Function.comp_def]

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [IsStrictOrderedRing K] [IsRealClosed K]
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include h1 ha hs hm hnat hsign in
/-- Every accepted node's right-hand side is the actual root moment vector.
Both preprocessing and moment reduction are interpreted from their checked
identities; the query certificates need not come from a producer. -/
theorem Node.check_values {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (n : Node E Ctx)
    (checked : n.check sign context p a b qs = true) :
    n.system.values = SignDet.moments n.system.rows (rootObservations f hz p qs a b) := by
  apply Vector.ext
  intro i hi
  let j : Fin n.size := ⟨i, hi⟩
  have query := (HexSturmMathlib.check_sound f hz h1 ha hs hm hnat sign hsign
    context p _ a b _ _ (checkMoment_query (Node.check_moment checked j))).2
  change n.system.values[j] = _
  rw [query]
  simp only [SignDet.moments, Vector.getElem_ofFn, rootObservations, List.map_map,
    Function.comp_def, Tarski.rootSum_eq_sum]
  rw [Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro x hx
  have root := ((Tarski.mem_rootsIn _ _ _ x).mp hx).1
  have zero : (interpret f hz p).eval x = 0 := Polynomial.isRoot_of_mem_roots root
  rw [Node.check_sign f hz h1 ha hs hm sign
    (fun x => (HexSturmMathlib.sign_spec f sign hsign x).1)
    context p a b qs n checked j x zero]
  exact moment_entry f hz ha hm h1 qs n.system.rows[j] x

include h1 ha hs hm hnat hsign in
/-- Accepted child queries interpret the same roots with the exact query
slices used by the recursive support proof. -/
theorem Replay.check_interprets {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (t : Replay E Ctx)
    (checked : t.check sign context p a b qs = true) :
    t.Interprets qs.length (rootObservations f hz p qs a b) := by
  induction t generalizing qs with
  | leaf n =>
    exact Node.check_values f hz h1 ha hs hm hnat sign hsign context p a b qs n
      (Replay.check_node checked)
  | split n l r ihl ihr =>
    obtain ⟨hl, hr, _⟩ := Replay.check_children checked
    refine ⟨Node.check_values f hz h1 ha hs hm hnat sign hsign context p a b qs n
      (Replay.check_node checked), ?_, ?_⟩
    · simpa only [List.length_take, rootObservations_take] using ihl _ hl
    · simpa only [List.length_drop, rootObservations_drop] using ihr _ hr

include h1 ha hs hm hnat hsign in
/-- An arbitrary accepted replay retains exactly the realizable sign
conditions. Omitted conditions have no root; no invertible-minor argument
is used to assume completeness of its candidate support. -/
theorem Replay.check_support {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (t : Replay E Ctx)
    (checked : t.check sign context p a b qs = true) (s : List Int) :
    s ∈ t.node.system.support ↔
      ∃ x ∈ Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f), signsAt f hz qs x = s := by
  rw [t.support_iff checked (rootObservations_valid f hz p qs a b)
    (t.check_interprets f hz h1 ha hs hm hnat sign hsign context p a b qs checked)]
  simp only [rootObservations, List.mem_map, Finset.mem_toList]

include h1 ha hs hm hnat hsign in
/-- The stored integer counts equal the multiplicities of sign conditions
among distinct roots, including zero counts and empty supports. -/
theorem Replay.check_counts {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (t : Replay E Ctx)
    (checked : t.check sign context p a b qs = true) :
    counts t.node.system.columns (rootObservations f hz p qs a b) = t.node.system.counts := by
  exact (t.support_complete checked (rootObservations_valid f hz p qs a b)
    (t.check_interprets f hz h1 ha hs hm hnat sign hsign context p a b qs checked)).2

include h1 ha hs hm hnat hsign in
/-- Sparse lookup is the cardinality of the roots realizing the requested
sign condition, including zero for conditions omitted from the table. -/
theorem Replay.count_roots {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (t : Replay E Ctx)
    (checked : t.check sign context p a b qs = true) (s : List Int) :
    t.node.system.count s =
      ((Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).filter
        (fun x => signsAt f hz qs x = s)).card := by
  rw [← t.table_lookup checked, t.table_count checked (rootObservations_valid f hz p qs a b)
    (t.check_interprets f hz h1 ha hs hm hnat sign hsign context p a b qs checked)]
  simp only [rootObservations, List.countP_map]
  simpa [Function.comp_def] using (Finset.nodup_toList
    (Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f))).card_eq_countP
      (P := fun x => signsAt f hz qs x = s) |>.symm

end Hex.SignDet
