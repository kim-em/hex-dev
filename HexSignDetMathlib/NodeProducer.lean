/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RationalSolve
public import HexSignDetMathlib.Basis

public section

namespace Hex.SignDet

/-- Successful rational solving preserves the input orders and returns an
accepted finite system, regardless of the supplied moment values. -/
theorem solveSystem_spec {r arity : Nat} {rows : Vector (List Nat) r}
    {columns : Vector (List Int) r} {values : Vector Int r} {s : System r}
    (h : solveSystem arity rows columns values = .ok s) :
    s.rows = rows ∧ s.columns = columns ∧ s.values = values ∧ s.check arity = true := by
  unfold solveSystem at h
  cases hi : Matrix.inverse? (Matrix.ofFn fun (i j : Fin r) =>
      (entry rows[i] columns[j] : Rat)) with
  | none => simp only [hi, bind, Except.bind] at h; contradiction
  | some inv =>
    simp only [hi, bind, Except.bind] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · rename_i hc
          cases h
          exact ⟨rfl, rfl, rfl, hc⟩
        · contradiction

/-- The scaled solver retains exactly the supplied matrix and denominator,
and every successful return passes the finite system checker. -/
theorem solveScaled_spec {r arity : Nat} {rows : Vector (List Nat) r}
    {columns : Vector (List Int) r} {values : Vector Int r}
    {denominator : Int} {inverse : Matrix Int r r} {s : System r}
    (h : solveScaled arity rows columns values denominator inverse = .ok s) :
    s.rows = rows ∧ s.columns = columns ∧ s.values = values ∧
      s.denominator = denominator ∧ s.inverse = inverse ∧ s.check arity = true := by
  unfold solveScaled at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · rename_i hc
          cases h
          exact ⟨rfl, rfl, rfl, rfl, rfl, hc⟩
        · contradiction

private theorem list_transport {α : Type*} {m n : Nat} (h : m = n) (v : Vector α n) :
    (h ▸ v : Vector α m).toList = v.toList := by
  cases h
  rfl

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]

/-- Every returned node binds the supplied domain and query list, has a
checked integer system, and retains the actual rank producer's certificate. -/
theorem buildNode_spec (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int))
    (reduced : Bool) (inverse : Option (Int × Matrix Int rows.length rows.length))
    (preparation : Option (QueryReduction E)) {n : Node E Ctx}
    (h : buildNode context domain qs rows columns reduced inverse preparation = .ok n) :
    n.context = context ∧ n.head = domain.head ∧ n.lower = domain.lower ∧
      n.upper = domain.upper ∧ n.queries = qs ∧ n.system.rows.toList = rows ∧
      n.system.columns.toList = columns ∧ n.system.check qs.length = true ∧
      n.basis = Matrix.rankCert n.system.retainedMatrix := by
  unfold buildNode at h
  dsimp only at h
  split at h
  · rename_i hdim
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i s hs
          cases h
          have hf : s.rows.toList = rows ∧ s.columns.toList = columns ∧
              s.check qs.length = true := by
            cases inverse with
            | none =>
              have hh := solveSystem_spec hs
              refine ⟨?_, ?_, hh.2.2.2⟩
              · rw [hh.1]; simp
              · rw [hh.2.1]
                simpa using list_transport hdim (columns.toArray.toVector : Vector _ columns.length)
            | some pair =>
              have hh := solveScaled_spec hs
              refine ⟨?_, ?_, hh.2.2.2.2.2⟩
              · rw [hh.1]; simp
              · rw [hh.2.1]
                simpa using list_transport hdim (columns.toArray.toVector : Vector _ columns.length)
          exact ⟨rfl, rfl, rfl, rfl, rfl, hf.1, hf.2.1, hf.2.2, rfl⟩
  · contradiction

/-- Each returned moment is the prepared query of the actual indexed operand;
the solver uses its literal value. Reductions are tied to the same row. -/
theorem buildNode_evidence (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int))
    (reduced : Bool) (inverse : Option (Int × Matrix Int rows.length rows.length))
    (preparation : Option (QueryReduction E)) {n : Node E Ctx}
    (h : buildNode context domain qs rows columns reduced inverse preparation = .ok n) :
    n.preparation = (if useReduction reduced domain then
      match preparation with
      | some r => some r
      | none => some (QueryReduction.build domain.sign domain.head qs)
      else none) ∧
    ∀ i : Fin n.size,
      n.reductions[i] = (if useReduction reduced domain then
        some (Reduction.build domain.sign domain.head
          (QueryReduction.operands qs n.preparation) n.system.rows[i]) else none) ∧
      n.moments[i] = Sturm.certifyPrepared context domain
        (queryPoly (QueryReduction.operands qs n.preparation) n.system.rows[i] n.reductions[i]) ∧
      n.system.values[i] = n.moments[i].value := by
  unfold buildNode at h
  dsimp only at h
  split at h
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i s hs
          cases h
          cases inverse with
          | none =>
            have hh := solveSystem_spec hs
            refine ⟨rfl, fun i => ?_⟩
            simp only [hh.1, hh.2.2.1, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn]
            trivial
          | some pair =>
            have hh := solveScaled_spec hs
            refine ⟨rfl, fun i => ?_⟩
            simp only [hh.1, hh.2.2.1, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn]
            trivial
  · contradiction

omit [Neg E] [Inv E] in
/-- The actual retained rank certificate discharges every matrix guard in
local replay. Polynomial query and preprocessing evidence remain explicit. -/
theorem Node.check_of_basis [DecidableEq Ctx] (sign : E → Int) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (qs : List (DensePoly E)) (n : Node E Ctx)
    (hb : n.context = context ∧ n.head = p ∧ n.lower = lo ∧ n.upper = hi ∧ n.queries = qs)
    (hs : n.system.check qs.length = true)
    (hr : n.basis = Matrix.rankCert n.system.retainedMatrix)
    (hp : (match n.preparation with | none => true | some r => r.check sign p qs) = true)
    (hm : ∀ i : Fin n.size, checkMoment sign context p lo hi
      (QueryReduction.operands qs n.preparation) n.system.rows[i] n.system.values[i]
      n.moments[i] n.reductions[i] = true) :
    n.check sign context p lo hi qs = true := by
  simp only [Node.check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hb, hs⟩, ?_⟩, ?_⟩,
    ⟨⟨⟨?_, ?_⟩, hp⟩, List.all_eq_true.mpr (fun i _ => hm i)⟩⟩
  · rw [hr]; exact n.system.basis_rank hs
  · rw [hr]; exact n.system.basis_columns hs
  · rw [hr]; exact n.system.basis_checks
  · rw [hr]; exact n.system.basis_inverse

end Hex.SignDet
