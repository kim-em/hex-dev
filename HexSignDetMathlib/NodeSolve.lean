/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.NodeProducer
public import HexSignDetMathlib.Solve
public import HexSignDetMathlib.ParentSystem

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]

/-- A checked candidate system with the actual queried moment values makes
node construction succeed. The finite system can be supplied by the complete
leaf or child-product constructions; this lemma does not infer support or
query semantics from its matrix equations. -/
theorem buildNode_complete (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int))
    (reduced : Bool) (inverse : Option (Int × Matrix Int rows.length rows.length))
    (preparation : Option (QueryReduction E)) (s : System rows.length)
    (hrows : s.rows.toList = rows) (hcols : s.columns.toList = columns)
    (hvalid : s.check qs.length = true)
    (hinv : ∀ d a, inverse = some (d, a) → d = s.denominator ∧ a = s.inverse)
    (hvalues :
      let prep := nodePreparation reduced domain qs preparation
      let operands := QueryReduction.operands qs prep
      ∀ i : Fin rows.length,
        (Sturm.certifyPrepared context domain (queryPoly operands s.rows[i]
          (nodeReduction reduced domain operands s.rows[i]))).value =
          s.values[i]) :
    ∃ n, buildNode context domain qs rows columns reduced inverse preparation = .ok n ∧
      n.system.counts.toList = s.counts.toList := by
  have hdim : rows.length = columns.length := by
    simpa using congrArg List.length hcols
  have hes : rows.toArray.toVector = s.rows := by
    apply Vector.toList_inj.mp
    simpa using hrows.symm
  have hcs : (hdim ▸ columns.toArray.toVector : Vector (List Int) rows.length) = s.columns := by
    apply Vector.toList_inj.mp
    exact (list_transport hdim (columns.toArray.toVector : Vector _ columns.length)).trans
      (by simpa using hcols.symm)
  have hh := hvalid
  simp only [System.check, Bool.and_eq_true] at hh
  have hr : rows.all (fun e => decide (e.length = qs.length) && e.all (· ≤ 2)) = true := by
    rw [← hrows]
    exact hh.1.1.1.1.1
  have hc : columns.all (fun c => decide (c.length = qs.length) &&
      c.all (fun x => decide (x = -1 ∨ x = 0 ∨ x = 1))) = true := by
    rw [← hcols]
    exact hh.1.1.1.1.2
  have hd : decide columns.Nodup = true := by
    rw [← hcols]
    exact hh.1.1.1.2
  let prep := nodePreparation reduced domain qs preparation
  let operands := QueryReduction.operands qs prep
  let reductions := s.rows.map (nodeReduction reduced domain operands)
  let certs : Vector (TarskiCertificate E E Ctx) rows.length := Vector.ofFn fun i =>
    Sturm.certifyPrepared context domain (queryPoly operands s.rows[i] reductions[i])
  have hv : certs.map (fun c => c.value) = s.values := by
    apply Vector.ext
    intro i hi
    simpa only [certs, reductions, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn] using
      hvalues ⟨i, hi⟩
  have solved : ∃ u, (match inverse with
      | none => solveSystem qs.length s.rows s.columns s.values
      | some (d, a) => solveScaled qs.length s.rows s.columns s.values d a) = .ok u ∧
      u.counts = s.counts := by
    cases inverse with
    | none =>
      obtain ⟨u, hu, _, _, _, hcounts, _⟩ := solveSystem_complete s hvalid
      exact ⟨u, hu, hcounts⟩
    | some pair =>
      obtain ⟨d, a⟩ := pair
      obtain ⟨hd, ha⟩ := hinv d a rfl
      exact ⟨s, by simpa only [hd, ha] using solveScaled_eq s hvalid, rfl⟩
  obtain ⟨u, hu, hcounts⟩ := solved
  simp only [buildNode, hdim, ↓reduceDIte, hr, hc, hd, Bool.not_true,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, hes, hcs]
  change ∃ n : Node E Ctx, (match (match inverse with
      | none => solveSystem qs.length s.rows s.columns (certs.map fun (c : TarskiCertificate E E Ctx) => c.value)
      | some (d, a) => solveScaled qs.length s.rows s.columns (certs.map fun (c : TarskiCertificate E E Ctx) => c.value) d a) with
      | .error err => Except.error err
      | .ok u => Except.ok ({
          context := context
          head := domain.head
          lower := domain.lower
          upper := domain.upper
          queries := qs
          size := rows.length
          system := u
          moments := certs
          reductions := reductions
          preparation := prep
          basis := Matrix.rankCert u.retainedMatrix} : Node E Ctx)) = Except.ok n ∧
    n.system.counts.toList = s.counts.toList
  rw [hv, hu]
  exact ⟨_, rfl, congrArg Vector.toList hcounts⟩

omit [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] in
/-- The finite child-product system has exactly the dimension and transported
inverse supplied by `buildTreeFrom` to `buildNode_complete`. No permutation,
new inverse search or root-sum premise is needed for this adapter. -/
theorem Node.parent_system (l r : Node E Ctx) {a b : Nat}
    (hl : l.system.check a = true) (hr : r.system.check b = true)
    (hbl : l.basis = Matrix.rankCert l.system.retainedMatrix)
    (hbr : r.basis = Matrix.rankCert r.system.retainedMatrix)
    (xs : List (List Int))
    (cl : ∀ x ∈ xs, x.take a ∈ l.system.support)
    (cr : ∀ x ∈ xs, x.drop a ∈ r.system.support) :
    ∃ s : System (product l.rows r.rows).length,
      s.rows.toList = product l.rows r.rows ∧
      s.columns.toList = product l.system.support r.system.support ∧
      s.check (a + b) = true ∧
      s.denominator = l.basis.denom * r.basis.denom ∧
      s.inverse = (by
        have hd : (product l.rows r.rows).length = l.basis.rank * r.basis.rank := by
          rw [length_product]
          simp [Node.rows]
        exact hd.symm ▸ tensor l.basis.adj r.basis.adj) ∧
      s.counts.toList = (counts (productVector l.basisCols r.basisCols) xs).toList ∧
      s.values.toList = (SignDet.moments (productVector l.basisRows r.basisRows) xs).toList := by
  have transport {m n : Nat} (h : m = n) (s : System m) (arity : Nat) :
      (h ▸ s : System n).rows.toList = s.rows.toList ∧
      (h ▸ s : System n).columns.toList = s.columns.toList ∧
      (h ▸ s : System n).check arity = s.check arity ∧
      (h ▸ s : System n).denominator = s.denominator ∧
      (h ▸ s : System n).inverse = (h ▸ s.inverse : Matrix Int n n) ∧
      (h ▸ s : System n).counts.toList = s.counts.toList ∧
      (h ▸ s : System n).values.toList = s.values.toList := by
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd : (product l.rows r.rows).length = l.basis.rank * r.basis.rank := by
    rw [length_product]
    simp [Node.rows]
  let s := System.mk (productVector l.basisRows r.basisRows)
    (productVector l.basisCols r.basisCols)
    (counts (productVector l.basisCols r.basisCols) xs)
    (SignDet.moments (productVector l.basisRows r.basisRows) xs)
    (tensor l.basis.adj r.basis.adj) (l.basis.denom * r.basis.denom)
  obtain ⟨hrows, hcols, hcheck, hden, hinv, hcounts, hvalues⟩ := transport hd.symm s (a + b)
  obtain ⟨rowsEq, colsEq, _⟩ := l.product_inverse r hl hr hbl hbr
  exact ⟨hd.symm ▸ s, hrows.trans rowsEq, hcols.trans colsEq,
    hcheck.trans (l.product_system r hl hr hbl hbr xs cl cr),
    hden, hinv, hcounts, hvalues⟩

end Hex.SignDet
