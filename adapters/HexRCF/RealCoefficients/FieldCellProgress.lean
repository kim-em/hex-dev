/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.ReplayCells
public import HexRCF.RealCoefficients.FieldBuildProgress
public section

namespace Hex.RCF.RealCoefficients

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable [ZPoly.CheckedIrreducible p]
local notation "E" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- Grouping monomials by the bound variable preserves the exact native field
polynomial, including coefficient and leading-term cancellation. The bounded
and complete producers can share this compilation while retaining the existing
explicit field checker. -/
theorem FieldSpecialize.grouped_eq (real : s.meetsRealAxis = true)
    (values : Fin n → E) (q : RealFormula.Poly (n + 1)) :
    RepresentationSpecialize.polynomial values q =
      FieldSpecialize.literalPolynomial values q := by
  let rep := Field.literalRep p s hw hp
  have same := Field.literalRep_mk p s hw hp
  have reality := Field.literalRep_real p s hw hp real
  let : Field E := PolyQuot.field p (SimpleRoot.ofSquare p s hw hp)
  have interpreted :
      HexPolyTheory.Interpret.interpret (Field.value rep)
        (Field.value_eq_zero rep same reality) (RepresentationSpecialize.polynomial values q) =
      HexPolyTheory.Interpret.interpret (Field.value rep)
        (Field.value_eq_zero rep same reality) (FieldSpecialize.literalPolynomial values q) := by
    apply Polynomial.funext
    intro x
    exact (RepresentationSpecialize.polynomial_eval (Field.value rep)
      (Field.value_eq_zero rep same reality) (Field.value_one rep same reality)
      (Field.value_add rep same reality) (Field.value_mul rep same reality)
      (Field.value_natCast rep same reality) (Field.value_neg rep same reality)
      values q x).trans
      ((FieldSpecialize.literalPolynomial_real rep same reality values q x).symm.trans
        (FieldCarrier.evaluate_interpret rep same reality x _))
  apply DensePoly.ext_coeff
  intro i
  apply (FieldSpecialize.realHom rep same reality).injective
  change Field.value rep _ = Field.value rep _
  simpa only [HexPolyTheory.Interpret.coeff_interpret] using
    congrArg (fun polynomial : Polynomial ℝ => polynomial.coeff i) interpreted

/-- A complete authenticated sign table certifies each actual nonzero leading
coefficient in the native exact field. This is a producer law; finite replay
continues to check these guards without assuming whole-field irreducibility. -/
theorem FieldTransport.leading_complete (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true) (q : DensePoly E)
    (present : (table.lookup? (q.coeff (q.size - 1))).isSome = true) :
    FieldTransport.leadingCheck table q = true := by
  unfold FieldTransport.leadingCheck FieldTransport.leadingWith QueryReplay.leading
  split
  · rfl
  · rename_i nonempty
    have leading : q.coeff (q.size - 1) ≠ 0 := by
      rw [← DensePoly.leadingCoeff_eq_coeff_last q (Nat.pos_of_ne_zero nonempty)]
      exact DensePoly.leadingCoeff_ne_zero_of_pos_size q (Nat.pos_of_ne_zero nonempty)
    have reality := FieldTransport.real table checked
    have nonzero : Field.value (Field.literalRep p s hw hp) (q.coeff (q.size - 1)) ≠ 0 :=
      fun zero => leading ((Field.value_eq_zero _
        (Field.literalRep_mk p s hw hp) reality _).mp zero)
    cases found : table.lookup? (q.coeff (q.size - 1)) with
    | none => simp [found] at present
    | some value =>
      have exactSign := Field.checkSignTable_lookup p s hw hp table checked
        (q.coeff (q.size - 1)) value found
      simp only [bne_iff_ne]
      rw [exactSign]
      intro zero
      apply nonzero
      cases sign : SignType.sign
          (Field.value (Field.literalRep p s hw hp) (q.coeff (q.size - 1))) with
      | neg => simp [sign] at zero
      | zero => exact sign_eq_zero_iff.mp sign
      | pos => simp [sign] at zero

/-- Native exact-field query acceptance supplies every finite replay gate
once its actual operand inventory is recorded in an authenticated table. -/
theorem FieldQuery.complete {Ctx : Type u} [DecidableEq Ctx]
    (table : LiteralSign.Table E) (checked : Field.checkSignTable p s hw hp table = true)
    (context : Ctx) (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E Ctx)
    (coverage : FieldQuery.covered table (FieldQuery.keys head a b cert) = true)
    (accepted : Sturm.check
      (fun x : E => (SignType.sign (Field.value (Field.literalRep p s hw hp) x) : Int))
      context head test a b value cert = true) :
    FieldQuery.check table context head test a b value cert = true := by
  have hits := List.all_eq_true.mp coverage
  have operands : FieldQuery.covered table (SignInputs.certificate head a b cert) = true := by
    apply List.all_eq_true.mpr
    intro key member
    apply hits key
    simp only [FieldQuery.keys, QueryReplay.keys, List.mem_append]
    exact Or.inl (Or.inl (Or.inl member))
  have top : FieldTransport.leadingCheck table head = true := by
    apply FieldTransport.leading_complete table checked
    apply hits (head.coeff (head.size - 1))
    simp [FieldQuery.keys, QueryReplay.keys]
  have squarefree : cert.squarefree.chain.all (FieldTransport.leadingCheck table) = true := by
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro q member
    apply FieldTransport.leading_complete table checked
    apply hits (q.coeff (q.size - 1))
    have present : q.coeff (q.size - 1) ∈
        cert.squarefree.chain.toList.map (fun q => q.coeff (q.size - 1)) :=
      List.mem_map.mpr ⟨q, by simpa using member, rfl⟩
    simp only [FieldQuery.keys, QueryReplay.keys, List.mem_append]
    exact Or.inl (Or.inr present)
  have remainders : cert.remainders.chain.all (FieldTransport.leadingCheck table) = true := by
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro q member
    apply FieldTransport.leading_complete table checked
    apply hits (q.coeff (q.size - 1))
    have present : q.coeff (q.size - 1) ∈
        cert.remainders.chain.toList.map (fun q => q.coeff (q.size - 1)) :=
      List.mem_map.mpr ⟨q, by simpa using member, rfl⟩
    simp only [FieldQuery.keys, QueryReplay.keys, List.mem_append]
    exact Or.inr present
  have same := SignInputs.certificate_check_congr (FieldQuery.cached table)
    (fun x : E => (SignType.sign (Field.value (Field.literalRep p s hw hp) x) : Int))
    context head test a b value cert (fun key member =>
      (FieldQuery.cached_eq table _ operands key member _).trans
        (Field.checkSignTable_spec p s hw hp table checked key))
  simp only [FieldQuery.check, FieldQuery.checkWith, QueryReplay.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨operands, top⟩, squarefree⟩, remainders⟩, same.trans accepted⟩

/-- Complete native isolation evidence passes the finite isolation checker
after its complete query inventory has been recorded. -/
theorem FieldIsolation.complete {Ctx : Type u} [DecidableEq Ctx]
    (table : LiteralSign.Table E) (checked : Field.checkSignTable p s hw hp table = true)
    (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (coverage : FieldQuery.covered table (FieldIsolation.keys head cert) = true)
    (accepted : cert.check
      (fun x : E => (SignType.sign (Field.value (Field.literalRep p s hw hp) x) : Int))
      FieldDecision.point context head = true) :
    FieldIsolation.check table context head cert = true := by
  simp only [IsolationReplay.check, Bool.and_eq_true] at accepted
  have hits := List.all_eq_true.mp coverage
  simp only [FieldIsolation.check, FieldIsolation.checkWith, Bool.and_eq_true]
  refine ⟨⟨accepted.1.1, ?_⟩, ?_⟩
  · apply FieldQuery.complete table checked context head 1 .negInf .posInf
      cert.isolations.intervals.size cert.total _ accepted.1.2
    apply List.all_eq_true.mpr
    intro key member
    apply hits key
    simp only [FieldIsolation.keys, List.mem_append]
    exact Or.inl member
  · apply List.all_eq_true.mpr
    intro i member
    apply FieldQuery.complete table checked context head 1 _ _ 1 cert.counts[i] _
      (List.all_eq_true.mp accepted.2 i member)
    apply List.all_eq_true.mpr
    intro key present
    apply hits key
    simp only [FieldIsolation.keys, List.mem_append]
    right
    exact List.mem_flatMap.mpr ⟨i, member, present⟩

/-- The actual row producer retains one row per atom occurrence in the
original order, including duplicates. This is stronger than find-first replay. -/
theorem FieldRootSigns.Table.build_entries {Ctx : Type u} [DecidableEq Ctx]
    (sign : E → Int) (context : Ctx) (head : DensePoly E)
    (cert : IsolationReplay E Ctx) (query : RealFormula.Poly n → DensePoly E)
    (formula : RealFormula.QF n)
    (table : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (built : FieldRootSigns.Table.build sign FieldDecision.point context head cert
      query formula = some table) :
    table.entries = formula.polys.map (fun atom =>
      ⟨atom, Vector.ofFn fun i => cert.queryAt sign FieldDecision.point context head
        (query atom) i⟩) := by
  unfold FieldRootSigns.Table.build at built
  dsimp only at built
  split at built
  · cases Option.some.inj built
    rfl
  · contradiction

/-- Every retained row from the actual producer passes finite replay. The
proof visits duplicate rows too and derives each query from the checked
isolation construction at that same selected interval. -/
theorem FieldRootSigns.Table.build_complete {Ctx : Type u} [DecidableEq Ctx]
    (signs : LiteralSign.Table E) (checked : Field.checkSignTable p s hw hp signs = true)
    (sign : E → Int)
    (sign_spec : ∀ x, sign x =
      (SignType.sign (Field.value (Field.literalRep p s hw hp) x) : Int))
    (context : Ctx) (head : DensePoly E) (intervals : IsolationCert)
    (cert : IsolationReplay E Ctx)
    (isolated : IsolationReplay.build sign FieldDecision.point context head intervals = some cert)
    (query : RealFormula.Poly n → DensePoly E) (formula : RealFormula.QF n)
    (table : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (built : FieldRootSigns.Table.build sign FieldDecision.point context head cert
      query formula = some table)
    (coverage : ∀ row ∈ table.entries, ∀ i : Fin cert.isolations.intervals.size,
      FieldQuery.covered signs (FieldQuery.keys head
        (.finite (PolyQuot.ofRat cert.isolations.intervals[i].lower.toRat))
        (.finite (PolyQuot.ofRat cert.isolations.intervals[i].upper.toRat)) row.evidence[i]) = true) :
    table.checkTransport signs context head cert.isolations.intervals.toVector query formula = true := by
  have entries := FieldRootSigns.Table.build_entries sign context head cert query formula table built
  let rep := Field.literalRep p s hw hp
  have same := Field.literalRep_mk p s hw hp
  have real := FieldTransport.real signs checked
  have accepted := (IsolationReplay.build_checked sign FieldDecision.point context head intervals cert isolated).2
  have chain := IsolationReplay.build_squarefree sign FieldDecision.point context head intervals cert isolated
  unfold FieldRootSigns.Table.checkTransport FieldRootSigns.Table.checkTransportWith
    FieldRootSigns.Table.checkRows
  rw [entries]
  simp only [List.map_map, Function.comp_def, List.map_id', decide_true, Bool.true_and]
  apply List.all_eq_true.mpr
  intro row rowMember
  obtain ⟨atom, atomMember, equality⟩ := List.mem_map.mp rowMember
  subst row
  apply List.all_eq_true.mpr
  intro i _
  have finite := coverage _ (by rw [entries]; exact List.mem_map.mpr ⟨atom, atomMember, rfl⟩) i
  simp only [Vector.getElem_ofFn, Fin.getElem_fin] at finite ⊢
  have native := IsolationReplay.queryAt_checked (Field.value rep)
    (Field.value_eq_zero rep same real) (Field.value_one rep same real)
    (Field.value_add rep same real) (Field.value_sub rep same real)
    (Field.value_mul rep same real) (Field.value_neg rep same real)
    (Field.value_inv rep same real) (Field.value_natCast rep same real)
    sign sign_spec FieldDecision.point context head (query atom) cert accepted chain i
  have sign_eq : sign = fun x : E =>
      (SignType.sign (Field.value (Field.literalRep p s hw hp) x) : Int) := funext sign_spec
  have changed := congrArg (fun oracle => Sturm.check oracle context head (query atom)
    (.finite (FieldDecision.point cert.isolations.intervals[i].lower))
    (.finite (FieldDecision.point cert.isolations.intervals[i].upper))
    (cert.queryAt sign FieldDecision.point context head (query atom) i).value
    (cert.queryAt sign FieldDecision.point context head (query atom) i)) sign_eq
  have replay := FieldQuery.complete signs checked context head (query atom) _ _ _ _ finite
    (by simpa only [FieldDecision.point, Fin.getElem_fin, Fin.eta] using changed.symm.trans native)
  have interval : cert.isolations.intervals.toVector[i.val] = cert.isolations.intervals[i.val] := by simp
  simpa only [FieldQuery.check, interval, Fin.getElem_fin, Fin.eta] using replay

/-- Native construction supplies the stronger finite cell envelope once all
of its exact operands are recorded. Root isolation and row production remain
the existing algorithms; none of these checks is an assumed semantic law. -/
theorem FieldCells.complete {Ctx : Type u} [DecidableEq Ctx]
    (signs : LiteralSign.Table E) (checked : Field.checkSignTable p s hw hp signs = true)
    (sign : E → Int)
    (sign_spec : ∀ x, sign x =
      (SignType.sign (Field.value (Field.literalRep p s hw hp) x) : Int))
    (context : Ctx) (query : RealFormula.Poly n → DensePoly E) (formula : RealFormula.QF n)
    (radical : RadicalCert E Ctx)
    (radical_checked : radical.check context
      (RepresentationCarrier.product (formula.polys.map query)) = true)
    (intervals : IsolationCert) (cert : IsolationReplay E Ctx)
    (isolated : IsolationReplay.build sign FieldDecision.point context radical.core intervals = some cert)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (built : FieldRootSigns.Table.build sign FieldDecision.point context radical.core cert
      query formula = some rows)
    (coverage : FieldQuery.covered signs
      (FieldCells.keys query formula radical.core cert rows) = true) :
    FieldCells.check signs context query formula radical cert rows = true := by
  have hits := List.all_eq_true.mp coverage
  have leading : formula.polys.all (fun atom =>
      FieldTransport.leadingCheck signs (query atom)) = true := by
    apply List.all_eq_true.mpr
    intro atom member
    apply FieldTransport.leading_complete signs checked
    apply hits ((query atom).coeff ((query atom).size - 1))
    simp only [FieldCells.keys, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨atom, member, rfl⟩)))
  have isolation_coverage : FieldQuery.covered signs (FieldIsolation.keys radical.core cert) = true := by
    apply List.all_eq_true.mpr
    intro key member
    apply hits key
    simp only [FieldCells.keys, List.mem_append]
    exact Or.inl (Or.inl (Or.inr member))
  have native := (IsolationReplay.build_checked sign FieldDecision.point context radical.core
    intervals cert isolated).2
  have sign_eq : sign = fun x : E =>
      (SignType.sign (Field.value (Field.literalRep p s hw hp) x) : Int) := funext sign_spec
  have same := congrArg (fun oracle =>
    cert.check oracle FieldDecision.point context radical.core) sign_eq
  have isolation_checked := FieldIsolation.complete signs checked context radical.core cert
    isolation_coverage (same.symm.trans native)
  have rows_checked := FieldRootSigns.Table.build_complete signs checked sign sign_spec
    context radical.core intervals cert isolated query formula rows built (by
      intro row rowMember i
      apply List.all_eq_true.mpr
      intro key member
      apply hits key
      simp only [FieldCells.keys, List.mem_append]
      apply Or.inl
      apply Or.inr
      apply List.mem_flatMap.mpr
      refine ⟨row, rowMember, ?_⟩
      exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, member⟩)
  have samples : FieldQuery.covered signs
      (SignInputs.openSamples FieldDecision.point cert (formula.polys.map query)) = true := by
    apply List.all_eq_true.mpr
    intro key member
    apply hits key
    simp only [FieldCells.keys, List.mem_append]
    exact Or.inr member
  change Field.checkSignTable p s hw hp signs &&
    formula.polys.all (fun atom => FieldTransport.leadingCheck signs (query atom)) &&
    radical.check context (RepresentationCarrier.product (formula.polys.map query)) &&
    FieldIsolation.check signs context radical.core cert &&
    rows.checkTransport signs context radical.core cert.isolations.intervals.toVector query formula &&
    FieldQuery.covered signs (SignInputs.openSamples FieldDecision.point cert
      (formula.polys.map query)) = true
  simp only [checked, leading, radical_checked, isolation_checked, rows_checked, samples]
  rfl

/-- Construct complete finite cell evidence directly from the grouped source
polynomials, using the existing radical, selected-field root and query
algorithms. Termination follows from their proved progress; the returned
envelope passes finite replay without assuming its acceptance. Every requested
original divisor has a recorded sign, independently of its nonvanishing. -/
def FieldCells.produce [RealAlgebraicNumber.Laws]
    (real : s.meetsRealAxis = true) {Ctx : Type u} [DecidableEq Ctx]
    (values : Fin n → E) (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (guards : List E := []) (depth : Nat := 256) :
    {data : FieldBuild.Result p s hw hp Ctx (n + 1) //
      FieldCells.check data.signs context (RepresentationSpecialize.polynomial values)
        formula data.radical data.isolation data.rootSigns = true ∧
      ∀ key ∈ guards, (data.signs.lookup? key).isSome = true} := by
  let rep := Field.literalRep p s hw hp
  have same := Field.literalRep_mk p s hw hp
  have reality := Field.literalRep_real p s hw hp real
  let query := RepresentationSpecialize.polynomial values
  let product := RepresentationCarrier.product (formula.polys.map query)
  have nonzero := RepresentationCarrier.product_ne_zero (Field.value rep)
    (Field.value_eq_zero rep same reality) (Field.value_one rep same reality)
    (Field.value_add rep same reality) (Field.value_mul rep same reality)
    (formula.polys.map query)
  let radicalProposal := RadicalCert.buildMonic context product
  have radicalAvailable : radicalProposal.isSome = true := by
    obtain ⟨cert, built⟩ := RadicalCert.buildMonic_success_real
      (Field.value rep) (Field.value_eq_zero rep same reality)
      (Field.value_one rep same reality) (Field.value_add rep same reality)
      (Field.value_sub rep same reality) (Field.value_mul rep same reality)
      (Field.value_div rep same reality) (Field.value_inv rep same reality)
      (Field.value_natCast rep same reality) context product nonzero
    change (RadicalCert.buildMonic context product).isSome = true
    rw [built]
    rfl
  let radical := radicalProposal.get radicalAvailable
  have radicalBuilt : RadicalCert.buildMonic context product = some radical :=
    Option.eq_some_of_isSome radicalAvailable
  have radicalChecked := RadicalCert.buildMonic_checked context product radical radicalBuilt
  have squarefree := RadicalCert.buildMonic_squarefree (Field.value rep)
    (Field.value_eq_zero rep same reality) (Field.value_sub rep same reality)
    (Field.value_mul rep same reality) (Field.value_div rep same reality)
    (Field.value_inv rep same reality) (Field.value_natCast rep same reality)
    context product radical radicalBuilt
  let prepared := Field.prepareSign p s hw hp real
  let sign := fun x : E => Sturm.queryPrepared prepared.val x.coeffs
  have sign_spec : ∀ x, sign x = (SignType.sign (Field.value rep x) : Int) :=
    Field.prepareSign_spec p s hw hp real
  have sign_eq : sign = FieldBuild.proposalSign rep same := by
    funext x
    exact (sign_spec x).trans (FieldBuild.proposalSign_spec rep same reality x).symm
  let isolation := FieldBuild.isolateUsing rep same reality context radical.core
    (RadicalCert.core_ne_zero context product radical radicalChecked)
    squarefree sign sign_eq depth
  have isolation_built : ∃ intervals,
      IsolationReplay.build sign FieldDecision.point context radical.core
        intervals = some isolation.val := by
    obtain ⟨intervals, builtIsolation⟩ := isolation.property.2
    refine ⟨intervals, ?_⟩
    rw [sign_eq]
    exact builtIsolation
  let proposal := FieldRootSigns.Table.build sign FieldDecision.point context radical.core
    isolation.val query formula
  have available : proposal.isSome = true := by
    obtain ⟨intervals, isolated⟩ := isolation_built
    obtain ⟨table, built⟩ := FieldRootSigns.Table.build_success (Field.value rep)
      (Field.value_eq_zero rep same reality) (Field.value_one rep same reality)
      (Field.value_add rep same reality) (Field.value_sub rep same reality)
      (Field.value_mul rep same reality) (Field.value_neg rep same reality)
      (Field.value_inv rep same reality) (Field.value_natCast rep same reality)
      sign sign_spec FieldDecision.point context radical.core intervals isolation.val
      isolated query formula
    change (FieldRootSigns.Table.build sign FieldDecision.point context radical.core
      isolation.val query formula).isSome = true
    rw [built]
    rfl
  let rows := proposal.get available
  have builtRows : FieldRootSigns.Table.build sign FieldDecision.point context radical.core
      isolation.val query formula = some rows := Option.eq_some_of_isSome available
  let keys := FieldCells.keys query formula radical.core isolation.val rows ++ guards
  let signProposal := FieldBuild.buildTable p s hw hp keys
  have signAvailable : signProposal.isSome = true := by
    obtain ⟨table, built⟩ := FieldBuild.buildTable_success p s hw hp real keys
    change (FieldBuild.buildTable p s hw hp keys).isSome = true
    rw [built]
    rfl
  let signs := signProposal.get signAvailable
  have builtSigns : FieldBuild.buildTable p s hw hp keys = some signs :=
    Option.eq_some_of_isSome signAvailable
  have header := FieldBuild.buildTable_checked p s hw hp keys signs builtSigns
  refine ⟨⟨radical, isolation.val, rows, signs⟩, ?_, ?_⟩
  · obtain ⟨intervals, isolated⟩ := isolation_built
    apply FieldCells.complete signs header sign sign_spec context query formula
      radical radicalChecked intervals isolation.val isolated rows builtRows
    apply List.all_eq_true.mpr
    intro key member
    exact FieldBuild.buildTable_lookup p s hw hp keys signs builtSigns key
      (List.mem_append_left _ member)
  · intro key member
    exact FieldBuild.buildTable_lookup p s hw hp keys signs builtSigns key
      (List.mem_append_right _ member)

omit [ZPoly.CheckedIrreducible p] in
/-- An accepted finite envelope gives a defined strict Boolean result for
either quantifier, including false. Actual ordinary real cells establish both
totality of the fold and agreement with the fixed source sentence. -/
theorem Replay.Input.cellValue_spec {Ctx : Type u} [DecidableEq Ctx]
    (input : Replay.Input p s hw hp Ctx n)
    (data : FieldBuild.Result p s hw hp Ctx (n + 1))
    (checked : FieldCells.check data.signs input.context
      (RepresentationSpecialize.polynomial input.values) input.formula
      data.radical data.isolation data.rootSigns = true) :
    ∃ value, input.cellValue data = some value ∧ (value = true ↔ input.toProp) := by
  have header := FieldCells.signs_checked data.signs input.context
    (RepresentationSpecialize.polynomial input.values) input.formula
    data.radical data.isolation data.rootSigns checked
  let valuation := fun x : ℝ => RealFormula.append
    (fun j => Field.value (Field.literalRep p s hw hp) (input.values j)) x
  have specialization := FieldCells.specialize data.signs header input.values
  obtain ⟨roots, ordered, meanings⟩ := FieldCells.cells data.signs input.context
    (RepresentationSpecialize.polynomial input.values) input.formula
    data.radical data.isolation data.rootSigns valuation specialization checked
  cases quantifier : input.quantifier with
  | forallReal =>
    obtain ⟨value, folded, semantic⟩ := RealCoefficients.forall_decision roots ordered
      input.formula valuation (Decision.cellSign (FieldQuery.cached data.signs)
        FieldDecision.point (RepresentationSpecialize.polynomial input.values)
        data.isolation (data.rootSigns.value data.isolation.total)) meanings
    exact ⟨value, by simpa only [Replay.Input.cellValue, quantifier] using folded,
      by simpa only [Replay.Input.toProp, quantifier, valuation] using semantic⟩
  | existsReal =>
    obtain ⟨value, folded, semantic⟩ := RealCoefficients.exists_decision roots ordered
      input.formula valuation (Decision.cellSign (FieldQuery.cached data.signs)
        FieldDecision.point (RepresentationSpecialize.polynomial input.values)
        data.isolation (data.rootSigns.value data.isolation.total)) meanings
    exact ⟨value, by simpa only [Replay.Input.cellValue, quantifier] using folded,
      by simpa only [Replay.Input.toProp, quantifier, valuation] using semantic⟩

/-- An authenticated complete table records a nonzero sign for every native
nonzero divisor. This producer law is separate from finite replay soundness. -/
theorem FieldTransport.lookup_complete (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true) (a : E)
    (present : (table.lookup? a).isSome = true) (nonzero : a ≠ 0) :
    (table.lookup? a).any (fun value => Decidable.decide (value ≠ 0)) = true := by
  cases found : table.lookup? a with
  | none => simp [found] at present
  | some value =>
    have exactSign := Field.checkSignTable_lookup p s hw hp table checked a value found
    have interpreted : Field.value (Field.literalRep p s hw hp) a ≠ 0 := fun zero =>
      nonzero ((Field.value_eq_zero _ (Field.literalRep_mk p s hw hp)
        (FieldTransport.real table checked) a).mp zero)
    simp only [Option.any_some, decide_eq_true_eq]
    rw [exactSign]
    intro zero
    apply interpreted
    cases sign : SignType.sign (Field.value (Field.literalRep p s hw hp) a) with
    | neg => simp [sign] at zero
    | zero => exact sign_eq_zero_iff.mp sign
    | pos => simp [sign] at zero

namespace Replay

variable {Ctx : Type u} [DecidableEq Ctx]

/-- Total algebraic production for grouped source polynomials. Original zero
divisors reject before any root work. The direct-depth parameter chooses a
starting strategy, rather than a mathematical limit on the complete search. -/
def buildCellsTotal [RealAlgebraicNumber.Laws] (input : Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth : Nat := 256) :
    Except BuildError (Certificate p s hw hp Ctx n) :=
  if input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) then
    .ok ⟨input, (FieldCells.produce real input.values input.formula input.context
      input.divisors depth).val⟩
  else .error .divisor

/-- Every result from the complete algebraic producer passes finite replay
with its actual verdict. There is no accepted-certificate premise or unproved
root/sign oracle. Replay itself requires no common-field irreducibility. -/
theorem buildCellsTotal_checked [RealAlgebraicNumber.Laws]
    (input : Input p s hw hp Ctx n) (real : s.meetsRealAxis = true) (depth : Nat)
    (cert : Certificate p s hw hp Ctx n)
    (built : buildCellsTotal input real depth = .ok cert) :
    ∃ value, checkCells input cert = .ok value := by
  unfold buildCellsTotal at built
  split at built
  · rename_i domains
    have same := Except.ok.inj built
    subst cert
    let produced := FieldCells.produce real input.values input.formula input.context
      input.divisors depth
    let data := produced.val
    have checked : FieldCells.check data.signs input.context
        (RepresentationSpecialize.polynomial input.values) input.formula
        data.radical data.isolation data.rootSigns = true := produced.property.1
    have header := FieldCells.signs_checked data.signs input.context
      (RepresentationSpecialize.polynomial input.values) input.formula
      data.radical data.isolation data.rootSigns checked
    have guards : input.divisors.all (fun divisor =>
        (data.signs.lookup? divisor).any (fun value => Decidable.decide (value ≠ 0))) = true := by
      apply List.all_eq_true.mpr
      intro divisor member
      exact FieldTransport.lookup_complete data.signs header divisor
        (produced.property.2 divisor member)
        (by simpa using List.all_eq_true.mp domains divisor member)
    obtain ⟨value, folded, _⟩ := input.cellValue_spec data checked
    refine ⟨value, ?_⟩
    change checkCells input ⟨input, data⟩ = .ok value
    simp only [checkCells, Input.matches_self, guards, checked, Bool.not_true,
      Bool.false_eq_true, ite_false, folded]
  · contradiction

/-- Every algebraic input with valid original divisors produces a certificate
accepted with the exact true or false real meaning. Finite replay soundness
continues to derive degrees, complete roots and ordinary real sample points. -/
theorem buildCellsTotal_spec [RealAlgebraicNumber.Laws]
    (input : Input p s hw hp Ctx n) (real : s.meetsRealAxis = true) (depth : Nat)
    (domains : ∀ divisor ∈ input.divisors, divisor ≠ 0) :
    ∃ cert value, buildCellsTotal input real depth = .ok cert ∧
      checkCells input cert = .ok value ∧ (value = true ↔ input.toProp) := by
  have guards : input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) = true :=
    List.all_eq_true.mpr (fun divisor member => by simpa using domains divisor member)
  let cert : Certificate p s hw hp Ctx n := ⟨input,
    (FieldCells.produce real input.values input.formula input.context input.divisors depth).val⟩
  have built : buildCellsTotal input real depth = .ok cert := by
    simp only [buildCellsTotal, guards, ↓reduceIte, cert]
  obtain ⟨value, checked⟩ := buildCellsTotal_checked input real depth cert built
  exact ⟨cert, value, built, checked, checkCells_spec input cert value checked⟩

end Replay

end Hex.RCF.RealCoefficients
