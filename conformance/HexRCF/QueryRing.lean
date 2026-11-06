/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.QueryReplay
public import HexRCF.RealCoefficients.IntervalSign
public meta import HexRCF.RealCoefficients.QueryReplay
public meta import HexRCF.RealCoefficients.IntervalSign
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import Lean.Elab.Command
public section

set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Hex.RCF.QueryRing
open RealCoefficients HexPolyTheory.Interpret

abbrev E := DensePoly Rat

@[expose] def parameter : E := DensePoly.ofList [0, 1]
@[expose] def head : DensePoly E := DensePoly.ofList [-parameter, 0, 1]
@[expose] def test : DensePoly E := 1
@[expose] def lower : Endpoint E := .finite (DensePoly.C 1)
@[expose] def upper : Endpoint E := .finite (DensePoly.C 2)

/-- Fixed literal bounds in this coefficient-ring test. They require no
inverse operation on the representation and no root or sign search. -/
@[expose] def lookup (q : E) : Option Int := IntervalSign.sign? q 2 2

noncomputable def read (q : E) : ℝ :=
  (interpret (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero) q).eval 2

private theorem read_zero : read 0 = 0 := by simp [read]

private theorem read_one : read 1 = 1 := by
  simp only [read, interpret_one (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by norm_num), Polynomial.eval_one]

theorem read_closed : Hex.RealClosure.Transport.Closed read (fun _ => True) where
  zero := trivial
  one := trivial
  add := fun _ _ _ _ => trivial
  mul := fun _ _ _ _ => trivial
  sub := fun _ _ _ _ => trivial
  natCast := fun _ => trivial
  read_zero := read_zero
  read_one := read_one
  read_add := fun a b _ _ => by
    simp only [read, interpret_add (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (fun a b => Rat.cast_add a b), Polynomial.eval_add]
  read_mul := fun a b _ _ => by
    simp only [read, interpret_mul (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (fun a b => Rat.cast_add a b)
      (fun a b => Rat.cast_mul a b), Polynomial.eval_mul]
  read_sub := fun a b _ _ => by
    simp only [read, interpret_sub (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (fun a b => Rat.cast_sub a b), Polynomial.eval_sub]
  read_natCast := by
    intro n
    have literal : (n : E) = DensePoly.C (n : Rat) := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_natCast, DensePoly.coeff_C]
      split_ifs <;> rfl
    rw [literal]
    simp only [read, interpret_C, Polynomial.eval_C]
    norm_num

theorem lookup_spec (q : E) (value : Int) (found : lookup q = some value) :
    value = (SignType.sign (read q) : Int) :=
  IntervalSign.sign_spec q 2 2 2 (by norm_num) (by norm_num) value found

/-- Evaluation is genuinely noninjective: this nonzero stored polynomial
vanishes at the fixed parameter. It cannot certify a nonzero leading term. -/
theorem killed : read (parameter - 2) = 0 := by
  have observed := lookup_spec (parameter - 2) 0 (by decide +kernel)
  have zero : SignType.sign (read (parameter - 2)) = 0 := by
    cases found : SignType.sign (read (parameter - 2)) with
    | neg => simp [found] at observed
    | zero => rfl
    | pos => simp [found] at observed
  exact sign_eq_zero_iff.mp zero

run_meta Lean.withoutExporting do
  let sign := fun q : E => (lookup q).getD 0
  let some cert := TarskiCertificate.certify sign (EndpointSigns.ofSign sign)
      SignedRemainderChain.normalizeId () head 1 lower upper |
    throwError "polynomial coefficient ring query production failed"
  unless cert.value == 1 && QueryReplay.check lookup () head 1 lower upper 1 cert do
    throwError "polynomial coefficient ring query did not replay"
  unless (parameter - 2 : E) != 0 && lookup (parameter - 2) == some 0 &&
      !QueryReplay.leading lookup (DensePoly.C (parameter - 2)) do
    throwError "noninjective coefficient evaluation lost its leading guard"
  let missing := cert.squarefree.initial.leftScale
  let limitedLookup := fun q : E => if q == missing then none else lookup q
  unless !(QueryReplay.check limitedLookup () head 1 lower upper 1 cert) do
    throwError "missing required coefficient sign accepted"
  unless !(QueryReplay.check lookup () head 1 lower upper 1 {cert with value := 2}) do
    throwError "changed query verdict accepted"
  unless !(QueryReplay.check lookup () (head + 1) 1 lower upper 1 cert) do
    throwError "changed query polynomial accepted"
  let certificate ← Lean.instantiateMVars (← FieldLiteral.tarskiExpr FieldLiteral.ratPolyExpr cert)
  let inputs := #[Lean.mkConst ``lookup, Lean.mkConst ``Unit.unit,
    Lean.mkConst ``head, Lean.mkConst ``test,
    Lean.mkConst ``lower, Lean.mkConst ``upper, Lean.mkIntLit 1, certificate]
  let checked ← Lean.Meta.mkAppM ``QueryReplay.check inputs
  let target ← Lean.instantiateMVars (← Lean.Meta.mkEq checked (Lean.mkConst ``Bool.true))
  let candidate ← Lean.Meta.mkFreshExprMVar target
  let remaining ← Lean.Elab.runTactic' candidate.mvarId!
    (← `(tactic|
      (simp only [QueryReplay.check, QueryReplay.covered, QueryReplay.leading,
        QueryReplay.cached, lookup, head, test, lower, upper, parameter,
        SignInputs.certificate, Sturm.check, TarskiCertificate.check_eq,
        SignedRemainderChain.check, Bool.and_eq_true, List.all_cons, List.all_nil,
        ← Array.all_toList, Array.toList_range])))
  let rec prove (goal : Lean.MVarId) : Lean.MetaM Unit := do
    let type ← Lean.Meta.whnf (← goal.getType)
    if type.isAppOfArity ``And 2 then
      let children ← goal.apply (Lean.mkConst ``And.intro)
      for child in children do prove child
    else
      let unresolved ← Lean.Elab.runTactic' goal (← `(tactic| decide +kernel))
      unless unresolved.isEmpty do throwError "frozen coefficient-ring query did not kernel-check"
  for goal in remaining do prove goal
  let proof ← Lean.instantiateMVars candidate
  let proof ← Hex.RCF.checkProof `Hex.RCF.QueryRing.accepted target proof
  Lean.withExporting (isExporting := true) do Lean.addDecl (.thmDecl {
    name := `Hex.RCF.QueryRing.accepted
    levelParams := []
    type := target
    value := proof })
  let transported ← Lean.Meta.mkAppM ``QueryReplay.checked
    (#[Lean.mkConst ``lookup, Lean.mkConst ``read, Lean.mkConst ``read_closed,
      Lean.mkConst ``lookup_spec] ++ inputs.extract 1 inputs.size ++
      #[Lean.mkConst `Hex.RCF.QueryRing.accepted])
  let meaning ← Lean.Meta.inferType transported
  let transported ← Hex.RCF.checkProof `Hex.RCF.QueryRing.real_checked meaning transported
  Lean.withExporting (isExporting := true) do Lean.addDecl (.thmDecl {
    name := `Hex.RCF.QueryRing.real_checked
    levelParams := []
    type := meaning
    value := transported })
  Lean.logInfo "QUERY_RING: fraction-free quadratic query; frozen ordinary-kernel replay; missing signs, changed bindings and nonzero-leading refusal checked"

end Hex.RCF.QueryRing
