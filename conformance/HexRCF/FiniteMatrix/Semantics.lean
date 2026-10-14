/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import KernelReplay.FiniteJoint
public import HexSturmMathlib.Soundness
public import HexRCF.RealCoefficients.FiniteQuote
public import HexRealClosureMathlib.Algebraic
public import HexRealClosureMathlib.TransportInventory
import all HexRealRootsMathlib.TarskiSum
import all HexRealClosureMathlib.Algebraic
import all KernelReplay.FiniteJoint
import all KernelReplay.FiniteTower
public section
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Semantics
@[expose] noncomputable def finiteRead := FiniteJoint.readAt FiniteJoint.alpha
@[expose] def rational (x : Rat) : ℝ := x
theorem zero_iff (x : Rat) : rational x = 0 ↔ x = 0 := Rat.cast_eq_zero
theorem unit : rational 1 = 1 := by simp [rational]
theorem add (a b : Rat) : rational (a+b) = rational a + rational b := Rat.cast_add a b
theorem sub (a b : Rat) : rational (a-b) = rational a - rational b := Rat.cast_sub a b
theorem mul (a b : Rat) : rational (a*b) = rational a * rational b := Rat.cast_mul a b
theorem nat (n : Nat) : rational n = n := by simp [rational]
theorem sign (x : Rat) : Hex.Sturm.orderSign x = (SignType.sign (rational x) : Int) :=
  Generated.cast_sign x
theorem neg (x : Rat) : rational (-x) = -rational x := Rat.cast_neg x
theorem inv (x : Rat) : rational x⁻¹ = (rational x)⁻¹ := Rat.cast_inv x
@[expose] noncomputable def read (a : Element FiniteTower.first) : ℝ :=
  a.denote rational zero_iff unit add sub mul nat sign

theorem zero : read 0 = 0 := Element.denote_zero rational zero_iff unit add sub mul nat sign

theorem closed : Transport.Closed read (fun _ => True) := by
  refine ⟨trivial, ?_, ?_, ?_, trivial, ?_, zero, ?_, ?_, ?_, ?_, ?_⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro a b _ _
    exact Element.denote_add rational zero_iff unit add sub mul nat sign neg inv a b
  · intro a b _ _
    exact Element.denote_mul rational zero_iff unit add sub mul nat sign neg inv a b
  · intro a b _ _
    exact Element.denote_sub rational zero_iff unit add sub mul nat sign neg inv a b
  · exact Element.denote_one rational zero_iff unit add sub mul nat sign neg inv
  · exact Element.denote_nat rational zero_iff unit add sub mul nat sign neg inv

theorem agreement (values : List (Element FiniteTower.first)) :
    Transport.Inventory.Agreement read (fun _ => True) Element.sign
      (fun x : ℝ => (SignType.sign x : Int)) values := by
  intro value _
  exact ⟨trivial, (Element.sign_spec rational zero_iff unit add sub mul nat sign neg inv value).symm,
    Element.denote_eq_zero rational zero_iff unit add sub mul nat sign neg inv value⟩
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret
theorem mapped (p : DensePoly Rat) :
    interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
      (Transport.polynomial FiniteDataProbe.read p) = interpret rational zero_iff p := by
  ext i
  rw [coeff_interpret, Transport.polynomial_coeff _ (show FiniteDataProbe.read 0 = 0 by simp [FiniteDataProbe.read]),
    coeff_interpret]
  rfl
theorem endpoint (e : Endpoint Rat) :
    (Transport.endpoint FiniteDataProbe.read e).map (fun y : ℝ => y) = e.map rational := by
  cases e <;> rfl

theorem root : FiniteJoint.alpha = FiniteTower.first.rootValue rational zero_iff unit add sub mul nat sign := by
  have selected := FiniteTower.first.finitePoint_spec FiniteDataProbe.read
    (show FiniteDataProbe.read 0 = 0 by simp [FiniteDataProbe.read])
    (show FiniteDataProbe.read 1 = 1 by simp [FiniteDataProbe.read]) FiniteJoint.firstData.descriptor
  apply FiniteTower.first.root.root_unique rational zero_iff unit add sub mul nat sign FiniteJoint.alpha
  · simpa only [mapped, endpoint, FiniteJoint.alpha] using selected.1
  · simpa only [signsAt, List.map_map, Function.comp_def, mapped, FiniteJoint.alpha] using selected.2

theorem read_eq : read = finiteRead := by
  funext a
  change (interpret rational zero_iff a.polynomial).eval
      (FiniteTower.first.rootValue rational zero_iff unit add sub mul nat sign) =
    (interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
      (Transport.polynomial FiniteDataProbe.read a.polynomial)).eval FiniteJoint.alpha
  rw [mapped, root]
theorem reflect (a : Element FiniteTower.first) : read a = 0 ↔ a = 0 :=
  Element.denote_eq_zero rational zero_iff unit add sub mul nat sign neg inv a

theorem negative (a : Element FiniteTower.first) : read (-a) = -read a :=
  Element.denote_neg rational zero_iff unit add sub mul nat sign neg inv a
theorem first_raw : FiniteTower.first.root.raw = FiniteTower.firstRaw := by
  rw [FiniteTower.first, Context.root_adjoin, FiniteTower.firstRoot_raw]
theorem first_head : interpret rational zero_iff FiniteTower.first.root.raw.head =
    (Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℝ) := by
  rw [first_raw]
  ext i
  rw [coeff_interpret]
  rcases i with _ | _ | _ | i
  all_goals simp [FiniteTower.firstRaw, DensePoly.coeff_ofCoeffs, rational,
    Polynomial.coeff_X_pow, Polynomial.coeff_C]
  all_goals rfl

theorem alpha_sqrt : FiniteJoint.alpha = Real.sqrt 2 := by
  have chosen := (Tarski.mem_rootsIn _ _ _ _).mp
    (FiniteTower.first.root.root_spec rational zero_iff unit add sub mul nat sign).1
  have bounds := chosen.2
  rw [first_raw] at bounds
  have positive : 0 ≤ FiniteTower.first.rootValue rational zero_iff unit add sub mul nat sign := by
    have lower : (1 : ℝ) < FiniteTower.first.rootValue rational zero_iff unit add sub mul nat sign := by
      simpa only [FiniteTower.firstRaw, Endpoint.map, rational, Rat.cast_one,
        Context.rootValue] using bounds.1
    exact le_of_lt (lt_trans (by norm_num) lower)
  have equation := Polynomial.isRoot_of_mem_roots chosen.1
  rw [first_head] at equation
  have squared : (FiniteTower.first.rootValue rational zero_iff unit add sub mul nat sign) ^ 2 = 2 := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero, Polynomial.IsRoot, Context.rootValue] using equation
  rw [root, ← squared, Real.sqrt_sq positive]
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Semantics
