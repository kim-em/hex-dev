/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.QueryReplay
public import HexRCF.RealCoefficients.Isolations
public section

namespace Hex.RCF.RealCoefficients.IsolationTransport
open Hex.RealClosure

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Retain the exact literal intervals and root counts under interpretation. -/
@[expose, reducible] noncomputable def map (read : E → ℝ)
    (cert : IsolationReplay E Ctx) : IsolationReplay ℝ Ctx where
  isolations := cert.isolations
  total := Transport.query read id cert.total
  counts := Vector.ofFn fun i => Transport.query read id cert.counts[i]

/-- Finite replay provides the existing real isolation checker without a
source field, source inverse operation or global reflection of zero. -/
theorem checked (lookup : E → Option Int) (read : E → ℝ)
    (closed : Transport.Closed read (fun _ => True))
    (sound : ∀ x value, lookup x = some value → value = (SignType.sign (read x) : Int))
    (point : Dyadic → E)
    (point_spec : ∀ d, read (point d) = HexRealRootsTheory.Dyadic.toReal d)
    (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (accepted : check lookup point context head cert = true) :
    (map read cert).check (fun x : ℝ => (SignType.sign x : Int))
      HexRealRootsTheory.Dyadic.toReal context (Transport.polynomial read head) = true := by
  simp only [check, Bool.and_eq_true] at accepted
  obtain ⟨⟨gaps, total⟩, counts⟩ := accepted
  have unit : Transport.polynomial read (1 : DensePoly E) = 1 :=
    Transport.polynomial_one read closed.read_zero closed.read_one
  simp only [IsolationReplay.check, map, Bool.and_eq_true]
  refine ⟨⟨gaps, ?_⟩, ?_⟩
  · have result := QueryReplay.checked lookup read closed sound context head 1 .negInf .posInf
      cert.isolations.intervals.size cert.total total
    simpa only [unit, Transport.endpoint] using result
  · apply List.all_eq_true.mpr
    intro i member
    have result := QueryReplay.checked lookup read closed sound context head 1
      (.finite (point cert.isolations.intervals[i].lower))
      (.finite (point cert.isolations.intervals[i].upper)) 1 cert.counts[i]
      (List.all_eq_true.mp counts i member)
    simpa [unit, Transport.endpoint, point_spec] using result

/-- Complete coverage and ordinary sector samples follow from the owner's
real root-count theorem applied to the transported finite certificate. -/
theorem roots (lookup : E → Option Int) (read : E → ℝ)
    (closed : Transport.Closed read (fun _ => True))
    (sound : ∀ x value, lookup x = some value → value = (SignType.sign (read x) : Int))
    (point : Dyadic → E)
    (point_spec : ∀ d, read (point d) = HexRealRootsTheory.Dyadic.toReal d)
    (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (accepted : check lookup point context head cert = true) :
    let polynomial := HexPolyTheory.Interpret.interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Transport.polynomial read head)
    ∃ root : Fin cert.isolations.intervals.size → ℝ,
      (∀ i, polynomial.IsRoot (root i) ∧
        HexRealRootsTheory.Dyadic.toReal cert.isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsTheory.Dyadic.toReal cert.isolations.intervals[i].upper) ∧
      StrictMono root ∧
      (∀ x, polynomial.IsRoot x ↔ ∃ i, root i = x) ∧
      (∀ cut, Cell.Region root (.open cut)
        (HexRealRootsTheory.Dyadic.toReal (cert.isolations.openPoint cut))) := by
  exact (map read cert).check_roots (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun x : ℝ => (SignType.sign x : Int)) (fun _ => rfl)
    HexRealRootsTheory.Dyadic.toReal (fun _ => rfl) context _
    (checked lookup read closed sound point point_spec context head cert accepted)

end Hex.RCF.RealCoefficients.IsolationTransport
