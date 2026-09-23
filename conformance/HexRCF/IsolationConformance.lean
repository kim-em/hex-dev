/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Isolations
public import HexSturm.Fixtures
public meta import HexRCF.RealCoefficients.IsolationCheck
public meta import HexSturm.Fixtures

public section

/-!
Oracle: none. Mode: always.

Covered operations: checked total and per-interval root counts, query signs at a
selected root, and signs at open-cell samples.
Covered properties: kernel acceptance of literal evidence, mathematical root
coverage, and agreement of a checked query with the selected root's sign.
Covered edge cases: missing roots, copied certificates, wrong context or head,
root endpoints, overlapping intervals, and the empty root set.
-/
namespace Hex.RCF.IsoTests

open RealCoefficients

@[expose] def half : Dyadic := Dyadic.ofInt 1 >>> (1 : Int)
@[expose] def intervals : IsolationCert := ⟨#[
  ⟨Dyadic.ofInt (-2), -half, by decide⟩,
  ⟨half, Dyadic.ofInt 2, by decide⟩]⟩

@[expose] def total : TarskiCertificate Rat Rat Nat :=
  { Sturm.Fixtures.literal with lower := .negInf, upper := .posInf }

@[expose] def negative : TarskiCertificate Rat Rat Nat :=
  { Sturm.Fixtures.literal with
    upper := .finite (-1 / 2)
    upperSigns := #[-1, -1, 1]
    upperVariations := 1
    value := 1 }

@[expose] def positive : TarskiCertificate Rat Rat Nat :=
  { Sturm.Fixtures.literal with
    lower := .finite (1 / 2)
    lowerSigns := #[-1, 1, 1]
    lowerVariations := 1
    value := 1 }

@[expose] def certificate : IsolationReplay Rat Nat :=
  ⟨intervals, total, ⟨#[negative, positive], by decide⟩⟩

/-- The kernel checks literal evidence, without running a chain producer. -/
theorem accepted : certificate.check Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p = true := by
  simp only [IsolationReplay.check, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Omitting a real root cannot be hidden by retaining its total certificate. -/
@[expose] def missing : IsolationReplay Rat Nat :=
  ⟨⟨#[intervals.intervals[1]'(by decide)]⟩, total, ⟨#[positive], by decide⟩⟩

example : missing.check Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p = false := by
  simp only [IsolationReplay.check, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel
example : certificate.check Sturm.orderSign Dyadic.toRat 8 Sturm.Fixtures.p = false := by
  simp only [IsolationReplay.check, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel
example : certificate.check Sturm.orderSign Dyadic.toRat 7 (Sturm.Fixtures.p + 1) = false := by
  simp only [IsolationReplay.check, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel
example : ({ certificate with counts := ⟨#[positive, negative], by decide⟩ }).check
    Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p = false := by
  simp only [IsolationReplay.check, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel
example : ({ certificate with total := { total with value := 1 } }).check
    Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p = false := by
  simp only [IsolationReplay.check, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

-- The compiled builder reuses the prepared chains and must reject an
-- incomplete proposal, a root endpoint, and overlapping intervals.
#guard (IsolationReplay.build Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p intervals).isSome
#guard (IsolationReplay.build Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p missing.isolations).isNone
#guard (IsolationReplay.build Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p
  ⟨#[⟨Dyadic.ofInt (-2), Dyadic.ofInt (-1), by decide⟩,
      ⟨half, Dyadic.ofInt 2, by decide⟩]⟩).isNone
#guard (IsolationReplay.build Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p
  ⟨#[intervals.intervals[0]'(by decide), intervals.intervals[0]'(by decide)]⟩).isNone
#guard (IsolationReplay.build Sturm.orderSign Dyadic.toRat 7 (DensePoly.ofCoeffs #[(1 : Rat), 0, 1])
  ⟨#[]⟩).isSome
#guard (IsolationReplay.build Sturm.orderSign Dyadic.toRat 7 (0 : DensePoly Rat) ⟨#[]⟩).isNone

-- Queries on one-root intervals return the actual signed root value. The
-- second check deliberately replays a copied query in the wrong interval.
@[expose] def samplePoly : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
@[expose] def negativeQuery : TarskiCertificate Rat Rat Nat :=
  IsolationReplay.queryAt Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p
    samplePoly certificate ⟨0, by decide⟩
@[expose] def positiveQuery : TarskiCertificate Rat Rat Nat :=
  IsolationReplay.queryAt Sturm.orderSign Dyadic.toRat 7 Sturm.Fixtures.p
    samplePoly certificate ⟨1, by decide⟩

/- The following literal is the producer's finite output for the negative
interval. Its replay proof below checks data rather than executing the
recursive producer inside the kernel. -/
@[expose] def negativeLiteral : TarskiCertificate Rat Rat Nat :=
  { context := 7
    head := Sturm.Fixtures.p
    queryPoly := samplePoly
    lower := .finite ((Dyadic.ofInt (-2)).toRat)
    upper := .finite (-half).toRat
    squarefree :=
      { chain := #[DensePoly.ofCoeffs #[-1, 0, 1],
          DensePoly.ofCoeffs #[0, 1], DensePoly.ofCoeffs #[1]]
        degrees := #[2, 1, 0]
        initial := ⟨1, DensePoly.ofCoeffs #[], 2⟩
        steps := #[⟨1, DensePoly.ofCoeffs #[0, 1], 1⟩]
        terminal := some (1, DensePoly.ofCoeffs #[0, 1]) }
    remainders :=
      { chain := #[DensePoly.ofCoeffs #[-1, 0, 1], DensePoly.ofCoeffs #[1]]
        degrees := #[2, 0]
        initial := ⟨1, DensePoly.ofCoeffs #[2], 2⟩
        steps := #[]
        terminal := some (1, DensePoly.ofCoeffs #[-1, 0, 1]) }
    lowerSigns := #[1, 1]
    upperSigns := #[-1, 1]
    lowerVariations := 0
    upperVariations := 1
    value := -1 }

#guard decide (negativeQuery = negativeLiteral)

#guard negativeQuery.value == -1
#guard positiveQuery.value == 1
#guard Sturm.check Sturm.orderSign 7 Sturm.Fixtures.p samplePoly
  (.finite ((Dyadic.ofInt (-2)).toRat)) (.finite ((-half).toRat))
  negativeQuery.value negativeQuery
#guard Sturm.check Sturm.orderSign 7 Sturm.Fixtures.p samplePoly
  (.finite half.toRat) (.finite (Dyadic.ofInt 2).toRat)
  positiveQuery.value positiveQuery
#guard !(Sturm.check Sturm.orderSign 7 Sturm.Fixtures.p samplePoly
  (.finite half.toRat) (.finite (Dyadic.ofInt 2).toRat)
  negativeQuery.value negativeQuery)

private theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

/-- Exact query replay gives the sign at the uniquely isolated negative
root, with the sole semantic dependency owned by the shared query theorem. -/
theorem negativeQuery_checked :
    Sturm.check Sturm.orderSign 7 Sturm.Fixtures.p samplePoly
      (.finite ((Dyadic.ofInt (-2)).toRat)) (.finite (-half).toRat)
      negativeLiteral.value negativeLiteral = true := by
  simp only [Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem negativeLiteral_wrong_interval :
    Sturm.check Sturm.orderSign 7 Sturm.Fixtures.p samplePoly
      (.finite half.toRat) (.finite (Dyadic.ofInt 2).toRat)
      negativeLiteral.value negativeLiteral = false := by
  simp only [Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- The accepted count-one query is the mathematical sign at that root. -/
theorem negativeQuery_semantics (x : ℝ)
    (hx : (HexPolyMathlib.Interpret.interpret (fun r : Rat => (r : ℝ))
      (fun _ => Rat.cast_eq_zero) Sturm.Fixtures.p).IsRoot x)
    (hl : HexRealRootsMathlib.Dyadic.toReal (Dyadic.ofInt (-2)) < x)
    (hu : x < HexRealRootsMathlib.Dyadic.toReal (-half)) :
    (SignType.sign ((HexPolyMathlib.Interpret.interpret
      (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) samplePoly).eval x) : Int) = -1 := by
  have hquery := certificate.check_sign
    (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp)
    Sturm.orderSign rational_sign Dyadic.toRat
    (fun d => (HexRealRootsMathlib.toReal_eq_cast_toRat d).symm)
    7 Sturm.Fixtures.p accepted ⟨0, by decide⟩ samplePoly
    negativeLiteral.value negativeLiteral negativeQuery_checked x hx hl hu
  exact hquery.symm

/-- The same accepted literal certificate covers every mathematical root.
This semantic result uses the explicitly owned shared query admission. -/
theorem covered : ∃ root : Fin certificate.isolations.intervals.size → ℝ,
    StrictMono root ∧ ∀ x,
      (HexPolyMathlib.Interpret.interpret (fun r : Rat => (r : ℝ))
        (fun _ => Rat.cast_eq_zero) Sturm.Fixtures.p).IsRoot x ↔ ∃ i, root i = x := by
  obtain ⟨root, _, hmono, hcomplete, _⟩ := certificate.check_roots
    (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) Sturm.orderSign rational_sign
    Dyadic.toRat (fun d => (HexRealRootsMathlib.toReal_eq_cast_toRat d).symm)
    7 Sturm.Fixtures.p accepted
  exact ⟨root, hmono, hcomplete⟩

/-- A real point left of both isolated roots has the sign computed at the
actual dyadic sample of that open cell. -/
theorem left_sample_sign :
    ∃ root : Fin certificate.isolations.intervals.size → ℝ,
      StrictMono root ∧ ∀ x,
        Cell.Region root (.open ⟨0, by decide⟩) x →
        Sturm.orderSign (Sturm.Fixtures.p.eval
          (Dyadic.toRat (certificate.isolations.openPoint ⟨0, by decide⟩))) =
          (SignType.sign ((HexPolyMathlib.Interpret.interpret
            (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
            Sturm.Fixtures.p).eval x) : Int) := by
  obtain ⟨root, _, hmono, hcomplete, hopen⟩ := certificate.check_roots
    (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) Sturm.orderSign rational_sign
    Dyadic.toRat (fun d => (HexRealRootsMathlib.toReal_eq_cast_toRat d).symm)
    7 Sturm.Fixtures.p accepted
  refine ⟨root, hmono, ?_⟩
  intro x hx
  exact certificate.open_sign
    (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_mul _ _)
    Sturm.orderSign rational_sign Dyadic.toRat
    (fun d => (HexRealRootsMathlib.toReal_eq_cast_toRat d).symm)
    Sturm.Fixtures.p Sturm.Fixtures.p root hmono hcomplete
    ⟨0, by decide⟩ (hopen ⟨0, by decide⟩)
    (Or.inr (fun _ h => h)) x hx

/-- info: 'Hex.RCF.IsoTests.covered' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms covered

/-- info: 'Hex.RCF.IsoTests.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepted

end Hex.RCF.IsoTests
