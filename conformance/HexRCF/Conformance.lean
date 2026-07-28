/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.Decision
import HexRCF.Tactic

/-!
# HexRCF conformance

**Oracle:** none for the core module; python-flint for the emitted CI profile.

**Mode:** core is `always`; the python-flint component is `if_available`.

**Covered operations:**

* the proof-producing `rcf` tactic;
* `Hex.RCF.decide`, `build?`, `Certificate.replay?`, and `Certificate.check`;
* the `SturmReplay`, `IsolationCert`, `CarrierCert`, and `CommonRootCert`
  arithmetic checkers.

**Covered properties:**

* each supported true goal is closed only through checked certificate evidence;
* compiled decisions return `some expected`, never treating builder failure as
  false;
* all four quantifiers respect the `(a,b]` cell-ownership convention;
* malformed replay, isolation, carrier, and common-root evidence fails closed;
* unsupported syntax and false verdicts produce distinct stable diagnostics.

**Covered edge cases:** constants, no real roots, root cells, shared and
repeated roots, included upper and excluded lower endpoints, equal/reversed
intervals, wrong recurrence data, malformed identities, multiple variables,
non-polynomial functions, variable division, and unsupported closed intervals.
-/

namespace Hex.RCF.Conformance

/-! # Public tactic contract -/

example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by rcf
example : ∀ x : ℝ, 0 ≤ x → x ^ 3 + x ≥ 0 := by rcf
example : ∀ x : ℝ, 0 < x → x ^ 2 + 1 ≥ 2 * x := by rcf
example : ∀ x : ℝ, x ^ 2 ≤ 1 → x ^ 4 - x ^ 2 ≤ 0 := by rcf
example : ∃ x : ℝ, x ^ 3 - x - 1 = 0 ∧ 1 < x ∧ x < 2 := by rcf

example : ∀ x : ℝ, x ^ 2 + 2 * x + 2 ≠ 0 := by rcf
example : ∃ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 ∧ x ^ 3 - x - 1 = 0 := by rcf
example : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x ≤ 1 := by rcf
example : ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 1 → x ^ 2 < 0 := by rcf
example : ∀ x : ℝ, x ∈ Set.Ioc (2 : ℝ) 1 → x ^ 2 < 0 := by rcf

private def poly (coeffs : List Int) : ZPoly :=
  DensePoly.ofCoeffs coeffs.toArray

private def atom (coeffs : List Int) (cmp : Cmp) : Formula :=
  .atom ⟨poly coeffs, cmp⟩

private def constantTrue : Sentence := .forallReal (atom [1] .gt)
private def constantFalse : Sentence := .existsReal (atom [1] .lt)
private def noRootsTrue : Sentence := .forallReal (atom [1, 0, 1] .gt)
private def noRootsFalse : Sentence := .existsReal (atom [1, 0, 1] .eq)
private def rootExists : Sentence := .existsReal (atom [0, 1] .eq)
private def upperIncluded : Sentence := .existsIoc 0 1 (atom [-1, 1] .eq)
private def lowerExcluded : Sentence := .existsIoc 1 2 (atom [-1, 1] .eq)
private def equalForall : Sentence := .forallIoc 1 1 (atom [0, 0, 1] .lt)
private def equalExists : Sentence := .existsIoc 1 1 (atom [1] .gt)
private def reversedForall : Sentence := .forallIoc 2 1 (atom [1] .lt)
private def reversedExists : Sentence := .existsIoc 2 1 (atom [0, 1] .eq)

#guard Hex.RCF.decide constantTrue == some true
#guard Hex.RCF.decide constantFalse == some false
#guard Hex.RCF.decide noRootsTrue == some true
#guard Hex.RCF.decide noRootsFalse == some false
#guard Hex.RCF.decide rootExists == some true
#guard Hex.RCF.decide upperIncluded == some true
#guard Hex.RCF.decide lowerExcluded == some false
#guard Hex.RCF.decide equalForall == some true
#guard Hex.RCF.decide equalExists == some false
#guard Hex.RCF.decide reversedForall == some true
#guard Hex.RCF.decide reversedExists == some false

private def checked (sentence : Sentence) (expected : Bool) : Bool :=
  match build? sentence with
  | none => false
  | some result =>
      result.verdict == expected &&
      result.certificate.replay? sentence == some expected &&
      result.certificate.check sentence == expected

#guard checked constantTrue true
#guard checked noRootsTrue true
#guard checked rootExists true
#guard checked constantFalse false

/-! # Fail-closed arithmetic replay -/

private def one : ZPoly := poly [1]
private def zX : ZPoly := poly [0, 1]
private def twiceX : ZPoly := poly [0, 2]
private def quad : ZPoly := poly [-1, 0, 1]

private def replay : SturmReplay where
  chain := #[quad, zX, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := zX, rightScale := 1 }]

#guard replay.check quad
#guard !({ replay with chain := #[poly [-2, 0, 2], zX, one] }).check quad
#guard !({ replay with derivScale := 3 }).check quad
#guard !({ replay with
  steps := #[{ leftScale := 2, quotient := zX, rightScale := 1 }] }).check quad
#guard !({ replay with
  steps := #[{ leftScale := -1, quotient := zX, rightScale := 1 }] }).check quad
#guard !({ replay with
  steps := #[{ leftScale := 1, quotient := 0, rightScale := 1 }] }).check quad

private def badDegree : SturmReplay where
  chain := #[quad, zX, one, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := zX, rightScale := 1 },
    { leftScale := 1, quotient := poly [1, 1], rightScale := 1 }]

private def badTerminal : SturmReplay where
  chain := #[quad, zX]
  derivScale := 2
  steps := #[]

#guard !badDegree.check quad
#guard !badTerminal.check quad

private def leftRoot : DyadicInterval :=
  DyadicInterval.mk (-2) 0 (by decide)

private def rightRoot : DyadicInterval :=
  DyadicInterval.mk 0 2 (by decide)

private def isolations : IsolationCert := ⟨#[leftRoot, rightRoot]⟩
private def incomplete : IsolationCert := ⟨#[leftRoot]⟩

#guard isolations.check replay
#guard !incomplete.check replay

private def carrierSentence : Sentence := .existsReal (Formula.atom ⟨quad, .eq⟩)

private def carrier : CarrierCert where
  carrier := quad
  repeated := one
  derivPart := twiceX
  factorScale := 1
  derivScale := 1
  replay := replay

#guard carrier.check carrierSentence
#guard !({ carrier with factorScale := 2 }).check carrierSentence

private def common : CommonRootCert where
  gcd := quad
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some replay

#guard common.check quad quad
#guard !({ common with atomFactor := zX }).check quad quad
#guard !({ common with atomCoeff := 0 }).check quad quad

/-! # Stable refusal and false-verdict diagnostics -/

/-- error: rcf: more than one variable or a nested quantifier is unsupported -/
#guard_msgs in
example : ∀ a x : ℝ, a * x ^ 2 + 1 > 0 := by rcf

/-- error: rcf: non-polynomial real functions such as sin and exp are unsupported -/
#guard_msgs in
example : ∀ x : ℝ, Real.sin x = 0 := by rcf

/-- error: rcf: division by an expression containing the variable is not polynomial. Clear denominators by hand -/
#guard_msgs in
example : ∀ x : ℝ, x + 1 / x ≥ 2 := by rcf

/--
error: rcf: Set.Icc quantifiers are unsupported. Rewrite
  ∀ x ∈ Set.Icc a b, φ x
as
  (a ≤ b → φ a) ∧ ∀ x ∈ Set.Ioc a b, φ x
-/
#guard_msgs in
example : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → x ≤ 1 := by rcf

/-- error: rcf: the universal sentence is false on the root cell isolated in (-2, 2] -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 > 0 := by rcf

/--
error: rcf: the existential sentence is false. Every relevant decomposition
cell was checked and found false, so there is no witness
-/
#guard_msgs in
example : ∃ x : ℝ, x ^ 2 + 1 = 0 := by rcf

end Hex.RCF.Conformance
