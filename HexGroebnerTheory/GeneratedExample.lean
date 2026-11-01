/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.PrimeExample
public import HexGroebnerTheory.CertificateBasis
public import HexGroebnerTheory.CertificateNormalForm

@[expose] public section

namespace HexGroebnerTheory.GeneratedExample

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev context := Hex.Groebner.PrimeExample.context
abbrev generators := Hex.Groebner.PrimeExample.generators
abbrev polynomials := Hex.Groebner.PrimeExample.polynomials
abbrev certificate := Hex.Groebner.PrimeExample.certificate
abbrev target := Hex.Groebner.PrimeExample.target
abbrev nonmember := Hex.Groebner.PrimeExample.nonmember

theorem basis : IsReducedBasis context generators polynomials :=
  checkBasis_sound context generators polynomials certificate (by decide +kernel)

/-- info: 'HexGroebnerTheory.GeneratedExample.basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms basis

/-- The ordinary polynomial x has nonzero normal form modulo this input ideal. -/
theorem x_not_mem : denote context target ∉ Ideal.span
    (Set.range fun i : Fin generators.size => denote context generators[i]) :=
  checkNonmember_sound context generators target nonmember (by decide +kernel)

/-- info: 'HexGroebnerTheory.GeneratedExample.x_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x_not_mem

end HexGroebnerTheory.GeneratedExample
