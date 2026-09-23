/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.RealCoefficients.Interpret
public import HexRCF.RealCoefficients.RootAliases
public import HexRCF.RealCoefficients.Coefficients
public import HexRCF.RealCoefficients.Specialize
public import HexRCF.RealCoefficients.Formula
public import HexRCF.RealCoefficients.IsolationBuild
public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.IsolationSemantics
public import HexRCF.RealCoefficients.Carrier
public import HexRCF.RealCoefficients.Field
public import HexRCF.RealCoefficients.LiteralSign

/-! Algebraic coefficient conversion, source preparation, polynomial
specialization, checked real-root isolation, carrier coverage and fixed-field
signs for the optional RCF adapter.
No coefficient solver is registered; source equivalence does not discharge
coefficient authentication, divisor guards or decision replay. -/
