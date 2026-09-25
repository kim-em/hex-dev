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
public import HexRCF.RealCoefficients.Field
public import HexRCF.RealCoefficients.LiteralSign
public import HexRCF.RealCoefficients.FieldSpecialize
public import HexRCF.RealCoefficients.SignInputs
public import HexRCF.RealCoefficients.FieldCarrier
public import HexRCF.RealCoefficients.Carrier
public import HexRCF.RealCoefficients.IsolationBuild
public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.IsolationSemantics
public import HexRCF.RealCoefficients.RadicalCheck
public import HexRCF.RealCoefficients.Radical
public import HexRCF.RealCoefficients.RadicalBuild
public import HexRCF.RealCoefficients.FieldDecision
public import HexRCF.RealCoefficients.FieldRootSigns
public import HexRCF.RealCoefficients.FieldReplay
public import HexRCF.RealCoefficients.FieldBuild
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.RealCoefficients.FieldRuntime
public import HexRCF.RealCoefficients.SquareTwo
public import HexRCF.RealCoefficients.CubeTwo
public import HexRCF.RealCoefficients.Selected
public meta import HexRCF.RealCoefficients.Tactic
public import HexRCF.RealCoefficients.CellFormula

/-! Algebraic coefficient conversion, source preparation, fixed-field
specialization, root-isolation search and checked cell decisions for the
optional RCF adapter. -/
