/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausTheory.FactorTactic

public import HexRCF.RealCoefficients.Registration
public import HexRCF.RealCoefficients.AlgebraicBounds
public meta import HexRCF.RealCoefficients.AlgebraicBounds
public meta import HexRCF.RealCoefficients.Finite
public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.RealCoefficients.Interpret
public import HexRCF.RealCoefficients.RationalRoot
public meta import HexRCF.RealCoefficients.RationalRoot
public import HexRCF.RealCoefficients.RootAliases
public import HexRCF.RealCoefficients.Conversion
public import HexRCF.RealCoefficients.Coefficients
public import HexRCF.RealCoefficients.Specialize
public import HexRCF.RealCoefficients.Formula
public import HexRCF.RealCoefficients.Field
public import HexRCF.RealCoefficients.CommonPresentation
public import HexRCF.RealCoefficients.LiteralSign
public import HexRCF.RealCoefficients.SignIndex
public import HexRCF.RealCoefficients.FieldIndex
public import HexRCF.RealCoefficients.FieldSpecialize
public import HexRCF.RealCoefficients.RepresentationSpecialize
public import HexRCF.RealCoefficients.Samples
public import HexRCF.RealCoefficients.SelectedFormula
public import HexRCF.RealCoefficients.SelectedBytes
public import HexRCF.RealCoefficients.NumberField
public import HexRCF.RealCoefficients.Realization
public import HexRCF.RealCoefficients.NativeFormula
public import HexRCF.RealCoefficients.NativeSpecialize
public import HexRCF.RealCoefficients.NativeSamples
public import HexRCF.RealCoefficients.NativeSources
public import HexRCF.RealCoefficients.NativeSelection
public import HexRCF.RealCoefficients.SectionReplay
public import HexRCF.RealCoefficients.ScalarPacket
public import HexRCF.RealCoefficients.SectionBuild
public meta import HexRCF.RealCoefficients.SectionQuote
public import HexRCF.RealCoefficients.PointReplay
public import HexRCF.RealCoefficients.PointBuild
public meta import HexRCF.RealCoefficients.PointQuote
public meta import HexRCF.RealCoefficients.Quote
public import HexRCF.RealCoefficients.RootReplay
public import HexRCF.RealCoefficients.RootBuild
public import HexRCF.RealCoefficients.RepresentationCarrier
public import HexRCF.RealCoefficients.RootCells
public import HexRCF.RealCoefficients.RepresentationCells
public import HexRCF.RealCoefficients.BoundarySigns
public import HexRCF.RealCoefficients.SectorSamples
public import HexRCF.RealCoefficients.PointRows
public import HexRCF.RealCoefficients.CellReplay
public import HexRCF.RealCoefficients.RowOperations
public import HexRCF.RealCoefficients.RowReplay
public import HexRCF.RealCoefficients.CellPackets
public import HexRCF.RealCoefficients.CellPacketRead
public import HexRCF.RealCoefficients.CellPacketConvert
public import HexRCF.RealCoefficients.CellPacketTransport
public import HexRCF.RealCoefficients.SectorReplay
public import HexRCF.RealCoefficients.CellRead
public import HexRCF.RealCoefficients.CellBuild
public import HexRCF.RealCoefficients.CellDiscover
public import HexRCF.RealCoefficients.CellAlignment
public import HexRCF.RealCoefficients.CellDecision
public import HexRCF.RealCoefficients.CellExecution
public import HexRCF.RealCoefficients.CellCodec
public import HexRCF.RealCoefficients.CellFootprint
public import HexRCF.RealCoefficients.RootCodec
public import HexRCF.RealCoefficients.RootTableCodec
public import HexRCF.RealCoefficients.CellOperations
public import HexRCF.RealCoefficients.CompleteReplay
public import HexRCF.RealCoefficients.NumberFieldCells
public import HexRCF.RealCoefficients.RowEncode
public import HexRCF.RealCoefficients.CellReuse
public meta import HexRCF.RealCoefficients.CellQuote
public import HexRCF.RealCoefficients.RootTable
public import HexRCF.RealCoefficients.RootTransport
public import HexRCF.RealCoefficients.Gather
public import HexRCF.RealCoefficients.GatherCells
public import HexRCF.RealCoefficients.AlgebraicCells
public meta import HexRCF.RealCoefficients.AlgebraicPreparation
public meta import HexRCF.RealCoefficients.RealModel
public import HexRCF.RealCoefficients.RegisteredGather
public import HexRCF.RealCoefficients.ReconciledGather
public import HexRCF.RealCoefficients.InverseReplay
public import HexRCF.RealCoefficients.SignInputs
public import HexRCF.RealCoefficients.FieldCarrier
public import HexRCF.RealCoefficients.Carrier
public import HexRCF.RealCoefficients.IsolationBuild
public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.IsolationSemantics
public import HexRCF.RealCoefficients.IsolationAssembly
public import HexRCF.RealCoefficients.IsolationProgress
public import HexRCF.RealCoefficients.RadicalCheck
public import HexRCF.RealCoefficients.Radical
public import HexRCF.RealCoefficients.RadicalBuild
public import HexRCF.RealCoefficients.RadicalProgress
public import HexRCF.RealCoefficients.FieldDecision
public import HexRCF.RealCoefficients.FieldRootSigns
public import HexRCF.RealCoefficients.FieldRootSignsProgress
public import HexRCF.RealCoefficients.FieldReplay
public import HexRCF.RealCoefficients.FieldBuild
public import HexRCF.RealCoefficients.FieldSignProgress
public import HexRCF.RealCoefficients.FieldRoots
public import HexRCF.RealCoefficients.FieldBuildProgress
public import HexRCF.RealCoefficients.FieldDecisionProgress
public import HexRCF.RealCoefficients.FieldBuildBudget
public import HexRCF.RealCoefficients.FiniteSigns
public import HexRCF.RealCoefficients.FiniteReplay
public import HexRCF.RealCoefficients.Replay
public import HexRCF.RealCoefficients.FieldRefinement
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.RealCoefficients.FieldCompile
public meta import HexRCF.RealCoefficients.FieldRuntime
public import HexRCF.RealCoefficients.SquareTwo
public import HexRCF.RealCoefficients.SquareRoot
public import HexRCF.RealCoefficients.CubeTwo
public import HexRCF.RealCoefficients.Selected
public meta import HexRCF.RealCoefficients.Tactic
public meta import HexRCF.RealCoefficients.Preparation
public meta import HexRCF.RealCoefficients.AlgebraicRoot
public meta import HexRCF.RealCoefficients.CommonTactic
public meta import HexRCF.RealCoefficients.FiniteQuote
public import HexRCF.RealCoefficients.CellFormula

/-! Algebraic coefficient conversion, source preparation, fixed-field
specialization, root-isolation search and checked cell decisions for the
optional RCF adapter. -/
