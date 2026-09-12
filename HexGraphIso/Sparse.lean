/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Colored
public import HexGraphIso.Sparse.Iso
public import HexGraphIso.Sparse.Uncolored
public import HexGraphIso.Sparse.Kernel
public import HexGraphIso.Sparse.Tactic
public import HexGraphIso.Sparse.Run
public import HexGraphIso.Sparse.Ops
public import HexGraphIso.Sparse.Canonical
public import HexGraphIso.Sparse.Autos
public import HexGraphIso.Sparse.UncoloredAutos
public import HexGraphIso.Nauty.Sparse.Cert.LimitComplete
public import HexGraphIso.Nauty.Sparse.Inverse
public import HexGraphIso.Nauty.Sparse.Key
public import HexGraphIso.Nauty.Sparse.Rows
public import HexGraphIso.Nauty.Sparse.GraphProps
public import HexGraphIso.Nauty.Sparse.Update
public import HexGraphIso.Nauty.Sparse.ComparePrefix
public import HexGraphIso.Nauty.Sparse.Autom
public import HexGraphIso.Nauty.Sparse.Initial
public import HexGraphIso.Nauty.Sparse.SortProps
public import HexGraphIso.Nauty.Sparse.SortOrder
public import HexGraphIso.Nauty.Sparse.SortStack
public import HexGraphIso.Nauty.Sparse.SortSorted
public import HexGraphIso.Nauty.Sparse.IndirectCongr
public import HexGraphIso.Nauty.Sparse.BfsRun
public import HexGraphIso.Nauty.Sparse.Scratch
public import HexGraphIso.Nauty.Sparse.TargetCache
public import HexGraphIso.Nauty.Sparse.TargetDispatch
public import HexGraphIso.Nauty.Sparse.RefineFuel
public import HexGraphIso.Nauty.Sparse.RefineBoundary
public import HexGraphIso.Nauty.Sparse.Root
public import HexGraphIso.Nauty.Sparse.ScratchSearch
public import HexGraphIso.Nauty.Sparse.CountCells
public import HexGraphIso.Nauty.Sparse.CountOrder
public import HexGraphIso.Nauty.Sparse.CountSize
public import HexGraphIso.Nauty.Sparse.CountPattern
public import HexGraphIso.Nauty.Sparse.CountValid
public import HexGraphIso.Nauty.Sparse.CompactRun
public import HexGraphIso.Nauty.Sparse.FillRun
public import HexGraphIso.Nauty.Sparse.FillIndex
public import HexGraphIso.Nauty.Sparse.SingletonIndex
public import HexGraphIso.Nauty.Sparse.SingletonCongr
public import HexGraphIso.Nauty.Sparse.NontrivialIndex
public import HexGraphIso.Nauty.Sparse.RefineStop
public import HexGraphIso.Nauty.Sparse.SpecCanon
public import HexGraphIso.Nauty.Sparse.TargetTransport
public import HexGraphIso.Nauty.Sparse.RefineTransport
public import HexGraphIso.Nauty.Sparse.RefineLiteral
public import HexGraphIso.Nauty.Sparse.CountConstant
public import HexGraphIso.Nauty.Sparse.CompactIndex
public import HexGraphIso.Nauty.Sparse.IndexFrame
public import HexGraphIso.Nauty.Sparse.IndexTwo
public import HexGraphIso.Nauty.Sparse.MinimaPerm
public import HexGraphIso.Nauty.Sparse.Recover
public import HexGraphIso.Nauty.Sparse.PolicyScratch
public import HexGraphIso.Nauty.Sparse.RefineBounds
public import HexGraphIso.Nauty.Sparse.SearchBounds
public import HexGraphIso.Nauty.Sparse.Reach
public import HexGraphIso.Nauty.Sparse.Fuel
public import HexGraphIso.Nauty.Sparse.ReferenceResult
public import HexGraphIso.Nauty.Sparse.StoreResult
public import HexGraphIso.Nauty.Sparse.LeafAutom
public import HexGraphIso.Nauty.Sparse.SmallStep
public import HexGraphIso.Nauty.Sparse.CheapLeaves
public import HexGraphIso.Nauty.Sparse.RootHistory
public import HexGraphIso.Nauty.Sparse.ComparisonOps
public import HexGraphIso.Nauty.Sparse.CheapAdmission
public import HexGraphIso.Nauty.Sparse.TargetHint
public import HexGraphIso.Nauty.Sparse.DescentAt
public import HexGraphIso.Nauty.Sparse.FirstReturn
public import HexGraphIso.Nauty.Sparse.TraceResult
public import HexGraphIso.Nauty.Sparse.Orbits
public import HexGraphIso.Nauty.Sparse.OrderStep
public import HexGraphIso.Nauty.Sparse.Fixed
public import HexGraphIso.Nauty.Sparse.PathState
public import HexGraphIso.Nauty.Sparse.PairsResult
public import HexGraphIso.Nauty.Sparse.Prune
public import HexGraphIso.Nauty.Sparse.RouteKey
public import HexGraphIso.Nauty.Sparse.CodeResult
public import HexGraphIso.Nauty.Sparse.CanonGuide
public import HexGraphIso.Nauty.Sparse.ReturnOrigin
public import HexGraphIso.Nauty.Sparse.FilterPrune
public import HexGraphIso.Nauty.Sparse.CanonCover
public import HexGraphIso.Nauty.Sparse.CodeBound
public import HexGraphIso.Nauty.Sparse.LeafBound
public import HexGraphIso.Nauty.Sparse.OrbitCover
public import HexGraphIso.Nauty.Sparse.TraceOrbit
public import HexGraphIso.Nauty.Sparse.MaxReject
public import HexGraphIso.Nauty.Sparse.ReceiveCover
public import HexGraphIso.Nauty.Sparse.MaxTarget
public import HexGraphIso.Nauty.Sparse.MaxCheap
public import HexGraphIso.Nauty.Sparse.MaxUpperNode
public import HexGraphIso.Nauty.Sparse.MaxFirstLeaf
public import HexGraphIso.Nauty.Sparse.MaxFirstResume
public import HexGraphIso.Nauty.Sparse.MaxUpperResult
public import HexGraphIso.Nauty.Sparse.MaxEmitter
public import HexGraphIso.Nauty.Sparse.MaxAutoCanon
public import HexGraphIso.Nauty.Sparse.MaxCoset
public import HexGraphIso.Nauty.Sparse.MaxNode
public import HexGraphIso.Nauty.Sparse.GenerationTrace
public import HexGraphIso.Nauty.Sparse.FirstSweep
public import HexGraphIso.Nauty.Sparse.FirstWitness
public import HexGraphIso.Nauty.Sparse.UniformReturn
public import HexGraphIso.Nauty.Sparse.ReferenceOrbit
public import HexGraphIso.Nauty.Sparse.ReferenceLoop
public import HexGraphIso.Nauty.Sparse.ReferenceComplete
public import HexGraphIso.Nauty.Sparse.GeneratedRoot
public import HexGraphIso.Nauty.Sparse.SmallUniform
public import HexGraphIso.Nauty.Sparse.GeneratedReceipt
public import HexGraphIso.Sparse.UncoloredOps

/-!
Native sparse coloured graphs, checked transporters, and total sparse-nauty
result extraction. The production search and parser are total, and the
canonical forms and complete decisions satisfy their declarative contracts.
-/
