/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Perm
public import HexGraphIso.Colored
public import HexGraphIso.Iso
public import HexGraphIso.Lex
public import HexGraphIso.Reference
public import HexGraphIso.Canon
public import HexGraphIso.Nauty.Bits
public import HexGraphIso.Nauty.Refine
public import HexGraphIso.Nauty.Image
public import HexGraphIso.Nauty.PopCount
public import HexGraphIso.Nauty.Equivariance
public import HexGraphIso.Nauty.Search
public import HexGraphIso.Nauty.CanonSpec
public import HexGraphIso.Nauty.CellPerm
public import HexGraphIso.Nauty.CellPermLoop
public import HexGraphIso.Nauty.SpecIso
public import HexGraphIso.IsoLit
public import HexGraphIso.NodeLit
public import HexGraphIso.Separator
public import HexGraphIso.Nauty.Cert
public import HexGraphIso.Nauty.CertAutom
public import HexGraphIso.ModuleBoundaryTests
public import HexGraphIso.Nauty.CanonForm
public import HexGraphIso.Nauty.TranscriptionInv
public import HexGraphIso.Nauty.LeafFaithful
public import HexGraphIso.Nauty.CodeFaithful
public import HexGraphIso.Nauty.SearchInv
public import HexGraphIso.Nauty.TraceAgree
public import HexGraphIso.Nauty.StoreValid
public import HexGraphIso.Nauty.SmallCell
public import HexGraphIso.Nauty.SmallCellBranch
public import HexGraphIso.Nauty.SmallCellIter
public import HexGraphIso.Nauty.SmallCellTriple
public import HexGraphIso.Nauty.SmallCellPair
public import HexGraphIso.Nauty.SmallCellLeaves
public import HexGraphIso.Nauty.SmallCellTie
public import HexGraphIso.Nauty.SmallCellExotic
public import HexGraphIso.Nauty.SmallCellExotic2
public import HexGraphIso.Nauty.SmallCellExotic3
public import HexGraphIso.Nauty.SmallCellAll
public import HexGraphIso.Nauty.FirstPath
public import HexGraphIso.Nauty.CertTotal
public import HexGraphIso.Nauty.CertReplay
public import HexGraphIso.Nauty.CertStore
public import HexGraphIso.Nauty.LoopCoverage
public import HexGraphIso.Nauty.SearchOutcome
public import HexGraphIso.Nauty.SearchOutcomeTarget
public import HexGraphIso.Nauty.SearchOutcomeLocated
public import HexGraphIso.Nauty.SearchOutcomeProof
public import HexGraphIso.Nauty.SearchOutcomeLocatedProof
public import HexGraphIso.Nauty.SearchOutcomeInduction
public import HexGraphIso.Nauty.SearchOutcomeFirst
public import HexGraphIso.Nauty.RootEquitable
public import HexGraphIso.Nauty.SearchReach
public import HexGraphIso.Nauty.Translator
public import HexGraphIso.Nauty.SpecCanon
public import HexGraphIso.Nauty.Achieved
public import HexGraphIso.Nauty.Complete
public import HexGraphIso.Nauty.SearchModel
public import HexGraphIso.Nauty.SearchAutom
public import HexGraphIso.Nauty.SearchOrbit
public import HexGraphIso.Nauty.Stabilize
public import HexGraphIso.Nauty.AutosLedger
public import HexGraphIso.Nauty.Domination
public import HexGraphIso.Nauty.QuartetStmt
public import HexGraphIso.Nauty.QuartetLoop
public import HexGraphIso.Nauty.QuartetNode
public import HexGraphIso.Nauty.OrbJoin
public import HexGraphIso.Nauty.Domination
public import HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
public import HexGraphIso.Nauty.TargetCell
public import HexGraphIso.Ops
public import HexGraphIso.Uncolored
public import HexGraphIso.Random
public import HexGraphIso.Tactic
public import HexGraphIso.Pairwise
public import HexGraphIso.PairwiseSound
public import HexGraphIso.Families

public section

/-!
`HexGraphIso` is the Mathlib-free coloured graph canonical labelling
library: nauty's individualization-and-refinement algorithm, run in Lean
and proved to agree with an exhaustive reference canonical form.

The user-facing surface is small. `Hex.GraphIso.canonicalize`, `canon` and
`label` are the fast canonical labelling; `Checked.canonicalize`, `Checked.canon`
and `Checked.label` are the twins that additionally validate every answer
through the certificate checker, with `canonicalize_eq_checked`
identifying the two. `findIso`, `isIso` and their `Checked` twins decide
isomorphism, and `Checked.iso_iff_canon_eq` is the biconditional the whole
library exists to prove. `certify?`, `checkCanon` and `canon?` are the
bounded produce-then-replay pipeline for proof terms, and `checkDiff` its
negative counterpart. `Families` supplies the named deterministic graphs
and `Random` the reproducible pseudo-random ones.

The whole surface is mirrored on bare graphs. `Hex.Graph.Isomorphic` is
isomorphism of `Graph n`, `Graph.canon`, `Graph.findIso` and their
`Graph.Checked` twins are the operations, and
`Graph.isomorphic_singleColor_iff` is the equivalence through
`Graph.singleColor` along which every uncoloured theorem is transported.

The `graph_iso` tactic closes closed `Isomorphic` and `¬ Isomorphic` goals,
coloured or uncoloured, with a kernel-checked proof; importing
`HexGraphIsoMathlib` extends the same tactic to Mathlib `SimpleGraph` goals.

Everything under `Hex.GraphIso.Nauty` is the verified engine rather than
the intended entry point: it is exported so that proofs can cite it, not
because callers are expected to reach into it.
-/
