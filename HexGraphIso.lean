/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Perm
public import HexGraphIso.Colored
public import HexGraphIso.Iso
public import HexGraphIso.Limits
public import HexGraphIso.Nauty.Search.Bits
public import HexGraphIso.Nauty.Search.VSet
public import HexGraphIso.Nauty.Search.Refine
public import HexGraphIso.Nauty.Spec.Equivariance
public import HexGraphIso.Nauty.Search.Search
public import HexGraphIso.Nauty.Spec.CanonSpec
public import HexGraphIso.Nauty.Spec.CellPerm
public import HexGraphIso.Nauty.Spec.CellPermLoop
public import HexGraphIso.Nauty.Spec.SpecIso
public import HexGraphIso.Kernel.IsoLit
public import HexGraphIso.Kernel.Packed
public import HexGraphIso.Kernel.CheckKey
public import HexGraphIso.Kernel.RootCode
public import HexGraphIso.Nauty.Cert.Cert
public import HexGraphIso.Nauty.Cert.CertAutom
public import HexGraphIso.Nauty.Cert.CanonForm
public import HexGraphIso.Nauty.Invariant.Refine
public import HexGraphIso.Nauty.Invariant.Leaves
public import HexGraphIso.Nauty.Invariant.Codes
public import HexGraphIso.Nauty.Invariant.Refine
public import HexGraphIso.Nauty.Cert.TraceAgree
public import HexGraphIso.Nauty.Invariant.Store
public import HexGraphIso.Nauty.SmallCell.Guard
public import HexGraphIso.Nauty.SmallCell.Branch
public import HexGraphIso.Nauty.SmallCell.Descent
public import HexGraphIso.Nauty.SmallCell.Flips
public import HexGraphIso.Nauty.SmallCell.Flips
public import HexGraphIso.Nauty.SmallCell.Leaves
public import HexGraphIso.Nauty.SmallCell.Transitive
public import HexGraphIso.Nauty.SmallCell.Exotic
public import HexGraphIso.Nauty.SmallCell.TwoTriple
public import HexGraphIso.Nauty.SmallCell.FourCell
public import HexGraphIso.Nauty.SmallCell.Transitive
public import HexGraphIso.Nauty.Cert.CertTotal
public import HexGraphIso.Nauty.Cert.CertReplay
public import HexGraphIso.Nauty.Cert.CertStore
public import HexGraphIso.Nauty.Invariant.Coverage
public import HexGraphIso.Nauty.Correct.Outcome
public import HexGraphIso.Nauty.Correct.Base
public import HexGraphIso.Nauty.Correct.Unwind.Target
public import HexGraphIso.Nauty.Correct.Unwind.Located
public import HexGraphIso.Nauty.Correct.Unwind.Trail
public import HexGraphIso.Nauty.Correct.State.Induction
public import HexGraphIso.Nauty.Correct.State.Ledger
public import HexGraphIso.Nauty.Correct.Frames
public import HexGraphIso.Nauty.Correct.RunInv.History
public import HexGraphIso.Nauty.Correct.RunInv.Mutual
public import HexGraphIso.Nauty.Correct.RunInv.Coset
public import HexGraphIso.Nauty.Correct.Exit.Final
public import HexGraphIso.Nauty.Correct.Exit.Classify
public import HexGraphIso.Nauty.Correct.Sweep.Base
public import HexGraphIso.Nauty.Correct.Sweep.Carry
public import HexGraphIso.Nauty.Correct.Sweep.Node
public import HexGraphIso.Nauty.Correct.OffPath.Loop
public import HexGraphIso.Nauty.Correct.OffPath.Node
public import HexGraphIso.Nauty.Correct.FirstPath.Loop
public import HexGraphIso.Nauty.Correct.FirstPath.Hyp
public import HexGraphIso.Nauty.Correct.FirstPath.Sweep
public import HexGraphIso.Nauty.Correct.Certify
public import HexGraphIso.Nauty.Equitable.Root
public import HexGraphIso.Nauty.Invariant.Reach
public import HexGraphIso.Nauty.Cert.Translator
public import HexGraphIso.Nauty.Spec.SpecCanon
public import HexGraphIso.Nauty.Spec.Achieved
public import HexGraphIso.Nauty.Model.Node
public import HexGraphIso.Nauty.Model.Autom
public import HexGraphIso.Nauty.Model.Store
public import HexGraphIso.Nauty.Invariant.Orbits
public import HexGraphIso.Nauty.Invariant.Stabilize
public import HexGraphIso.Nauty.Invariant.Autos
public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.Invariant.Incumbent
public import HexGraphIso.Nauty.Invariant.Closure
public import HexGraphIso.Nauty.Invariant.Incumbent
public import HexGraphIso.Nauty.Invariant.Orbits
public import HexGraphIso.Nauty.Equitable.Basic
public import HexGraphIso.Nauty.Equitable.Step
public import HexGraphIso.Nauty.Equitable.Fix
public import HexGraphIso.Nauty.Invariant.TargetCell
public import HexGraphIso.Ops
public import HexGraphIso.Autos
public import HexGraphIso.Uncolored
public import HexGraphIso.Random
public import HexGraphIso.Tactic
public import HexGraphIso.Families

public section

/-!
`HexGraphIso` is the Mathlib-free coloured graph canonical labelling
library: nauty's individualization-and-refinement algorithm, run in Lean
and proved to compute the declarative canonical form `Nauty.specCanon`.

The user-facing surface is small. `Hex.GraphIso.canonicalize`, `canon` and
`label` are the canonical labelling, `findIso` and `isIso` decide
isomorphism, and `iso_iff_canon_eq` is the biconditional the whole
library exists to prove. `Nauty.certifyKey?` and `Nauty.checkCanon` are
the produce-then-replay pipeline for proof terms, and `Nauty.checkDiff`
its negative counterpart. `autos` reports the automorphism generators
the search discovers, with the vertex orbits, the orbit count and the
group order.
`Families` supplies the named deterministic graphs
and `Random` the reproducible pseudo-random ones.

The whole surface is mirrored on bare graphs. `Hex.Graph.Isomorphic` is
isomorphism of `Graph n`, `Graph.canon`, `Graph.findIso`, `Graph.isIso` and
`Graph.autos` are the operations, and `Graph.isomorphic_singleColor_iff` is the
equivalence through `Graph.singleColor` along which every uncoloured
theorem is transported.

The `graph_iso` tactic closes closed `Isomorphic` and `¬ Isomorphic` goals,
coloured or uncoloured, with a kernel-checked proof; importing
`HexGraphIsoMathlib` extends the same tactic to Mathlib `SimpleGraph` goals.

Everything under `Hex.GraphIso.Nauty` is the verified engine rather than
the intended entry point: it is exported so that proofs can cite it, not
because callers are expected to reach into it.
-/
