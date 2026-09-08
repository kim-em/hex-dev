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
public import HexGraphIso.Nauty.Policy.Result
public import HexGraphIso.Nauty.Policy.Complete
public import HexGraphIso.Nauty.Policy.CheapKey
public import HexGraphIso.Nauty.Policy.Prune
public import HexGraphIso.Nauty.Policy.Exhaustive
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
public import HexGraphIso.Nauty.Invariant.Store
public import HexGraphIso.Nauty.Equitable.Cells
public import HexGraphIso.Nauty.Equitable.Individualize
public import HexGraphIso.Nauty.Spec.Descent
public import HexGraphIso.Nauty.SmallCell.Count
public import HexGraphIso.Nauty.SmallCell.Flip
public import HexGraphIso.Nauty.SmallCell.Guard
public import HexGraphIso.Nauty.SmallCell.Shapes
public import HexGraphIso.Nauty.SmallCell.Transitive
public import HexGraphIso.Nauty.Cert.CertTotal
public import HexGraphIso.Nauty.Cert.CertReplay
public import HexGraphIso.Nauty.Cert.Certify
public import HexGraphIso.Nauty.Cert.CertStore
public import HexGraphIso.Nauty.Invariant.Coverage
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
public import HexGraphIso.Nauty.Invariant.Orbits
public import HexGraphIso.Nauty.Equitable.Basic
public import HexGraphIso.Nauty.Equitable.Step
public import HexGraphIso.Nauty.Equitable.Fix
public import HexGraphIso.Nauty.Invariant.TargetCell
public import HexGraphIso.Ops
public import HexGraphIso.Autos
public import HexGraphIso.AutTrace
public import HexGraphIso.AutComplete
public import HexGraphIso.AutIndiv
public import HexGraphIso.Uncolored
public import HexGraphIso.UncoloredComplete
public import HexGraphIso.Random
public import HexGraphIso.Tactic
public import HexGraphIso.Families

public section

/-!
`HexGraphIso` is the Mathlib-free coloured graph canonical labelling
library: nauty's individualization-and-refinement algorithm, run in Lean
and proved to compute the declarative canonical form `Nauty.specCanon`.

The user-facing surface is small. `Hex.GraphIso.canonicalize`, `canon`
and `label` are the canonical labelling, `findIso` and `isIso` decide
isomorphism, and `iso_iff_canon_eq` is the biconditional the whole
library exists to prove. `autos` reports the automorphism generators the
search discovers, with the vertex orbits, the orbit count and the group
order, and `Aut.gens`, `Aut.orbits`, `Aut.numOrbits` and `Aut.order` are
those four on their own. `Families` supplies the named deterministic
graphs and `Random` the reproducible pseudo-random ones.

The whole surface is mirrored on bare graphs. `Hex.Graph.Isomorphic` is
isomorphism of `Graph n`, `Graph.canon`, `Graph.findIso`, `Graph.isIso`
and `Graph.autos` are the operations, and
`Graph.isomorphic_singleColor_iff` is the equivalence through
`Graph.singleColor` along which every uncoloured theorem is transported.

The `graph_iso` tactic closes closed `Isomorphic` and `¬ Isomorphic`
goals, coloured or uncoloured, with a kernel-checked proof. Importing
`HexGraphIsoMathlib` extends the same tactic to Mathlib `SimpleGraph`
goals.

`Hex.GraphIso.Nauty` is the verified search and its proof, organized by
concept: `Search` is the structured executable, `Spec` the
declarative canonical form, `Cert` the certificates and the trusted
`checkCanon` replay, and `Policy` the generic recursion contracts and
engine correctness. `Generation`, `Invariant`, `Equitable`, `SmallCell`
and `Model` supply the supporting theories. The umbrella exports the canonicalization theory for proofs
that need it. Generation exposes its public contracts and small witness
types, keeping the larger implementation behind private imports.

`Hex.GraphIso.Kernel` holds the obligations `graph_iso` hands to the
kernel: `Kernel.checkIso` for a transporter, `Kernel.checkKey` for a
certificate replay and `Kernel.rootCode` for a root refinement code,
each spelled over packed `Nat` state and proved equal to the `Array`
definition the compiled search runs.
-/
