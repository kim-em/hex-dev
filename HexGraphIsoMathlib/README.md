# hex-graph-iso-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence and tactic layer for
[`hex-graph-iso`](https://github.com/leanprover/hex-graph-iso). It gives
Mathlib-facing ordered-coloured graphs over an arbitrary finite vertex type,
finite encodings into the dense and sparse executable representations with their
correspondence theorems, and extends `graph_iso` to closed `SimpleGraph`
goals.

# Quickstart

```toml
[[require]]
name = "hex-graph-iso-mathlib"
git = "https://github.com/leanprover/hex-graph-iso-mathlib.git"
rev = "main"
```

```lean
import HexGraphIsoMathlib

open SimpleGraph

def c5a : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j => j = i + 1
def c5b : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j => j = i + 2
def p5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j => j.val = i.val + 1

instance : DecidableRel c5a.Adj := fun _ _ =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj ..).symm
instance : DecidableRel c5b.Adj := fun _ _ =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj ..).symm
instance : DecidableRel p5.Adj := fun _ _ =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj ..).symm

example : c5a ≃g c5b := by graph_iso
example : IsEmpty (c5a ≃g p5) := by graph_iso
```

# Functionality

- `Colored V k` is a `SimpleGraph V` on a `Fintype` together with a
  surjective ordered colouring into `Fin k`. `Colored.ofColor?` is the
  checked constructor; it declines rather than silently compressing or
  reordering unused colours. `onecell` is the one-cell view of a bare
  `SimpleGraph` over a nonempty vertex type.
- `Colored.Iso` and `Colored.Isomorphic` are the Mathlib-side
  colour-preserving isomorphism and its `Nonempty` form.
- `encode` transports a Mathlib coloured graph along an equivalence
  `V ≃ Fin n` into the executable `Hex.GraphIso.Colored n k`;
  `encode_adj`, `encode_color`, and `encode_iso_iff` are the
  correspondence theorems.
- `Sparse.encode` constructs native sparse rows without allocating a dense
  matrix. Given an arbitrary decidable adjacency relation, it still tests
  vertex pairs. `Sparse.encode_iso_iff`, `Sparse.iso_iff_canon_eq` and
  `Sparse.canon_encode_eq` prove isomorphism correspondence, canonical-form
  correctness and independence from the chosen enumeration.
- Direct `graph_iso` calls on Mathlib goals use the dense encoding. To
  select sparse nauty, apply `Sparse.encode_iso_iff` in the proof and then
  call `graph_iso` on the resulting sparse goal. `Sparse.isoOfFindIso`
  also decodes a transporter returned by the total sparse API.
- `Sparse.autos_complete` proves that the decoded sparse generators
  generate the full colour-preserving Mathlib automorphism group.
  `Sparse.autos_sameOrbit`, `Sparse.autNumOrbits_card` and
  `Sparse.autOrder_card` identify the reported orbits, orbit count and
  group order with the full group's action and cardinality.
- `colored_iso_iff_canon_eq` is the headline equivalence: Mathlib-side
  isomorphism holds exactly when the executable certified canonical forms of
  the two encodings agree.
- `graph_iso` gains `SimpleGraph` goals (`G ≃g H`, `Nonempty (G ≃g H)`,
  `IsEmpty (G ≃g H)`, `¬ Nonempty (G ≃g H)`) and the corresponding
  `Colored.Iso` and `Colored.Isomorphic` goals, reusing the Mathlib-free
  search under the same tactic name. It accepts the same two limits,
  `(maxSearchNodes := ...)` and `(maxCertRecords := ...)`, and does not
  reinterpret them. Kernel replay uses Lean's actual resource controls.

# Verification

This library adds no search and no decision procedure. A positive goal
encodes both graphs, runs the Mathlib-free `findIso`, and emits a literal
transporter the kernel checks through `Kernel.checkIso` and
`Kernel.isIso_of_checkIso`, exactly as the Mathlib-free tactic does. A
negative goal takes the same root-separator and certificate-replay routes
and decodes the result through the `not_encode_iso` theorems. Cardinality
and colour-class refutations (`isEmpty_iso_of_card_ne`,
`not_isomorphic_of_card_color_ne`) are proved on the Mathlib side and run
before any search.

```lean
theorem encode_iso_iff (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔
      Hex.GraphIso.Isomorphic (encode eV G) (encode eW H)

theorem colored_iso_iff_canon_eq (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔
      canon (encode eV G) = canon (encode eW H)
```

Use [`hex-graph-iso`](https://github.com/leanprover/hex-graph-iso) alone for
Mathlib-free computation. See the
[SPEC](SPEC/hex-graph-iso-mathlib.md) for the encoding contract, tactic
registration, and failure semantics.
The [manual](https://kim-em.github.io/hex-dev/HexGraphIso___-coloured-graph-canonical-labelling/The-Mathlib-correspondence/)
includes a sparse-search recipe whose definitions and conclusions use
Mathlib types, with the encoding confined to the proofs.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
