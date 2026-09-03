# hex-graph-iso-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence and tactic layer for
[`hex-graph-iso`](https://github.com/leanprover/hex-graph-iso). It gives
Mathlib-facing ordered-coloured graphs over an arbitrary finite vertex type,
the finite encoding into the executable representation with its
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
  reordering unused colours. `Colored.singleColor` is the one-cell view of a bare
  `SimpleGraph` over a nonempty vertex type, and the zero-colour empty graph
  otherwise.
- `Colored.Iso` and `Colored.Isomorphic` are the Mathlib-side
  colour-preserving isomorphism and its `Nonempty` form.
- `encode` transports a Mathlib coloured graph along an equivalence
  `V ≃ Fin n` into the executable `Hex.GraphIso.Colored n k`;
  `encode_adj`, `encode_color`, and `encode_iso_iff` are the correspondence
  theorems, and `canon_encode_indep` shows the canonical form does not depend
  on the chosen enumeration.
- `colored_iso_iff_canon_eq` is the headline equivalence: Mathlib-side
  isomorphism holds exactly when the executable certified canonical forms of
  the two encodings agree.
- `graph_iso` gains `SimpleGraph` goals — `G ≃g H`, `Nonempty (G ≃g H)`,
  `IsEmpty (G ≃g H)`, `¬ Nonempty (G ≃g H)` — and the corresponding
  `Colored.Iso` / `Colored.Isomorphic` goals, reusing the Mathlib-free
  engine under the same tactic name.

# Verification

The bridge adds no search and no decision procedure. Every positive goal
emits a literal transporter that the kernel replays through the Mathlib-free
`checkIso?`, and every negative goal goes through the shared negative engine
and decodes across `not_encode_iso`. Cheap cardinality and colour-class
refutations (`isEmpty_iso_of_card_ne`,
`not_isomorphic_of_card_color_ne`) are proved on the Mathlib side.

```lean
theorem encode_iso_iff (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔
      Hex.GraphIso.Isomorphic (encode eV G) (encode eW H)

theorem colored_iso_iff_canon_eq (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔
      Checked.canon (encode eV G) = Checked.canon (encode eW H)

theorem canon_encode_indep (eV eV' : V ≃ Fin n) :
    Checked.canon (encode eV G) = Checked.canon (encode eV' G)
```

Use [`hex-graph-iso`](https://github.com/leanprover/hex-graph-iso) alone for
Mathlib-free computation. See the
[SPEC](SPEC/hex-graph-iso-mathlib.md) for the encoding contract, tactic
registration, and failure semantics.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
