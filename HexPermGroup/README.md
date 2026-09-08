# hex-perm-group

Checked finite permutation groups for Lean 4. The computational library is
Mathlib-free and represents every permutation on an explicit `Fin n` domain,
so declared fixed points are preserved.

# Quickstart

```toml
[[require]]
name = "hex-perm-group"
git = "https://github.com/leanprover/hex-perm-group.git"
rev = "main"
```

```lean
import HexPermGroup

open Hex Hex.PermGroup

def rotation : Perm 4 := ⟨#v[1, 2, 3, 0], by decide, by decide⟩
def reflection : Perm 4 := ⟨#v[0, 3, 2, 1], by decide, by decide⟩
def d4 : Group 4 := Group.ofGenerators #[rotation, reflection]

#eval d4.order                    -- 8
#eval (d4.stabilizer 0).order     -- 2
#eval d4.contains rotation
#eval (d4.word? rotation).isSome
```

# Functionality

Composition is a left action: `(p.comp q) x = p (q x)`. Programs returned by
`word?` use the original generator order and can be checked independently with
`checkWord`.

The public surface includes point and pointwise stabilizers, containment,
joins, element enumeration with output caps, left cosets, rank/unrank and
supplied-index sampling, finite tuple/subset/partition actions, images and
kernels, complete or budgeted subgroup search, blocks and primitivity, normal
closure, core, derived series, and direct and imprimitive wreath products.

`Group.buildWith` and the bounded normal/product operations reserve cumulative
producer work before each operation. Exhaustion returns the proved stopping
state only: it never means negative membership, exact ambient order,
nonsolvability, or a final image/kernel. Certificate and program replay use
their own limits. A checked kernel boundary validates raw chains, programs,
actions, search trees, normal-structure traces, and product certificates
without trusting the producer that created them.

# Verification

Every group producer returns a chain accepted by `checkChain`, and the theorem
surface connects acceptance, membership, order, rank, actions, search, normal
structure, and products to their mathematical specifications. Conformance
fixtures are independently checked by a small-degree enumerator and GAP.

The Mathlib correspondence layer is published separately as
[`hex-perm-group-mathlib`](https://github.com/leanprover/hex-perm-group-mathlib).

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo. Run `lake build`, the
`HexPermGroup.Conformance` target, and `hexpermgroup_bench verify` before
submitting changes.
