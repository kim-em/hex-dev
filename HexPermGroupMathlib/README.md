# hex-perm-group-mathlib

Mathlib correspondences for [`hex-perm-group`](https://github.com/leanprover/hex-perm-group).
The companion identifies Hex's explicit `Fin n` permutations, generated
subgroups, orders, actions, stabilizers, blocks, normal structure, and product
constructions with Mathlib's group-theoretic objects.

```lean
import HexPermGroupMathlib

open Hex Hex.PermGroup

def transposition : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
def cycle : Perm 3 := ⟨#v[1, 2, 0], by decide, by decide⟩
def s3 : Group 3 := Group.ofGenerators #[transposition, cycle]

#eval s3.order -- 6
```

All algorithms and certificate checkers remain in the Mathlib-free library.
This package supplies correspondence proofs and Mathlib-facing APIs; it does
not enlarge the trusted runtime boundary.

# Quickstart

```toml
[[require]]
name = "hex-perm-group-mathlib"
git = "https://github.com/leanprover/hex-perm-group-mathlib.git"
rev = "main"
```

The companion manifest pins `hex-perm-group`; import `HexPermGroupMathlib` as
above.

# Functionality

The modules cover the permutation, generated-subgroup, action, block,
normal-structure, and wreath-product correspondences used by downstream
Mathlib developments.

# Verification

`HexPermGroupMathlib.Tests` builds the bridge contracts against the pinned
Mathlib revision while the computational package remains Mathlib-free.

# Contributing

Develop this companion in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo beside the computational surface it relates to Mathlib.
