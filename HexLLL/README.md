# hex-lll

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-lll` provides executable LLL reduction of an integer lattice basis,
following Cohen's integer-only recurrence. It depends on
[`hex-gram-schmidt`](https://github.com/kim-em/hex-gram-schmidt) for the
integer Gram-Schmidt data the algorithm carries. See
[`hex-lll-mathlib`](https://github.com/kim-em/hex-lll-mathlib) for the
correspondence with Mathlib and the full reducedness and short-vector theory.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-lll"
git = "https://github.com/kim-em/hex-lll.git"
rev = "main"
```

```lean
import HexLLL

open Hex

-- A small integer lattice basis, one row per basis vector.
def B : Matrix Int 3 3 := Matrix.ofFn fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 0, 1 => 1 | 0, 2 => 1
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 2
  | 2, 0 => 3 | 2, 1 => 5 | 2, 2 => 6
  | _, _ => 0

-- Reduce the basis at the factor δ = 3/4; read off the shortest vector.
#eval lll.firstShortVectorUnchecked B (3 / 4) (by decide +kernel) (by decide +kernel) (by decide)
#eval lll.shortVectorsUnchecked B (3 / 4) (by decide +kernel) (by decide +kernel) (by decide)

-- The executable integer reducedness oracle.
#eval lllReducedInt (1 : Matrix Int 3 3) (3 / 4) (1 / 2)   -- true
```

# Functionality

- `lll`: LLL reduction of an integer basis at a rational factor `δ`, returning
  a `(δ, 11/20)`-reduced basis of the same lattice;
- `lll.firstShortVector` and `lll.shortVectors`: the shortest reduced row and
  the ordered reduced rows, the short-vector entry points for downstream
  consumers such as [`hex-berlekamp-zassenhaus`](https://github.com/kim-em/hex-berlekamp-zassenhaus);
- `lllNative`: the exact integer `d`/`ν` reducer at the classical `η = 1/2`
  bound, and proof-free `Unchecked` variants of the entry points;
- `LLLState` with `sizeReduce` and `swapStep`: the integer state and its
  step operations, with `LLLState.potential` and the noncomputable GS
  projection `LLLState.gramSchmidtCoeff`;
- `certCheck`: the integer certificate checker for an external reducer's
  output, and `lllReducedInt` / `lllReducedInterval`, the exact and
  fixed-precision reducedness oracles;
- `Matrix.memLattice`, `Matrix.independent`, and `Vector.normSq` for stating
  and checking the inputs and guarantees.

# Verification

The library is Mathlib-free, so the deep correctness of LLL lives in the
Mathlib bridge. What is proven here is the short-vector bound reduced to the
size-reduction hypothesis, and the same-lattice half of the external
certificate.

The short-vector bound, `short_vector_bound_of_size_bound`: a reduced,
independent basis has a first row no longer than `(1/(δ − η²))^(n-1)` times
any nonzero lattice vector.

```lean
theorem short_vector_bound_of_size_bound (b : Matrix Int n m) {δ η : Rat}
    (hli : Matrix.independent b) (hred : isLLLReduced b δ η)
    (hη : (1 / 2 : Rat) ≤ η) (hδη : η * η < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    {v : Vector Int m} (hv : Matrix.memLattice b v) (hv' : v ≠ 0) :
    (((b.row ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩).normSq : Int) : Rat) ≤
      (1 / (δ - η * η)) ^ (n - 1) *
        ((v.normSq : Int) : Rat)
```

The certificate's same-lattice clause, `Matrix.sameLatticeCert_sound`: when the
integer transforms check out, the input and candidate span the same lattice.

```lean
theorem sameLatticeCert_sound {B B' : Matrix Int n m} {U V : Matrix Int n n} :
    sameLatticeCert B B' U V = true →
      ∀ v, B.memLattice v ↔ B'.memLattice v
```

The end-to-end guarantees of `lll` are proved in
[`hex-lll-mathlib`](https://github.com/kim-em/hex-lll-mathlib): that its output
is `(δ, 11/20)`-reduced, spans the same lattice, and satisfies the short-vector
bound `lll_short_vector`, together with the certificate soundness theorem
`certCheck_sound`.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
