# hex-lll

`hex-lll` implements Lenstra-Lenstra-Lovász reduction for integer row
bases. It depends on `hex-matrix` and `hex-gram-schmidt` and has no
Mathlib dependency.

The public implementation has two reduction functions:

- `lllNative`, an exact Lean implementation using only integer
  arithmetic;
- `lll`, which may ask an installed external reducer for a candidate,
  verifies the candidate exactly, and otherwise uses `lllNative`.

The external reducer is an acceleration mechanism. Its output has no
logical authority.

## Mathematical predicates

For an integer matrix `b : Matrix Int n m`, the row lattice is

```lean
def Matrix.memLattice (b : Matrix Int n m) (v : Vector Int m) : Prop :=
  ∃ c : Vector Int n, Matrix.vecMul c b = v
```

`Matrix.independent b` says that the rows are linearly independent.
`isLLLReduced b δ η` combines:

1. size reduction, `|μᵢⱼ| ≤ η` for `j < i`;
2. the Lovász inequalities with parameter `δ`.

The native function proves the classical size bound `η = 1/2` and
accepts `1/4 < δ ≤ 1`. The accelerated public function certifies the
slightly wider bound `η = 11/20` and accepts `121/400 < δ ≤ 1`.
The native result is therefore also valid for the public bound.

The public correctness theorems state:

- equality of the input and output row lattices;
- preservation of row independence;
- `isLLLReduced` for the stated parameters;
- the usual first-row short-vector estimate.

At `δ = 3/4`, the native estimate gives
`‖b₁‖ ≤ 2^((n-1)/2) λ₁`.

## Exact integer representation

`LLLState n m` stores:

- the current row basis `b`;
- Gram determinants `d₀, ..., dₙ`;
- scaled Gram-Schmidt coefficients
  `νᵢⱼ = d_(j+1) μᵢⱼ`.

The invariants `d_eq` and `ν_eq` relate these integers to the
mathematical Gram-Schmidt quantities. Rational coefficients are
noncomputable projections used in proofs; the executable reduction
never stores or computes them.

`LLLState.ofBasis` constructs the initial state from the exact integer
Gram-Schmidt calculation. The main transformations are:

- `sizeReduce`, which replaces a row by an integer row combination and
  updates the affected scaled coefficients;
- `swapStep`, which swaps adjacent rows and updates the affected Gram
  determinants and scaled coefficients by exact division;
- the main reduction loop, which alternates size reduction and Lovász
  tests.

The transformations use targeted row, vector, and matrix updates. A
size-reduction step changes only one basis row and one initial segment
of a scaled-coefficient row. A swap changes only the two basis rows,
one Gram determinant, and the two affected coefficient rows or
columns.

## Exact division

Every division in `swapStep` is proved exact from determinant
identities. Executable division is performed by `Matrix.exactDiv` and
its checked companions. A failed divisibility check is represented
explicitly; it is never justified by truncating integer division.

The proof modules separate:

- the integer Gram-Schmidt identities;
- the state invariant;
- size-reduction preservation;
- adjacent-swap preservation;
- termination through the decreasing determinant potential;
- reducedness and lattice preservation;
- the short-vector theorem.

`HexLLL.Reduction` is the supported reduction surface.
`HexLLLMathlib.ReductionInvariant` contains the state invariant used by the
Mathlib proof of that surface.

## Certified external reduction

An external reducer receives the row-major input matrix and requested
parameters. It returns:

- a proposed reduced basis `B'`;
- an integer matrix `U` with `U B = B'`;
- optionally an integer matrix `V` intended to be `U⁻¹`.

`certCheck` accepts the candidate only after checking:

1. all array dimensions;
2. `U B = B'`;
3. the inverse identities when `V` is present;
4. exact reducedness of `B'`;
5. the row-lattice equality witnessed by the transformations.

Malformed arrays, arithmetic disagreement, an unavailable external
function, or a failed reducedness check all select `lllNative`.
Consequently the theorem for `lll` does not assume that the external
function is correct.

The shared-library loader is explicit. `lll.loadExternalReducer path` loads a
named library and resolves the documented symbol. There is no
environment-variable lookup and no implicit library load. A function
linked directly into the process may be found by the one-time static
symbol lookup.

The requested floating-point parameters include a margin inside the
certified `(δ, 11/20)` bounds. The checker always verifies the public
bounds, not the requested approximations.

## Short-vector entry points

`lllNative.shortVectors` returns the complete reduced row basis from
the exact reducer. `lll.firstShortVector` returns the first row of the
certified public reduction.

Berlekamp-Zassenhaus recombination uses the complete reduced rows:
after a Gram-Schmidt length cut, it projects them to the coordinates
that indicate selected lifted factors. The short-vector theorem is
also exposed for clients that need only the first-row approximation.

## Mathlib companion

`hex-lll-mathlib` identifies executable row-lattice membership with
membership in the Mathlib submodule generated by the rows. It also
proves the prefix-submodule facts needed by the logarithmic-derivative
lattice argument.

## Native linkage

The root library always contains the exact Lean implementation.
Executables that use the optional external reducer must link the FFI
object listed in `lakefile.lean`. The release includes the
`hexlll_external_reduction` executable, which checks both the absent case
and explicit loading of a shared library.

## Verification

Changes must pass:

- the root build and trust-surface check;
- LLL conformance fixtures;
- exact-reduction and certified-external-reduction tests;
- native linkage checks with and without an installed external
  reducer;
- benchmark verification across the six input families listed in
  `HexLLL/PERFORMANCE.md`.

Performance reports state the source revision, Lean toolchain,
machine, CPU placement, input corpus, repetitions, timeout, and
external reducer revision. Raw external reduction, Lean exact
reduction, Lean-certified external reduction, and the corresponding
verified Isabelle measurements remain separate series.
