# Proof examples and paired measurements

The `libraries.yml` `proof_probes` field identifies build-only proof sources.
A few representative files built on every PR satisfy Phase 4. A larger suite
is retained only when its SPEC names a choice or independent measured contract
that paired fresh-module evidence can affect. Absolute timing ladders inherited
from the generic proof-track contract do not by themselves name such a choice.
Ordinary correctness tests remain in library and conformance targets.

| Declared root | Evidence | Lean files | Decision or correctness coverage |
| --- | --- | ---: | --- |
| `bench/HexRationalFn/ProofProbe` | CI examples | 3 | accepted literal Bezout replay and a corrupted identity. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexRealFormulaMathlib/ProofProbe` | CI examples | 3 | parameterized reification and quantifier alternation. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexPermGroupMathlib/ProofProbe` | CI examples | 1 | One kernel replay/tactic example; no timing harness. |
| `bench/HexGraphIso/ProofProbe` | CI examples | 5 | positive/negative dense and ordered-colour replay. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexGraphIso/SparseProofProbe` | CI examples | 5 | positive/negative sparse and ordered-colour replay. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexGraphIsoMathlib/ProofProbe` | CI examples | 3 | positive and negative Mathlib graph replay. No paired measurement selects an algorithm, representation or policy. |
| [`bench/HexPrimality/ProofProbe`](../HexPrimality/SPEC/hex-primality.md) | Paired decision | 225 | Stage-2/construction policy and certificate replay alternatives; HexPrimality SPEC §construction and caller resources. |
| `bench/HexIntFactor/ProofProbe` | CI examples | 4 | small and ten-node factor-certificate replay and primality exhaustion. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexMvPolyMathlib/ProofProbe` | CI examples | 1 | ordinary kernel polynomial cancellation, powers and coefficient lookup. No paired measurement selects an algorithm, representation or policy. |
| [`bench/HexKroneckerMathlib/ProofProbe`](../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md) | Paired decision | 189 | Winning regimes against ring/grobner determine eligibility for default chains; companion SPEC §proof probes. |
| `bench/HexRowReduceMathlib/ProofProbe` | CI examples | 6 | inverse results, product equalities, singularity, unique/affine solutions and inconsistency. No paired measurement selects an algorithm, representation or policy. |
| [`bench/HexCharPolyMathlib/ProofProbe`](../HexCharPolyMathlib/SPEC/hex-char-poly-mathlib.md) | Paired decision | 4 | Packed versus original/scalar kernel targets guide certificate optimization; SPEC §char_poly and SPEC/matrix-tactics §The bar against Mathlib. |
| `bench/HexMinPolyMathlib/ProofProbe` | CI examples | 4 | cyclic, repeated-block, nilpotent and rational minimal polynomials. No paired measurement selects an algorithm, representation or policy. |
| [`bench/HexBareissMathlib/ProofProbe`](../HexBareissMathlib/SPEC/hex-bareiss-mathlib.md) | Paired decision | 21 | Independent numeric determinant measured contract against eval_det; SPEC §Comparator and SPEC/matrix-tactics §The bar against Mathlib. |
| `bench/HexDeterminantalIdealMathlib/ProofProbe` | CI examples | 3 | full and deficient rank loci. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexRankMathlib/ProofProbe` | CI examples | 6 | full and deficient integer ranks and rational, quadratic and number-field carriers. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexGenericRankMathlib/ProofProbe` | CI examples | 4 | generic rank, discharged hypotheses, residual side goals and finite characteristic. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexPolyDetMathlib/ProofProbe` | CI examples | 5 | numeric, symbolic and quotient equalities plus numeric and symbolic result production. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexHermiteMathlib/ProofProbe` | CI examples | 4 | tall and empty kernel bases, membership and nonmembership. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexSmithMathlib/ProofProbe` | CI examples | 4 | chain, deficient, rectangular and empty quotient presentations. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexBerlekampMathlib/ProofProbe` | CI examples | 3 | factorization, irreducibility and repeated factors. No paired measurement selects an algorithm, representation or policy. |
| [`bench/HexPrimalityMathlib/ProofProbe`](../HexPrimalityMathlib/SPEC/hex-primality-mathlib.md) | Paired decision | 27 | Same-input trial/certificate crossover selects the norm_num threshold; bridge SPEC §positive policy. |
| [`bench/HexECPPMathlib/ProofProbe`](../HexECPPMathlib/SPEC/hex-ecpp-mathlib.md) | Paired decision | 20 | Replay/parser policy defaults and admitted endpoint sizes; SPEC §Conformance and evidence. |
| `bench/HexBerlekampZassenhausMathlib/ProofProbe` | CI examples | 4 | factorization, irreducibility, repeated factors and literal replay. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexIntervalMathlib` | CI examples | 2 | direct and reflected centered-interval proofs. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexRealRootsMathlib/ProofProbe` | CI examples | 3 | natural and refined isolation plus real-closed replay. No paired measurement selects an algorithm, representation or policy. |
| `bench/HexSignDetMathlib/ProofProbe` | CI examples | 5 | Five representative replay/sign/completion/re-encoding/nested examples; diagnostics outside the root. |
| `bench/HexRCF/ProofProbe` | CI examples | 4 | quadratic positivity, an existential witness and registered real constants. No paired measurement selects an algorithm, representation or policy. |

The shared `scripts/bench/fresh_module_sweep.py` runner remains for the
primality policy, numeric determinant and Kronecker decisions. Its tests and
build-only/Mathlib import lints remain useful. ECPP's endpoint experiments and
characteristic-polynomial comparisons use their existing focused drivers.
The generic sweep drivers, generation grids, import-only controls, raw results
and proof-only headline reports of the reduced roots are removed. The
sign-determination archived sources and completed samples remain as specified
by its evidence contract. No replacement harness or CI job is needed.

CPU leasing lives in `scripts/bench/cpu_lease.py`; compiled measurement drivers
use it independently of proof probes. Phase state and computational LeanBench
contracts are unchanged.
