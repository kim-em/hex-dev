# hex-sturm-mathlib

`HexSturmMathlib` is part of [Hex](https://github.com/kim-em/hex-dev), executable
computer algebra for Lean 4 developed from specifications and verified APIs.
It proves the domain, root-sum and certificate contracts for `HexSturm`.

It depends on `HexSturm`, `HexPolyMathlib` and `HexRealRootsMathlib`.
Mathlib and Tau Ceti belong to this proof layer. This development library
is not yet released.

The [manual chapter](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-sturm)
documents the computational API alongside its domain, replay and root-count
theorems.

# Quickstart

Use this import from the `hex-dev` monorepo; there is no released package yet.
The theorem connects a successful natural count to the existing integer count.
Its success hypothesis entails root-free endpoints.

```lean
import HexSturmMathlib
open Hex

example (p : DensePoly Rat) (interval : DyadicInterval) (n : Nat)
    (answer : Sturm.rootCount Sturm.orderSign p
      (.finite interval.lower.toRat)
      (.finite interval.upper.toRat) = some n) :
    (n : Int) =
      ZPoly.sturmCount (ZPoly.clearDenominators p).2 interval :=
  HexSturmMathlib.rootCount_sturm p interval n answer
```

# Functionality

`Domain` states the mathematical domain: a nonzero squarefree interpreted
polynomial, strictly ordered finite/infinite endpoints and nonvanishing at
finite endpoints. `query_isSome` and `prepare_isSome` characterize that domain
exactly. `prepare_sound` proves exact input bindings; `prepared_domain` proves
validity for every prepared object. `certify_checks` and `certifyPrepared_checks`
prove acceptance of produced literal certificates, and `check_domain` extracts
the mathematical domain from accepted replay. `query_rat_eq` proves whole-`Option`
agreement between rational and integer/dyadic queries after positive denominator
clearing, on finite ordered dyadic intervals. `check_rat_value` proves value
agreement for arbitrary accepted certificates on those corresponding inputs.
The theorems permit noninjective coefficient interpretations and require no
field instance on noncanonical representatives.

`withEndpoints_isSome` characterizes success of endpoint retargeting by the
same mathematical domain, and `withEndpoints_domain` proves validity for the
actual returned object. The core `PreparedDomain.withEndpoints_bindings`
theorem preserves the literal sign, head and chain and binds the new endpoints.
`certifyCountPrepared_checks` proves acceptance of query-one certificates made
from that stored chain. These results use the domain and arithmetic proofs.

`query_congr` proves whole-`Option` agreement between field representations
at corresponding finite or infinite endpoints, allowing positive scaling of
both polynomial inputs. `check_congr` compares arbitrary accepted certificates.
`DenominatorClearing.certificate_checks` proves acceptance of translated rational
evidence over the integers; `IntCast.certificate_checks` embeds integer evidence
and its endpoints into the rational frontend. These translations retain the
full context and value and do not rerun the polynomial producer.

# Verification

The shared Sturm–Tarski theorem proves root-sum semantics for arbitrary
accepted certificates over an ordered real closed field. `query_sound` and
`queryPrepared_sound` apply it to the ordinary and prepared producers;
`query_iff` characterizes both failure and the returned signed root sum;
`query_count`, `query_sign` and `query_bound` give counts, singleton signs and
degree bounds. `query_nonneg` justifies the exact natural-number conversion in
`Sturm.rootCount`, whose success domain is unchanged. `rootCount_sturm`
also bridges successful finite-dyadic natural counts to the existing half-open
integer Sturm count after positive denominator clearing; it does not change
that API's upper-endpoint-root behavior.
`countPrepared_sound` relates the actual prepared count to the number of
distinct roots in its current open interval through the proved shared theorem.
`countPrepared_nonneg` proves nonnegativity under the same coefficient laws
before a consumer converts the count to `Nat`.

`HexSturmMathlib.Soundness` belongs to the ordinary companion target and is
exported by `import HexSturmMathlib`. It consumes the shared semantics from
HexRealRootsMathlib; Tau Ceti remains confined to Mathlib companions. This
companion is still unreleased. Semantic regression tests build through
`HexQuerySemantics`, alongside the remaining owners’ development adapters.
Their axiom audits admit only `propext`, `Classical.choice` and `Quot.sound`. This theorem-only companion has no dedicated
Phase-4 performance deliverable. Ordinary-kernel correctness checks are built
by `HexSturmMathlibTests` and `HexQuerySemantics`; Phase-4 prerequisite
eligibility remains in the readiness audit. The public semantic import gap
is closed. See [the specification](SPEC/hex-sturm-mathlib.md).

Executable translations live in Mathlib-free `HexSturm.Transport`; see the
[SPEC](SPEC/hex-sturm-mathlib.md) for their endpoint and binding contracts.

# Contributing

Development happens in [hex-dev](https://github.com/kim-em/hex-dev).
Contributions are welcome as PRs to `SPEC/`: describe the behavior you want.
