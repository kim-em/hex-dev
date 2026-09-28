# hex-sturm-mathlib

Mathlib correspondence for the shared ordered-field query frontend.
This development library is not yet released.

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

`query_congr` proves whole-`Option` agreement between field representations
at corresponding finite or infinite endpoints, allowing positive scaling of
both polynomial inputs. `check_congr` compares arbitrary accepted certificates.
`DenominatorClearing.certificate_checks` proves acceptance of translated rational
evidence over the integers; `IntCast.certificate_checks` embeds integer evidence
and its endpoints into the rational frontend. These translations retain the
full context and value and do not rerun the polynomial producer.

The integer query-one count follows from the existing real Sturm theorem;
`query_rat_count` and `query_rat_nonneg` transport it to rational polynomials
on dyadic intervals. The generic signed root-sum theorem, semantic replay
soundness, arbitrary ordered-field count and singleton results, and remaining
Phase-4 evidence are still required. The shared IVT/Rolle and
signed-remainder/Cauchy-index foundation is an explicit gate for root-sum
semantics and their consequences. See [the specification](SPEC/hex-sturm-mathlib.md).

The optional development target `HexQuerySemantics` builds
`adapters/HexSturmMathlib/Soundness.lean` together with the BKR root-semantics
modules. They prove field-query and sign-table consequences of the named
`HexRealRootsMathlib.Tarski.check_rootSum` statement, whose proof is admitted
under #10389. These modules are not published; their dependency probes audit
the admission rather than establish independent query correctness.

Executable translations live in Mathlib-free `HexSturm.Transport`; see the
[SPEC](SPEC/hex-sturm-mathlib.md) for their endpoint and binding contracts.
