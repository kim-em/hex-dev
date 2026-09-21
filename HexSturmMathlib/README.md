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

The signed root-sum theorem, semantic replay soundness, root-count and singleton
results, and remaining Phase-4 evidence are still required. The shared IVT/Rolle and
signed-remainder/Cauchy-index foundation is an explicit gate for root-sum
semantics and their consequences. See [the specification](SPEC/hex-sturm-mathlib.md).
