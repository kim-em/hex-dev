# hex-sturm-mathlib

Mathlib correspondence for the shared ordered-field query frontend.
This development library is not yet released.

`Domain` states the mathematical domain: a nonzero squarefree interpreted
polynomial, strictly ordered finite/infinite endpoints and nonvanishing at
finite endpoints. `query_isSome` and `prepare_isSome` characterize that domain
exactly. `prepare_sound` proves exact input bindings; `prepared_domain` proves
validity for every prepared object. `certify_checks` and `certifyPrepared_checks`
prove acceptance of produced literal certificates, and `check_domain` extracts
the mathematical domain from accepted replay. `query_rat_domain` proves that
positive denominator clearing preserves the complete failure domain between the
rational and integer/dyadic frontends; equality of successful values remains open.
The theorems permit noninjective coefficient interpretations and require no
field instance on noncanonical representatives.

The signed root-sum theorem, semantic replay soundness, root-count and singleton
results, whole-Option rational/backend correspondence and Phase-4 evidence remain
required. The shared IVT/Rolle and signed-remainder/Cauchy-index foundation is
an explicit proof gate, not an axiom. See [the specification](SPEC/hex-sturm-mathlib.md).
