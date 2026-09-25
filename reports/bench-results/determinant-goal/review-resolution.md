# Experimental implementation review resolution

The read-only Opus review is retained in [opus-final-review.txt](opus-final-review.txt).
Its findings were checked against the local source and handled as follows.

1. **Audits concealed first-pass failures:** added `bounded_first`, which disables
   the second scalar pass. Rank-one quotients, product denominators, nested
   quotients and inverse products close through it. Atom-level checks also require
   successful monomial splitting. Validation asserts the dependencies printed by
   every accepted audit theorem, in addition to per-sample assertions.
2. **Opaque product denominators:** bounded scalar normalization now applies to
   denominators and inverse arguments too. A multi-term argument remains opaque.
   Added a product-denominator measurement direction and direct correctness tests.
3. **Scalar multiplication swallowed refusal:** exceptions propagate from that
   branch during speculation. Tests check atom rollback for scalar multiplication,
   nested successful division followed by refusal, and a large polynomial power.
4. **Timeout limits:** an invocation now requires its full requested time; otherwise
   the batch records `budget`. The suggestion to ignore smaller-ceiling timeouts
   was not adopted: the user's instruction forbids escalating after a timeout.
   Reports identify each recorded ceiling and do not infer a 60-second tactic
   runtime from a shorter or process-level timeout.
5. **Guard tests could launch Lean on regression:** all guard subprocesses use
   `--admission-only`; successful admission returns before creating a sample.
6. **Directory-scoped ledger:** all this goal's runs use the same documented round
   parent and are counted together. This is explicitly a local experiment harness,
   not global accounting across arbitrary directories. The serial lock and refusal
   of unfinished cases protect this round; changing parents to evade it is forbidden.
7. **Meta-state rollback:** both speculative evaluators restore saved Meta state,
   as well as atom state, when discarding normalization.
8. **Unbounded second comparison:** retained as an experimental limitation under
   the invocation ceiling; the production proposal requires a separate bound.
9. **Positional flags:** retained solely to reproduce historical experiment arms.
   The production recommendation requires a scalar-policy type instead.

The proposal also distinguishes semiring/ring instance parameters when suggesting
reuse of existing congruence lemmas. That substitution has not been measured.
Only controlled direct-versus-compact results isolate proof assembly; comparisons
against Mathlib also include normalization-policy differences.
