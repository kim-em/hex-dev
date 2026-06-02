# HexGFq Phase 6 API Review

## Scope

Audited surfaces:

- `SPEC/Libraries/hex-gfq.md`
- `SPEC/Libraries/hex-conway.md`
- `PLAN/Phase6.md`
- `HexGFq/Basic.lean`
- `HexGFq/Conformance.lean`
- `HexGFq/CrossCheck.lean`
- `HexGFq.lean`
- `reports/hex-gfq-gf2q-equivalence-audit.md`
- `reports/hex-gfq-performance.md`

The review focused on the Mathlib-free canonical constructor layer:
generic `GFq`, packed binary `GF2q`, their constructor/projection
lemmas, automation annotations, import hygiene, and the boundary between
executable maps and Mathlib bridge equivalences.

## Prioritized Findings

### P1: Make the generic `GFq p n` constructor ergonomic for committed entries

The SPEC presents the user-facing constructor as `GFq p n`, with Conway
data selected automatically when a committed entry is available. The
current API still requires callers to pass an explicit
`Conway.SupportedEntry p n` argument:

- `GFq (p n : Nat) [ZMod64.Bounds p] (h : Conway.SupportedEntry p n)`
- `GFq.modulus h`
- `GFq.ofPoly h`

This is internally clean and keeps the finite committed-table evidence
explicit, but it means the user writes `GFq 2 1 Conway.supportedEntry_2_1`
rather than `GFq 2 1`. The packed binary side already has the better
ergonomic shape through `[Conway.PackedGF2Entry n]`, so users can write
`GF2q 1` and let instance synthesis find the entry.

The gap is visible in downstream call sites: conformance and benchmarks
define local aliases like `Entry21` and `Generic21` before using
`GFq.ofPoly` and `GFq.repr`. That is acceptable for internal tests, but
it is not yet the promised canonical user surface for committed Conway
entries.

Worker-sized follow-up:

- Add an ergonomic committed-entry layer for generic `GFq`, either by
  introducing typeclass-backed supported-entry instances or by adding a
  separate convenience abbreviation that preserves the explicit-evidence
  constructor.
- Provide matching `GFq.modulus`, `GFq.ofPoly`, `GFq.repr`, and
  `GFq.frob` wrappers for the ergonomic surface.
- Keep the existing explicit-entry API available for proofs that need to
  name the exact `SupportedEntry` witness.
- Verify downstream examples can state the committed generic field as
  `GFq 2 1` or an equivalently short canonical spelling without local
  `Entry21` plumbing.

### P1: Extend packed `GF2q` committed-entry coverage beyond `n = 1`

`HexConway/Basic.lean` already contains committed binary Conway entries
for degrees `2` through `6`, but `HexGFq/Basic.lean` only exposes a
`Conway.PackedGF2Entry` instance for `n = 1`. As a result, the optimized
constructor API has the right typeclass shape but only the trivial linear
field is available as a public committed `GF2q n`.

The broader packed-vs-generic story is exercised in
`HexGFq/CrossCheck.lean` at degrees `4`, `8`, `16`, and `32`, but those
fixtures use ad-hoc moduli rather than committed Conway entries. They are
valuable regression checks, not a public constructor surface.

Worker-sized follow-up:

- Add `Conway.PackedGF2Entry` instances for the committed binary Conway
  entries that fit the single-word packed representation, starting with
  `n = 2` through `n = 6`.
- For each instance, prove `conway_eq_packed`, `degree_pos`,
  `degree_lt_word`, and `packed_irreducible` from Lean-checked evidence.
- Extend `HexGFq/Conformance.lean` to cover at least one nontrivial
  committed packed entry, including `GF2q.modulus`, `GF2q.ofWord`,
  `GF2q.repr`, `GF2q.reprFpPoly`, and `GF2q.toGFq`.

### P2: Add a direct representative lemma for packed-word-to-generic projection

The packed side exposes the intended one-way Mathlib-free bridge:

- `GF2q.reprFpPoly`
- `GF2q.toGFq`
- `GF2q.toGFq_eq_ofPoly`
- `GF2q.toGFq_ofWord`
- `GF2q.toGFq_repr`

This keeps `RingEquiv` out of `HexGFq/Basic.lean`, which is the correct
layering decision. However, the most common executable bridge question is
whether `GF2q.toGFq (GF2q.ofWord w)` has the same generic representative
as reducing the low-bit `FpPoly 2` view of the packed result. Currently a
caller combines `toGFq_ofWord`, `toGFq_repr`, `repr_ofWord`, and
`reprFpPoly_eq_wordFpPoly`.

That is usable, but Phase 6's characterising-lemma standard favors one
named lemma for this common projection goal.

Worker-sized follow-up:

- Add a lemma such as `GF2q.toGFq_ofWord_repr` or
  `GF2q.repr_toGFq_ofWord` stating the representative of
  `GF2q.toGFq (GF2q.ofWord w)` directly in terms of
  `GFqRing.reduceMod`, `GFq.modulus`, and `GF2q.wordFpPoly`.
- Mark it `@[simp]` only if local tests show it does not duplicate or
  loop with the existing `toGFq_repr` and `toGFq_ofWord` rules.
- Add a tiny conformance example for the committed packed entry.

### P2: Keep Mathlib equivalence documentation at the constructor boundary

The absence of a Mathlib `RingEquiv` in `HexGFq/Basic.lean` is correct.
`reports/hex-gfq-gf2q-equivalence-audit.md` shows that the intended
equivalence belongs in `HexGFqMathlib/GF2q.lean`, where
`GF2q.equivGFq` already exists but is still proof-incomplete.

`HexGFq/Basic.lean` documents `GF2q.toGFq` as a map into the generic
canonical model, but it does not explicitly say that the bidirectional
equivalence is intentionally a bridge-layer theorem. A short module
comment sentence would prevent future workers from trying to import
Mathlib into the Mathlib-free constructor layer.

Worker-sized follow-up:

- In the `HexGFq/Basic.lean` module doc or near `GF2q.toGFq`, document
  that `GF2q.toGFq` is the Mathlib-free executable projection and that
  `GF2q.equivGFq` belongs in `HexGFqMathlib`.
- Do not import Mathlib or move equivalence declarations into
  `HexGFq/Basic.lean`.
- Cross-reference the existing bridge-layer audit in the follow-up issue
  body rather than duplicating its proof plan.

### P3: Recheck automation once the ergonomic constructor layer is added

The current wrapper lemmas are conservatively annotated. The
representative lemmas for `GFq` and `GF2q` are mostly `@[simp]`, and
field-level inverse/division facts are left untagged where broad
rewriting could be risky. No `grind` annotations are needed in this
thin wrapper today because the heavy algebraic automation lives in the
underlying field and packed backends.

After an ergonomic `GFq p n` layer is introduced, the project should
recheck whether its new wrapper lemmas are transparent enough for common
goals without forcing users to unfold the convenience abbreviation.

Worker-sized follow-up:

- Add small examples or conformance checks for `simp` over
  `GFq.modulus`, `GFq.repr (GFq.ofPoly ...)`, `GFq.repr (GFq.frob ...)`,
  and the analogous packed projection facts through the ergonomic layer.
- Prefer narrow `@[simp]` characterising lemmas over unfolding the
  constructor definition in downstream proofs.
- Add `@[grind]` only for facts that materially improve automated goals.

## Audited Surfaces With No Follow-Up Needed

- Generic constructor evidence: `GFq.modulus_nonconstant`,
  `GFq.modulus_irreducible`, and `GFq.modulus_prime` expose the
  Lean-checked Conway evidence needed to justify field construction.
- Generic representative API: `GFq.ofPoly`, `GFq.repr`, `GFq.ext`, and
  representative lemmas for zero, one, addition, multiplication,
  negation, subtraction, casts, scalar actions, powers, inverse-zero,
  division, and Frobenius let callers reason through named facts rather
  than unfolding `GFqField.FiniteField`.
- Packed constructor/projection API: `GF2q.supportedEntry`,
  `GF2q.lower`, `GF2q.modulus`, `GF2q.ofWord`, `GF2q.repr`,
  `GF2q.wordFpPoly`, `GF2q.reprFpPoly`, and `GF2q.toGFq` expose the
  expected single-word packed story for entries that have a
  `PackedGF2Entry` instance.
- Packed arithmetic representative API: addition, subtraction,
  multiplication, inverse, division, powers, and scalar actions all have
  public representative lemmas, with statements tied to the packed
  backend rather than to private proof scaffolding.
- Field-construction claims are backed by Lean evidence. The committed
  `GFq` path uses `Conway.conwayPoly_irreducible`; the committed packed
  `GF2q 1` path uses `packedGF2Entry_2_1_irreducible`; cross-check
  fixtures at higher degrees use local Lean certificates or checked
  irreducibility theorems.
- Import hygiene is clean. `HexGFq/Basic.lean` imports only
  Mathlib-free dependencies (`HexConway`, `HexGF2`, `HexGFqField`), and
  the root `HexGFq.lean` imports the API plus conformance/cross-check
  modules.
- Runtime bans are respected in the audited `HexGFq` files: no `sorry`,
  no `axiom`, and no `native_decide`.

## Phase 6 Verdict

`HexGFq` is close to Phase 6 quality as a Mathlib-free wrapper layer, but
it should not be marked Phase 6 complete yet. The explicit-entry generic
constructor falls short of the SPEC's user-facing `GFq p n` spelling, and
the optimized packed constructor currently exposes only the trivial
committed binary entry. The existing theorem surface is otherwise sound:
constructor claims are Lean-backed, the packed-vs-generic split is kept
out of Mathlib-free `RingEquiv` territory, and the wrapper lemmas provide
mostly complete characterising facts for the APIs that are currently
public.

Recommended follow-up issue titles:

- `HexGFq Phase 6: add ergonomic committed-entry GFq constructor layer`
- `HexGFq Phase 6: expose nontrivial committed PackedGF2Entry instances`
- `HexGFq Phase 6: add direct GF2q.toGFq representative projection lemma`
- `HexGFq Phase 6: document bridge-layer boundary for GF2q.equivGFq`
