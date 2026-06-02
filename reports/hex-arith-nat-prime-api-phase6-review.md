# HexArith Nat.Prime API Phase 6 Review

Scope: `HexArith/Nat/Prime.lean` (392 lines), checked against
`SPEC/Libraries/hex-arith.md` §"Binomial coefficients and Fermat's
little theorem" / §"Euclid's lemma" and `PLAN/Phase6.md`.

This is a review-only Phase 6 slice. No Lean source is edited as
part of this report.

## Findings

### 1. Public Pascal helpers are privately re-derived in `HexPolyFp/SquareFree.lean`

`HexPolyFp/SquareFree.lean:262-284` defines two private theorems that
exactly duplicate the public versions in `HexArith/Nat/Prime.lean`:

```lean
-- HexPolyFp/SquareFree.lean
private theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) :
    Hex.Nat.choose n k = 0 := ...
private theorem choose_self (n : Nat) : Hex.Nat.choose n n = 1 := ...
```

The public counterparts `Hex.Nat.choose_eq_zero_of_lt` (Prime.lean:45)
and `Hex.Nat.choose_self` (Prime.lean:63) have the same statement and
the same proof shape. The local copies are called at
`HexPolyFp/SquareFree.lean:407`, `:409`, `:501`, `:541` and would work
unchanged after replacement (the call sites already use the
`Hex.Nat`-namespaced `choose`).

Suggested follow-up: delete the local duplicates and route the call
sites to the public lemmas (either fully qualified or under `open
Hex.Nat`).

### 2. `Prime.coprime_of_not_dvd` is private but is re-derived downstream

`HexArith/Nat/Prime.lean:95-104` defines a private helper:

```lean
private theorem coprime_of_not_dvd {p a : Nat} (hp : Hex.Nat.Prime p)
    (ha : ¬ p ∣ a) : Nat.Coprime p a := ...
```

`HexModArith/Prime.lean:69-77` (`inv_mul_eq_one_of_prime`) re-derives
the same `Nat.Coprime aval p` from `¬ p ∣ aval` using a verbatim copy
of the private proof, because the helper is not exposed.

Both call sites are forward step of "I know `¬ p ∣ x`, give me a
coprimality witness." Promoting the helper to a public
`Hex.Nat.Prime.coprime_of_not_dvd` (or, for symmetry,
`coprime_iff_not_dvd`) would cut the duplicate at the only existing
downstream caller and matches the shape `Hex.Nat.Prime.dvd_mul`
already takes for its sister bridging role.

### 3. `Prime.dvd_mul` is forward-only; the iff form is what Mathlib exposes

`HexArith/Nat/Prime.lean:110-114` states Euclid's lemma in the
forward-only direction:

```lean
theorem dvd_mul {p a b : Nat} (hp : Hex.Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b
```

Mathlib's `Nat.Prime.dvd_mul` is an iff (`p ∣ m * n ↔ p ∣ m ∨ p ∣ n`).
SPEC anchor (`hex-arith.md:442-444`) only commits to the forward
direction, but the reverse is trivial from `Nat.dvd_mul_left` /
`Nat.dvd_mul_right` and the iff shape is more idiomatic for an API
surface that downstream consumers will `rcases` on.

The only current caller (`HexModArith/Prime.lean:46`) uses `rcases`
on the forward direction, so an iff version is backward-compatible
via `(Hex.Nat.Prime.dvd_mul hp).mp hdvd` or by destructuring the iff
directly. Suggested follow-up: re-state `Prime.dvd_mul` as an iff and
update the one caller; SPEC anchor can be left as-is or strengthened
to the iff form to match.

### 4. Docstrings missing on non-obvious private combinatorial scaffolding

Per `SPEC/design-principles.md:170-176`, non-obvious private helpers
that encode an invariant or a subtle algorithmic choice should carry
a docstring. The combinatorial partial-sum scaffolding behind
`add_pow_prime_mod` falls into that bucket but is currently
undocumented:

- `chooseTerm` (Prime.lean:167): the `k`-th term `C(n,k) · a^(n−k) · b^k`
  of the binomial expansion.
- `chooseSum` (Prime.lean:170): the partial sum `Σ_{k<m} chooseTerm n a b k`.
- `chooseSum_succ_row` (Prime.lean:177): the row-recurrence
  `chooseSum (n+1) a b (m+1) = a · chooseSum n a b (m+1) + b · chooseSum n a b m`.
- `add_pow_chooseSum` (Prime.lean:201): `(a+b)^n = chooseSum n a b (n+1)`.
- `chooseTerm_dvd_of_middle`, `chooseTerm_mod_eq_zero_of_middle`,
  `chooseSum_prefix_mod` (Prime.lean:221-235): `p`-divisibility of
  middle terms and the prefix mod-reduction used to erase them
  modulo a prime.
- `add_pow_prime_mod_of_choose_dvd` (Prime.lean:257): the abstracted
  Freshman's-dream-modulo-`p` step parameterised over the
  binomial-divisibility hypothesis.
- `pow_prime_mod_from_add_pow` (Prime.lean:278): the induction step
  deriving Fermat's little theorem from the Freshman's dream.
- `choose_succ_mul_eq` (Prime.lean:139): the multiplicative Pascal
  identity `(k+1) · C(n+1,k+1) = (n+1) · C(n,k)`.
- `choose_prime_dvd_from_mul_identity` (Prime.lean:152): the Euclid
  step that turns the multiplicative identity into divisibility.

Routine plumbing is exempt (e.g. `not_dvd_of_pos_lt`, `choose_one_right`,
`range_all_eq_true_of_isPrimeTrial`, `two_le_of_isPrimeTrial`,
`chooseSum_zero` — all transparent from name).

Suggested follow-up: add one-line docstrings to the helpers listed
above explaining the invariant each one carries within the proof
strategy.

## Checked Clusters With No Follow-Up Needed

- **Imports / namespace hygiene.** The only import is
  `HexArith.Nat.ModArith`. All declarations live under `Hex.Nat`
  (with the `Prime.*` accessors inside `Hex.Nat.Prime`). No leak
  into the root namespace.
- **`@[simp]` on Pascal-recurrence lemmas.** `choose_zero_right`,
  `choose_zero_succ`, `choose_succ_succ`, `choose_self` are tagged
  `@[simp]` and play exactly the boundary/recurrence-normalisation
  role downstream `simp` calls expect. The `choose_eq_zero_of_lt`
  conditional rewrite is intentionally untagged: it carries an
  arithmetic side condition `n < k` that `simp` would not always
  discharge cheaply. This matches Mathlib's choice for the
  corresponding `Nat.choose_eq_zero_of_lt`.
- **Prime accessors.** `two_le`, `one_lt`, `pos`, `ne_zero`,
  `ne_one` mirror Mathlib's `Nat.Prime` accessor surface and are
  intentionally untagged (loop risk if `simp` saw `2 ≤ p` whenever
  `Prime p` was in context). Caller sites
  (`HexPolyFp/Frobenius.lean`, `HexPolyFp/Quotient.lean`, etc.)
  apply them directly without unfolding.
- **Fermat trio.** `choose_prime_dvd`, `add_pow_prime_mod`,
  `pow_prime_mod` carry docstrings, match the SPEC text
  (`hex-arith.md:426-433`), and are untagged. None of them is a
  net-positive `simp` candidate: each has a `Prime p` hypothesis
  that `simp` cannot discharge, and the LHS shapes are too
  specific to fire opportunistically.
- **`isPrimeTrial` and its soundness theorem.** Both carry
  docstrings explaining their intended use as the BZ extended
  prime-search constructor. The two private unfolding helpers
  (`range_all_eq_true_of_isPrimeTrial`, `two_le_of_isPrimeTrial`)
  are routine `unfold`-and-destructure plumbing, transparent from
  name, and exempt from the docstring rule.
- **`Prime` as `And` rather than `structure`.** Numeric `.1`/`.2`
  access is mitigated by the `two_le` and dvd-direction accessors;
  the existing pattern is consistent with the rest of the
  `Mathlib`-free port and changing it would churn every downstream
  caller (≈12 files) without changing the public theorem surface.
  Left as-is.

## Residual Risk Checked

- The trial-division checker materialises `List.range n`. For the
  Conway-prime call sites this is bounded by the largest small
  prime in `HexConway/Basic.lean`, well within machine-word
  ranges. Not a Phase 6 concern; flagged here only to record that
  it was considered.
- The audit did not re-verify the proofs of `choose_prime_dvd`,
  `add_pow_prime_mod`, `pow_prime_mod`, or `isPrimeTrial_isPrime`.
  Phase 5 (`libraries.yml[HexArith].done_through = 5`) signed off
  on correctness; Phase 6 is API polish.
- The audit did not look at performance of `choose` for large
  inputs. The downstream consumers use `choose` only with prime
  modulus arguments (mostly `p` small) inside congruences, never
  as a runtime value, so the naive Pascal recursion suffices.
