# issue #8854: transport layer COMPLETE + green; assembly finish-line pinned

## Done + committed (green, no sorry/axiom)

Full reusable Mathlib-free transport, 8 commits on issue-8854:
- MonicUnique.lean (monic-division uniqueness)
- WordStep.lean: Grind.CommRing (WordMod) + scalar bridge
- WordTransport.lean: toWP/ofWP + toWP_add/sub/mul/one/zero/congr/reduceModPow,
  ofWP_toWP_of_canonical, toWP size/monic/degree preservation.

## Assembly written twice, reverted twice (Mathlib-free tactic walls)

The Quadratic.lean guarded dispatch + byte-identity was written in full both times
(kernel, quadraticHenselStepBignum, dispatch, the reroute of 4 spec `unfold`s, and
the helpers below — all compile) but two constructs are Mathlib-only here:
- `set` (used to name bignum intermediates) — REPLACE with
  `obtain ⟨x, hx⟩ : ∃ x, x = v := ⟨_, rfl⟩` (core), then `rw [hx]` to unfold.
- record equality of `QuadraticLiftResult` — add
  `private theorem ext' {r1 r2} (hg hh hs ht) : r1 = r2 := by cases r1; cases r2; simp_all`
  and `refine ext' ?_ ?_ ?_ ?_`; each field goal is `ofWP ctx WORD = (bignum).field`.

## The helpers that DO compile (place AFTER the private divModMonicModSquare lemmas,
## i.e. right before quadraticHenselStep_factor_spec):

toWP_{reduceModSquare,addModSquare,subModSquare,mulModSquare} (each = toWP a `op` toWP b,
via toWP_reduceModPow with p=m,k=2 since ctx.toNat = m*m = m^2, bridged by Nat.pow_two);
reduceModSquare_coeff_lt (coeffs in [0,m*m)); ofWP_toWP_reduceModSquare (canonical round
trip); one_lt_of_mul (1<m from 1<m*m via `rcases m with _|_|k`); and
toWP_divModMonicModSquare (division transport via MonicUnique — needs
divModMonicModSquare_reconstruct_congr + _remainder_coeff_eq_zero_of_monic; the monic-
division hypotheses close with `rw [hlc, WordMod.div_one, Lean.Grind.Semiring.mul_one]`
+ a `WordMod.sub_self` lemma to add to WordStep). ALSO add
ofWP_toWP_{add,sub}ModSquare (= reduceModSquare round trip after unfolding the op) so the
final record rewrites match `addModSquare`/`subModSquare` syntactically.

## Assembly shape (validated in pieces)

Kernel guard `m*m<2^64 ∧ odd ∧ 1<m*m ∧ leadingCoeff g = 1 ∧ 0<deg g`. Under it:
`generalize` the 8 word intermediates (eW, fqW, gWv, hWv, bWv, bqW, tWv, sWv);
prove 8 correspondences `word = toWP(bignum)` in order (each a few `rw`s with the
toWP_*ModSquare helpers + toWP_divModMonicModSquare for the two divisions); g' monic +
0<deg g' via `g'.coeff (g.size-1) = 1` (leading coeff survives the correction because the
remainder vanishes at index ≥ g.size-1); finish each of the 4 fields with
ofWP_toWP_{add,sub}ModSquare. eq_bignum: `by_cases` on the guard conjunction; guard-fails
branch shows `quadraticHenselStepWord? = none` (split_ifs; the all-true case contradicts
the guard) then `Option.getD_none`.

## Next step

Redo Quadratic.lean with `obtain` (not `set`) + `ext'`. ~150 lines; all supporting
lemmas exist/committed. Then reroute specs through eq_bignum, build the SD4 bench, re-measure.
