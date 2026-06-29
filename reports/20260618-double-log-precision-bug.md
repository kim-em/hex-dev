## Premise check: the gate is unsatisfiable at the executable's actual lift precision — STOP per the issue's own clause

Per the "Directives are hypotheses" doctrine I sanity-checked the gate before implementing, and it triggers this issue's own stop condition: **adding the gate flips an existing fixture from `some` to `none`**, which the issue says indicates a latent inadequate-precision problem to surface rather than land. The root cause is a precision-wiring mismatch, not something a cheap acceptance gate can fix. A second opinion (Codex) independently reproduced the same wiring and arithmetic.

### The wiring (verified in `HexBerlekampZassenhaus/Basic.lean`)

`precisionForCoeffBound` is applied **twice** on the public path:

1. The public caller computes `a := precisionForCoeffBound B primeData.p` and passes `a` as the loop's coefficient-bound parameter (`Basic.lean:7699`, `:7714`), with `B = factorFastPrecisionCap core` (`:7994`).
2. The loop passes the schedule variable `k` into `toMonicLiftData core k primeData` (`:7017`), and `toMonicLiftData` applies `precisionForCoeffBound` **again**: `toMonicLiftData core k primeData = henselLiftData (toMonic core).monic (precisionForCoeffBound k primeData.p) primeData` (`:7001`), with `(henselLiftData f B d).k = B` (`:2751`).

So the actual Hensel/CLD lift exponent consumed by `bhksRecoverClassified` and the CLD lattice (`bhksLatticeBasis f d.p d.k …`, `:6744`) is

```
liftData.k = precisionForCoeffBound k primeData.p = ceilLogP p (2k+1)
```

where the schedule variable `k` itself only ranges up to `a = precisionForCoeffBound(cap) p`. The exponent collapses **double-logarithmically**.

### Concrete counterexample (existing fixture `cldGuardF = x²−5x+6 = (x−2)(x−3)`, `p=5`)

Computed by `#eval` (pure-integer, no extern):

| quantity | value |
|---|---|
| `bhksCoeffBound (toMonic cldGuardF).monic 0` | `16` |
| required floor exponent `precisionForCoeffBound 16 5` | `3` (since `5²=25 < 33 ≤ 125=5³`) |
| `factorFastPrecisionCap cldGuardF` | `50 803 201` |
| outer `a = precisionForCoeffBound 50803201 5` | `12` |
| schedule `henselPrecisionSchedule a (initialHenselPrecision a) …` | `[4, 8, 12]` |
| `liftData.k` at **every** scheduled `k` (`precisionForCoeffBound k 5`) | `2, 2, 2` |
| gate `precisionForCoeffBound 16 5 ≤ liftData.k` | `3 ≤ 2` → **false at every precision, including the cap** |

So `factorFastCoreWithBound cldGuardF 4 … = some bhksGuardFactors` (`Basic.lean:7428`, expected `[(x−2),(x−3)]`) would become `none` under the gate, and the public fast path would return `none` for essentially all inputs.

### Why no acceptance gate at the current schedule can supply hsep/hthr

The #7917/#7925 endpoint needs, for the recovered-lift basis `L = bhksLatticeBasis (toMonic core).monic d.p d.k d.liftedFactors`:

```
hsep : ∀ S j, 2 * bhksCoeffBound (lift S).f j < (lift S).p ^ (lift S).a
```

with `(lift S).f = (toMonic core).monic`, `(lift S).p = d.p`, `(lift S).a = d.k = liftData.k = 2`. For `cldGuardF` this is `2·16 < 5² = 25`, i.e. `32 < 25` — **false**, not merely underivable. hsep is a statement about the lattice's *actual* precision `d.k`, and the executable runs that lattice at a precision below the BHKS CLD-adequacy threshold. The product check (`Array.polyProduct candidates == f`, `:6754`) rescues *correctness* empirically (the true factor coefficients here are tiny), but it certifies only "candidates multiply to `f`", not column-adequacy — exactly the gap #7894/#7917 set out to close.

(The only reading under which a `k`-based floor is satisfiable is comparing against the **outer schedule variable** `k` (`3 ≤ 12` holds), but that is not the exponent the CLD lattice uses, so it would not make hsep — a statement about `d.k=2` — true.)

### Recommendation

The premise "the cap `bhksBound` already dominates the CLD bound, so the gate is cheap and outputs are unchanged" is unsound: the *nominal* cap (`bhksBound ≈ 5e7`) does dominate the CLD bound (16), but the **schedule's actual lift exponent** (`d.k = 2`, modulus 25) does not, because of the double `precisionForCoeffBound`. The real fix is a **precision-schedule correction** so the lift reaches CLD-adequate precision (e.g. drop the double conversion: pass the coefficient cap `B`/`factorFastPrecisionCap` into the loop and let `toMonicLiftData` do the single conversion; or walk coefficient-magnitude bounds up to the true cap). After that, the terminal precision — or an acceptance gate — would legitimately supply hsep/hthr.

That is a soundness-sensitive change well beyond "add a cheap acceptance gate": it alters the fast-path lift precision and touches the CI-gated determinism lemmas (`factorFastCoreWithBound_isSome_of_recovery_on_schedule`, the `bhksRecover_eq_some_of_forwardInputs` producers in `Recovery.lean`, and the `…_of_forwardInputs_on_schedule` wrappers in `PartitionRefinement.lean`). It should be re-scoped and re-authored as a precision-schedule fix, not landed as an acceptance gate against the current (inadequate) `liftData.k`.

Per the doctrine I am not filing a sub-decomposition or inventing sorries; leaving this claimable for an updated directive. No Lean source was changed this session.

