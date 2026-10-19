I approve this delta. It is behavior-preserving and sound, and no caller needs to change. I have one non-blocking design point and two small proof nits.

I couldn't run anything: my `lake build` of `HexRealAlgebraicTheory.Sqrt`, `.Tests` and `.Norm` was denied by the permission mode. So the build and axiom results rest on your report; everything below comes from reading the source.

**Behavior.** Before the change, `sqrt? a` was `if a < 0 then none else sqrtRoot? a`, and `sqrtRoot?` starts with the same `a < 0` check. So the old `sqrt?` and the new one, which just calls `sqrtRoot?`, return the same value for every input. The only difference is one fewer exact sign test on nonnegative inputs.

- **Negative inputs are rejected:** the check now lives only in `sqrtRoot?` (`Roots.lean:126-127`), and the forward direction of `sqrt?_isSome` (`Sqrt.lean:57-61`) proves it from that check.
- **Every nonnegative input succeeds:** `sqrtRoot?_isSome` (`Sqrt.lean:62`) is reused unchanged.
- **Soundness:** `sqrt?_sound` is now just `sqrtRoot?_sound`. The `change` and the `exact` both rely on unfolding `sqrt?`, which is fine since it is `@[expose]`.
- **Axioms:** nothing new is introduced. `by_contra` is classical, but `Classical.choice` is already in the pinned set. `sqrt?_isSome` and `sqrt?_sound` have no `#print axioms` test of their own, but `sqrt?_eq_none` and `sqrt_sq` depend on both and stay pinned to `[propext, Classical.choice, Quot.sound]` (`Tests.lean:67-73`). That is adequate.

**Callers.** None need changes, because the value of `sqrt?` and every public theorem statement are unchanged:
- `HexRealAlgebraic/Norm.lean:22` (`abs` matches on `normSq.sqrt?`).
- `HexRealAlgebraicTheory/Norm.lean:38` (uses `sqrt?_eq_some`).
- `conformance/HexRealAlgebraic/{Checks,Conformance,EmitFixtures}.lean`, `bench/HexRealAlgebraic/Bench.lean:212`, `HexManual/Chapters/HexRealAlgebraic.lean:81-82` and `HexRealAlgebraic/README.md:14`.

Emitted fixtures can't change. Only `runSqrt` timing moves, and the report's new paragraph correctly marks the earlier baselines as historical.

**Findings**

1. **The fix goes the opposite way from the earlier review (design, non-blocking).** `status/reviews/issue-10577-opus.md:100` asked for `sqrtRoot?` to be the pure root selection with the sign check in `sqrt?`. This patch keeps the check in `sqrtRoot?` and makes `sqrt?` a one-line alias, so there are now two public names for the same function.
   - `sqrtRoot?_isSome` is now just the reverse direction of `sqrt?_isSome`. SPEC lines 248-249 justify it as making sure "a failed root search cannot masquerade as a negative argument", but `sqrtRoot?` now returns `none` for both cases itself, so that reason is mostly gone.
   - The alternative is `sqrtRoot? a := ofAlgebraic? a.toAlgebraic.sqrt`, with `sqrt?` keeping its check. The old `sqrt?_isSome`/`sqrt?_sound` proofs (the ones this diff deletes) would then work as they were. `sqrtRoot?_isSome` would lose its `ite_eq_right` rewrite, and `sqrtRoot?_sound` would take `(ha : 0 ≤ a)`, since `complex_sqrt` needs it.
   - Performance is identical either way (one sign test, then the selection), and the current version meets the SPEC's wording. I'd choose the pure-selector form for clarity, but this shouldn't block. If you keep the current shape, add a sentence to the `sqrtRoot?` docstring saying it is also the sign-checking entry point.

2. **The forward proof of `sqrt?_isSome` depends on where the sign check lives (nit).** It unfolds `sqrtRoot?` and simplifies its `if` (`Sqrt.lean:58-61`), so moving the check (finding 1) would break it. Deriving it from soundness works with the check in either place:
   ```lean
   · intro h
     obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
     rw [← (sqrtRoot?_sound a b hb).2]
     exact sq_nonneg b
   ```
   `sq_nonneg` on `RealAlgebraicNumber` is already used in `sqrt_square`. Separately, `if_pos hneg` is the more common way to write `ite_eq_left hneg`.

3. **`sqrt?_sound` doesn't need tactic mode (style nit).** It can be `:= sqrtRoot?_sound a b h`.

**Report.** The new paragraph is accurate, and it explicitly says the earlier square-root baselines give no current performance admission. The table row at line 28 still reads "Baseline and branch checks". That's acceptable given the paragraph, but adding "(pre-change source)" there would keep the table self-contained. `status/reviews/issue-10577-opus-final.md:44` still says "still there", which is fine as a historical review record.
