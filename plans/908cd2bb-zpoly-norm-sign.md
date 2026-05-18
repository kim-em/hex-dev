## Current state

The Monic-route projection cluster at
`HexBerlekampZassenhausMathlib/Basic.lean:6720-6749` exposes named
helpers for three of the four fields of
`monic_primitive_sign_normalized_of_monic` (the triple-witness theorem
at line 4473):

* `zpoly_size_pos_of_monic`  — derived (`0 < f.size`)
* `zpoly_ne_zero_of_monic`   — derived (`f ≠ 0`, via `size_pos`)
* `zpoly_lc_pos_of_monic`    — derived (`0 < leadingCoeff f`)
* `zpoly_primitive_of_monic` — `.2.1` projection (`Hex.ZPoly.Primitive f`)

PR #5013 (closing #5010, commit `4061fa11`) landed
`zpoly_primitive_of_monic` and the per-window summarize #5018 records
that the cluster is "complete" at this point. However, the **`.2.2`
field** of the triple — `Hex.normalizeFactorSign f = f` — has no
corresponding named helper, and five inline call sites destructure the
full triple to access this single field. Two of those sites also use
the `.2.1` field through a `simpa [Hex.ZPoly.Primitive] using hcontent`
adapter that the new `zpoly_primitive_of_monic` helper would eliminate.

The five inline `obtain ⟨_, hcontent, hnorm⟩ := ...` sites are at
`Basic.lean:7828, 9534, 10083, 10193, 13595` (post-`origin/main`
`d61f920c` line numbers). Of these, the **two cleanest sites** (7828
and 9534) both pair the `hcontent` field with
`Hex.ZPoly.primitivePart_eq_self_of_primitive _` through the
`simpa [Hex.ZPoly.Primitive] using hcontent` adapter and use `hnorm`
in a subsequent `rw`. These two sites are rewired here. The remaining
three sites (10083, 10193 feeding existentials; 13595 passing through
a positional theorem call) have shape-specific consumers that may
require type-level care, and are deliberately out of scope here to
keep this issue atomic.

## Triple structure

`monic_primitive_sign_normalized_of_monic` (`Basic.lean:4473-4515`) has
return type

```lean
Hex.DensePoly.Monic factor ∧
  Hex.ZPoly.content factor = 1 ∧
    Hex.normalizeFactorSign factor = factor
```

so `.1 = Monic`, `.2.1 = content = 1`, `.2.2 = normalizeFactorSign = id`.
`Hex.ZPoly.Primitive` is defined at `HexPolyZ/Basic.lean:37-38` as
`content f = 1`, hence `zpoly_primitive_of_monic` (returning
`Hex.ZPoly.Primitive`) is definitionally equal to `.2.1` and a
consumer expecting either form accepts both.

## Per-site breakdown (post-`origin/main` `d61f920c` line numbers)

### Helper (new theorem, insert after line 6749)

Add a `theorem zpoly_normalize_factor_sign_of_monic` paralleling the
existing four cluster siblings:

```lean
/-- Monic integer polynomials are fixed by `Hex.normalizeFactorSign`. -/
theorem zpoly_normalize_factor_sign_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) : Hex.normalizeFactorSign f = f :=
  (monic_primitive_sign_normalized_of_monic h).2.2
```

Place it immediately after `zpoly_primitive_of_monic` (currently
ending at line 6749), before `private theorem zpoly_monic_one` at
line 6751. The visibility (`theorem`, not `private theorem`) matches
its three immediate siblings (`zpoly_ne_zero_of_monic`,
`zpoly_lc_pos_of_monic`, `zpoly_primitive_of_monic`).

### Site 1 — `Basic.lean:7828-7831`

Before:
```lean
-- A monic poly has trivial content and trivial sign normalisation.
obtain ⟨_, hcontent, hnorm⟩ := monic_primitive_sign_normalized_of_monic hcl_monic
have hprim : Hex.ZPoly.primitivePart cl = cl :=
  Hex.ZPoly.primitivePart_eq_self_of_primitive cl
    (by simpa [Hex.ZPoly.Primitive] using hcontent)
```

After:
```lean
-- A monic poly has trivial content and trivial sign normalisation.
have hnorm : Hex.normalizeFactorSign cl = cl :=
  zpoly_normalize_factor_sign_of_monic hcl_monic
have hprim : Hex.ZPoly.primitivePart cl = cl :=
  Hex.ZPoly.primitivePart_eq_self_of_primitive cl
    (zpoly_primitive_of_monic hcl_monic)
```

Net per-site: 5 lines → 5 lines (wash). The `simpa` adapter is
eliminated. The local name `hcontent` disappears (it had a single
consumer on the next line, now inlined via `zpoly_primitive_of_monic`).
`hnorm` retains its name and is consumed at line 7836 in
`rw [...,← hcl_def, hprim, hnorm]`.

### Site 2 — `Basic.lean:9534-9540`

Before:
```lean
obtain ⟨_, hcontent, hnorm⟩ :=
  monic_primitive_sign_normalized_of_monic hcl_monic
have hprim :
    Hex.ZPoly.primitivePart (Hex.centeredLiftPoly lp (d.p ^ d.k)) =
      Hex.centeredLiftPoly lp (d.p ^ d.k) :=
  Hex.ZPoly.primitivePart_eq_self_of_primitive _
    (by simpa [Hex.ZPoly.Primitive] using hcontent)
```

After:
```lean
have hnorm : Hex.normalizeFactorSign (Hex.centeredLiftPoly lp (d.p ^ d.k)) =
    Hex.centeredLiftPoly lp (d.p ^ d.k) :=
  zpoly_normalize_factor_sign_of_monic hcl_monic
have hprim :
    Hex.ZPoly.primitivePart (Hex.centeredLiftPoly lp (d.p ^ d.k)) =
      Hex.centeredLiftPoly lp (d.p ^ d.k) :=
  Hex.ZPoly.primitivePart_eq_self_of_primitive _
    (zpoly_primitive_of_monic hcl_monic)
```

Net per-site: 7 lines → 8 lines (+1). The explicit type ascription on
`hnorm` is the cost of inlining the projection cleanly (without it the
elaborator cannot derive the term's type from the helper's `f`
implicit). `hnorm` is consumed at line 9545 in `rw [..., hprim, hnorm]`.

## Deliverables

1. Insert `zpoly_normalize_factor_sign_of_monic` (5 lines including
   docstring) at `Basic.lean:6750`, immediately after
   `zpoly_primitive_of_monic`.

2. Rewire the two sites above (`Basic.lean:7828-7831` and
   `Basic.lean:9534-9540`) per the diffs given. No edits to
   surrounding `have` blocks, `rw` chains, or docstrings — only the
   `obtain` blocks and the `hprim` `have`s shown above change.

3. The three remaining inline triple-destructure sites
   (`Basic.lean:10083, 10193, 13595`) are deliberately left for a
   separate issue; their consumers' shape requires per-site type
   inspection.

4. No new `sorry`, `axiom`, `native_decide`, `TODO`, or `FIXME`.

5. No other edits to `HexBerlekampZassenhausMathlib/Basic.lean` or
   `HexBerlekampZassenhausMathlib/IntReductionMod.lean`.

## Naming

`zpoly_normalize_factor_sign_of_monic` follows the established
`zpoly_<derived>_of_monic` convention used by the four siblings
already in the cluster. The full token spells out the field
(`normalize_factor_sign`) because there is no shorter unambiguous
synonym at this layer (`zpoly_norm_of_monic` would collide with the
content-normalisation reading).

## Verification

* `git grep -c "zpoly_normalize_factor_sign_of_monic"
   HexBerlekampZassenhausMathlib/Basic.lean`: 0 → 3 (1 definition +
  2 use sites).
* `git grep -c "(monic_primitive_sign_normalized_of_monic .*).2.2"
   HexBerlekampZassenhausMathlib/Basic.lean`: 0 → 1 (only the new
  helper's body).
* `git grep -c "obtain ⟨_, hcontent, hnorm⟩"
   HexBerlekampZassenhausMathlib/Basic.lean`: 4 → 2 (Sites 1 and 2
  rewired; three other sites unchanged).
* `git grep -c "simpa \[Hex.ZPoly.Primitive\] using hcontent"
   HexBerlekampZassenhausMathlib/Basic.lean`: 4 → 2 (the same two
  sites; the `simpa` adapter is eliminated only where rewired).
* `lake build HexBerlekampZassenhausMathlib.Basic`: baseline 16
  errors at `origin/main d61f920c` (11 whnf timeouts + 1 cases-
  failure + 4 kernel-unknown constants); post-edit error set must be
  byte-identical except for line-number offsets reflecting the
  insertion at line 6750 (+5 lines) and the per-site deltas above
  (+0 at Site 1, +1 at Site 2).
* `lake build HexBerlekampZassenhausMathlib`: same 16-error baseline,
  no new errors.
* `python3 scripts/check_dag.py`: exit 0.
* `git diff --check`: clean.
* `git diff origin/main -- HexBerlekampZassenhausMathlib/Basic.lean
   | grep -E "^\+.*\b(sorry|axiom|native_decide|TODO|FIXME)\b"`:
  empty.

## Context

* Cluster precedent: PR #5001 (closing #5000) extracted
  `zpoly_ne_zero_of_monic`/`zpoly_ne_zero_of_pos_lc`. PR #5009
  (closing #5005) extracted `zpoly_lc_pos_of_monic`. PR #5013
  (closing #5010) extracted `zpoly_primitive_of_monic`. This issue
  closes the cluster on the fourth and final field of the triple.
* The four pre-existing cluster siblings live at lines 6720, 6733,
  6740, 6747 — a contiguous block. The new helper extends that block
  by one entry.
* `Hex.ZPoly.Primitive` is `def`'d at `HexPolyZ/Basic.lean:37` as
  `content f = 1`, confirming the def-eq used in `zpoly_primitive_of_monic`'s
  body.
* The follow-up issue covering the three remaining inline triple-
  destructure sites (`10083, 10193, 13595`) is **not** filed by this
  issue — let a subsequent /plan cycle file it after this one lands.

## Out of scope

* Rewiring `Basic.lean:10083, 10193, 13595`.
* Changing visibility of any existing cluster sibling (e.g. promoting
  `zpoly_size_pos_of_monic` from `private` to public, or vice versa).
* Any edits to `HexBerlekampZassenhausMathlib/IntReductionMod.lean`
  (it does not reference `monic_primitive_sign_normalized_of_monic`
  directly).
