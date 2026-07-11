/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRoots

/-!
Core conformance checks for `HexRoots`, the certified complex-root isolator.

Oracle: python-flint (`fmpz_poly.complex_roots()`; ci tier, wired by a sibling
work unit). Mode: if_available.

The checks below assert *independently derived* mathematical facts about the
roots of committed polynomials — the number of roots (fundamental theorem of
algebra), the exact rational roots, roots of unity on the unit circle,
Chebyshev roots on the real axis, the closed-form separation and Cauchy
precisions — never a value obtained by re-running the operation under test.
Disc containment and geometry are checked in exact `Rat` arithmetic via
`Dyadic.toRat` of the stored centres and radii.

Covered operations:
- `isolate` — all-atoms driver for squarefree inputs.
- `isolateAll?` — worklist driver returning atoms and clusters.
- `DyadicRootIsolation.refineTo?` — precision refinement of one atom.
- `RefinedIsolation.sameRoot` — root identity up to isolation.
- `witnessCheck` / `witness` — three-radius strong Pellet certificate.
- `nkWitnessCheck` / `nkWitness` — Newton-Kantorovich atom certificate.
- `rootFree` — single-radius `T₀` emptiness certificate.
- `taylor` — exact Gaussian-dyadic Taylor expansion.
- `mahlerPrec` — closed-form separation precision.
- `cauchyExp` — Cauchy root-bound exponent.
- `Component.refine1` — one subdivision + `T₀` discard + gluing round.
- `Component.certify?` — per-component certification.

Covered properties:
- a squarefree degree-`n` polynomial isolates to exactly `n` atoms;
- each known rational root lies in the circumscribed disc of exactly one atom
  (discs are pairwise disjoint at the emitted precision);
- every atom of a cyclotomic polynomial sits on the unit circle, and every
  atom of a Chebyshev polynomial sits on the real axis inside `[−1, 1]`;
- the three atom strategies `nk`, `pellet`, `nkThenPellet` agree on the atom
  count and produce pairwise-matching atoms (each atom of one strategy meets
  exactly one atom of another);
- a non-squarefree input keeps its multiple root as a `k = 2` cluster rather
  than atomizing it;
- `refineTo?` reaches the requested precision and preserves the root (the old
  and new discs still meet);
- `sameRoot` is `true` within a root's isolation class and `false` across
  distinct roots;
- both witnesses fire at a simple root and fail off-root or at the wrong count;
- `rootFree` certifies discs far from every root;
- `taylor p 0` is the coefficient cast and a shifted expansion matches the
  hand-computed synthetic division;
- `mahlerPrec` and `cauchyExp` equal their closed forms.

Covered edge cases:
- the zero polynomial (`isolate` returns `none`);
- a nonzero constant (`isolate` returns `some #[]`);
- the linear polynomial `x` (one atom at the origin);
- the non-squarefree `(x²+1)(x−5)²` (a `k = 2` cluster survives);
- components far from every root (`refine1` empties them, `certify?` returns
  `none`, `rootFree` is `true`).

Two SPEC core-tier fixtures are exercised only on their cheap operations, for
reasons recorded at their use sites: the small Mignotte polynomial
`x⁵ − (100x − 1)²`, whose full `isolate` currently drops roots (its atom count
is therefore not asserted here — the coverage defect is tracked in
https://github.com/kim-em/hex-dev/issues/8736), and the degree-10 Chebyshev
`T₁₀`, whose full `isolate` runs far past this module's elaboration-time budget.
-/

namespace Hex
namespace RootsConformance

/-! ### Committed polynomial fixtures (coefficients low degree first). -/

/-- `(x − 1)(x − 2)(x + 3) = x³ − 7x + 6`; roots `1, 2, −3`. This is the SPEC's
    `p₁`, with `mahlerPrec p₁ = 16` and `cauchyExp p₁ = 3`. -/
private def rat1 : ZPoly := DensePoly.ofCoeffs #[6, -7, 0, 1]
/-- `x³ − x`; roots `0, 1, −1`. -/
private def rat2 : ZPoly := DensePoly.ofCoeffs #[0, -1, 0, 1]
/-- The 5th cyclotomic polynomial `Φ₅ = x⁴ + x³ + x² + x + 1`; roots are the
    primitive 5th roots of unity. -/
private def phi5 : ZPoly := DensePoly.ofCoeffs #[1, 1, 1, 1, 1]
/-- The 7th cyclotomic polynomial `Φ₇`; roots are the primitive 7th roots of
    unity. -/
private def phi7 : ZPoly := DensePoly.ofCoeffs #[1, 1, 1, 1, 1, 1, 1]
/-- The 12th cyclotomic polynomial `Φ₁₂ = x⁴ − x² + 1`; roots are the primitive
    12th roots of unity. -/
private def phi12 : ZPoly := DensePoly.ofCoeffs #[1, 0, -1, 0, 1]
/-- The Chebyshev polynomial `T₅ = 16x⁵ − 20x³ + 5x`; roots `cos((2k−1)π/10)`
    lie on the real axis inside `[−1, 1]`. -/
private def cheb5 : ZPoly := DensePoly.ofCoeffs #[0, 5, 0, -20, 0, 16]
/-- The Chebyshev polynomial `T₁₀`; roots `cos((2k−1)π/20)` on the real axis. -/
private def cheb10 : ZPoly :=
  DensePoly.ofCoeffs #[-1, 0, 50, 0, -400, 0, 1120, 0, -1280, 0, 512]
/-- The small Mignotte polynomial `x⁵ − (100x − 1)² = x⁵ − 10000x² + 200x − 1`,
    with a root pair near `1/100`. Squarefree; `p(0) = −1`, `p(1) = −9800`. -/
private def mignotte : ZPoly := DensePoly.ofCoeffs #[-1, 200, -10000, 0, 0, 1]
/-- `(x² + 1)(x − 5)² = x⁴ − 10x³ + 26x² − 10x + 25`; simple roots `±i` and a
    double root at `5`. Not squarefree. -/
private def multiple : ZPoly := DensePoly.ofCoeffs #[25, -10, 26, -10, 1]
/-- A nonzero constant: degenerate degree-0 input with no roots. -/
private def constant : ZPoly := DensePoly.ofCoeffs #[7]
/-- The linear polynomial `x`: one simple root at the origin. -/
private def linear : ZPoly := DensePoly.ofCoeffs #[0, 1]

/-! ### Geometry helpers (exact `Rat` arithmetic on stored squares). -/

/-- The circumscribed disc of `s` (radius `√2·2^{−prec}`, squared `2·4^{−prec}`)
    contains the rational point `(x, y)`: `(x − cᵣ)² + (y − cᵢ)² ≤ 2·hw²` with
    `hw = 2^{−prec}` the half-width. Every certified root lies in its stored
    square's circumscribed disc, so this is the exact membership test. -/
private def discCovers (s : DyadicSquare) (x y : Rat) : Bool :=
  let cre := s.re.toRat
  let cim := s.im.toRat
  let hw := s.halfWidth.toRat
  decide ((x - cre) * (x - cre) + (y - cim) * (y - cim) ≤ 2 * hw * hw)

/-- How many atoms' circumscribed discs contain the rational point `(x, y)`.
    Because the emitted discs are pairwise disjoint, a genuine root is covered
    exactly once. -/
private def coverCount {p : ZPoly} (x y : Rat)
    (atoms : Array (DyadicRootIsolation p)) : Nat :=
  atoms.foldl (fun n i => if discCovers i.square x y then n + 1 else n) 0

/-- The centre of `s` is within the documented slack of the unit circle:
    `1 − 5·r' ≤ |centre|² ≤ 1 + 5·r'` with `r' = radiusHi` (the dyadic upper
    bound on the circumscribed radius). Any true containment of a unit-modulus
    root implies this. -/
private def onUnitCircle (s : DyadicSquare) : Bool :=
  let ns := s.re.toRat * s.re.toRat + s.im.toRat * s.im.toRat
  let r := s.radiusHi.toRat
  decide (1 - 5 * r ≤ ns ∧ ns ≤ 1 + 5 * r)

/-- The centre of `s` lies on the real axis inside `[−1, 1]` up to the disc
    radius: `|cᵢ| ≤ r'` and `|cᵣ| ≤ 1 + r'` with `r' = radiusHi`. Every atom of
    a Chebyshev polynomial (all of whose roots are real and in `[−1, 1]`)
    satisfies this. -/
private def nearRealAxis (s : DyadicSquare) : Bool :=
  let cre := s.re.toRat
  let cim := s.im.toRat
  let r := s.radiusHi.toRat
  decide (-r ≤ cim ∧ cim ≤ r ∧ -(1 + r) ≤ cre ∧ cre ≤ 1 + r)

/-- Each atom of `a` meets exactly one atom of `b`. At the emitted precision two
    atoms meet exactly when they isolate the same root, so this is the pairwise
    strategy-agreement test. -/
private def matchAcross {p : ZPoly} (a b : Array (DyadicRootIsolation p)) : Bool :=
  a.size == b.size &&
    a.all fun ai =>
      (b.filter fun bi => DyadicSquare.discsMeet ai.square bi.square).size == 1

/-! ### Runtime entry points.

`HasOnlySimpleRoots` is discharged at runtime through its compiled `Decidable`
instance (an `if h : …`), not by kernel `decide`: the instance routes through a
rational-gcd computation whose well-founded recursion the kernel cannot unfold. -/

/-- `isolate` under a chosen strategy, obtaining the squarefreeness hypothesis
    from the runtime decision procedure. -/
private def isoAtoms (p : ZPoly) (prec : Int) (strat : AtomStrategy) :
    Option (Array (DyadicRootIsolation p)) :=
  if h : HasOnlySimpleRoots p then isolate p h prec strat else none

/-! ### `isolate`: atom count, root coverage, geometry, strategy agreement.

Each squarefree fixture is isolated under all three strategies once; the single
check per fixture asserts the atom count (its degree), the cross-strategy
pairwise match, and the coverage/geometry property of its roots. `cheb5` omits
the `pellet` strategy (Pellet-only subdivision of its real, grid-line roots runs
past budget) and matches `nk` against `nkThenPellet` instead. `phi7` is checked
under `nkThenPellet` alone for the same budget reason. -/

-- `rat1`: three atoms, roots `1, 2, −3` each covered exactly once.
#guard
  (match isoAtoms rat1 32 .nk, isoAtoms rat1 32 .pellet, isoAtoms rat1 32 .nkThenPellet with
    | some an, some ap, some ax =>
        an.size == 3 && matchAcross an ap && matchAcross an ax &&
          coverCount 1 0 ax == 1 && coverCount 2 0 ax == 1 && coverCount (-3) 0 ax == 1
    | _, _, _ => false)

-- `rat2 = x³ − x`: three atoms, roots `0, 1, −1` each covered exactly once.
#guard
  (match isoAtoms rat2 32 .nk, isoAtoms rat2 32 .pellet, isoAtoms rat2 32 .nkThenPellet with
    | some an, some ap, some ax =>
        an.size == 3 && matchAcross an ap && matchAcross an ax &&
          coverCount 0 0 ax == 1 && coverCount 1 0 ax == 1 && coverCount (-1) 0 ax == 1
    | _, _, _ => false)

-- `Φ₅`: four atoms, all on the unit circle.
#guard
  (match isoAtoms phi5 32 .nk, isoAtoms phi5 32 .pellet, isoAtoms phi5 32 .nkThenPellet with
    | some an, some ap, some ax =>
        an.size == 4 && matchAcross an ap && matchAcross an ax &&
          ax.all fun i => onUnitCircle i.square
    | _, _, _ => false)

-- `Φ₁₂`: four atoms, all on the unit circle.
#guard
  (match isoAtoms phi12 32 .nk, isoAtoms phi12 32 .pellet, isoAtoms phi12 32 .nkThenPellet with
    | some an, some ap, some ax =>
        an.size == 4 && matchAcross an ap && matchAcross an ax &&
          ax.all fun i => onUnitCircle i.square
    | _, _, _ => false)

-- `T₅`: five atoms, all on the real axis in `[−1, 1]`. `nk` and `nkThenPellet`
-- agree; the `pellet`-only run is omitted for elaboration time.
#guard
  (match isoAtoms cheb5 32 .nk, isoAtoms cheb5 32 .nkThenPellet with
    | some an, some ax =>
        an.size == 5 && matchAcross an ax && ax.all fun i => nearRealAxis i.square
    | _, _ => false)

-- `Φ₇`: six atoms, all on the unit circle (single-strategy for budget).
#guard
  (match isoAtoms phi7 32 .nkThenPellet with
    | some ax => ax.size == 6 && ax.all fun i => onUnitCircle i.square
    | none => false)

/-! ### `isolate`: degenerate inputs.

`HasOnlySimpleRoots 0` holds (the gcd of `0` and its derivative is `0`, whose
stored size is `0 ≤ 1`), so the zero polynomial reaches `isolate`, which pins it
to `none`; a nonzero constant yields `some #[]`; the linear `x` yields a single
atom whose disc covers the origin. -/

#guard (if h : HasOnlySimpleRoots (0 : ZPoly) then (isolate (0 : ZPoly) h 8).isSome else true) == false
#guard (isoAtoms constant 8 .nkThenPellet).map (·.size) == some 0
#guard
  (match isoAtoms linear 8 .nkThenPellet with
    | some a => a.size == 1 && coverCount 0 0 a == 1
    | none => false)

/-! ### `isolateAll?`: clusters and direct atom output.

The multiple-root input keeps its double root as a `k = 2` cluster whose
enclosing disc covers `(5, 0)`, alongside the two simple atoms at `±i`; the
squarefree fixtures return all atoms. -/

-- `(x²+1)(x−5)²`: three certified results, exactly one `k = 2` cluster whose
-- enclosing disc covers `(5, 0)`, and two atoms covering `±i`.
#guard
  (match (if h : 0 < multiple.degree?.getD 0 then
            isolateAll? multiple 4 #[Component.cauchy multiple h] else none) with
    | some rs =>
        rs.size == 3 &&
          (rs.filter fun c => match c with | .cluster _ => true | .atom _ => false).size == 1 &&
          (rs.all fun c => match c with
            | .cluster cl => cl.k == 2 && discCovers (encSquare cl.squares) 5 0
            | .atom iso => discCovers iso.square 0 1 || discCovers iso.square 0 (-1))
    | none => false)

-- `rat1` from the Cauchy start: three results, all atoms.
#guard
  (match (if h : 0 < rat1.degree?.getD 0 then
            isolateAll? rat1 32 #[Component.cauchy rat1 h] else none) with
    | some rs => rs.size == 3 && rs.all fun c => match c with | .atom _ => true | .cluster _ => false
    | none => false)

-- Linear `x` from the Cauchy start: a single atom.
#guard
  (match (if h : 0 < linear.degree?.getD 0 then
            isolateAll? linear 8 #[Component.cauchy linear h] else none) with
    | some rs => rs.size == 1
    | none => false)

/-! ### `refineTo?` and `sameRoot`.

A coarse atom is built by hand at an exact integer root of `rat1` (its centre is
the root, so both witnesses certify) — `isolate` itself always overshoots to a
much finer precision via speculative Newton, so a hand-built coarse atom is the
only way to exercise the refinement path. Its `atomWitness` is discharged by
kernel `decide` (degree 3), and the `RefinedIsolation` precision side-condition
`mahlerPrec rat1 = 16 ≤ prec` likewise. -/

/-- A coarse atom of `rat1` at the real root `re`, half-width `2^{−prec}`. -/
private def rootAtom (re prec : Int) (h : atomWitness rat1 ⟨re, 0, prec⟩) :
    DyadicRootIsolation rat1 := ⟨⟨re, 0, prec⟩, h⟩

private def atom1_20 : DyadicRootIsolation rat1 := rootAtom 1 20 (Or.inl (by decide))
private def atom1_22 : DyadicRootIsolation rat1 := rootAtom 1 22 (Or.inl (by decide))
private def atom2_20 : DyadicRootIsolation rat1 := rootAtom 2 20 (Or.inl (by decide))

-- `refineTo?` reaches at least the target precision and preserves the root (the
-- old and refined discs still meet), under both atom strategies; refining to a
-- precision no finer than the current one returns the atom unchanged.
#guard
  (match atom1_20.refineTo? 64 .nk with
    | some r => 64 ≤ r.square.prec && DyadicSquare.discsMeet atom1_20.square r.square
    | none => false)
#guard
  (match atom1_20.refineTo? 64 .pellet with
    | some r => 64 ≤ r.square.prec && DyadicSquare.discsMeet atom1_20.square r.square
    | none => false)
#guard (atom1_20.refineTo? 20 .nkThenPellet).map (·.square.prec) == some 20

private def refined1_20 : RefinedIsolation rat1 := ⟨atom1_20, by decide⟩
private def refined1_22 : RefinedIsolation rat1 := ⟨atom1_22, by decide⟩
private def refined2_20 : RefinedIsolation rat1 := ⟨atom2_20, by decide⟩

-- `sameRoot` is `true` for two isolations of the root `1` and `false` across
-- the distinct roots `1` and `2`.
#guard RefinedIsolation.sameRoot refined1_20 refined1_22
#guard RefinedIsolation.sameRoot refined1_20 refined1_20
#guard !RefinedIsolation.sameRoot refined1_20 refined2_20

/-! ### Witnesses `witness` / `nkWitness` at degree 3.

At degree 3 both witnesses are dischargeable by kernel `decide` (the `@[expose]`
list-fold witness bodies reduce), which is exercised here on the square
`⟨1, 0, 4⟩` centred at the root `1`; the Boolean checkers additionally pin
success at each root and failure off-root or at the wrong root count. -/

example : nkWitness rat1 ⟨1, 0, 4⟩ := by decide
example : witness rat1 ⟨1, 0, 4⟩ 1 := by decide

-- `witnessCheck`: `k = 1` fires at the roots `1` and `2`, but `k = 2` fails (the
-- disc holds a single simple root).
#guard witnessCheck rat1 ⟨1, 0, 4⟩ 1
#guard witnessCheck rat1 ⟨2, 0, 4⟩ 1
#guard !witnessCheck rat1 ⟨1, 0, 4⟩ 2

-- `nkWitnessCheck`: fires at the roots `1` and `2`, fails far from every root.
#guard nkWitnessCheck rat1 ⟨1, 0, 4⟩
#guard nkWitnessCheck rat1 ⟨2, 0, 4⟩
#guard !nkWitnessCheck rat1 ⟨10, 10, 4⟩

/-! ### `rootFree`: `T₀` emptiness certificate.

Certifies a disc holds no root far from the roots, and (correctly) fails to
certify a disc centred on a root. -/

#guard rootFree rat1 ⟨10, 10, 4⟩
#guard !rootFree rat1 ⟨1, 0, 4⟩
#guard !rootFree rat1 ⟨-3, 0, 4⟩
#guard rootFree cheb10 ⟨10, 10, 4⟩

/-! ### `taylor`: exact Gaussian-dyadic expansion.

`taylor p 0` casts the coefficients (`p(X + 0) = p(X)`); a shift by the root `1`
of `rat1` gives `p(X + 1) = X³ + 3X² − 4X`, hand-computed by synthetic division.
The `mignotte` and `cheb10` expansions at `0` re-derive their committed
coefficient arrays. -/

#guard taylor rat1 (0, 0) == #[((6 : Dyadic), (0 : Dyadic)), (-7, 0), (0, 0), (1, 0)]
#guard taylor rat1 (1, 0) == #[((0 : Dyadic), (0 : Dyadic)), (-4, 0), (3, 0), (1, 0)]
#guard taylor mignotte (0, 0) ==
  #[((-1 : Dyadic), (0 : Dyadic)), (200, 0), (-10000, 0), (0, 0), (0, 0), (1, 0)]
#guard taylor cheb10 (0, 0) ==
  #[((-1 : Dyadic), (0 : Dyadic)), (0, 0), (50, 0), (0, 0), (-400, 0), (0, 0),
    (1120, 0), (0, 0), (-1280, 0), (0, 0), (512, 0)]

/-! ### `mahlerPrec` and `cauchyExp`: closed forms.

Each value is the hand-evaluated closed form of the module docstrings, not a
value read back from the function. -/

-- `mahlerPrec = 3 + ⌈T/2⌉` with `T = (n+2)⌈lg n⌉ + (n−1)⌈lg(n+1)⌉ + 2(n−1)⌈lg A⌉`.
#guard mahlerPrec rat1 == 16              -- n = 3, A = 7
#guard mahlerPrec mignotte == 76          -- n = 5, A = 10000
#guard mahlerPrec cheb10 == 144           -- n = 10, A = 1280
#guard mahlerPrec linear == 3             -- degenerate n = 1

-- `cauchyExp = ⌈lg ⌈(L + M)/L⌉⌉` for leading magnitude `L`, max non-leading `M`.
#guard cauchyExp rat1 == 3                -- L = 1, M = 7
#guard cauchyExp mignotte == 14           -- L = 1, M = 10000
#guard cauchyExp cheb10 == 2              -- L = 512, M = 1280
#guard cauchyExp constant == 0            -- degenerate degree 0

/-! ### `Component.refine1`: subdivision, `T₀` discard, gluing.

One round splits each square into four children one bit finer, discards children
whose discs certifiably hold no root, and glues the survivors. Far from every
root all four children are discarded and the component dies; the Cauchy square of
`rat1` keeps all four survivors (a connected `2×2` block) at one finer level; a
second round reaches two levels finer, with `candidateK` preserved throughout. -/

/-- The Cauchy start component of `rat1` (a single square at `prec = −3`). -/
private def cauchyRat1 : Component :=
  if h : 0 < rat1.degree?.getD 0 then Component.cauchy rat1 h else ⟨#[], 0⟩

#guard (Component.refine1 rat1 ⟨#[⟨100, 100, 4⟩], 1⟩).isEmpty
#guard
  (match Component.refine1 rat1 cauchyRat1 with
    | #[c] =>
        c.squares.size == 4 && c.candidateK == cauchyRat1.candidateK &&
          c.squares.all fun s => s.prec == -(cauchyExp rat1 : Int) + 1
    | _ => false)
#guard
  ((Component.refine1 rat1 cauchyRat1).flatMap (Component.refine1 rat1)).all fun c =>
    c.candidateK == cauchyRat1.candidateK &&
      c.squares.all fun s => s.prec == -(cauchyExp rat1 : Int) + 2

/-! ### `Component.certify?`: per-component certification.

A tight component at a simple root certifies as an atom; a component far from
every root certifies as nothing; a component around the double root of the
non-squarefree input certifies as a `k = 2` cluster. -/

#guard
  (match Component.certify? rat1 .nkThenPellet ⟨#[⟨1, 0, 20⟩], 1⟩ with
    | some (.atom _) => true
    | _ => false)
#guard (Component.certify? rat1 .nkThenPellet ⟨#[⟨100, 100, 20⟩], 1⟩).isNone
#guard
  (match Component.certify? multiple .nkThenPellet ⟨#[⟨5, 0, 4⟩], 2⟩ with
    | some (.cluster cl) => cl.k == 2
    | _ => false)

/-! ### `mignotte` (squarefree): cheap-operation coverage.

The runtime squarefreeness decision confirms `mignotte` has only simple roots,
and its coefficient array is re-derived by `taylor` at `0` above. Its full
`isolate` atom count is not asserted: on this fixture `isolate` returns two
atoms (the close pair near `1/100`) and drops the three large-magnitude roots
— a real root lies in `(21, 22)` since `p(21) = −321700` and `p(22) = 318031`.
That coverage defect is tracked in
https://github.com/kim-em/hex-dev/issues/8736; asserting the correct count here
would (rightly) fail, and asserting the observed count would lock in wrong
output, so neither is done. -/

#guard (if HasOnlySimpleRoots mignotte then true else false)

end RootsConformance
end Hex
