/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Taylor
public import Init.Data.Dyadic.Round

public section

/-!
# Bounded-precision coefficient balls for soft Pellet tests

This file contains the Mathlib-free arithmetic kernel used by the Graeffe
Pellet filter.  `CoeffBall` encloses a Gaussian-dyadic coefficient by a centre
and an `L¹` error radius.  Every arithmetic operation rounds the centre and
the accumulated error to a signed dyadic precision selected from the value's
binary magnitude.  Consequently `bits` bounds mantissa growth rather than the
number of digits after the binary point; large and tiny coefficients cost the
same working precision.

`taylorBalls` encloses the coefficients of the locally scaled polynomial
`p(c + hX)`, where `h = 2^(−s.prec)`.  The scale makes the square's
circumscribed radius a constant `√2`.  `graeffe` applies

```
  E(X)² - X O(X)²,       p(X) = E(X²) + X O(X²),
```

whose roots are the squares of the roots of `p`.  Repeated squaring therefore
amplifies root-modulus separation while coefficient mantissas remain bounded.
The companion `HexRootsMathlib.SoftPellet` proves every enclosure and the
root-count preservation theorem.
-/

namespace Hex

/-- The existing rational lower bound `181/128 < √2`, duplicated here under a
kernel-specific name so this module remains below `Pellet` in the import
graph. -/
@[expose] def softSqrt2Lo : Dyadic := .ofIntWithPrec 181 7

/-- The existing rational upper bound `√2 < 1449/1024`. -/
@[expose] def softSqrt2Hi : Dyadic := .ofIntWithPrec 1449 10

/-- A Gaussian dyadic centre with an `L¹` error radius.  The computational
constructors below always produce a nonnegative radius; keeping that fact out
of the structure leaves proof fields out of the hot path. -/
structure CoeffBall where
  center : GaussDyadic
  radius : Dyadic
  deriving DecidableEq

namespace CoeffBall

/-- The exact zero coefficient ball. -/
@[expose] def zero : CoeffBall := ⟨(0, 0), 0⟩

/-- `|re z| + |im z|`, an executable upper bound for the complex modulus. -/
@[expose] def normOne (z : GaussDyadic) : Dyadic :=
  Dyadic.abs z.1 + Dyadic.abs z.2

/-- Signed endpoint precision retaining roughly `bits` significant binary
digits. -/
@[expose] def sigPrec (bits : Nat) (x : Dyadic) : Int :=
  (bits : Int) - Dyadic.ceilLog2 (Dyadic.abs x)

/-- Round a nonnegative error bound upward while retaining about `bits`
significant binary digits. -/
@[expose] def roundRadius (bits : Nat) (x : Dyadic) : Dyadic :=
  x.roundUp (sigPrec bits x)

/-- Round a Gaussian centre and add the exact `L¹` displacement to an existing
error bound. -/
@[expose] def normalize (bits : Nat) (z : GaussDyadic) (error : Dyadic) : CoeffBall :=
  let re := z.1.roundDown (sigPrec bits z.1)
  let im := z.2.roundDown (sigPrec bits z.2)
  let displacement := Dyadic.abs (z.1 - re) + Dyadic.abs (z.2 - im)
  ⟨(re, im), roundRadius bits (error + displacement)⟩

/-- A rounded ball enclosing one exact Gaussian dyadic. -/
@[expose] def point (bits : Nat) (z : GaussDyadic) : CoeffBall :=
  normalize bits z 0

/-- Outward-rounded sum. -/
@[expose] def add (bits : Nat) (x y : CoeffBall) : CoeffBall :=
  normalize bits (GaussDyadic.add x.center y.center) (x.radius + y.radius)

/-- Outward-rounded difference. -/
@[expose] def sub (bits : Nat) (x y : CoeffBall) : CoeffBall :=
  normalize bits (GaussDyadic.sub x.center y.center) (x.radius + y.radius)

/-- Outward-rounded product.  The error formula is the standard
`L¹`-submultiplicative bound
`|cx|₁·ey + |cy|₁·ex + ex·ey`. -/
@[expose] def mul (bits : Nat) (x y : CoeffBall) : CoeffBall :=
  let error := normOne x.center * y.radius +
    normOne y.center * x.radius + x.radius * y.radius
  normalize bits (GaussDyadic.mul x.center y.center) error

/-- Lower modulus bound: `max(|re c|, |im c|) - error`, clamped at zero. -/
@[expose] def lo (x : CoeffBall) : Dyadic :=
  let raw := Dyadic.max (Dyadic.abs x.center.1) (Dyadic.abs x.center.2) - x.radius
  Dyadic.max 0 raw

/-- Upper modulus bound from the centre's `L¹` norm plus the error radius. -/
@[expose] def hi (x : CoeffBall) : Dyadic :=
  normOne x.center + x.radius

end CoeffBall

/-- One step of the soft Taylor coefficient fold. -/
@[expose] def softTaylorStep (p : ZPoly) (c : GaussDyadic) (bits k : Nat)
    (acc : CoeffBall × CoeffBall) (r : Nat) : CoeffBall × CoeffBall :=
  let cBall := CoeffBall.point bits c
  let scalar : Int := Int.ofNat (Nat.binom (k + r) k) * p.coeff (k + r)
  let term := CoeffBall.mul bits (CoeffBall.point bits (GaussDyadic.ofInt scalar)) acc.2
  (CoeffBall.add bits acc.1 term, CoeffBall.mul bits acc.2 cBall)

/-- State after `n` terms of one soft Taylor coefficient. -/
@[expose] def softTaylorState (p : ZPoly) (c : GaussDyadic) (bits k n : Nat) :
    CoeffBall × CoeffBall :=
  (List.range n).foldl (softTaylorStep p c bits k)
    (CoeffBall.zero, CoeffBall.point bits (GaussDyadic.ofInt 1))

/-- One bounded-precision coefficient of `p(c + hX)`.  The Taylor sum carries
the next power of `c` in its fold, so all coefficients together cost `O(n²)`
ball operations rather than recomputing powers. -/
@[expose] def softTaylorCoeff (p : ZPoly) (c : GaussDyadic) (h : Dyadic)
    (bits k : Nat) : CoeffBall :=
  let state := softTaylorState p c bits k (p.size - k)
  let hk := h ^ k
  CoeffBall.mul bits state.1 (CoeffBall.point bits (hk, 0))

/-- Coefficient balls for the locally scaled Taylor polynomial
`p(s.center + 2^(−s.prec) X)`. -/
@[expose] def taylorBalls (p : ZPoly) (s : DyadicSquare) (bits : Nat) : Array CoeffBall :=
  let h : Dyadic := .ofIntWithPrec 1 s.prec
  (Array.range p.size).map fun k => softTaylorCoeff p s.center h bits k

/-- Rounded balls made from a supplied exact Taylor coefficient array. -/
@[expose] def seededTaylorBalls (cs : Array GaussDyadic) (s : DyadicSquare)
    (bits : Nat) : Array CoeffBall :=
  let h : Dyadic := .ofIntWithPrec 1 s.prec
  (Array.range cs.size).map fun k =>
    CoeffBall.point bits <|
      GaussDyadic.mul (cs.getD k (0, 0)) (h ^ k, 0)

/-- Rounded balls made from a freshly computed exact Taylor shift. This
compatibility wrapper is used by proof-facing and standalone callers; cached
certification paths pass their existing coefficients to `seededTaylorBalls`. -/
@[expose] def exactTaylorBalls (p : ZPoly) (s : DyadicSquare)
    (bits : Nat) : Array CoeffBall :=
  seededTaylorBalls (taylor p s.center) s bits

/-- Even-even convolution contributing coefficient `k` of one Graeffe step. -/
@[expose] def graeffeEven (bits : Nat) (cs : Array CoeffBall) (k : Nat) : CoeffBall :=
  (List.range (k + 1)).foldl (init := CoeffBall.zero) fun acc i =>
    CoeffBall.add bits acc <|
      CoeffBall.mul bits (cs.getD (2 * i) CoeffBall.zero)
        (cs.getD (2 * (k - i)) CoeffBall.zero)

/-- Odd-odd convolution contributing the shifted coefficient `k+1` of one
Graeffe step. -/
@[expose] def graeffeOdd (bits : Nat) (cs : Array CoeffBall) (k : Nat) : CoeffBall :=
  (List.range (k + 1)).foldl (init := CoeffBall.zero) fun acc i =>
    CoeffBall.add bits acc <|
      CoeffBall.mul bits (cs.getD (2 * i + 1) CoeffBall.zero)
        (cs.getD (2 * (k - i) + 1) CoeffBall.zero)

/-- One outward-rounded Graeffe step.  The output retains the input array size;
out-of-range convolution terms are exact zero balls. -/
@[expose] def graeffe (bits : Nat) (cs : Array CoeffBall) : Array CoeffBall :=
  (Array.range cs.size).map fun k =>
    if k = 0 then graeffeEven bits cs 0
    else CoeffBall.sub bits (graeffeEven bits cs k) (graeffeOdd bits cs (k - 1))

@[simp] theorem graeffe_size (bits : Nat) (cs : Array CoeffBall) :
    (graeffe bits cs).size = cs.size := by
  simp [graeffe]

/-- One Pellet comparison on coefficient balls.  The lower bound of the
selected coefficient is compared with upper bounds for every other
coefficient. -/
@[expose] def softPelletAt (cs : Array CoeffBall) (k : Nat)
    (rlo rhi : Dyadic) : Bool :=
  if k < cs.size then
    let lhs := (cs.getD k CoeffBall.zero).lo * rlo ^ k
    let rhs :=
      ((List.range cs.size).foldl (init := ((0 : Dyadic), (1 : Dyadic)))
        fun acc i =>
          let acc' := if i = k then acc.1
            else acc.1 + (cs.getD i CoeffBall.zero).hi * acc.2
          (acc', acc.2 * rhi)).1
    decide (rhs < lhs)
  else
    false

/-- BSSY's number of Graeffe rounds.  The nested logarithm is tiny (at most
nine rounds through degree 255), while the added five rounds give their fixed
isolation-ratio constants. -/
@[expose] def graeffeRounds (degree : Nat) : Nat :=
  ceilLog2 (1 + ceilLog2 (Nat.max 2 degree)) + 5

/-- The three radius intervals transported together through Graeffe
iteration.  All six endpoints are stored explicitly because every radius,
not merely the base radius, must be squared after roots are squared. -/
structure SoftRadii where
  baseLo : Dyadic
  baseHi : Dyadic
  twoLo : Dyadic
  twoHi : Dyadic
  fourLo : Dyadic
  fourHi : Dyadic
  deriving DecidableEq

/-- Initial local-coordinate bounds for `√2`, `2√2`, and `4√2`. -/
@[expose] def SoftRadii.initial : SoftRadii :=
  ⟨softSqrt2Lo, softSqrt2Hi,
    softSqrt2Lo <<< (1 : Int), softSqrt2Hi <<< (1 : Int),
    softSqrt2Lo <<< (2 : Int), softSqrt2Hi <<< (2 : Int)⟩

/-- Transport all three radius intervals through one root-squaring step. -/
@[expose] def SoftRadii.square (rs : SoftRadii) : SoftRadii :=
  ⟨rs.baseLo * rs.baseLo, rs.baseHi * rs.baseHi,
    rs.twoLo * rs.twoLo, rs.twoHi * rs.twoHi,
    rs.fourLo * rs.fourLo, rs.fourHi * rs.fourHi⟩

/-- Check the three transported Pellet radii at this Graeffe level. -/
@[expose] def softPelletThree (cs : Array CoeffBall) (k : Nat)
    (rs : SoftRadii) : Bool :=
  softPelletAt cs k rs.baseLo rs.baseHi &&
    softPelletAt cs k rs.twoLo rs.twoHi &&
    softPelletAt cs k rs.fourLo rs.fourHi

private theorem softPelletThree_false {cs : Array CoeffBall} {k : Nat}
    (rs : SoftRadii) (h : cs.size ≤ k) : softPelletThree cs k rs = false := by
  simp [softPelletThree, softPelletAt, Nat.not_lt.mpr h]

/-- Try the initial locally scaled Taylor polynomial and every Graeffe level
through `rounds`.  Squaring the radius bounds in lockstep matches the root
squaring transformation. -/
@[expose] def softGraeffeLoop (bits k : Nat) :
    Nat → Array CoeffBall → SoftRadii → Bool
  | 0, cs, rs => softPelletThree cs k rs
  | rounds + 1, cs, rs =>
      softPelletThree cs k rs ||
        softGraeffeLoop bits k rounds (graeffe bits cs) rs.square

private theorem softGraeffeLoop_false {bits k rounds : Nat}
    {cs : Array CoeffBall} {rs : SoftRadii} (h : cs.size ≤ k) :
    softGraeffeLoop bits k rounds cs rs = false := by
  induction rounds generalizing cs rs with
  | zero => exact softPelletThree_false rs h
  | succ rounds ih =>
      rw [softGraeffeLoop, softPelletThree_false rs h, Bool.false_or]
      apply ih
      simpa using h

/-- One working-precision attempt at the three-radius soft Graeffe witness. -/
@[expose] def softWitnessAt (p : ZPoly) (s : DyadicSquare)
    (k bits : Nat) : Bool :=
  softGraeffeLoop bits k (graeffeRounds (p.degree?.getD 0))
    (taylorBalls p s bits) SoftRadii.initial

/-- Three-radius Graeffe witness seeded from one exact Taylor shift.  This is
the tighter and cheaper shallow-centre variant. -/
@[expose] def softSeededWitness (p : ZPoly) (s : DyadicSquare)
    (k bits : Nat) : Bool :=
  softGraeffeLoop bits k (graeffeRounds (p.degree?.getD 0))
    (exactTaylorBalls p s bits) SoftRadii.initial

/-- Three-radius exact-seeded witness reusing an existing Taylor shift. -/
@[expose] def TaylorShift.softSeededWitness {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k bits : Nat) : Bool :=
  softGraeffeLoop bits k (graeffeRounds (p.degree?.getD 0))
    (seededTaylorBalls shift.coeffs s bits) SoftRadii.initial

/-- A valid cached shift gives the standalone exact-seeded witness. -/
theorem TaylorShift.softSeededWitness_eq {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k bits : Nat) :
    shift.softSeededWitness s k bits =
      _root_.Hex.softSeededWitness p s k bits := by
  have hshift : shift = TaylorShift.compute p s.center := Subsingleton.elim _ _
  subst shift
  rfl

/-- Working precisions tried by the soft filter.  Failure at all tiers is not
negative evidence: callers retain the exact Pellet fallback. -/
@[expose] def softPrecisions : List Nat := [64, 128, 256]

/-- Adaptive soft Graeffe witness reusing an existing exact shift on the
shallow seeded route. -/
@[expose] def TaylorShift.softWitnessCheck {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k : Nat) : Bool :=
  if s.prec < 32 then
    shift.softSeededWitness s k 64 ||
      (softPrecisions.any fun bits => softWitnessAt p s k bits)
  else
    (softPrecisions.any fun bits => softWitnessAt p s k bits) ||
      shift.softSeededWitness s k 64

/-- Adaptive soft Graeffe witness. Standalone callers compute the shallow
exact seed once; cached certifiers use `TaylorShift.softWitnessCheck`. -/
@[expose] def softWitnessCheck (p : ZPoly) (s : DyadicSquare) (k : Nat) : Bool :=
  (TaylorShift.compute p s.center).softWitnessCheck s k

/-- No soft root-count witness can select a coefficient outside the
    polynomial's coefficient array. -/
theorem softWitnessCheck_false {p : ZPoly} {s : DyadicSquare} {k : Nat}
    (h : p.size ≤ k) : softWitnessCheck p s k = false := by
  have hAt (bits : Nat) : softWitnessAt p s k bits = false := by
    apply softGraeffeLoop_false
    simpa [taylorBalls] using h
  have hSeed (bits : Nat) :
      (TaylorShift.compute p s.center).softSeededWitness s k bits = false := by
    apply softGraeffeLoop_false
    simpa [seededTaylorBalls, TaylorShift.compute, taylor_size] using h
  simp [softWitnessCheck, TaylorShift.softWitnessCheck, softPrecisions, hAt, hSeed]

/-- Any valid cached shift gives the same adaptive soft witness as the public
standalone wrapper. -/
theorem TaylorShift.softWitnessCheck_eq {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k : Nat) :
    shift.softWitnessCheck s k = _root_.Hex.softWitnessCheck p s k := by
  have hshift : shift = TaylorShift.compute p s.center := Subsingleton.elim _ _
  subst shift
  rfl

/-- First positive root count whose three-radius comparison succeeds at one
Graeffe level. -/
@[expose] def firstSoftCandidate? (cs : Array CoeffBall) (rs : SoftRadii) :
    List Nat → Option Nat
  | [] => none
  | k :: ks =>
      if 0 < k && softPelletThree cs k rs then some k
      else firstSoftCandidate? cs rs ks

/-- Scan all candidate counts at each Graeffe level before transforming the
coefficient array once. -/
@[expose] def softCandidateLoop (bits : Nat) (ks : List Nat) :
    Nat → Array CoeffBall → SoftRadii → Option Nat
  | 0, cs, rs => firstSoftCandidate? cs rs ks
  | rounds + 1, cs, rs =>
      match firstSoftCandidate? cs rs ks with
      | some k => some k
      | none => softCandidateLoop bits ks rounds (graeffe bits cs) rs.square

/-- One working-precision all-count candidate search. -/
@[expose] def softCandidateAt? (p : ZPoly) (s : DyadicSquare)
    (ks : List Nat) (bits : Nat) : Option Nat :=
  softCandidateLoop bits ks (graeffeRounds (p.degree?.getD 0))
    (taylorBalls p s bits) SoftRadii.initial

/-- One-precision all-count candidate search seeded from an exact Taylor
shift. -/
@[expose] def softSeededCandidate? (p : ZPoly) (s : DyadicSquare)
    (ks : List Nat) (bits : Nat) : Option Nat :=
  softCandidateLoop bits ks (graeffeRounds (p.degree?.getD 0))
    (exactTaylorBalls p s bits) SoftRadii.initial

/-- One-precision all-count candidate search reusing an existing exact Taylor
shift for its coefficient balls. -/
@[expose] def TaylorShift.softSeededCandidate? {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (ks : List Nat) (bits : Nat) : Option Nat :=
  softCandidateLoop bits ks (graeffeRounds (p.degree?.getD 0))
    (seededTaylorBalls shift.coeffs s bits) SoftRadii.initial

/-- Try an all-count candidate search at each working precision. -/
@[expose] def softCandidateAdaptive? (p : ZPoly) (s : DyadicSquare)
    (ks : List Nat) : List Nat → Option Nat
  | [] => none
  | bits :: rest =>
      (softCandidateAt? p s ks bits).orElse fun _ =>
        softCandidateAdaptive? p s ks rest

/-- Adaptive all-count soft Graeffe search. -/
@[expose] def softCandidate? (p : ZPoly) (s : DyadicSquare)
    (ks : List Nat) : Option Nat :=
  softCandidateAdaptive? p s ks softPrecisions

/-- Certification search tuned for subdivision and reusing its cached exact
shift: one seeded 64-bit pass while exact centres are still cheap, then the
fully soft ladder once centre bit-length reaches 32. -/
@[expose] def TaylorShift.softRefinementCandidate? {p : ZPoly}
    (s : DyadicSquare) (shift : TaylorShift p s.center)
    (ks : List Nat) : Option Nat :=
  if s.prec < 32 then shift.softSeededCandidate? s ks 64
  else softCandidate? p s ks

/-- Standalone refinement candidate search. Cached certifiers call the
`TaylorShift` method directly. -/
@[expose] def softRefinementCandidate? (p : ZPoly) (s : DyadicSquare)
    (ks : List Nat) : Option Nat :=
  (TaylorShift.compute p s.center).softRefinementCandidate? s ks

/-- A valid cached shift gives the public standalone candidate result. -/
theorem TaylorShift.softRefinementCandidate?_eq {p : ZPoly}
    (s : DyadicSquare) (shift : TaylorShift p s.center) (ks : List Nat) :
    shift.softRefinementCandidate? s ks =
      _root_.Hex.softRefinementCandidate? p s ks := by
  have hshift : shift = TaylorShift.compute p s.center := Subsingleton.elim _ _
  subst shift
  rfl

/-- First candidate count at one base radius.  Unlike
`firstSoftCandidate?`, this includes `k = 0`, so callers can distinguish a
certified discard from a certified positive root count. -/
@[expose] def firstSoftRootCount? (cs : Array CoeffBall) (rlo rhi : Dyadic) :
    List Nat → Option Nat
  | [] => none
  | k :: ks =>
      if softPelletAt cs k rlo rhi then some k
      else firstSoftRootCount? cs rlo rhi ks

/-- Search all requested root counts at the base radius, reusing each
Graeffe transform for the whole list. -/
@[expose] def softRootCountLoop (bits : Nat) (ks : List Nat) :
    Nat → Array CoeffBall → Dyadic → Dyadic → Option Nat
  | 0, cs, rlo, rhi => firstSoftRootCount? cs rlo rhi ks
  | rounds + 1, cs, rlo, rhi =>
      match firstSoftRootCount? cs rlo rhi ks with
      | some k => some k
      | none => softRootCountLoop bits ks rounds (graeffe bits cs)
          (rlo * rlo) (rhi * rhi)

/-- Base-radius all-count filter seeded by one exact Taylor shift. -/
@[expose] def softSeededRootCount? (p : ZPoly) (s : DyadicSquare)
    (ks : List Nat) (bits : Nat) : Option Nat :=
  softRootCountLoop bits ks (graeffeRounds (p.degree?.getD 0))
    (exactTaylorBalls p s bits) softSqrt2Lo softSqrt2Hi

/-- A returned first-level candidate is positive and passes its comparison. -/
theorem firstSoftCandidate?_sound {cs : Array CoeffBall} {rs : SoftRadii}
    {ks : List Nat} {k : Nat} (h : firstSoftCandidate? cs rs ks = some k) :
    0 < k ∧ softPelletThree cs k rs = true := by
  induction ks with
  | nil => contradiction
  | cons j js ih =>
      unfold firstSoftCandidate? at h
      split at h <;> rename_i hj
      · simp only [Option.some.injEq] at h
        subst j
        have hj' : decide (0 < k) = true ∧ softPelletThree cs k rs = true := by
          simpa only [Bool.and_eq_true] using hj
        exact ⟨of_decide_eq_true hj'.1, hj'.2⟩
      · exact ih h

/-- An all-count loop result is also a successful per-count loop result. -/
theorem softCandidateLoop_sound {bits : Nat} {ks : List Nat} {rounds : Nat}
    {cs : Array CoeffBall} {rs : SoftRadii} {k : Nat}
    (h : softCandidateLoop bits ks rounds cs rs = some k) :
    0 < k ∧ softGraeffeLoop bits k rounds cs rs = true := by
  induction rounds generalizing cs rs with
  | zero =>
      exact firstSoftCandidate?_sound h
  | succ rounds ih =>
      unfold softCandidateLoop at h
      split at h <;> rename_i hfirst
      · rename_i j
        simp only [Option.some.injEq] at h
        subst j
        have hs := firstSoftCandidate?_sound hfirst
        exact ⟨hs.1, by simp [softGraeffeLoop, hs.2]⟩
      · have hs := ih h
        exact ⟨hs.1, by simp [softGraeffeLoop, hs.2]⟩

/-- One-precision candidate search implies the ordinary witness check at that
precision. -/
theorem softCandidateAt?_sound {p : ZPoly} {s : DyadicSquare}
    {ks : List Nat} {bits k : Nat}
    (h : softCandidateAt? p s ks bits = some k) :
    0 < k ∧ softWitnessAt p s k bits = true := by
  exact softCandidateLoop_sound h

/-- An exact-seeded candidate is accepted by its exact-seeded per-count
witness. -/
theorem softSeededCandidate?_sound {p : ZPoly} {s : DyadicSquare}
    {ks : List Nat} {bits k : Nat}
    (h : softSeededCandidate? p s ks bits = some k) :
    0 < k ∧ softSeededWitness p s k bits = true := by
  exact softCandidateLoop_sound h

/-- The adaptive all-count search returns only a positive count accepted by
the public per-count soft witness. -/
theorem softCandidate?_sound {p : ZPoly} {s : DyadicSquare}
    {ks : List Nat} {k : Nat} (h : softCandidate? p s ks = some k) :
    0 < k ∧ softWitnessCheck p s k = true := by
  have go : ∀ precisions,
      softCandidateAdaptive? p s ks precisions = some k →
        0 < k ∧ ∃ bits ∈ precisions, softWitnessAt p s k bits = true := by
    intro precisions
    induction precisions with
    | nil => intro h; contradiction
    | cons bits rest ih =>
        intro hresult
        unfold softCandidateAdaptive? at hresult
        cases hbits : softCandidateAt? p s ks bits with
        | none =>
            simp only [hbits, Option.orElse_none] at hresult
            obtain ⟨hk, witnessBits, hmem, hwitness⟩ := ih hresult
            exact ⟨hk, witnessBits, by simp [hmem], hwitness⟩
        | some j =>
            simp only [hbits, Option.orElse_some, Option.some.injEq] at hresult
            subst j
            have hs := softCandidateAt?_sound hbits
            exact ⟨hs.1, bits, by simp, hs.2⟩
  obtain ⟨hk, bits, hmem, hbits⟩ := go softPrecisions h
  have hany : softPrecisions.any (fun bits => softWitnessAt p s k bits) = true :=
    List.any_eq_true.mpr ⟨bits, hmem, hbits⟩
  refine ⟨hk, ?_⟩
  by_cases hprec : s.prec < 32 <;>
    simp [softWitnessCheck, TaylorShift.softWitnessCheck, hprec, hany]

/-- The depth-aware candidate search still returns an ordinary public soft
witness. -/
theorem softRefinementCandidate?_sound {p : ZPoly} {s : DyadicSquare}
    {ks : List Nat} {k : Nat} (h : softRefinementCandidate? p s ks = some k) :
    0 < k ∧ softWitnessCheck p s k = true := by
  unfold softRefinementCandidate? TaylorShift.softRefinementCandidate? at h
  by_cases hprec : s.prec < 32
  · have hs : softSeededCandidate? p s ks 64 = some k := by
      rw [if_pos hprec] at h
      change softSeededCandidate? p s ks 64 = some k at h
      exact h
    have hsound := softSeededCandidate?_sound hs
    have hseed :
        (TaylorShift.compute p s.center).softSeededWitness s k 64 = true := by
      change softSeededWitness p s k 64 = true
      exact hsound.2
    exact ⟨hsound.1, by
      simp [softWitnessCheck, TaylorShift.softWitnessCheck, hprec, hseed]⟩
  · have hs : softCandidate? p s ks = some k := by
      simpa [hprec] using h
    exact softCandidate?_sound hs

/-- Base-radius `T₀` comparison at the initial level and every Graeffe
level.  Unlike the three-radius atom witness, exclusion needs only the square's
circumscribed disc. -/
@[expose] def softRootFreeLoop (bits : Nat) :
    Nat → Array CoeffBall → Dyadic → Dyadic → Bool
  | 0, cs, rlo, rhi => softPelletAt cs 0 rlo rhi
  | rounds + 1, cs, rlo, rhi =>
      softPelletAt cs 0 rlo rhi ||
        softRootFreeLoop bits rounds (graeffe bits cs)
          (rlo * rlo) (rhi * rhi)

/-- Soft single-radius Graeffe `T₀` filter for subdivision. -/
@[expose] def softRootFreeAt (p : ZPoly) (s : DyadicSquare) (bits : Nat) : Bool :=
  softRootFreeLoop bits (graeffeRounds (p.degree?.getD 0))
    (taylorBalls p s bits) softSqrt2Lo softSqrt2Hi

/-- Adaptive soft `T₀` discard. -/
@[expose] def softRootFree (p : ZPoly) (s : DyadicSquare) : Bool :=
  softPrecisions.any fun bits => softRootFreeAt p s bits

end Hex
