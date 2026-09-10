/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyZ.Kronecker
public meta import HexPolyZ.Decomposition
public meta import HexPolyZGcd.Brown
public meta import HexPolyZGcd.Heu
public meta import HexPolyZGcd.Prs
public import HexPolyZ.Kronecker
public import HexPolyZ.Decomposition
public import HexPolyZGcd.Brown
public import HexPolyZGcd.Heu
public import HexPolyZGcd.Prs

public section
set_option backward.proofsInPublic true

/-!
The usable integer-polynomial gcd API.

Fast candidates are replayed by one checker and fall through to the total
extended-subresultant route.  The earlier rational implementation remains in
this file as an independently named reference implementation and test oracle;
it is not part of public dispatch.
-/

namespace Hex

namespace ZPoly

/-- Vanishing integer content characterizes the zero polynomial. -/
private theorem eqZeroOfContent {f : ZPoly} (hcontent : content f = 0) :
    f = 0 := by
  have hreconstruct := content_mul_primitivePart f
  rw [hcontent] at hreconstruct
  simpa using hreconstruct.symm

/-- Coefficientwise rationalization is injective. -/
private theorem toRatInjective {p q : ZPoly} (h : toRatPoly p = toRatPoly q) :
    p = q := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun r : DensePoly Rat => r.coeff n) h
  rw [coeff_toRatPoly, coeff_toRatPoly] at hcoeff
  exact_mod_cast hcoeff

/-- Coefficientwise rationalization preserves polynomial addition. -/
private theorem toRatAdd (p q : ZPoly) :
    toRatPoly (p + q) = toRatPoly p + toRatPoly q := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly,
    DensePoly.coeff_add (R := Int) (hzero := by rfl),
    DensePoly.coeff_add (R := Rat) (hzero := by exact Rat.zero_add 0),
    coeff_toRatPoly, coeff_toRatPoly]
  exact Rat.intCast_add _ _

/-- A polynomial of size at most one is its constant coefficient. -/
private theorem eqCOfSizeLe {p : DensePoly Rat} (hsize : p.size ≤ 1) :
    p = DensePoly.C (p.coeff 0) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  cases n with
  | zero => simp
  | succ n =>
      rw [DensePoly.coeff_eq_zero_of_size_le p (by omega)]
      rfl

/-- Cancel a nonzero rational scalar from a polynomial equality. -/
private theorem ratUnscale {c : Rat} (hc : c ≠ 0) {p q : DensePoly Rat}
    (hscale : DensePoly.scale c p = q) :
    p = DensePoly.scale c⁻¹ q := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun r : DensePoly Rat => r.coeff n) hscale
  rw [DensePoly.coeff_scale_semiring] at hcoeff ⊢
  rw [← hcoeff, ← Rat.mul_assoc, Rat.inv_mul_cancel c hc, Rat.one_mul]

/-- Sign normalization changes a polynomial only by the unit `-1`, so it
preserves divisibility into any target. -/
private theorem normalizeDvd {p f : ZPoly} (hpf : p ∣ f) :
    normalizePrimitiveSign p ∣ f := by
  unfold normalizePrimitiveSign
  split
  · rcases hpf with ⟨q, hq⟩
    refine ⟨DensePoly.scale (-1 : Int) q, ?_⟩
    rw [hq]
    symm
    calc
      DensePoly.scale (-1 : Int) p * DensePoly.scale (-1 : Int) q =
          DensePoly.scale (-1 : Int)
            (DensePoly.scale (-1 : Int) p * q) :=
        (DensePoly.mul_scale (-1 : Int) (DensePoly.scale (-1 : Int) p) q).symm
      _ = DensePoly.scale (-1 : Int)
          (DensePoly.scale (-1 : Int) (p * q)) := by
        exact congrArg (DensePoly.scale (-1 : Int))
          (DensePoly.scale_mul (-1 : Int) p q).symm
      _ = DensePoly.scale ((-1 : Int) * (-1 : Int)) (p * q) :=
        DensePoly.scale_scale (-1 : Int) (-1 : Int) (p * q)
      _ = p * q := by
        apply DensePoly.ext_coeff
        intro n
        rw [DensePoly.coeff_scale_semiring]
        omega
  · exact hpf

/-- A scalar divisor of the integer content, multiplied by the primitive
integer representative of a rational divisor, divides the original input. -/
private theorem scaledPrimitiveDvd {f : ZPoly} {rg : DensePoly Rat} {c : Int}
    (hrg : rg ∣ toRatPoly f) (hc : c ∣ content f) :
    DensePoly.scale c (ratPolyPrimitivePart rg) ∣ f := by
  by_cases hf : f = 0
  · subst f
    refine ⟨0, ?_⟩
    exact ((DensePoly.mul_comm_poly _ 0).trans (DensePoly.zero_mul _)).symm
  · let r := ratPolyPrimitivePart rg
    have hrgNe : rg ≠ 0 := by
      intro hzero
      rcases hrg with ⟨q, hq⟩
      apply toRatPoly_ne_zero_of_ne_zero f hf
      rw [hzero, DensePoly.zero_mul] at hq
      exact hq
    have hrNe : r ≠ 0 := by
      rcases ratPolyPrimitivePart_rational_associate rg with ⟨u, hu⟩
      intro hzero
      apply hrgNe
      dsimp only [r] at hzero
      rw [hu, hzero, toRatPoly_zero]
      exact DensePoly.scale_zero_right u
    have hrPrimitive : Primitive r := by
      apply ratPolyPrimitivePart_primitive
      intro hcontent
      exact hrNe (eqZeroOfContent hcontent)
    have hrRatF : toRatPoly r ∣ toRatPoly f := by
      rcases hrg with ⟨a, ha⟩
      rcases ratPolyPrimitivePart_rational_associate rg with ⟨u, hu⟩
      have hu' : rg = DensePoly.scale u (toRatPoly r) := by
        simpa only [r] using hu
      refine ⟨DensePoly.scale u a, ?_⟩
      calc
        toRatPoly f = rg * a := ha
        _ = DensePoly.scale u (toRatPoly r) * a := by rw [hu']
        _ = DensePoly.scale u (toRatPoly r * a) :=
          (DensePoly.scale_mul u (toRatPoly r) a).symm
        _ = toRatPoly r * DensePoly.scale u a :=
          DensePoly.mul_scale u (toRatPoly r) a
    have hcontentNe : content f ≠ 0 := by
      intro hzero
      exact hf (eqZeroOfContent hzero)
    have hcontentRatNe : ((content f : Int) : Rat) ≠ 0 := by
      exact_mod_cast hcontentNe
    have hrRatPrimitive : toRatPoly r ∣ toRatPoly (primitivePart f) := by
      rcases hrRatF with ⟨q, hq⟩
      have hscaled :
          DensePoly.scale ((content f : Int) : Rat)
              (toRatPoly (primitivePart f)) = toRatPoly r * q := by
        rw [← toRatPoly_scale_int, content_mul_primitivePart]
        exact hq
      refine ⟨DensePoly.scale (((content f : Int) : Rat)⁻¹) q, ?_⟩
      calc
        toRatPoly (primitivePart f) =
            DensePoly.scale (((content f : Int) : Rat)⁻¹) (toRatPoly r * q) :=
          ratUnscale hcontentRatNe hscaled
        _ = toRatPoly r *
            DensePoly.scale (((content f : Int) : Rat)⁻¹) q :=
          DensePoly.mul_scale _ _ _
    have hrDvd : r ∣ primitivePart f :=
      dvd_of_toRatPoly_dvd_of_primitive hrPrimitive hrRatPrimitive
    rcases hrDvd with ⟨s, hs⟩
    rcases hc with ⟨k, hk⟩
    refine ⟨DensePoly.scale k s, ?_⟩
    calc
      f = DensePoly.scale (content f) (primitivePart f) :=
        (content_mul_primitivePart f).symm
      _ = DensePoly.scale (c * k) (r * s) := by rw [hk, hs]
      _ = DensePoly.scale c r * DensePoly.scale k s := by
        symm
        calc
          DensePoly.scale c r * DensePoly.scale k s =
              DensePoly.scale k (DensePoly.scale c r * s) :=
            (DensePoly.mul_scale k (DensePoly.scale c r) s).symm
          _ = DensePoly.scale k (DensePoly.scale c (r * s)) := by
            exact congrArg (DensePoly.scale k)
              (DensePoly.scale_mul c r s).symm
          _ = DensePoly.scale (k * c) (r * s) :=
            DensePoly.scale_scale k c (r * s)
          _ = DensePoly.scale (c * k) (r * s) := by rw [Int.mul_comm]

/-- The canonical integer candidate obtained from the rational gcd, with the
common integer content restored. -/
def rationalGcdCandidate (f h : ZPoly) : ZPoly :=
  let primitive :=
    ratPolyPrimitivePart (DensePoly.gcd (toRatPoly f) (toRatPoly h))
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  normalizePrimitiveSign (DensePoly.scale commonContent primitive)

/-- On a primitive left input, rational candidate construction is exactly the
positive primitive representative of the rational gcd. -/
theorem rationalGcdCandidate_of_primitive {f h : ZPoly} (hf : Primitive f) :
    rationalGcdCandidate f h =
      ratPolyPrimitivePart (DensePoly.gcd (toRatPoly f) (toRatPoly h)) := by
  let primitive :=
    ratPolyPrimitivePart (DensePoly.gcd (toRatPoly f) (toRatPoly h))
  have hscaleOne : DensePoly.scale (1 : Int) primitive = primitive := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale_semiring, Int.one_mul]
  unfold rationalGcdCandidate
  rw [show Int.gcd (content f) (content h) = 1 by
    rw [show content f = 1 from hf]
    exact Nat.gcd_eq_left_iff_dvd.mpr (Nat.one_dvd _)]
  change normalizePrimitiveSign (DensePoly.scale (1 : Int) primitive) = primitive
  rw [hscaleOne]
  unfold normalizePrimitiveSign
  rw [ite_eq_right (by
    have hlead := leadingCoeff_ratPolyPrimitivePart_nonneg
      (DensePoly.gcd (toRatPoly f) (toRatPoly h))
    have hleadPrimitive : 0 ≤ DensePoly.leadingCoeff primitive := by
      simpa only [primitive] using hlead
    omega)]

/-- A nontrivial input pair has a nonzero rational gcd. -/
private theorem ratGcdNe {f h : ZPoly} (hnz : f ≠ 0 ∨ h ≠ 0) :
    DensePoly.gcd (toRatPoly f) (toRatPoly h) ≠ 0 := by
  rcases hnz with hf | hh
  · intro hzero
    rcases DensePoly.gcd_dvd_left (toRatPoly f) (toRatPoly h) with ⟨a, ha⟩
    apply toRatPoly_ne_zero_of_ne_zero f hf
    rw [hzero, DensePoly.zero_mul] at ha
    exact ha
  · intro hzero
    rcases DensePoly.gcd_dvd_right (toRatPoly f) (toRatPoly h) with ⟨a, ha⟩
    apply toRatPoly_ne_zero_of_ne_zero h hh
    rw [hzero, DensePoly.zero_mul] at ha
    exact ha

/-- Clearing and primitive normalization preserve a nonzero rational gcd. -/
private theorem ratPrimitiveNe {rg : DensePoly Rat} (hrg : rg ≠ 0) :
    ratPolyPrimitivePart rg ≠ 0 := by
  rcases ratPolyPrimitivePart_rational_associate rg with ⟨u, hu⟩
  intro hzero
  apply hrg
  rw [hu, hzero, toRatPoly_zero]
  exact DensePoly.scale_zero_right u

/-- The integer representative of a nonzero rational polynomial is primitive. -/
private theorem ratPrimitive {rg : DensePoly Rat} (hrg : rg ≠ 0) :
    Primitive (ratPolyPrimitivePart rg) := by
  apply ratPolyPrimitivePart_primitive
  intro hcontent
  exact ratPrimitiveNe hrg (eqZeroOfContent hcontent)

/-- A nontrivial pair has positive common integer content. -/
private theorem commonContentNe {f h : ZPoly} (hnz : f ≠ 0 ∨ h ≠ 0) :
    Int.gcd (content f) (content h) ≠ 0 := by
  intro hzero
  rcases Int.gcd_eq_zero_iff.mp hzero with ⟨hf, hh⟩
  rcases hnz with hnz | hnz
  · exact hnz (eqZeroOfContent hf)
  · exact hnz (eqZeroOfContent hh)

/-- The candidate contains exactly the gcd of the two input contents. -/
private theorem candidateContent {f h : ZPoly} (hnz : f ≠ 0 ∨ h ≠ 0) :
    content (rationalGcdCandidate f h) =
      Int.ofNat (Int.gcd (content f) (content h)) := by
  let rg := DensePoly.gcd (toRatPoly f) (toRatPoly h)
  let r := ratPolyPrimitivePart rg
  let c : Int := Int.ofNat (Int.gcd (content f) (content h))
  have hrgNe : rg ≠ 0 := by simpa only [rg] using ratGcdNe hnz
  have hrPrimitive : Primitive r := by simpa only [r] using ratPrimitive hrgNe
  have hrContent : DensePoly.content r = 1 := by
    simpa [Primitive, content] using hrPrimitive
  change content (normalizePrimitiveSign (DensePoly.scale c r)) = c
  unfold normalizePrimitiveSign
  split
  · change DensePoly.content (DensePoly.scale (-1 : Int) (DensePoly.scale c r)) = c
    rw [DensePoly.content_scale_neg_one, DensePoly.content_scale_int, hrContent]
    simp only [Int.mul_one]
    dsimp only [c]
    simp
  · change DensePoly.content (DensePoly.scale c r) = c
    rw [DensePoly.content_scale_int, hrContent]
    simp only [Int.mul_one]
    dsimp only [c]
    simp

/-- The candidate is nonzero unless both inputs are zero. -/
theorem rationalGcdCandidate_ne_zero {f h : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0) :
    rationalGcdCandidate f h ≠ 0 := by
  let rg := DensePoly.gcd (toRatPoly f) (toRatPoly h)
  let primitive := ratPolyPrimitivePart rg
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  have hrgNe : rg ≠ 0 := by
    rcases hnz with hf | hh
    · intro hzero
      dsimp only [rg] at hzero
      rcases DensePoly.gcd_dvd_left (toRatPoly f) (toRatPoly h) with ⟨a, ha⟩
      apply toRatPoly_ne_zero_of_ne_zero f hf
      rw [hzero, DensePoly.zero_mul] at ha
      exact ha
    · intro hzero
      dsimp only [rg] at hzero
      rcases DensePoly.gcd_dvd_right (toRatPoly f) (toRatPoly h) with ⟨a, ha⟩
      apply toRatPoly_ne_zero_of_ne_zero h hh
      rw [hzero, DensePoly.zero_mul] at ha
      exact ha
  have hprimitiveNe : primitive ≠ 0 := by
    rcases ratPolyPrimitivePart_rational_associate rg with ⟨u, hu⟩
    intro hzero
    dsimp only [primitive] at hzero
    apply hrgNe
    rw [hu, hzero, toRatPoly_zero]
    exact DensePoly.scale_zero_right u
  have hcommonNat : Int.gcd (content f) (content h) ≠ 0 := by
    intro hzero
    rcases Int.gcd_eq_zero_iff.mp hzero with ⟨hf, hh⟩
    rcases hnz with hnz | hnz
    · exact hnz (eqZeroOfContent hf)
    · exact hnz (eqZeroOfContent hh)
  have hcommonNe : commonContent ≠ 0 := by
    change Int.ofNat (Int.gcd (content f) (content h)) ≠ 0
    exact Int.ofNat_ne_zero.mpr hcommonNat
  have hscaledNe : DensePoly.scale commonContent primitive ≠ 0 := by
    intro hzero
    have hsize : primitive.size = 0 := by
      rw [← scale_size_of_ne_zero commonContent primitive hcommonNe, hzero]
      rfl
    exact hprimitiveNe ((DensePoly.size_eq_zero_iff primitive).mp hsize)
  change normalizePrimitiveSign (DensePoly.scale commonContent primitive) ≠ 0
  intro hzero
  have hsize : (normalizePrimitiveSign (DensePoly.scale commonContent primitive)).size = 0 := by
    rw [hzero]
    rfl
  rw [size_normalizePrimitiveSign] at hsize
  exact hscaledNe ((DensePoly.size_eq_zero_iff _).mp hsize)

/-- The rational candidate satisfies the public normalization predicate. -/
private theorem candidateNormalized {f h : ZPoly} (hnz : f ≠ 0 ∨ h ≠ 0) :
    NormalizedGcd (rationalGcdCandidate f h) = true := by
  have hgNe := rationalGcdCandidate_ne_zero hnz
  have hleadNonneg :
      0 ≤ DensePoly.leadingCoeff (rationalGcdCandidate f h) := by
    simpa only [rationalGcdCandidate] using
      leadingCoeff_normalizePrimitiveSign_nonneg
        (DensePoly.scale (Int.ofNat (Int.gcd (content f) (content h)))
          (ratPolyPrimitivePart (DensePoly.gcd (toRatPoly f) (toRatPoly h))))
  have hleadNe := leadingCoeff_ne_zero_of_ne_zero _ hgNe
  have hlead : 0 < DensePoly.leadingCoeff (rationalGcdCandidate f h) := by omega
  have hcontent : 0 < content (rationalGcdCandidate f h) := by
    rw [candidateContent hnz]
    have hpos := Nat.pos_of_ne_zero (commonContentNe hnz)
    exact Int.natCast_pos.mpr hpos
  simp [NormalizedGcd, hlead, hcontent]

/-- Removing the full common content leaves cofactors with coprime integer
contents. -/
private theorem cofactorContents {f h cofL cofR : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0)
    (hleft : rationalGcdCandidate f h * cofL = f)
    (hright : rationalGcdCandidate f h * cofR = h) :
    Int.gcd (content cofL) (content cofR) = 1 := by
  let common := Int.gcd (content f) (content h)
  have hcommonPos : 0 < common := Nat.pos_of_ne_zero (commonContentNe hnz)
  have hgContent : content (rationalGcdCandidate f h) = Int.ofNat common := by
    simpa only [common] using candidateContent hnz
  have hfContent : content f =
      content (rationalGcdCandidate f h) * content cofL := by
    have h := congrArg content hleft
    rw [content_mul] at h
    exact h.symm
  have hhContent : content h =
      content (rationalGcdCandidate f h) * content cofR := by
    have h := congrArg content hright
    rw [content_mul] at h
    exact h.symm
  have hfactor : common = common * Int.gcd (content cofL) (content cofR) := by
    calc
      common = Int.gcd (content f) (content h) := rfl
      _ = Int.gcd
          (content (rationalGcdCandidate f h) * content cofL)
          (content (rationalGcdCandidate f h) * content cofR) := by
        rw [hfContent, hhContent]
      _ = (content (rationalGcdCandidate f h)).natAbs *
          Int.gcd (content cofL) (content cofR) :=
        Int.gcd_mul_left _ _ _
      _ = common * Int.gcd (content cofL) (content cofR) := by
        rw [hgContent]
        simp
  apply Nat.eq_of_mul_eq_mul_left hcommonPos
  simpa using hfactor.symm

/-- The rational candidate and the rational gcd have the same polynomial
size; all intervening transformations are by nonzero scalars or signs. -/
private theorem candidateSize {f h : ZPoly} (hnz : f ≠ 0 ∨ h ≠ 0) :
    (toRatPoly (rationalGcdCandidate f h)).size =
      (DensePoly.gcd (toRatPoly f) (toRatPoly h)).size := by
  let rg := DensePoly.gcd (toRatPoly f) (toRatPoly h)
  let r := ratPolyPrimitivePart rg
  let c : Int := Int.ofNat (Int.gcd (content f) (content h))
  have hrgNe : rg ≠ 0 := by simpa only [rg] using ratGcdNe hnz
  have hcNe : c ≠ 0 := by
    change Int.ofNat (Int.gcd (content f) (content h)) ≠ 0
    exact Int.ofNat_ne_zero.mpr (commonContentNe hnz)
  rcases ratPolyPrimitivePart_rational_associate rg with ⟨u, hu⟩
  have huNe : u ≠ 0 := by
    intro hzero
    apply hrgNe
    rw [hu, hzero]
    exact DensePoly.scale_zero_left_semiring (toRatPoly r)
  calc
    (toRatPoly (rationalGcdCandidate f h)).size =
        (rationalGcdCandidate f h).size := size_toRatPoly _
    _ = (DensePoly.scale c r).size := by
      simpa only [rationalGcdCandidate, rg, r, c] using
        size_normalizePrimitiveSign (DensePoly.scale c r)
    _ = r.size := scale_size_of_ne_zero c r hcNe
    _ = (toRatPoly r).size := (size_toRatPoly r).symm
    _ = (DensePoly.scale u (toRatPoly r)).size :=
      (rat_size_scale huNe (toRatPoly r)).symm
    _ = rg.size := by rw [← hu]
    _ = (DensePoly.gcd (toRatPoly f) (toRatPoly h)).size := rfl

/-- Exact cofactors of the rational gcd are coprime over `Rat[x]`; equivalently,
their rational gcd has size at most one. -/
private theorem cofactorRatGcdSize {f h cofL cofR : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0)
    (hleft : rationalGcdCandidate f h * cofL = f)
    (hright : rationalGcdCandidate f h * cofR = h) :
    (DensePoly.gcd (toRatPoly cofL) (toRatPoly cofR)).size ≤ 1 := by
  let g := rationalGcdCandidate f h
  let gRat := toRatPoly g
  let d := DensePoly.gcd (toRatPoly cofL) (toRatPoly cofR)
  let rg := DensePoly.gcd (toRatPoly f) (toRatPoly h)
  have hgNe : gRat ≠ 0 := by
    dsimp only [gRat, g]
    exact toRatPoly_ne_zero_of_ne_zero _ (rationalGcdCandidate_ne_zero hnz)
  have hfRat : toRatPoly f = gRat * toRatPoly cofL := by
    dsimp only [gRat, g]
    rw [← toRatPoly_mul, hleft]
  have hhRat : toRatPoly h = gRat * toRatPoly cofR := by
    dsimp only [gRat, g]
    rw [← toRatPoly_mul, hright]
  have hdNe : d ≠ 0 := by
    intro hzero
    have hcofLZero : toRatPoly cofL = 0 := by
      rcases DensePoly.gcd_dvd_left (toRatPoly cofL) (toRatPoly cofR) with ⟨a, ha⟩
      dsimp only [d] at hzero
      rw [hzero, DensePoly.zero_mul] at ha
      exact ha
    have hcofRZero : toRatPoly cofR = 0 := by
      rcases DensePoly.gcd_dvd_right (toRatPoly cofL) (toRatPoly cofR) with ⟨a, ha⟩
      dsimp only [d] at hzero
      rw [hzero, DensePoly.zero_mul] at ha
      exact ha
    have hfZero : f = 0 := by
      have hfRatZero : toRatPoly f = 0 := by
        rw [hfRat, hcofLZero]
        exact (DensePoly.mul_comm_poly gRat 0).trans (DensePoly.zero_mul gRat)
      exact (DensePoly.size_eq_zero_iff f).mp (by
        rw [← size_toRatPoly f, hfRatZero]
        rfl)
    have hhZero : h = 0 := by
      have hhRatZero : toRatPoly h = 0 := by
        rw [hhRat, hcofRZero]
        exact (DensePoly.mul_comm_poly gRat 0).trans (DensePoly.zero_mul gRat)
      exact (DensePoly.size_eq_zero_iff h).mp (by
        rw [← size_toRatPoly h, hhRatZero]
        rfl)
    rcases hnz with hnz | hnz
    · exact hnz hfZero
    · exact hnz hhZero
  have hprodLeft : gRat * d ∣ toRatPoly f := by
    rcases DensePoly.gcd_dvd_left (toRatPoly cofL) (toRatPoly cofR) with ⟨a, ha⟩
    have ha' : toRatPoly cofL = d * a := by simpa only [d] using ha
    refine ⟨a, ?_⟩
    calc
      toRatPoly f = gRat * toRatPoly cofL := hfRat
      _ = gRat * (d * a) := by rw [ha']
      _ = (gRat * d) * a := (DensePoly.mul_assoc_poly gRat d a).symm
  have hprodRight : gRat * d ∣ toRatPoly h := by
    rcases DensePoly.gcd_dvd_right (toRatPoly cofL) (toRatPoly cofR) with ⟨a, ha⟩
    have ha' : toRatPoly cofR = d * a := by simpa only [d] using ha
    refine ⟨a, ?_⟩
    calc
      toRatPoly h = gRat * toRatPoly cofR := hhRat
      _ = gRat * (d * a) := by rw [ha']
      _ = (gRat * d) * a := (DensePoly.mul_assoc_poly gRat d a).symm
  have hprodDvd : gRat * d ∣ rg := by
    dsimp only [rg]
    exact DensePoly.dvd_gcd (gRat * d) (toRatPoly f) (toRatPoly h)
      hprodLeft hprodRight
  have hgPos : 0 < gRat.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hgNe ((DensePoly.size_eq_zero_iff gRat).mp hzero)
  have hdPos : 0 < d.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hdNe ((DensePoly.size_eq_zero_iff d).mp hzero)
  have hprodSize := rat_size_mul gRat d hgNe hdNe
  have hprodPos : 0 < (gRat * d).size := by omega
  have hrgNe : rg ≠ 0 := by simpa only [rg] using ratGcdNe hnz
  have hrgPos : 0 < rg.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrgNe ((DensePoly.size_eq_zero_iff rg).mp hzero)
  have hsizeLe := rat_size_le_of_dvd_nonzero
    (Nat.ne_of_gt hprodPos) (Nat.ne_of_gt hrgPos) hprodDvd
  have hsame : gRat.size = rg.size := by
    simpa only [gRat, g, rg] using candidateSize hnz
  have hsumLe : gRat.size + d.size - 1 ≤ rg.size := by
    rw [← hprodSize]
    exact hsizeLe
  rw [hsame] at hsumLe
  have hrearrange : rg.size + d.size - 1 = rg.size + (d.size - 1) := by omega
  rw [hrearrange] at hsumLe
  have hsubLe : d.size - 1 ≤ 0 := by
    apply Nat.le_of_add_le_add_left (a := rg.size)
    simpa using hsumLe
  dsimp only [d] at hdPos hsubLe ⊢
  omega

/-- The rational gcd candidate divides the left integer input. -/
private theorem candidateDvdLeft {f h : ZPoly} :
    rationalGcdCandidate f h ∣ f := by
  let rg := DensePoly.gcd (toRatPoly f) (toRatPoly h)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  have hleftBase :
      DensePoly.scale commonContent (ratPolyPrimitivePart rg) ∣ f := by
    apply scaledPrimitiveDvd (DensePoly.gcd_dvd_left (toRatPoly f) (toRatPoly h))
    exact Int.gcd_dvd_left (content f) (content h)
  simpa only [rationalGcdCandidate, rg, commonContent] using
    normalizeDvd hleftBase

/-- The rational gcd candidate divides the right integer input. -/
private theorem candidateDvdRight {f h : ZPoly} :
    rationalGcdCandidate f h ∣ h := by
  let rg := DensePoly.gcd (toRatPoly f) (toRatPoly h)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  have hrightBase :
      DensePoly.scale commonContent (ratPolyPrimitivePart rg) ∣ h := by
    apply scaledPrimitiveDvd (DensePoly.gcd_dvd_right (toRatPoly f) (toRatPoly h))
    exact Int.gcd_dvd_right (content f) (content h)
  simpa only [rationalGcdCandidate, rg, commonContent] using
    normalizeDvd hrightBase

/-- The rational gcd candidate exactly divides both integer inputs. -/
theorem rationalGcdCandidate_divisions {f h : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0) :
    (divExact? f (rationalGcdCandidate f h)).isSome = true ∧
      (divExact? h (rationalGcdCandidate f h)).isSome = true := by
  have hcandidateNe := rationalGcdCandidate_ne_zero hnz
  exact ⟨divExact?_isSome_of_dvd hcandidateNe candidateDvdLeft,
    divExact?_isSome_of_dvd hcandidateNe candidateDvdRight⟩

/-- Least common denominator of the stored coefficients of a rational
polynomial. -/
private def ratDen (f : DensePoly Rat) : Nat :=
  f.toArray.foldl (fun d q => Nat.lcm d q.den) 1

/-- Clear a rational polynomial with a denominator known to be a common
multiple of all coefficient denominators. -/
private def clearRat (den : Nat) (f : DensePoly Rat) : ZPoly :=
  DensePoly.ofList <|
    (List.range f.size).map fun i =>
      let q := f.coeff i
      q.num * Int.ofNat (den / q.den)

/-- Divisibility by the initial accumulator is preserved by an lcm fold. -/
private theorem dvdFoldLcm (coeffs : List Rat) {d acc : Nat} (hacc : d ∣ acc) :
    d ∣ coeffs.foldl (fun n q => Nat.lcm n q.den) acc := by
  induction coeffs generalizing acc with
  | nil => exact hacc
  | cons q coeffs ih =>
      simp only [List.foldl_cons]
      exact ih (Nat.dvd_trans hacc (Nat.dvd_lcm_left acc q.den))

/-- Every member denominator divides the result of the lcm fold. -/
private theorem denDvdFoldLcm (coeffs : List Rat) {q : Rat} {acc : Nat}
    (hq : q ∈ coeffs) :
    q.den ∣ coeffs.foldl (fun n q => Nat.lcm n q.den) acc := by
  induction coeffs generalizing acc with
  | nil => cases hq
  | cons head coeffs ih =>
      simp only [List.foldl_cons, List.mem_cons] at hq ⊢
      rcases hq with hhead | htail
      · subst head
        exact dvdFoldLcm coeffs (Nat.dvd_lcm_right acc q.den)
      · exact ih htail

/-- Every coefficient denominator divides `ratDen`. -/
private theorem coeffDenDvdRatDen (f : DensePoly Rat) (i : Nat) :
    (f.coeff i).den ∣ ratDen f := by
  by_cases hi : i < f.size
  · unfold ratDen
    rw [← Array.foldl_toList]
    apply denDvdFoldLcm
    unfold DensePoly.coeff DensePoly.toArray Array.getD
    simp [show i < f.coeffs.size by simpa [DensePoly.size] using hi]
  · have hcoeff : f.coeff i = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    rw [hcoeff]
    exact Nat.one_dvd _

/-- The lcm denominator fold is positive. -/
private theorem ratDenPos (f : DensePoly Rat) : 0 < ratDen f := by
  unfold ratDen
  rw [← Array.foldl_toList]
  have go : ∀ (coeffs : List Rat) (acc : Nat), 0 < acc →
      0 < coeffs.foldl (fun d q => Nat.lcm d q.den) acc := by
    intro coeffs
    induction coeffs with
    | nil => intro acc hpos; exact hpos
    | cons q coeffs ih =>
        intro acc hpos
        simp only [List.foldl_cons]
        exact ih (Nat.lcm acc q.den) (Nat.lcm_pos hpos q.den_pos)
  exact go f.toArray.toList 1 (by decide)

/-- Clearing one rational coefficient against a multiple of its denominator
recovers scalar multiplication after casting back to `Rat`. -/
private theorem clearCoeffCast (den : Nat) (q : Rat) (hden : q.den ∣ den) :
    (((q.num * Int.ofNat (den / q.den) : Int) : Rat)) = (den : Rat) * q := by
  rcases hden with ⟨k, rfl⟩
  rw [Nat.mul_div_right _ q.den_pos]
  have hdenNe : ((q.den : Nat) : Rat) ≠ 0 := by simp [q.den_nz]
  have hq : ((q.num : Rat) / (q.den : Rat)) = q := by
    simpa [Rat.divInt_eq_div, Rat.intCast_natCast] using q.num_divInt_den
  calc
    ((q.num * Int.ofNat k : Int) : Rat) =
        (q.num : Rat) * (k : Rat) := by
      rw [Rat.intCast_mul, Int.ofNat_eq_natCast, Rat.intCast_natCast]
    _ = ((q.num : Rat) * (k : Rat) * (q.den : Rat)) / (q.den : Rat) := by
      exact (Rat.mul_div_cancel hdenNe).symm
    _ = ((q.den * k : Nat) : Rat) * ((q.num : Rat) / (q.den : Rat)) := by
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    _ = ((q.den * k : Nat) : Rat) * q := by rw [hq]

/-- Clearing all coefficients against a common denominator is scalar
multiplication after rationalization. -/
private theorem toRatPoly_clearRat (den : Nat) (f : DensePoly Rat)
    (hden : ∀ i, (f.coeff i).den ∣ den) :
    toRatPoly (clearRat den f) = DensePoly.scale (den : Rat) f := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_toRatPoly]
  unfold clearRat
  rw [DensePoly.coeff_ofList]
  by_cases hi : i < f.size
  · have hget :
        ((List.range f.size).map fun j =>
            (f.coeff j).num * Int.ofNat (den / (f.coeff j).den)).getD i 0 =
          (f.coeff i).num * Int.ofNat (den / (f.coeff i).den) := by
      simp [hi]
    change (((((List.range f.size).map fun j =>
        (f.coeff j).num * Int.ofNat (den / (f.coeff j).den)).getD i 0 : Int) : Rat)) =
      (DensePoly.scale (den : Rat) f).coeff i
    rw [hget, DensePoly.coeff_scale_semiring]
    exact clearCoeffCast den (f.coeff i) (hden i)
  · have hcoeff : f.coeff i = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    have hget :
        ((List.range f.size).map fun j =>
            (f.coeff j).num * Int.ofNat (den / (f.coeff j).den)).getD i 0 = 0 := by
      simp [hi]
    change (((((List.range f.size).map fun j =>
        (f.coeff j).num * Int.ofNat (den / (f.coeff j).den)).getD i 0 : Int) : Rat)) =
      (DensePoly.scale (den : Rat) f).coeff i
    rw [hget, DensePoly.coeff_scale_semiring, hcoeff]
    exact (Rat.mul_zero (den : Rat)).symm

/-- Clear the extended rational gcd identity into an integral combination.
For coprime cofactors the rational gcd is a nonzero constant, so the returned
`k` is nonzero and the checker verifies the identity directly. -/
def rationalCoprimeWitness (f h : ZPoly) : CoprimeWitness :=
  let xg := DensePoly.xgcd (toRatPoly f) (toRatPoly h)
  let scalar := xg.gcd.coeff 0
  let den := Nat.lcm (ratDen xg.left) (Nat.lcm (ratDen xg.right) scalar.den)
  let u := clearRat den xg.left
  let v := clearRat den xg.right
  let k := scalar.num * Int.ofNat (den / scalar.den)
  .constant u v k

set_option maxHeartbeats 1600000 in
/-- Clearing the extended-gcd identity for rationally coprime integer
polynomials produces a certificate accepted by the integer checker. -/
private theorem rationalCoprimeWitness_checks {f h : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0)
    (hsize : (DensePoly.gcd (toRatPoly f) (toRatPoly h)).size ≤ 1) :
    checkCoprime f h (rationalCoprimeWitness f h) = true := by
  let xg := DensePoly.xgcd (toRatPoly f) (toRatPoly h)
  let scalar := xg.gcd.coeff 0
  let den := Nat.lcm (ratDen xg.left)
    (Nat.lcm (ratDen xg.right) scalar.den)
  let u := clearRat den xg.left
  let v := clearRat den xg.right
  let k := scalar.num * Int.ofNat (den / scalar.den)
  have hxgSize : xg.gcd.size ≤ 1 := by
    rw [DensePoly.xgcd_gcd_eq_gcd]
    exact hsize
  have hxgNe : xg.gcd ≠ 0 := by
    rw [DensePoly.xgcd_gcd_eq_gcd]
    exact ratGcdNe hnz
  have hxgC : xg.gcd = DensePoly.C scalar := by
    simpa only [scalar] using eqCOfSizeLe hxgSize
  have hscalarNe : scalar ≠ 0 := by
    intro hzero
    apply hxgNe
    rw [hxgC, hzero]
    rfl
  have hleftDen : ∀ i, (xg.left.coeff i).den ∣ den := by
    intro i
    exact Nat.dvd_trans (coeffDenDvdRatDen xg.left i)
      (Nat.dvd_lcm_left _ _)
  have hrightDen : ∀ i, (xg.right.coeff i).den ∣ den := by
    intro i
    exact Nat.dvd_trans (coeffDenDvdRatDen xg.right i)
      (Nat.dvd_trans (Nat.dvd_lcm_left _ _)
        (Nat.dvd_lcm_right _ _))
  have hscalarDen : scalar.den ∣ den :=
    Nat.dvd_trans (Nat.dvd_lcm_right _ _)
      (Nat.dvd_lcm_right _ _)
  have hdenPos : 0 < den := by
    exact Nat.lcm_pos (ratDenPos xg.left)
      (Nat.lcm_pos (ratDenPos xg.right) scalar.den_pos)
  have huRat : toRatPoly u = DensePoly.scale (den : Rat) xg.left := by
    simpa only [u] using toRatPoly_clearRat den xg.left hleftDen
  have hvRat : toRatPoly v = DensePoly.scale (den : Rat) xg.right := by
    simpa only [v] using toRatPoly_clearRat den xg.right hrightDen
  have hkRat : ((k : Int) : Rat) = (den : Rat) * scalar := by
    simpa only [k] using clearCoeffCast den scalar hscalarDen
  have hkNe : k ≠ 0 := by
    intro hzero
    have hcastZero : ((k : Int) : Rat) = 0 := by rw [hzero]; rfl
    rw [hkRat] at hcastZero
    rcases Rat.mul_eq_zero.mp hcastZero with hdenZero | hscalarZero
    · have : den = 0 := by exact_mod_cast hdenZero
      omega
    · exact hscalarNe hscalarZero
  have hbezRat :
      xg.left * toRatPoly f + xg.right * toRatPoly h = xg.gcd := by
    simpa only [xg] using DensePoly.xgcd_bezout (toRatPoly f) (toRatPoly h)
  have hscaleC :
      DensePoly.scale (den : Rat) (DensePoly.C scalar) =
        DensePoly.C ((k : Int) : Rat) := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_C,
      DensePoly.coeff_C]
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact hkRat.symm
    · simp only [hn, ↓reduceIte]
      exact Rat.mul_zero (den : Rat)
  have hbezInt : u * f + v * h = DensePoly.C k := by
    apply toRatInjective
    rw [toRatAdd, toRatPoly_mul, toRatPoly_mul, huRat, hvRat]
    calc
      DensePoly.scale (den : Rat) xg.left * toRatPoly f +
            DensePoly.scale (den : Rat) xg.right * toRatPoly h =
          DensePoly.scale (den : Rat) (xg.left * toRatPoly f) +
            DensePoly.scale (den : Rat) (xg.right * toRatPoly h) := by
        rw [DensePoly.scale_mul, DensePoly.scale_mul]
      _ = DensePoly.scale (den : Rat)
            (xg.left * toRatPoly f + xg.right * toRatPoly h) :=
        (DensePoly.scale_add _ _ _).symm
      _ = DensePoly.scale (den : Rat) xg.gcd := by rw [hbezRat]
      _ = DensePoly.scale (den : Rat) (DensePoly.C scalar) := by rw [hxgC]
      _ = DensePoly.C ((k : Int) : Rat) := hscaleC
      _ = toRatPoly (DensePoly.C k) := (toRatPoly_C k).symm
  rw [show rationalCoprimeWitness f h = .constant u v k by rfl]
  unfold checkCoprime
  rw [Bool.and_eq_true]
  exact ⟨by simpa only [decide_eq_true_eq], by simpa only [beq_iff_eq]⟩

/-- The canonical certificate for the doubly-zero input.  Unit cofactors keep
the coprimality obligation meaningful even though the gcd itself is zero. -/
def zeroGcdCert : GcdCert :=
  { gcd := 0
    cofL := 1
    cofR := 1
    coprime := .constant 1 0 1 }

/-- Accept a structural certificate only through the public checker. -/
private def acceptStructural? (f h : ZPoly) (cert : GcdCert) : Option GcdCert :=
  if checkGcd f h cert then some cert else none

/-- Structural certificate when the left input is zero and the right input is
nonzero.  Normalizing the right input changes it only by a unit, and exact
division recovers that unit as the right cofactor. -/
private def zeroLeftCert? (h : ZPoly) : Option GcdCert := do
  let g := normalizePrimitiveSign h
  let cofR ← divExact? h g
  acceptStructural? 0 h
    { gcd := g
      cofL := 0
      cofR
      coprime := .constant 0 1 (cofR.coeff 0) }

/-- Structural certificate when the right input is zero and the left input is
nonzero. -/
private def zeroRightCert? (f : ZPoly) : Option GcdCert := do
  let g := normalizePrimitiveSign f
  let cofL ← divExact? f g
  acceptStructural? f 0
    { gcd := g
      cofL
      cofR := 0
      coprime := .constant 1 0 (cofL.coeff 0) }

/-- Structural certificate when the left input is a nonzero constant.  The
canonical gcd is the positive gcd of that constant and the content of the
right input. -/
private def constantLeftCert? (f h : ZPoly) : Option GcdCert := do
  let d : Int := Int.ofNat (Int.gcd (f.coeff 0) (content h))
  let g : ZPoly := DensePoly.C d
  let cofL ← divExact? f g
  let cofR ← divExact? h g
  acceptStructural? f h
    { gcd := g
      cofL
      cofR
      coprime := .constant 1 0 (cofL.coeff 0) }

/-- Structural certificate when the right input is a nonzero constant. -/
private def constantRightCert? (f h : ZPoly) : Option GcdCert := do
  let d : Int := Int.ofNat (Int.gcd (content f) (h.coeff 0))
  let g : ZPoly := DensePoly.C d
  let cofL ← divExact? f g
  let cofR ← divExact? h g
  acceptStructural? f h
    { gcd := g
      cofL
      cofR
      coprime := .constant 0 1 (cofR.coeff 0) }

/-- Mandatory route 0 certificates for zero and nonzero-constant inputs.
Every returned certificate has already passed `checkGcd`; `none` means that
the pair is genuinely nonstructural or a checked arithmetic invariant
regressed. -/
private def structuralGcdCert? (f h : ZPoly) : Option GcdCert :=
  if f.isZero then
    if h.isZero then acceptStructural? f h zeroGcdCert else zeroLeftCert? h
  else if h.isZero then
    zeroRightCert? f
  else if f.size = 1 then
    constantLeftCert? f h
  else if h.size = 1 then
    constantRightCert? f h
  else
    none

/-- The structural acceptance gate exposes only certificates that passed the
checker. -/
private theorem acceptStructural?_checks {f h : ZPoly} {offered cert : GcdCert}
    (hcert : acceptStructural? f h offered = some cert) :
    checkGcd f h cert = true := by
  unfold acceptStructural? at hcert
  split at hcert
  · rename_i hcheck
    cases hcert
    exact hcheck
  · contradiction

private theorem zeroLeftCert?_checks {h : ZPoly} {cert : GcdCert}
    (hcert : zeroLeftCert? h = some cert) :
    checkGcd 0 h cert = true := by
  unfold zeroLeftCert? at hcert
  dsimp only at hcert
  generalize hdiv : divExact? h (normalizePrimitiveSign h) = quotient? at hcert
  cases quotient? with
  | none => simp at hcert
  | some quotient =>
      exact acceptStructural?_checks hcert

private theorem zeroRightCert?_checks {f : ZPoly} {cert : GcdCert}
    (hcert : zeroRightCert? f = some cert) :
    checkGcd f 0 cert = true := by
  unfold zeroRightCert? at hcert
  dsimp only at hcert
  generalize hdiv : divExact? f (normalizePrimitiveSign f) = quotient? at hcert
  cases quotient? with
  | none => simp at hcert
  | some quotient =>
      exact acceptStructural?_checks hcert

private theorem constantLeftCert?_checks {f h : ZPoly} {cert : GcdCert}
    (hcert : constantLeftCert? f h = some cert) :
    checkGcd f h cert = true := by
  unfold constantLeftCert? at hcert
  dsimp only at hcert
  generalize hleft : divExact? f
      (DensePoly.C (Int.ofNat (Int.gcd (f.coeff 0) (content h)))) = left? at hcert
  cases left? with
  | none => simp at hcert
  | some left =>
      generalize hright : divExact? h
          (DensePoly.C (Int.ofNat (Int.gcd (f.coeff 0) (content h)))) =
        right? at hcert
      cases right? with
      | none => simp at hcert
      | some right => exact acceptStructural?_checks hcert

private theorem constantRightCert?_checks {f h : ZPoly} {cert : GcdCert}
    (hcert : constantRightCert? f h = some cert) :
    checkGcd f h cert = true := by
  unfold constantRightCert? at hcert
  dsimp only at hcert
  generalize hleft : divExact? f
      (DensePoly.C (Int.ofNat (Int.gcd (content f) (h.coeff 0)))) = left? at hcert
  cases left? with
  | none => simp at hcert
  | some left =>
      generalize hright : divExact? h
          (DensePoly.C (Int.ofNat (Int.gcd (content f) (h.coeff 0)))) =
        right? at hcert
      cases right? with
      | none => simp at hcert
      | some right => exact acceptStructural?_checks hcert

/-- Every certificate returned by the mandatory zero/constant prepass passed
the checker. -/
private theorem structuralGcdCert?_checks {f h : ZPoly} {cert : GcdCert}
    (hcert : structuralGcdCert? f h = some cert) :
    checkGcd f h cert = true := by
  unfold structuralGcdCert? at hcert
  split at hcert
  · rename_i hfzero
    have hf : f = 0 :=
      (DensePoly.size_eq_zero_iff f).mp
        ((DensePoly.isZero_eq_true_iff f).mp hfzero)
    subst f
    split at hcert
    · rename_i hhzero
      have hh : h = 0 :=
        (DensePoly.size_eq_zero_iff h).mp
          ((DensePoly.isZero_eq_true_iff h).mp hhzero)
      subst h
      exact acceptStructural?_checks hcert
    · exact zeroLeftCert?_checks hcert
  · split at hcert
    · rename_i hhzero
      have hh : h = 0 :=
        (DensePoly.size_eq_zero_iff h).mp
          ((DensePoly.isZero_eq_true_iff h).mp hhzero)
      subst h
      exact zeroRightCert?_checks hcert
    · split at hcert
      · exact constantLeftCert?_checks hcert
      · split at hcert
        · exact constantRightCert?_checks hcert
        · contradiction

/-- Long division by a nonzero divisor returns the exact cofactor whenever
the divisor is known to divide the input. -/
private theorem divModProduct {f g : ZPoly} (hg : g ≠ 0) (hdvd : g ∣ f) :
    g * (DensePoly.divMod f g).1 = f := by
  rcases hdvd with ⟨q, hq⟩
  have hqmul : q * g = f := by
    rw [DensePoly.mul_comm_poly q g]
    exact hq.symm
  have hdiv := divMod_eq_mul_of_ne_zero f g q hg hqmul
  have hquot : (DensePoly.divMod f g).1 = q := by
    rw [hdiv]
  rw [hquot]
  exact hq.symm

/-- Long division by the nonzero rational candidate reconstructs the left
input exactly. -/
theorem rationalGcdCandidate_mul_quotient {f h : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0) :
    rationalGcdCandidate f h *
        (DensePoly.divMod f (rationalGcdCandidate f h)).1 = f :=
  divModProduct (rationalGcdCandidate_ne_zero hnz) candidateDvdLeft

/-- Deterministic rational fallback certificate.

The cofactors are the concrete long-division quotients.  Their exactness is
part of `rationalGcdCert_checks`, but no proof is used to extract runtime
data: if the rational-gcd or division implementation regresses, `checkGcd`
reports the concrete certificate as invalid rather than extracting data from
an impossible branch. -/
def rationalGcdCert (f h : ZPoly) : GcdCert :=
  if f = 0 ∧ h = 0 then
    zeroGcdCert
  else
    let g := rationalGcdCandidate f h
    let cofL := (DensePoly.divMod f g).1
    let cofR := (DensePoly.divMod h g).1
    { gcd := g
      cofL
      cofR
      coprime := rationalCoprimeWitness cofL cofR }

/-- Correctness of the deterministic rational fallback, concentrated in one
proof obligation while the executable certificate remains fully concrete. -/
theorem rationalGcdCert_checks (f h : ZPoly) :
    checkGcd f h (rationalGcdCert f h) = true := by
  by_cases hzero : f = 0 ∧ h = 0
  · rcases hzero with ⟨rfl, rfl⟩
    decide
  · have hnz : f ≠ 0 ∨ h ≠ 0 := by
      by_cases hf : f = 0
      · exact Or.inr (fun hh => hzero ⟨hf, hh⟩)
      · exact Or.inl hf
    let g := rationalGcdCandidate f h
    let cofL := (DensePoly.divMod f g).1
    let cofR := (DensePoly.divMod h g).1
    have hgNe : g ≠ 0 := by
      simpa only [g] using rationalGcdCandidate_ne_zero hnz
    have hleft : g * cofL = f := by
      simpa only [g, cofL] using divModProduct hgNe candidateDvdLeft
    have hright : g * cofR = h := by
      simpa only [g, cofR] using divModProduct hgNe candidateDvdRight
    have hcofNz : cofL ≠ 0 ∨ cofR ≠ 0 := by
      rcases hnz with hf | hh
      · left
        intro hcof
        apply hf
        have hmulZero : g * (0 : ZPoly) = 0 :=
          (DensePoly.mul_comm_poly g 0).trans (DensePoly.zero_mul g)
        exact hleft.symm.trans (by simpa only [hcof] using hmulZero)
      · right
        intro hcof
        apply hh
        have hmulZero : g * (0 : ZPoly) = 0 :=
          (DensePoly.mul_comm_poly g 0).trans (DensePoly.zero_mul g)
        exact hright.symm.trans (by simpa only [hcof] using hmulZero)
    have hcontents : Int.gcd (content cofL) (content cofR) = 1 := by
      simpa only [g] using cofactorContents hnz hleft hright
    have hcopSize :
        (DensePoly.gcd (toRatPoly cofL) (toRatPoly cofR)).size ≤ 1 := by
      simpa only [g] using cofactorRatGcdSize hnz hleft hright
    have hcop :
        checkCoprime cofL cofR (rationalCoprimeWitness cofL cofR) = true :=
      rationalCoprimeWitness_checks hcofNz hcopSize
    rw [rationalGcdCert, ite_eq_right hzero]
    change checkGcd f h
      { gcd := g, cofL := cofL, cofR := cofR,
        coprime := rationalCoprimeWitness cofL cofR } = true
    unfold checkGcd
    rw [mulEqPacked_complete hleft, mulEqPacked_complete hright]
    have hnorm : NormalizedGcd g = true := by
      simpa only [g] using candidateNormalized hnz
    rw [hnorm]
    simp [hcontents, hcop]

/-- The nondegenerate rational fallback stores the canonical rational gcd
candidate in its gcd field. -/
theorem rationalGcdCert_gcd {f h : ZPoly} (hnz : f ≠ 0 ∨ h ≠ 0) :
    (rationalGcdCert f h).gcd = rationalGcdCandidate f h := by
  unfold rationalGcdCert
  rw [ite_eq_right (by
    intro hzero
    rcases hnz with hf | hh
    · exact hf hzero.1
    · exact hh hzero.2)]

/-- Scan the low coefficients for the exponent of the first nonzero term. -/
private def xOrder.go (f : ZPoly) : Nat → Nat → Nat
  | index, 0 => index
  | index, fuel + 1 =>
      if f.coeff index == 0 then xOrder.go f (index + 1) fuel else index

/-- Largest exponent `k` such that `x^k` divides `f`; zero has order zero for
the structural route, which handles it separately. -/
def xOrder (f : ZPoly) : Nat :=
  if f.isZero then 0 else xOrder.go f 0 f.size

/-- The monic power `x^k`. -/
def xPower (k : Nat) : ZPoly :=
  DensePoly.ofList (List.replicate k 0 ++ [1])

/-- Common scalar and `x`-power removed before every primitive route. -/
structure StructuralReduction where
  factor : ZPoly
  left : ZPoly
  right : ZPoly

/-- Prefer the deterministic extended-subresultant certificate, with the
rational implementation as the classified fallback if no actual terminal
row exists. -/
private def fallbackGcdCert (f h : ZPoly) : GcdCert :=
  match prsCert? f h with
  | some cert => cert
  | none => rationalGcdCert f h

/-- The deterministic PRS route and its rational contingency both return
accepted certificates. -/
private theorem fallbackGcdCert_checks (f h : ZPoly) :
    checkGcd f h (fallbackGcdCert f h) = true := by
  unfold fallbackGcdCert
  generalize hprs : prsCert? f h = cert?
  cases cert? with
  | some cert => exact prsCert_checks hprs
  | none => exact rationalGcdCert_checks f h

/-- Route 0: extract the common integer content and common power of `x`.
Both divisions are explicit checked operations, so a representation or
division regression declines instead of inventing a reduced input. -/
def structuralReduction? (f h : ZPoly) : Option StructuralReduction := do
  if f.isZero || h.isZero then none else pure ()
  let commonPower := min (xOrder f) (xOrder h)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  let factor := DensePoly.scale commonContent (xPower commonPower)
  let left ← divExact? f factor
  let right ← divExact? h factor
  pure { factor, left, right }

/-- A successful structural reduction records exact products for both
inputs. -/
private theorem structuralReduction?_products {f h : ZPoly}
    {reduced : StructuralReduction}
    (hresult : structuralReduction? f h = some reduced) :
    reduced.factor * reduced.left = f ∧
      reduced.factor * reduced.right = h := by
  unfold structuralReduction? at hresult
  dsimp only at hresult
  by_cases hzero : f.isZero || h.isZero
  · rw [ite_eq_left hzero] at hresult
    contradiction
  · rw [ite_eq_right hzero] at hresult
    let commonPower := min (xOrder f) (xOrder h)
    let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
    let factor := DensePoly.scale commonContent (xPower commonPower)
    generalize hleft : divExact? f factor = left? at hresult
    cases left? with
    | none => simp at hresult
    | some left =>
        generalize hright : divExact? h factor = right? at hresult
        cases right? with
        | none => simp at hresult
        | some right =>
            cases hresult
            have hleftProduct := divExact?_product hleft
            have hrightProduct := divExact?_product hright
            exact ⟨(DensePoly.mul_comm_poly factor left).trans hleftProduct,
              (DensePoly.mul_comm_poly factor right).trans hrightProduct⟩

/-- Restore route 0's common factor around a certificate for the reduced
pair.  The public checker is the only acceptance gate. -/
def restoreStructural? (f h : ZPoly) (reduced : StructuralReduction)
    (cert : GcdCert) : Option GcdCert :=
  let restored : GcdCert :=
    { gcd := normalizePrimitiveSign (reduced.factor * cert.gcd)
      cofL := cert.cofL
      cofR := cert.cofR
      coprime := cert.coprime }
  if checkGcd f h restored then some restored else none

/-- Structural restoration exposes only the checker-approved result. -/
private theorem restoreStructural?_checks {f h : ZPoly}
    {reduced : StructuralReduction} {cert restored : GcdCert}
    (hresult : restoreStructural? f h reduced cert = some restored) :
    checkGcd f h restored = true := by
  unfold restoreStructural? at hresult
  dsimp only at hresult
  split at hresult
  · rename_i hcheck
    cases hresult
    exact hcheck
  · contradiction

/-- Largest reduced input size at which the evaluation heuristic runs before
Brown reconstruction. Above this point dense evaluation builds integers whose
bit width grows with the whole polynomial, while Brown can offer and check an
image candidate directly. -/
private def heuSizeLimit : Nat :=
  32

/-- Above this coefficient height, a full coprime image gcd on the unreduced
ambient degree costs more than reconstructing the smaller common factor. -/
private def brownBitCutoff : Nat :=
  16

private def brownOrFallback (f h : ZPoly) : GcdCert :=
  match brownCert? f h with
  | some cert => cert
  | none => fallbackGcdCert f h

private theorem brownOrFallback_checks (f h : ZPoly) :
    checkGcd f h (brownOrFallback f h) = true := by
  unfold brownOrFallback
  generalize hbrown : brownCert? f h = cert?
  cases cert? with
  | some cert => exact brownCert?_checks hbrown
  | none => exact fallbackGcdCert_checks f h

private def afterCoprime (f h : ZPoly) : GcdCert :=
  if max f.size h.size <= heuSizeLimit then
    match heuCert? f h with
    | some cert => cert
    | none => brownOrFallback f h
  else
    brownOrFallback f h

private theorem afterCoprime_checks (f h : ZPoly) :
    checkGcd f h (afterCoprime f h) = true := by
  unfold afterCoprime
  by_cases hsmall : max f.size h.size ≤ heuSizeLimit
  · rw [ite_eq_left hsmall]
    generalize hheu : heuCert? f h = cert?
    cases cert? with
    | some cert => exact heuCert?_checks hheu
    | none => exact brownOrFallback_checks f h
  · rw [ite_eq_right hsmall]
    exact brownOrFallback_checks f h

/-- Routes 1--4 on inputs after structural content and `x`-power removal. -/
def reducedGcdCert (f h : ZPoly) : GcdCert :=
  let coefficientBits := max (maxAbs f).log2 (maxAbs h).log2
  match differenceCert? f h with
  | some cert => cert
  | none =>
      if brownBitCutoff < coefficientBits then
        brownOrFallback f h
      else
        match coprimeCert? f h with
        | some cert => cert
        | none => afterCoprime f h

/-- Every nonstructural route either returns a checked fast certificate or
the checked deterministic fallback. -/
private theorem reducedGcdCert_checks (f h : ZPoly) :
    checkGcd f h (reducedGcdCert f h) = true := by
  unfold reducedGcdCert
  dsimp only
  generalize hdiff : differenceCert? f h = difference?
  cases difference? with
  | some cert => exact differenceCert?_checks hdiff
  | none =>
      by_cases hbits : brownBitCutoff < max (maxAbs f).log2 (maxAbs h).log2
      · rw [ite_eq_left hbits]
        exact brownOrFallback_checks f h
      · rw [ite_eq_right hbits]
        generalize hcop : coprimeCert? f h = coprime?
        cases coprime? with
        | some cert => exact coprimeCert?_checks hcop
        | none => exact afterCoprime_checks f h

/-- Internal route tag used by executable dispatch guards. -/
private inductive GcdRoute where
  | structural
  | reduced
  | fallback
deriving BEq

/-- Dispatch together with the selected route.  Keeping this private avoids
expanding the public API while allowing regression guards to assert that
mandatory structural inputs never enter the generic producers. -/
private def dispatchGcdCert (f h : ZPoly) : GcdCert × GcdRoute :=
  match structuralGcdCert? f h with
  | some cert => (cert, .structural)
  | none =>
      match structuralReduction? f h with
      | none => (fallbackGcdCert f h, .fallback)
      | some reduced =>
          let cert := reducedGcdCert reduced.left reduced.right
          if reduced.factor == 1 then
            -- Primitive inputs with no common `x` power are already the
            -- reduced problem. Replaying the complete certificate again in
            -- `restoreStructural?` would duplicate both dense product checks.
            (cert, .reduced)
          else
            match restoreStructural? f h reduced cert with
            | some restored => (restored, .reduced)
            | none => (fallbackGcdCert f h, .fallback)

/-- Produce a checked gcd certificate.  Mandatory zero and constant
certificates run before content or `x` extraction.  Remaining route-0
reduction runs next; rejected fast candidates and failed restoration fall
through to total, data-only extended-subresultant route 4. -/
def gcdCert (f h : ZPoly) : GcdCert :=
  (dispatchGcdCert f h).1

/-- Every public certificate has passed the checker. -/
theorem gcdCert_checks (f h : ZPoly) :
    checkGcd f h (gcdCert f h) = true := by
  unfold gcdCert dispatchGcdCert
  generalize hstruct : structuralGcdCert? f h = structural?
  cases structural? with
  | some cert =>
      exact structuralGcdCert?_checks hstruct
  | none =>
      simp only
      generalize hreduction : structuralReduction? f h = reduction?
      cases reduction? with
      | none =>
          exact fallbackGcdCert_checks f h
      | some reduced =>
          simp only
          let cert := reducedGcdCert reduced.left reduced.right
          by_cases hfactor : reduced.factor == 1
          · rw [ite_eq_left hfactor]
            have hfactorEq : reduced.factor = 1 := by
              simpa only [beq_iff_eq] using hfactor
            have hproducts := structuralReduction?_products hreduction
            have hleft : reduced.left = f := by
              rw [hfactorEq] at hproducts
              rw [DensePoly.mul_comm_poly (1 : ZPoly) reduced.left,
                DensePoly.mul_one_right_poly] at hproducts
              exact hproducts.1
            have hright : reduced.right = h := by
              rw [hfactorEq] at hproducts
              rw [DensePoly.mul_comm_poly (1 : ZPoly) reduced.right,
                DensePoly.mul_one_right_poly] at hproducts
              exact hproducts.2
            simpa only [cert, hleft, hright] using
              reducedGcdCert_checks reduced.left reduced.right
          · rw [ite_eq_right hfactor]
            generalize hrestore : restoreStructural? f h reduced cert = restored?
            cases restored? with
            | some restored =>
                exact restoreStructural?_checks hrestore
            | none =>
                exact fallbackGcdCert_checks f h

/-- Canonically normalized gcd of two integer polynomials.  Exposure is
limited to the projection equation `gcd_eq_cert`; `gcdCert` and its route
search remain opaque to kernel replay. -/
@[expose]
def gcd (f h : ZPoly) : ZPoly :=
  (gcdCert f h).gcd

/-- Controlled unfolding lemma for the otherwise opaque producer-facing gcd
definition. -/
theorem gcd_eq_cert (f h : ZPoly) :
    gcd f h = (gcdCert f h).gcd := rfl

/-- Exact cofactors belonging to the checked gcd. -/
def cofactors (f h : ZPoly) : ZPoly × ZPoly :=
  let cert := gcdCert f h
  (cert.cofL, cert.cofR)

/-- Decide coprimality using the canonical gcd. -/
def isCoprime (f h : ZPoly) : Bool :=
  gcd f h == 1

/-- Fold gcd over a list; the empty-list convention is zero. -/
def gcdList (fs : List ZPoly) : ZPoly :=
  fs.foldl gcd 0

/-- Canonically normalized least common multiple. -/
def lcm (f h : ZPoly) : ZPoly :=
  if f.isZero || h.isZero then
    0
  else
    let cert := gcdCert f h
    normalizePrimitiveSign (cert.gcd * cert.cofL * cert.cofR)

/-- Monic rational-polynomial gcd. -/
def ratGcd (f h : DensePoly Rat) : DensePoly Rat :=
  let fInt := clearRat (ratDen f) f
  let hInt := clearRat (ratDen h) h
  let g := toRatPoly (gcd fInt hInt)
  if g.isZero then 0 else DensePoly.scale g.leadingCoeff⁻¹ g

/-! Small executable pins for the degenerate contracts and content handling. -/

-- Mandatory structural inputs are tagged before generic dispatch.  These
-- guards also inspect the concrete constant witnesses rather than checking
-- only the resulting gcd.

#guard
  match dispatchGcdCert (0 : ZPoly) 0 with
  | (cert, .structural) =>
      cert.gcd == 0 && cert.cofL == 1 && cert.cofR == 1 &&
        match cert.coprime with
        | .constant u v k =>
            u == 1 && v == 0 && k == 1 && checkGcd 0 0 cert
        | .modular .. => false
  | _ => false

#guard
  let h : ZPoly := DensePoly.ofList [6, -3]
  match dispatchGcdCert 0 h with
  | (cert, .structural) =>
      cert.gcd == DensePoly.ofList [-6, 3] && cert.cofL == 0 &&
        cert.cofR == DensePoly.C (-1) &&
          match cert.coprime with
          | .constant u v k =>
              u == 0 && v == 1 && k == -1 && checkGcd 0 h cert
          | .modular .. => false
  | _ => false

#guard
  let f : ZPoly := DensePoly.ofList [6, -3]
  match dispatchGcdCert f 0 with
  | (cert, .structural) =>
      cert.gcd == DensePoly.ofList [-6, 3] &&
        cert.cofL == DensePoly.C (-1) && cert.cofR == 0 &&
          match cert.coprime with
          | .constant u v k =>
              u == 1 && v == 0 && k == -1 && checkGcd f 0 cert
          | .modular .. => false
  | _ => false

#guard
  let f : ZPoly := DensePoly.C (-12)
  let h : ZPoly := DensePoly.ofList [0, 18]
  match dispatchGcdCert f h with
  | (cert, .structural) =>
      cert.gcd == DensePoly.C 6 && cert.cofL == DensePoly.C (-2) &&
        cert.cofR == DensePoly.ofList [0, 3] &&
          match cert.coprime with
          | .constant u v k =>
              u == 1 && v == 0 && k == -2 && checkGcd f h cert
          | .modular .. => false
  | _ => false

#guard
  let f : ZPoly := DensePoly.ofList [0, -18]
  let h : ZPoly := DensePoly.C (-12)
  match dispatchGcdCert f h with
  | (cert, .structural) =>
      cert.gcd == DensePoly.C 6 &&
        cert.cofL == DensePoly.ofList [0, -3] &&
          cert.cofR == DensePoly.C (-2) &&
            match cert.coprime with
            | .constant u v k =>
                u == 0 && v == 1 && k == -2 && checkGcd f h cert
            | .modular .. => false
  | _ => false

#guard
  let f : ZPoly := DensePoly.C (-1)
  let h : ZPoly := DensePoly.ofList [4, 6, 8]
  match dispatchGcdCert f h with
  | (cert, .structural) =>
      cert.gcd == 1 && cert.cofL == DensePoly.C (-1) &&
        cert.cofR == h && checkGcd f h cert
  | _ => false

#guard
  let f : ZPoly := DensePoly.C (-12)
  let h : ZPoly := DensePoly.C 18
  match dispatchGcdCert f h with
  | (cert, .structural) =>
      cert.gcd == DensePoly.C 6 && cert.cofL == DensePoly.C (-2) &&
        cert.cofR == DensePoly.C 3 && checkGcd f h cert
  | _ => false

-- A genuinely nonstructural pair must continue to route-0 reduction and the
-- ordinary producers rather than being accepted by the mandatory prepass.
#guard
  let f : ZPoly := DensePoly.ofList [1, 1]
  let h : ZPoly := DensePoly.ofList [2, 1]
  match structuralGcdCert? f h, dispatchGcdCert f h with
  | none, (cert, .reduced) => checkGcd f h cert
  | _, _ => false

-- Direct reference canaries.  These deliberately bypass dispatch so the
-- retained rational implementation remains useful as an independent oracle.

#guard
  let f : ZPoly := 0
  let h : ZPoly := 0
  let cert := rationalGcdCert f h
  cert.gcd == 0 && checkGcd f h cert

-- The degenerate direct fallback and its checker also remain reducible in the
-- ordinary kernel while the definition is in scope.  Larger rational
-- Euclidean searches intentionally stay outside the replay closure.
example :
    checkGcd (0 : ZPoly) 0 (rationalGcdCert 0 0) = true := by
  decide +kernel

#guard
  let f : ZPoly := DensePoly.ofList [2, 4, 2]
  let h : ZPoly := 0
  let cert := rationalGcdCert f h
  cert.gcd == f && checkGcd f h cert

#guard
  let f : ZPoly := DensePoly.ofList [0, 12]
  let h : ZPoly := DensePoly.ofList [0, 18]
  let cert := rationalGcdCert f h
  cert.gcd == DensePoly.ofList [0, 6] && checkGcd f h cert

#guard
  let common : ZPoly := DensePoly.ofList [1, 1]
  let f := common * DensePoly.ofList [2, 1]
  let h := common * DensePoly.ofList [3, 1]
  let cert := rationalGcdCert f h
  cert.gcd == common && checkGcd f h cert

#guard gcd (0 : ZPoly) 0 == 0

#guard
  let two : ZPoly := DensePoly.C 2
  let twoX : ZPoly := DensePoly.ofList [0, 2]
  gcd two twoX == two

#guard
  let twelveX : ZPoly := DensePoly.ofList [0, 12]
  let eighteenX : ZPoly := DensePoly.ofList [0, 18]
  gcd twelveX eighteenX == DensePoly.ofList [0, 6]

#guard
  let f : ZPoly := DensePoly.ofList [0, 0, 0, 12, 12]
  let h : ZPoly := DensePoly.ofList [0, 0, 36, 18]
  match structuralReduction? f h with
  | none => false
  | some reduced =>
      reduced.factor == DensePoly.ofList [0, 0, 6] &&
        match prsCert? reduced.left reduced.right with
        | none => false
        | some reducedCert =>
            match restoreStructural? f h reduced reducedCert with
            | some cert =>
                cert.gcd == DensePoly.ofList [0, 0, 6] && checkGcd f h cert
            | none => false

#guard
  let f : ZPoly := DensePoly.ofList [1, 1]
  let h : ZPoly := DensePoly.ofList [2, 1]
  isCoprime f h

#guard
  let common : ZPoly := DensePoly.ofList [1, 1]
  let f := common * DensePoly.ofList [2, 1]
  let h := common * DensePoly.ofList [3, 1]
  gcd f h == common && checkGcd f h (gcdCert f h)

#guard
  let common : ZPoly := DensePoly.ofList [2, 1]
  let f := common * DensePoly.ofList [1, 2]
  let h := common * DensePoly.ofList [1, 3]
  gcd f h == common &&
    checkCoprime (gcdCert f h).cofL (gcdCert f h).cofR
      (gcdCert f h).coprime

#guard
  let f : ZPoly := DensePoly.ofList [1, 1]
  let h : ZPoly := DensePoly.ofList [2, 1]
  (coprimeCert? f h).isSome

#guard
  let common : ZPoly := DensePoly.ofList [1, 1]
  let f := common * DensePoly.ofList [2, 1]
  let h := common * DensePoly.ofList [3, 1]
  (coprimeCert? f h).isNone

#guard
  let twoX : ZPoly := DensePoly.ofList [0, 2]
  let fourX : ZPoly := DensePoly.ofList [0, 4]
  gcdList [twoX, fourX] == twoX && lcm twoX fourX == fourX

#guard
  let f : DensePoly Rat := DensePoly.ofList [1, 2]
  let h : DensePoly Rat := DensePoly.ofList [2, 4]
  ratGcd f h == DensePoly.ofList [1 / 2, 1]

#guard
  let common : DensePoly Rat :=
    DensePoly.ofList [(1 : Rat) / 1000003, 1]
  let f := common * DensePoly.ofList [(1 : Rat) / 1000033, 1]
  let h := common * DensePoly.ofList [(1 : Rat) / 1000037, 1]
  ratGcd f h == common

#guard
  let common : DensePoly Rat :=
    DensePoly.ofList [-(1 : Rat) / 1000003, -1]
  let f := common * DensePoly.ofList [(1 : Rat) / 1000033, 1]
  let h := common * DensePoly.ofList [(1 : Rat) / 1000037, 1]
  ratGcd f h == DensePoly.ofList [(1 : Rat) / 1000003, 1]

end ZPoly

end Hex
