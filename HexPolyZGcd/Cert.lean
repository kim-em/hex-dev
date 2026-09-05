/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Modulus
public import HexPolyFp
public import HexPolyZ.Kronecker
public import HexPolyZGcd.Divide

public section
set_option backward.proofsInPublic true

/-!
Checked certificates for integer-polynomial gcd candidates.

Candidate production is deliberately kept out of this file.  The checker only
replays two exact product identities, normalization, coprime integer contents,
and one of two independently checkable coprimality witnesses.
-/

namespace Hex

namespace ZPoly

/-- Coefficientwise reduction of an integer polynomial into a bundled
word-sized residue ring.  This copy is local to the gcd checker so its kernel
closure does not depend on the Hensel implementation. -/
@[expose]
def reduceModP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) : FpPoly p :=
  DensePoly.ofList <|
    (List.range f.size).map (fun i => ZMod64.intCast p (f.coeff i))

/-- Coefficientwise specification of reduction modulo `p`. -/
@[simp]
theorem coeff_reduceModP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) (i : Nat) :
    (reduceModP p f).coeff i = ZMod64.intCast p (f.coeff i) := by
  unfold reduceModP
  rw [DensePoly.coeff_ofList]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), hcoeff]
    change (0 : ZMod64 p) = ZMod64.intCast p 0
    rfl

/-- Reduction can only trim high zero residues. -/
theorem size_reduceModP_le (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    (reduceModP p f).size ≤ f.size := by
  unfold reduceModP
  exact Nat.le_trans (DensePoly.size_ofList_le _)
    (by simp)

private theorem intCast_add (p : Nat) [ZMod64.Bounds p] (a b : Int) :
    ZMod64.intCast p (a + b) = ZMod64.intCast p a + ZMod64.intCast p b := by
  exact Lean.Grind.Ring.intCast_add a b

private theorem intCast_mul (p : Nat) [ZMod64.Bounds p] (a b : Int) :
    ZMod64.intCast p (a * b) = ZMod64.intCast p a * ZMod64.intCast p b := by
  exact Lean.Grind.Ring.intCast_mul a b

private theorem intCast_diagonal (p : Nat) [ZMod64.Bounds p]
    (f g : ZPoly) (n i : Nat) :
    ZMod64.intCast p (DensePoly.diagonalMulCoeffTerm f g n i) =
      DensePoly.diagonalMulCoeffTerm (reduceModP p f) (reduceModP p g) n i := by
  unfold DensePoly.diagonalMulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
    rfl
  · simp only [hn, ↓reduceIte, coeff_reduceModP]
    exact intCast_mul p (f.coeff i) (g.coeff (n - i))

private theorem intCast_foldDiagonal (p : Nat) [ZMod64.Bounds p]
    (f g : ZPoly) (n : Nat) :
    ∀ (xs : List Nat) (acc : Int),
      ZMod64.intCast p
          (xs.foldl (fun c i => c + DensePoly.diagonalMulCoeffTerm f g n i) acc) =
        xs.foldl
          (fun c i => c +
            DensePoly.diagonalMulCoeffTerm (reduceModP p f) (reduceModP p g) n i)
          (ZMod64.intCast p acc) := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons i xs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih, intCast_add, intCast_diagonal]

private theorem foldDiagonal_extend (p : Nat) [ZMod64.Bounds p]
    (f g : ZPoly) (n d : Nat) :
    (List.range ((reduceModP p f).size + d)).foldl
        (fun c i => c +
          DensePoly.diagonalMulCoeffTerm (reduceModP p f) (reduceModP p g) n i) 0 =
      (List.range (reduceModP p f).size).foldl
        (fun c i => c +
          DensePoly.diagonalMulCoeffTerm (reduceModP p f) (reduceModP p g) n i) 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih]
      have hcoeff : (reduceModP p f).coeff ((reduceModP p f).size + d) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le _ (by omega)
      by_cases hn : n < (reduceModP p f).size + d
      · have hterm : DensePoly.diagonalMulCoeffTerm
            (reduceModP p f) (reduceModP p g) n ((reduceModP p f).size + d) = 0 := by
          unfold DensePoly.diagonalMulCoeffTerm
          rw [ite_eq_left hn]
          rfl
        rw [hterm]
        exact Lean.Grind.Semiring.add_zero _
      · have hterm : DensePoly.diagonalMulCoeffTerm
            (reduceModP p f) (reduceModP p g) n ((reduceModP p f).size + d) = 0 := by
          unfold DensePoly.diagonalMulCoeffTerm
          rw [ite_eq_right hn, hcoeff]
          exact Lean.Grind.Semiring.zero_mul _
        rw [hterm]
        exact Lean.Grind.Semiring.add_zero _

/-- Coefficientwise reduction is multiplicative. -/
theorem reduceModP_mul (p : Nat) [ZMod64.Bounds p] (f g : ZPoly) :
    reduceModP p (f * g) = reduceModP p f * reduceModP p g := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_reduceModP, DensePoly.coeff_mul, DensePoly.coeff_mul,
    DensePoly.mulCoeffSum_eq_diagonal f g n, intCast_foldDiagonal]
  have hzero : ZMod64.intCast p 0 = (0 : ZMod64 p) := rfl
  rw [hzero]
  have hle := size_reduceModP_le p f
  have hsum : (reduceModP p f).size + (f.size - (reduceModP p f).size) = f.size := by
    omega
  calc
    (List.range f.size).foldl
          (fun c i => c +
            DensePoly.diagonalMulCoeffTerm (reduceModP p f) (reduceModP p g) n i) 0 =
        (List.range (reduceModP p f).size).foldl
          (fun c i => c +
            DensePoly.diagonalMulCoeffTerm (reduceModP p f) (reduceModP p g) n i) 0 := by
      rw [← hsum, foldDiagonal_extend]
    _ = DensePoly.mulCoeffSum (reduceModP p f) (reduceModP p g) n :=
      (DensePoly.mulCoeffSum_eq_diagonal (reduceModP p f) (reduceModP p g) n).symm

/-- Evidence that the two cofactors have no common nonunit factor. -/
inductive CoprimeWitness
  /-- A degree-preserving reduction and a Bezout identity over a prime field. -/
  | modular (p : ZMod64.Prime)
      (alpha beta : @FpPoly p.m p.bounds)
  /-- An integral polynomial combination equal to a nonzero constant. -/
  | constant (u v : ZPoly) (k : Int)

/-- A gcd candidate, its two exact cofactors, and checked coprimality data. -/
structure GcdCert where
  /-- The proposed normalized greatest common divisor. -/
  gcd : ZPoly
  /-- The exact cofactor of the left input. -/
  cofL : ZPoly
  /-- The exact cofactor of the right input. -/
  cofR : ZPoly
  /-- Replayable evidence that the two cofactors have no common nonunit. -/
  coprime : CoprimeWitness

/-- The normalization convention for integer gcds.  Zero is admitted for the
unique degenerate answer `gcd 0 0`; every nonzero result has positive leading
coefficient and positive content. -/
@[expose]
def NormalizedGcd (g : ZPoly) : Bool :=
  g == 0 ||
    (decide (0 < DensePoly.leadingCoeff g) && decide (0 < content g))

/-- Check a dense integer-polynomial product by one Kronecker evaluation.

The slot width covers both the convolution bound and every target coefficient,
so equality of the packed integers is equality coefficient by coefficient.
Unlike materialising `p * q` through either schoolbook convolution or
Kronecker unpacking, the checker needs no result polynomial: it packs the
target once and compares the two integers directly. -/
@[expose]
def mulEqPacked (p q target : ZPoly) : Bool :=
  if p.isZero || q.isZero then
    target == 0
  else
    let slots := p.size + q.size - 1
    let width := bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target))
    let b := 2 * width + ceilLog2 (min p.size q.size) + 1
    let bias : Int := Int.ofNat (2 ^ (b - 1))
    decide (target.size ≤ slots) &&
      (packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size +
          constPack b bias slots ==
        packAux b (fun i => target.coeff i + bias) 0 slots)

/-- Packing a target with the Kronecker bias is the same integer that the
ordinary Kronecker product kernel would unpack for `target * 1`. -/
private theorem packTarget (target : ZPoly) (b slots : Nat)
    (hsize : target.size ≤ slots) :
    let bias : Int := ((2 ^ (b - 1) : Nat) : Int)
    packAux b (fun i => target.coeff i + bias) 0 slots =
      packAux b target.coeff 0 target.size *
          packAux b (1 : ZPoly).coeff 0 (1 : ZPoly).size +
        constPack b bias slots := by
  dsimp only
  rw [packAux_eq, packAux_eq, packAux_eq, constPack_eq]
  simp only [Nat.zero_add]
  rw [packSpec_add_fun, packSpec_eq_eval b target slots hsize,
    packSpec_eq_eval b target target.size (Nat.le_refl _),
    packSpec_eq_eval b (1 : ZPoly) (1 : ZPoly).size (Nat.le_refl _)]
  have hone : DensePoly.eval (1 : ZPoly) ((2 : Int) ^ b) = 1 := by
    change DensePoly.eval (DensePoly.C (1 : Int)) ((2 : Int) ^ b) = 1
    exact DensePoly.eval_C_semiring 1 ((2 : Int) ^ b)
  rw [hone, Int.mul_one]

/-- A successful packed multiplication comparison is an exact polynomial
identity. -/
theorem mulEqPacked_sound {p q target : ZPoly}
    (hcheck : mulEqPacked p q target = true) :
    p * q = target := by
  unfold mulEqPacked at hcheck
  by_cases hz : p.isZero || q.isZero
  · rw [ite_eq_left hz] at hcheck
    have htarget : target = 0 := by
      simpa [beq_iff_eq] using hcheck
    have hz' : p.isZero = true ∨ q.isZero = true := by
      simpa only [Bool.or_eq_true] using hz
    rcases hz' with hp | hq
    · have hp0 : p = 0 :=
        (DensePoly.size_eq_zero_iff p).mp ((DensePoly.isZero_eq_true_iff p).mp hp)
      rw [hp0, htarget]
      exact DensePoly.zero_mul q
    · have hq0 : q = 0 :=
        (DensePoly.size_eq_zero_iff q).mp ((DensePoly.isZero_eq_true_iff q).mp hq)
      rw [hq0, htarget, DensePoly.mul_comm_poly]
      exact DensePoly.zero_mul p
  · rw [ite_eq_right hz] at hcheck
    dsimp only at hcheck
    have hparts :
        target.size ≤ p.size + q.size - 1 ∧
          packAux
                (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1)
                p.coeff 0 p.size *
              packAux
                (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1)
                q.coeff 0 q.size +
              constPack
                (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1)
                (Int.ofNat
                  (2 ^ (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1 - 1)))
                (p.size + q.size - 1) =
            packAux
              (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                  ceilLog2 (min p.size q.size) + 1)
              (fun i => target.coeff i +
                Int.ofNat
                  (2 ^ (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1 - 1)))
              0 (p.size + q.size - 1) := by
      simpa [Bool.and_eq_true, beq_iff_eq] using hcheck
    let A := max (max (maxAbs p) (maxAbs q)) (maxAbs target)
    let width := bitLen A
    let b := 2 * width + ceilLog2 (min p.size q.size) + 1
    let slots := p.size + q.size - 1
    have hsize : target.size ≤ slots := by
      simpa [slots] using hparts.1
    have hpack :
        packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size +
            constPack b (((2 ^ (b - 1) : Nat) : Int)) slots =
          packAux b (fun i => target.coeff i + ((2 ^ (b - 1) : Nat) : Int)) 0 slots := by
      simpa [A, width, b, slots] using hparts.2
    have hb : 0 < b := by
      simp only [b]
      omega
    have hpBound : ∀ i, (p.coeff i).natAbs ≤ A := fun i =>
      Nat.le_trans (natAbs_coeff_le_maxAbs p i)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    have hqBound : ∀ i, (q.coeff i).natAbs ≤ A := fun i =>
      Nat.le_trans (natAbs_coeff_le_maxAbs q i)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    have hproductBudget : ∀ n, ((p * q).coeff n).natAbs < 2 ^ (b - 1) := by
      intro n
      have hle := natAbs_coeff_mul_le_min p q A hpBound hqBound n
      have hpow : (2 : Nat) ^ (b - 1) =
          2 ^ ceilLog2 (min p.size q.size) * (2 ^ width * 2 ^ width) := by
        rw [show b - 1 = ceilLog2 (min p.size q.size) + (width + width) by
          simp only [b]
          omega, Nat.pow_add, Nat.pow_add]
      have hA : A < 2 ^ width := by
        simpa only [width] using lt_two_pow_bitLen A
      have hxpos : 0 < 2 ^ width := Nat.two_pow_pos _
      have haa : A * A < 2 ^ width * 2 ^ width := by
        have h1 : A * A ≤ A * 2 ^ width :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt hA)
        have h2 : A * 2 ^ width < 2 ^ width * 2 ^ width :=
          (Nat.mul_lt_mul_right hxpos).mpr hA
        omega
      have hMpos : 0 < 2 ^ ceilLog2 (min p.size q.size) := Nat.two_pow_pos _
      have h3 : min p.size q.size * (A * A) ≤
          2 ^ ceilLog2 (min p.size q.size) * (A * A) :=
        Nat.mul_le_mul_right _ (le_two_pow_ceilLog2 _)
      have h4 : 2 ^ ceilLog2 (min p.size q.size) * (A * A) <
          2 ^ ceilLog2 (min p.size q.size) * (2 ^ width * 2 ^ width) :=
        (Nat.mul_lt_mul_left hMpos).mpr haa
      omega
    have htargetBudget : ∀ n, (target.coeff n).natAbs < 2 ^ (b - 1) := by
      intro n
      have hcoeff : (target.coeff n).natAbs ≤ A :=
        Nat.le_trans (natAbs_coeff_le_maxAbs target n) (Nat.le_max_right _ _)
      have hA : A < 2 ^ width := by
        simpa only [width] using lt_two_pow_bitLen A
      have hexp : width ≤ b - 1 := by
        simp only [b]
        omega
      exact Nat.lt_of_le_of_lt hcoeff <|
        Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)
    have hproduct := kronecker_identity p q b slots hb
      (by simpa only [slots] using DensePoly.size_mul_le p q) hproductBudget
    have htarget := kronecker_identity target (1 : ZPoly) b slots hb
      (by simpa only [DensePoly.mul_one_right_poly] using hsize)
      (by
        intro n
        simpa only [DensePoly.mul_one_right_poly] using htargetBudget n)
    rw [hpack, packTarget target b slots hsize] at hproduct
    rw [DensePoly.mul_one_right_poly] at htarget
    exact hproduct.symm.trans htarget

/-- Every exact polynomial product passes the packed multiplication checker. -/
theorem mulEqPacked_complete {p q target : ZPoly}
    (hproduct : p * q = target) :
    mulEqPacked p q target = true := by
  unfold mulEqPacked
  by_cases hz : p.isZero || q.isZero
  · rw [ite_eq_left hz]
    rw [beq_iff_eq]
    rw [← hproduct]
    have hz' : p.isZero = true ∨ q.isZero = true := by
      simpa only [Bool.or_eq_true] using hz
    rcases hz' with hp | hq
    · have hp0 : p = 0 :=
        (DensePoly.size_eq_zero_iff p).mp
          ((DensePoly.isZero_eq_true_iff p).mp hp)
      rw [hp0]
      exact DensePoly.zero_mul q
    · have hq0 : q = 0 :=
        (DensePoly.size_eq_zero_iff q).mp
          ((DensePoly.isZero_eq_true_iff q).mp hq)
      rw [hq0, DensePoly.mul_comm_poly]
      exact DensePoly.zero_mul p
  · rw [ite_eq_right hz]
    dsimp only
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    let A := max (max (maxAbs p) (maxAbs q)) (maxAbs target)
    let width := bitLen A
    let b := 2 * width + ceilLog2 (min p.size q.size) + 1
    let slots := p.size + q.size - 1
    have hsize : target.size ≤ slots := by
      rw [← hproduct]
      simpa only [slots] using DensePoly.size_mul_le p q
    refine ⟨by simpa only [slots] using hsize, ?_⟩
    have hpPack :
        packAux b p.coeff 0 p.size = DensePoly.eval p ((2 : Int) ^ b) := by
      rw [packAux_eq]
      simpa using packSpec_eq_eval b p p.size (Nat.le_refl _)
    have hqPack :
        packAux b q.coeff 0 q.size = DensePoly.eval q ((2 : Int) ^ b) := by
      rw [packAux_eq]
      simpa using packSpec_eq_eval b q q.size (Nat.le_refl _)
    have htPack :
        packAux b target.coeff 0 target.size =
          DensePoly.eval target ((2 : Int) ^ b) := by
      rw [packAux_eq]
      simpa using packSpec_eq_eval b target target.size (Nat.le_refl _)
    have hOnePack :
        packAux b (1 : ZPoly).coeff 0 (1 : ZPoly).size = 1 := by
      rw [packAux_eq]
      simp only [Nat.zero_add]
      have heval := packSpec_eq_eval b (1 : ZPoly) (1 : ZPoly).size
        (Nat.le_refl _)
      rw [heval]
      exact DensePoly.eval_C_semiring 1 ((2 : Int) ^ b)
    have hpacked :
        packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size +
            constPack b (((2 ^ (b - 1) : Nat) : Int)) slots =
          packAux b (fun i => target.coeff i +
            ((2 ^ (b - 1) : Nat) : Int)) 0 slots := by
      rw [packTarget target b slots hsize]
      rw [hpPack, hqPack, htPack, hOnePack, Int.mul_one,
        ← DensePoly.eval_mul_commring, hproduct]
    simpa only [A, width, b, slots, Int.ofNat_eq_natCast] using hpacked

/-- A common divisor of two polynomials with coprime contents is primitive. -/
private theorem primitiveCommon {f h d : ZPoly}
    (hcontent : Int.gcd (content f) (content h) = 1)
    (hdf : d ∣ f) (hdh : d ∣ h) :
    Primitive d := by
  rcases hdf with ⟨a, ha⟩
  rcases hdh with ⟨b, hb⟩
  have hdcf : content d ∣ content f := by
    refine ⟨content a, ?_⟩
    rw [ha, content_mul]
  have hdch : content d ∣ content h := by
    refine ⟨content b, ?_⟩
    rw [hb, content_mul]
  rw [Int.gcd_eq_one_iff] at hcontent
  have hdone : content d ∣ (1 : Int) := hcontent (content d) hdcf hdch
  have hnat : DensePoly.contentNat d ∣ (1 : Nat) := by
    apply Int.ofNat_dvd.mp
    simpa [content, DensePoly.content] using hdone
  show content d = 1
  rw [content, DensePoly.content, Nat.eq_one_of_dvd_one hnat]
  rfl

/-- A primitive integer polynomial of size at most one is a unit. -/
private theorem unitOfPrimitive {d : ZPoly}
    (hprimitive : Primitive d) (hsize : d.size ≤ 1) :
    IsUnit d := by
  have hpos : 0 < d.size := by
    rcases Nat.eq_zero_or_pos d.size with hzero | hpos
    · have hdzero : d = 0 := (DensePoly.size_eq_zero_iff d).mp hzero
      subst d
      change content (0 : ZPoly) = 1 at hprimitive
      have hczero : content (0 : ZPoly) = 0 := by rfl
      rw [hczero] at hprimitive
      omega
    · exact hpos
  have hsizeOne : d.size = 1 := by omega
  have hdC : d = DensePoly.C (d.coeff 0) := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_C]
    cases n with
    | zero => simp
    | succ n =>
        rw [DensePoly.coeff_eq_zero_of_size_le d (by omega)]
        rfl
  have habsCast : ((d.coeff 0).natAbs : Int) = 1 := by
    have hp := hprimitive
    rw [hdC] at hp
    simpa [Primitive, content] using hp
  have habs : (d.coeff 0).natAbs = 1 := by
    exact_mod_cast habsCast
  rcases Int.natAbs_eq (d.coeff 0) with hc | hc
  · left
    rw [hdC, hc, habs]
    rfl
  · right
    rw [hdC, hc, habs]
    rfl

/-- A primitive integer polynomial is nonzero. -/
private theorem neZeroOfPrimitive {d : ZPoly} (hprimitive : Primitive d) :
    d ≠ 0 := by
  intro hzero
  subst d
  change content (0 : ZPoly) = 1 at hprimitive
  have hczero : content (0 : ZPoly) = 0 := by rfl
  rw [hczero] at hprimitive
  omega

/-- An exact nonzero constant Bezout combination forces every common divisor
to have size at most one. -/
private theorem sizeCommonConstant {f h d u v : ZPoly} {k : Int}
    (hk : k ≠ 0) (hbez : u * f + v * h = DensePoly.C k)
    (hprimitive : Primitive d) (hdf : d ∣ f) (hdh : d ∣ h) :
    d.size ≤ 1 := by
  rcases hdf with ⟨a, ha⟩
  rcases hdh with ⟨b, hb⟩
  have hu : u * (d * a) = d * (u * a) := by
    calc
      u * (d * a) = (u * d) * a := (DensePoly.mul_assoc_poly u d a).symm
      _ = (d * u) * a := by rw [DensePoly.mul_comm_poly u d]
      _ = d * (u * a) := DensePoly.mul_assoc_poly d u a
  have hv : v * (d * b) = d * (v * b) := by
    calc
      v * (d * b) = (v * d) * b := (DensePoly.mul_assoc_poly v d b).symm
      _ = (d * v) * b := by rw [DensePoly.mul_comm_poly v d]
      _ = d * (v * b) := DensePoly.mul_assoc_poly d v b
  have hdvd : d ∣ DensePoly.C k := by
    refine ⟨u * a + v * b, ?_⟩
    calc
      DensePoly.C k = u * f + v * h := hbez.symm
      _ = u * (d * a) + v * (d * b) := by rw [ha, hb]
      _ = d * (u * a) + d * (v * b) := by rw [hu, hv]
      _ = d * (u * a + v * b) := (DensePoly.mul_add_right_poly d (u * a) (v * b)).symm
  have hCne : DensePoly.C k ≠ (0 : ZPoly) := by
    intro hzero
    have hcoeff := congrArg (fun p : ZPoly => p.coeff 0) hzero
    rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
    simp only [↓reduceIte] at hcoeff
    exact hk hcoeff
  exact Nat.le_trans
    (size_le_of_dvd_nonzero (neZeroOfPrimitive hprimitive) hCne hdvd)
    (DensePoly.size_C_le_one k)

/-- A degree-preserving prime-field Bezout witness forces every primitive
common divisor to have size at most one. -/
private theorem sizeCommonModular
    (prime : ZMod64.Prime)
    (f h d : ZPoly) (alpha beta : @FpPoly prime.m prime.bounds)
    (hfsize : (@reduceModP prime.m prime.bounds f).size = f.size)
    (hhsize : (@reduceModP prime.m prime.bounds h).size = h.size)
    (hbez : alpha * @reduceModP prime.m prime.bounds f +
        beta * @reduceModP prime.m prime.bounds h = 1)
    (hprimitive : Primitive d) (hdf : d ∣ f) (hdh : d ∣ h) :
    d.size ≤ 1 := by
  letI : ZMod64.Bounds prime.m := prime.bounds
  letI : ZMod64.PrimeModulus prime.m := ZMod64.primeModulusOfPrime prime.prime
  let fd := reduceModP prime.m f
  let hd := reduceModP prime.m h
  let dd := reduceModP prime.m d
  have hbez' : alpha * fd + beta * hd = 1 := by
    simpa only [fd, hd] using hbez
  rcases hdf with ⟨a, ha⟩
  rcases hdh with ⟨b, hb⟩
  let ad := reduceModP prime.m a
  let bd := reduceModP prime.m b
  have hfa : fd = dd * ad := by
    dsimp only [fd, dd, ad]
    rw [ha, reduceModP_mul]
  have hhb : hd = dd * bd := by
    dsimp only [hd, dd, bd]
    rw [hb, reduceModP_mul]
  have halpha : alpha * (dd * ad) = dd * (alpha * ad) := by
    calc
      alpha * (dd * ad) = (alpha * dd) * ad :=
        (DensePoly.mul_assoc_poly alpha dd ad).symm
      _ = (dd * alpha) * ad :=
        congrArg (fun x => x * ad) (DensePoly.mul_comm_poly alpha dd)
      _ = dd * (alpha * ad) := DensePoly.mul_assoc_poly dd alpha ad
  have hbeta : beta * (dd * bd) = dd * (beta * bd) := by
    calc
      beta * (dd * bd) = (beta * dd) * bd :=
        (DensePoly.mul_assoc_poly beta dd bd).symm
      _ = (dd * beta) * bd :=
        congrArg (fun x => x * bd) (DensePoly.mul_comm_poly beta dd)
      _ = dd * (beta * bd) := DensePoly.mul_assoc_poly dd beta bd
  have hddvd : dd ∣ (1 : FpPoly prime.m) := by
    refine ⟨alpha * ad + beta * bd, ?_⟩
    calc
      (1 : FpPoly prime.m) = alpha * fd + beta * hd := hbez'.symm
      _ = alpha * (dd * ad) + beta * (dd * bd) := by rw [hfa, hhb]
      _ = dd * (alpha * ad) + dd * (beta * bd) := by rw [halpha, hbeta]
      _ = dd * (alpha * ad + beta * bd) :=
        (DensePoly.mul_add_right_poly dd (alpha * ad) (beta * bd)).symm
  rcases hddvd with ⟨e, he⟩
  have hcoeffOne : (1 : ZMod64 prime.m) ≠ 0 :=
    ZMod64.one_ne_zero_of_prime prime.prime
  have honeSize : (1 : FpPoly prime.m).size = 1 :=
    DensePoly.size_C_of_ne_zero hcoeffOne
  have honeNe : (1 : FpPoly prime.m) ≠ 0 := by
    intro hzero
    have hsizeZero : (1 : FpPoly prime.m).size = 0 := by rw [hzero]; rfl
    omega
  have hddNe : dd ≠ 0 := by
    intro hzero
    apply honeNe
    rw [he, hzero]
    exact DensePoly.zero_mul e
  have heNe : e ≠ 0 := by
    intro hzero
    apply honeNe
    rw [he, hzero]
    exact (DensePoly.mul_comm_poly dd 0).trans (DensePoly.zero_mul dd)
  have hddSize : dd.size ≤ 1 := by
    have hmul := FpPoly.size_mul_eq_add_sub_one dd e hddNe heNe
    rw [← he] at hmul
    have hddPos := FpPoly.size_pos_of_ne_zero hddNe
    have hePos := FpPoly.size_pos_of_ne_zero heNe
    omega
  have hnonzero : fd ≠ 0 ∨ hd ≠ 0 := by
    by_cases hfd : fd = 0
    · right
      intro hhd
      rw [hfd, hhd] at hbez'
      have ha0 : alpha * (0 : FpPoly prime.m) = 0 :=
        (DensePoly.mul_comm_poly alpha 0).trans (DensePoly.zero_mul alpha)
      have hb0 : beta * (0 : FpPoly prime.m) = 0 :=
        (DensePoly.mul_comm_poly beta 0).trans (DensePoly.zero_mul beta)
      have hsumZero : (0 : FpPoly prime.m) + 0 = 0 := DensePoly.zero_add 0
      rw [ha0, hb0, hsumZero] at hbez'
      exact honeNe hbez'.symm
    · exact Or.inl hfd
  rcases hnonzero with hfdNe | hhdNe
  · have hfNe : f ≠ 0 := by
      intro hfzero
      have hfSizeZero : f.size = 0 := by rw [hfzero]; rfl
      have hsizeZero : fd.size = 0 := by
        dsimp only [fd]
        exact hfsize.trans hfSizeZero
      exact hfdNe ((DensePoly.size_eq_zero_iff fd).mp hsizeZero)
    have haNe : a ≠ 0 := by
      intro hazero
      apply hfNe
      rw [ha, hazero, DensePoly.mul_comm_poly]
      exact DensePoly.zero_mul d
    have hadNe : ad ≠ 0 := by
      intro hadzero
      apply hfdNe
      rw [hfa, hadzero]
      exact (DensePoly.mul_comm_poly dd 0).trans (DensePoly.zero_mul dd)
    have himage := FpPoly.size_mul_eq_add_sub_one dd ad hddNe hadNe
    rw [← hfa] at himage
    have hfdSize : fd.size = f.size := by simpa only [fd] using hfsize
    have hdPos : 0 < d.size := by
      apply Nat.pos_of_ne_zero
      intro hsizeZero
      exact neZeroOfPrimitive hprimitive ((DensePoly.size_eq_zero_iff d).mp hsizeZero)
    have haPos : 0 < a.size := by
      apply Nat.pos_of_ne_zero
      intro hsizeZero
      exact haNe ((DensePoly.size_eq_zero_iff a).mp hsizeZero)
    have hinteger := mul_size_eq_top_succ_of_nonzero d a hdPos haPos
    rw [← ha] at hinteger
    rw [hfdSize, hinteger] at himage
    have hadSize := size_reduceModP_le prime.m a
    dsimp only [ad] at himage hadSize
    dsimp only [dd] at himage hddSize
    omega
  · have hhNe : h ≠ 0 := by
      intro hhzero
      have hhSizeZero : h.size = 0 := by rw [hhzero]; rfl
      have hsizeZero : hd.size = 0 := by
        dsimp only [hd]
        exact hhsize.trans hhSizeZero
      exact hhdNe ((DensePoly.size_eq_zero_iff hd).mp hsizeZero)
    have hbNe : b ≠ 0 := by
      intro hbzero
      apply hhNe
      rw [hb, hbzero, DensePoly.mul_comm_poly]
      exact DensePoly.zero_mul d
    have hbdNe : bd ≠ 0 := by
      intro hbdzero
      apply hhdNe
      rw [hhb, hbdzero]
      exact (DensePoly.mul_comm_poly dd 0).trans (DensePoly.zero_mul dd)
    have himage := FpPoly.size_mul_eq_add_sub_one dd bd hddNe hbdNe
    rw [← hhb] at himage
    have hhdSize : hd.size = h.size := by simpa only [hd] using hhsize
    have hdPos : 0 < d.size := by
      apply Nat.pos_of_ne_zero
      intro hsizeZero
      exact neZeroOfPrimitive hprimitive ((DensePoly.size_eq_zero_iff d).mp hsizeZero)
    have hbPos : 0 < b.size := by
      apply Nat.pos_of_ne_zero
      intro hsizeZero
      exact hbNe ((DensePoly.size_eq_zero_iff b).mp hsizeZero)
    have hinteger := mul_size_eq_top_succ_of_nonzero d b hdPos hbPos
    rw [← hb] at hinteger
    rw [hhdSize, hinteger] at himage
    have hbdSize := size_reduceModP_le prime.m b
    dsimp only [bd] at himage hbdSize
    dsimp only [dd] at himage hddSize
    omega

/-- Replay the coprimality half of a gcd certificate. -/
@[expose]
def checkCoprime (f h : ZPoly) : CoprimeWitness → Bool
  | .constant u v k =>
      decide (k ≠ 0) && (u * f + v * h == DensePoly.C k)
  | .modular p alpha beta =>
      letI : ZMod64.Bounds p.m := p.bounds
      letI : ZMod64.PrimeModulus p.m := ZMod64.primeModulusOfPrime p.prime
      let fp := reduceModP p.m f
      let hp := reduceModP p.m h
      decide (fp.size = f.size) &&
        decide (hp.size = h.size) &&
        (alpha * fp + beta * hp == 1)

/-- Check a gcd certificate.  Every producer, including deterministic
fallbacks, must pass through this function before its candidate is exposed. -/
@[expose]
def checkGcd (f h : ZPoly) (c : GcdCert) : Bool :=
  mulEqPacked c.gcd c.cofL f &&
    mulEqPacked c.gcd c.cofR h &&
    NormalizedGcd c.gcd &&
    decide (Int.gcd (content c.cofL) (content c.cofR) = 1) &&
    checkCoprime c.cofL c.cofR c.coprime

/-- The cofactor identities together with absence of a common nonunit
cofactor. -/
@[expose]
def CoprimeCofactors (f h g : ZPoly) : Prop :=
  ∃ f' h', f = g * f' ∧ h = g * h' ∧
    ∀ d : ZPoly, d ∣ f' → d ∣ h' → IsUnit d

/-- A successful checker establishes both exact cofactor identities and
coprimality of the cofactors. -/
theorem checkGcd_sound {f h : ZPoly} {c : GcdCert}
    (hc : checkGcd f h c = true) :
    f = c.gcd * c.cofL ∧ h = c.gcd * c.cofR ∧
      ∀ d : ZPoly, d ∣ c.cofL → d ∣ c.cofR → IsUnit d := by
  have hparts :
      (((mulEqPacked c.gcd c.cofL f = true ∧
          mulEqPacked c.gcd c.cofR h = true) ∧
          NormalizedGcd c.gcd = true) ∧
          Int.gcd (content c.cofL) (content c.cofR) = 1) ∧
        checkCoprime c.cofL c.cofR c.coprime = true := by
    simpa [checkGcd, Bool.and_eq_true, decide_eq_true_eq] using hc
  refine ⟨(mulEqPacked_sound hparts.1.1.1.1).symm,
    (mulEqPacked_sound hparts.1.1.1.2).symm, ?_⟩
  intro d hdl hdr
  have hprimitive := primitiveCommon hparts.1.2 hdl hdr
  have hcop := hparts.2
  cases hw : c.coprime with
  | constant u v k =>
      rw [hw] at hcop
      have hconstant : k ≠ 0 ∧
          u * c.cofL + v * c.cofR = DensePoly.C k := by
        simpa [checkCoprime, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          using hcop
      exact unitOfPrimitive hprimitive
        (sizeCommonConstant hconstant.1 hconstant.2 hprimitive hdl hdr)
  | modular prime alpha beta =>
      rw [hw] at hcop
      letI : ZMod64.Bounds prime.m := prime.bounds
      letI : ZMod64.PrimeModulus prime.m :=
        ZMod64.primeModulusOfPrime prime.prime
      have hmodular :
          ((reduceModP prime.m c.cofL).size = c.cofL.size ∧
            (reduceModP prime.m c.cofR).size = c.cofR.size) ∧
            alpha * reduceModP prime.m c.cofL +
                beta * reduceModP prime.m c.cofR = 1 := by
        simpa [checkCoprime, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          using hcop
      exact unitOfPrimitive hprimitive <|
        sizeCommonModular prime c.cofL c.cofR d alpha beta
          hmodular.1.1 hmodular.1.2 hmodular.2 hprimitive hdl hdr

/-- Checker soundness packaged in the public cofactor predicate. -/
theorem coprimeCofactors_of_checkGcd {f h : ZPoly} {c : GcdCert}
    (hc : checkGcd f h c = true) :
    CoprimeCofactors f h c.gcd := by
  rcases checkGcd_sound hc with ⟨hf, hh, hcop⟩
  exact ⟨c.cofL, c.cofR, hf, hh, hcop⟩

end ZPoly

end Hex
