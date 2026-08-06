/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.RawEvaluation
public meta import HexNumberFieldTower.RawEvaluation

public section

/-!
# Successive number-field towers

This module fixes the runtime representation used by the tower library. Levels
are stored top-first, while element coordinates use the mixed-radix order in
which the oldest generator varies fastest. A level stores only the lower
coefficients of its monic defining polynomial; the leading coefficient is
implicitly one.
-/
namespace Hex

namespace NumberTower

/-- The monic polynomial represented by a raw level, including its implicit
leading coefficient. -/
@[expose]
def Level.polynomial (level : Level) (lower : List Level) :
    Array (Array Rat) :=
  level.defining.push (Arithmetic.fixedCoeffs (levelsDim lower) #[1])

/-- A rational-presentation level relation agrees with the monic rational
associate of the stored absolute root's checked integer polynomial. -/
@[expose]
def Level.RationalRelation (level : Level) (lower : List Level) : Prop :=
  lower = [] ∧
    ∃ original : ZPoly, ∃ _checked : ZPoly.CheckedIrreducible original,
      level.root.p = ZPoly.normalizePrimitiveSign original ∧
        Factor.toRatPoly (level.polynomial lower) =
          DensePoly.scale ((level.root.p.leadingCoeff : Rat)⁻¹)
            (ZPoly.toRatPoly level.root.p)

/-- Meaningful construction evidence for one level. The base constructor ties
the relation directly to a checked irreducible integer presentation and its
selected root. A relative constructor records successful execution of the
recursive Trager irreducibility checker and the fixed-embedding zero check. -/
inductive Level.Certificate (level : Level) (lower : List Level) : Prop
  | rational (relation : level.RationalRelation lower)
  | relative
      (degree_gt_one : 1 < level.degree)
      (irreducible : Factor.isIrreducible lower
        (level.polynomial lower) = true)
      (embedding : RawEvaluation.vanishesAt? lower
        (level.polynomial lower) level.root = some true)

/-- Every top-first level has canonical coefficient widths relative to the
tail beneath it and carries constructor-produced irreducibility and fixed-
embedding evidence. -/
@[expose]
def LevelsValid : List Level → Prop
  | [] => True
  | level :: lower =>
      level.Structural (levelsDim lower) ∧
        level.Certificate lower ∧ LevelsValid lower

end NumberTower

/-- A validated, fixed-embedding tower of successive algebraic extensions of
{name}`Rat`. Construction is sealed, and checked smart constructors are the
only API for extending towers. -/
structure NumberTower where
  private mk ::
  levels : Array NumberTower.Level
  valid : NumberTower.LevelsValid levels.toList

namespace NumberTower

/-- The rational tower, with no algebraic extension levels. -/
def rat : NumberTower :=
  .mk #[] (by simp [LevelsValid])

/-- The rational tower has no proper extension levels. -/
@[simp]
theorem rat_levels : rat.levels.toList = [] := by
  rfl

/-- Absolute dimension over `Rat`. -/
@[expose]
def dim (T : NumberTower) : Nat :=
  levelsDim T.levels.toList

/-- Internal checked boundary for adjoining one proper extension level. Raw
level arrays are accepted only after structural, recursive irreducibility, and
fixed-embedding checks all succeed. -/
def Internal.extend? (T : NumberTower) (level : Level) : Option NumberTower :=
  if hdegree : 1 < level.degree then
    if hstruct : level.structuralCheck T.dim = true then
      if hirred : Factor.isIrreducible T.levels.toList
          (level.polynomial T.levels.toList) = true then
        if hembed : RawEvaluation.vanishesAt? T.levels.toList
            (level.polynomial T.levels.toList) level.root = some true then
          let levels := #[level] ++ T.levels
          some <| .mk levels (by
            rw [show levels.toList = level :: T.levels.toList by simp [levels]]
            exact ⟨Level.structural_of_check hstruct,
              .relative hdegree hirred hembed, T.valid⟩)
        else
          none
      else
        none
    else
      none
  else
    none

/-- The internal extension constructor succeeds once all of its explicit
checks have been discharged. -/
theorem Internal.extend?_isSome (T : NumberTower) (level : Level)
    (hdegree : 1 < level.degree)
    (hstruct : level.structuralCheck T.dim = true)
    (hirred : Factor.isIrreducible T.levels.toList
      (level.polynomial T.levels.toList) = true)
    (hembed : RawEvaluation.vanishesAt? T.levels.toList
      (level.polynomial T.levels.toList) level.root = some true) :
    (Internal.extend? T level).isSome := by
  unfold Internal.extend?
  simp [hdegree, hstruct, hirred, hembed]

/-- A successful checked extension prepends exactly the admitted level. -/
theorem Internal.extend?_levels (T : NumberTower) (level : Level)
    {U : NumberTower} (h : Internal.extend? T level = some U) :
    U.levels.toList = level :: T.levels.toList := by
  unfold Internal.extend? at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Option.some.injEq] at h
  subst U
  simp

/-- A successful checked extension multiplies the lower tower dimension by
the admitted relative degree. -/
theorem Internal.extend?_dim (T : NumberTower) (level : Level)
    {U : NumberTower} (h : Internal.extend? T level = some U) :
    U.dim = level.degree * T.dim := by
  unfold dim
  rw [Internal.extend?_levels T level h]
  rfl

/-- Number of proper algebraic extension levels. -/
@[expose]
def height (T : NumberTower) : Nat :=
  T.levels.size

/-- Canonical mixed-radix rational coordinates in a fixed tower. -/
structure Elem (T : NumberTower) where
  private mk ::
  data : Array Rat
  size_eq : data.size = T.dim

/-- Normalize an arbitrary coordinate array to the tower dimension by
truncating excess coordinates and padding missing coordinates with zero. -/
@[expose]
def normalizeCoeffs (T : NumberTower) (coefficients : Array Rat) : Array Rat :=
  (Vector.ofFn fun i : Fin T.dim => coefficients.getD i.val 0).toArray

/-- Normalization fixes an array that already has the tower width. -/
theorem normalizeCoeffs_eq_self (T : NumberTower) (coefficients : Array Rat)
    (hsize : coefficients.size = T.dim) :
    normalizeCoeffs T coefficients = coefficients := by
  apply Array.ext
  · simp [normalizeCoeffs, hsize]
  · intro i hi₁ hi₂
    simp [normalizeCoeffs, Array.getD, hi₂]

/-- Construct the unique fixed-width element represented by a raw coordinate
array. -/
def ofCoeffs (T : NumberTower) (coefficients : Array Rat) : Elem T :=
  .mk (normalizeCoeffs T coefficients) (by simp [normalizeCoeffs])

/-- Canonical flattened rational coordinates. -/
@[expose]
def coeffs {T : NumberTower} (a : Elem T) : Array Rat :=
  a.data

/-- Every element exposes exactly the tower's mixed-radix width. -/
@[simp]
theorem coeffs_size {T : NumberTower} (a : Elem T) :
    (coeffs a).size = T.dim := by
  exact a.size_eq

/-- Reading a freshly normalized element returns its normalized coordinates. -/
@[simp]
theorem coeffs_ofCoeffs (T : NumberTower) (coefficients : Array Rat) :
    coeffs (ofCoeffs T coefficients) = normalizeCoeffs T coefficients := by
  rfl

/-- Equality is exact coordinate equality inside a fixed tower. -/
@[ext]
theorem Elem.ext {T : NumberTower} {a b : Elem T}
    (h : coeffs a = coeffs b) : a = b := by
  cases a
  cases b
  change _ = _ at h
  cases h
  rfl

instance {T : NumberTower} : DecidableEq (Elem T) := fun a b =>
  match decEq (coeffs a).toList (coeffs b).toList with
  | isTrue h =>
      isTrue (Elem.ext (by simpa using h))
  | isFalse h =>
      isFalse fun hab => h (by simp [hab])

/-- Embed a rational number into the constant mixed-radix coordinate. -/
def ofRat (T : NumberTower) (q : Rat) : Elem T :=
  ofCoeffs T #[q]

/-- Rational embedding is the singleton-coordinate constructor. -/
theorem ofRat_eq_ofCoeffs (T : NumberTower) (q : Rat) :
    T.ofRat q = T.ofCoeffs #[q] := by
  rfl

/-- A dependent extension result carries the canonical lower-field embedding,
the new generator, and its selected absolute algebraic root. -/
structure Extension (T : NumberTower) where
  tower : NumberTower
  embed : Elem T → Elem tower
  gen : Elem tower
  root : AlgebraicRoot

/-- Primitive associate with positive leading coefficient. This leaves every
complex root fixed and only normalizes a possible global sign. -/
@[expose]
def positiveAssociate (p : ZPoly) : ZPoly :=
  ZPoly.normalizePrimitiveSign p

/-- Checked integer irreducibility forces primitive content. -/
theorem positiveAssociate_primitive (p : ZPoly)
    (checked : ZPoly.CheckedIrreducible p) :
    ZPoly.Primitive (positiveAssociate p) := by
  apply ZPoly.primitive_normalizePrimitiveSign
  have hpne : p ≠ 0 := by
    intro hp
    subst p
    have hpos := checked.pos_degree
    simp at hpos
  have hdegree : p.degree?.getD 0 ≠ 0 := Nat.ne_of_gt checked.pos_degree
  have hirred := checked.is_true
  rw [ZPoly.isIrreducible, if_neg hpne, if_neg hdegree] at hirred
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hirred
  have hscalar : (ZPoly.factorize p).scalar.natAbs = 1 := by
    exact hirred.1.1
  rw [factorize_scalar, if_neg hpne] at hscalar
  have hcontentAbs : (ZPoly.content p).natAbs = 1 := by
    by_cases hlead : p.leadingCoeff < 0
    · simpa [hlead] using hscalar
    · simpa [hlead] using hscalar
  have hcontent : 0 ≤ ZPoly.content p := by
    show 0 ≤ DensePoly.content p
    rw [DensePoly.content]
    exact Int.natCast_nonneg _
  have hcast := congrArg Int.ofNat hcontentAbs
  simpa [ZPoly.Primitive, Int.natAbs_of_nonneg hcontent] using hcast

/-- A checked positive-degree polynomial's positive associate has positive
leading coefficient. -/
theorem positiveAssociate_lc_pos (p : ZPoly)
    (checked : ZPoly.CheckedIrreducible p) :
    0 < (positiveAssociate p).leadingCoeff := by
  apply ZPoly.leadingCoeff_normalizePrimitiveSign_pos_of_ne_zero
  intro hp
  subst p
  have hpos := checked.pos_degree
  simp at hpos

/-- Sign association preserves positive degree. -/
theorem positiveAssociate_degree_pos (p : ZPoly)
    (checked : ZPoly.CheckedIrreducible p) :
    0 < (positiveAssociate p).degree?.getD 0 := by
  simpa [positiveAssociate] using checked.pos_degree

/-- Sign association preserves the executable simple-root certificate. -/
theorem positiveAssociate_simple (p : ZPoly) (hsf : HasOnlySimpleRoots p) :
    HasOnlySimpleRoots (positiveAssociate p) := by
  exact ZPoly.squareFreeRat_normalizePrimitiveSign p hsf

/-- Global sign normalization preserves the Mahler refinement precision. -/
theorem mahlerPrec_positiveAssociate (p : ZPoly) :
    mahlerPrec (positiveAssociate p) = mahlerPrec p := by
  unfold mahlerPrec positiveAssociate
  rw [ZPoly.degree?_normalizePrimitiveSign,
    ZPoly.coeffAbsMax_normalizePrimitiveSign]

/-- Transport a refined isolation across global sign normalization. -/
def RefinedIsolation.positiveAssociate {p : ZPoly}
    (rep : RefinedIsolation p) : RefinedIsolation (positiveAssociate p) :=
  ⟨⟨rep.1.square, .normalize rep.1.witness⟩, by
    rw [mahlerPrec_positiveAssociate]
    exact rep.2⟩

/-- Build a one-level tower for a checked rational presentation. The level
relation is the monic rational associate of `p`; its absolute generator uses
the supplied isolation, transported only across a possible global sign. -/
def ofQAdjoin {p : ZPoly} {x : SimpleRoot p}
    [checked : ZPoly.CheckedIrreducible p]
    (hsf : HasOnlySimpleRoots p) (rep : RefinedIsolation p)
    (_h : SimpleRoot.mk rep = x) : Extension rat :=
  let q := positiveAssociate p
  let qrep := NumberTower.RefinedIsolation.positiveAssociate rep
  let root : AlgebraicRoot :=
    { p := q
      prim := positiveAssociate_primitive p checked
      pos_lc := positiveAssociate_lc_pos p checked
      pos_degree := positiveAssociate_degree_pos p checked
      squarefree := positiveAssociate_simple p hsf
      x := SimpleRoot.mk qrep
      rep := qrep
      rep_mk := rfl }
  let d := q.degree?.getD 0
  let leading : Rat := q.leadingCoeff
  let defining := ((List.range d).map fun i =>
    #[(q.coeff i : Rat) / leading]).toArray
  if hd : d = 1 then
    { tower := rat
      embed := id
      gen := ofRat rat (-((q.coeff 0 : Rat) / leading))
      root }
  else
    let level : Level := ⟨d, defining, root⟩
    let tower : NumberTower := .mk #[level] (by
      change level.Structural 1 ∧ level.Certificate [] ∧ True
      refine ⟨?_, ?_, trivial⟩
      · refine ⟨?_, by simp [level, defining], ?_⟩
        · have hpositive := root.pos_degree
          have hdpositive : 0 < d := by
            simpa [d, root] using hpositive
          change 1 < d
          omega
        intro i hi
        simp [level, defining]
      · apply Level.Certificate.rational
        refine ⟨rfl, ?_⟩
        refine ⟨p, checked, rfl, ?_⟩
        apply DensePoly.ext_coeff
        intro i
        rw [DensePoly.coeff_scale (R := Rat) _ _ i (Rat.mul_zero _)]
        by_cases hi : i < d
        · have hi' : i < d + 1 := by omega
          simp [Level.polynomial, level, defining, Factor.toRatPoly,
            ZPoly.coeff_toRatPoly, q, root, d, leading, Array.getD,
            hi, hi', Rat.div_def, Rat.mul_comm]
        · have hqdegree := positiveAssociate_degree_pos p checked
          change 0 < q.degree?.getD 0 at hqdegree
          have hqne : q ≠ 0 := by
            intro hq
            rw [hq, DensePoly.degree?_zero_getD] at hqdegree
            omega
          have hqsizePos : 0 < q.size := ZPoly.size_pos_of_ne_zero q hqne
          have hdEq : d = q.size - 1 := by
            simp [d, DensePoly.degree?, hqne]
          have hqsize : q.size = d + 1 := by omega
          by_cases hid : i = d
          · subst i
            have hleading : leading ≠ 0 := by
              change (q.leadingCoeff : Rat) ≠ 0
              intro h
              have hint : q.leadingCoeff = 0 := Rat.intCast_eq_zero_iff.mp h
              have hpos : 0 < q.leadingCoeff := by
                change 0 < (positiveAssociate p).leadingCoeff
                exact positiveAssociate_lc_pos p checked
              omega
            have hlc : q.coeff d = q.leadingCoeff := by
              rw [DensePoly.leadingCoeff_eq_coeff_last q hqsizePos, hqsize]
              simp
            have hleft :
                (Factor.toRatPoly (level.polynomial [])).coeff d = 1 := by
              simp [Level.polynomial, level, defining, Factor.toRatPoly,
                Arithmetic.fixedCoeffs, levelsDim, d, Array.getD]
            rw [hleft, ZPoly.coeff_toRatPoly, hlc]
            change (1 : Rat) = leading⁻¹ * leading
            exact (Rat.inv_mul_cancel leading hleading).symm
          · have hdi : d < i := by omega
            have hsize :
                (Factor.toRatPoly (level.polynomial [])).size ≤ i := by
              apply Nat.le_trans (DensePoly.size_ofCoeffs_le _)
              simp [Level.polynomial, level, defining, d]
              omega
            rw [DensePoly.coeff_eq_zero_of_size_le _ hsize]
            have hqzero : q.coeff i = 0 :=
              DensePoly.coeff_eq_zero_of_size_le q (by omega)
            rw [ZPoly.coeff_toRatPoly]
            change 0 = leading⁻¹ * (q.coeff i : Rat)
            rw [hqzero]
            exact (Rat.mul_zero _).symm)
    { tower
      embed := fun a => ofRat tower ((coeffs a).getD 0 0)
      gen := ofCoeffs tower #[0, 1]
      root }

/-! Compiled representation checks. -/

#guard rat.dim = 1 && rat.height = 0

#guard
    let a := ofCoeffs rat #[3, 4]
    let b := ofRat rat 3
    a == b && coeffs a = #[3]

end NumberTower
end Hex
