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
    ∃ _checked : ZPoly.CheckedIrreducible level.root.p,
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
`Rat`. Construction is sealed; later modules extend towers only through checked
smart constructors. -/
structure NumberTower where
  private mk ::
  levels : Array NumberTower.Level
  valid : NumberTower.LevelsValid levels.toList

namespace NumberTower

/-- The rational tower, with no algebraic extension levels. -/
def rat : NumberTower :=
  .mk #[] (by simp [LevelsValid])

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
  sorry

/-- A checked positive-degree polynomial's positive associate has positive
leading coefficient. -/
theorem positiveAssociate_lc_pos (p : ZPoly)
    (checked : ZPoly.CheckedIrreducible p) :
    0 < (positiveAssociate p).leadingCoeff := by
  sorry

/-- Sign association preserves positive degree. -/
theorem positiveAssociate_degree_pos (p : ZPoly)
    (checked : ZPoly.CheckedIrreducible p) :
    0 < (positiveAssociate p).degree?.getD 0 := by
  sorry

/-- Global sign normalization preserves the executable integer
irreducibility check. -/
theorem positiveAssociate_irreducible (p : ZPoly)
    (checked : ZPoly.CheckedIrreducible p) :
    ZPoly.isIrreducible (positiveAssociate p) = true := by
  sorry

/-- Sign association preserves the executable simple-root certificate. -/
theorem positiveAssociate_simple (p : ZPoly) (hsf : HasOnlySimpleRoots p) :
    HasOnlySimpleRoots (positiveAssociate p) := by
  sorry

/-- A root atom is unchanged by multiplication of its polynomial by `-1`. -/
theorem atomWitness_positiveAssociate {p : ZPoly} {square : DyadicSquare}
    (h : atomWitness p square) :
    atomWitness (positiveAssociate p) square := by
  sorry

/-- Global sign normalization preserves the Mahler refinement precision. -/
theorem mahlerPrec_positiveAssociate (p : ZPoly) :
    mahlerPrec (positiveAssociate p) = mahlerPrec p := by
  sorry

/-- Transport a refined isolation across global sign normalization. -/
def RefinedIsolation.positiveAssociate {p : ZPoly}
    (rep : RefinedIsolation p) : RefinedIsolation (positiveAssociate p) :=
  ⟨⟨rep.1.square, atomWitness_positiveAssociate rep.1.witness⟩, by
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
      · refine ⟨root.pos_degree, by simp [level, defining], ?_⟩
        intro i hi
        simp [level, defining]
      · apply Level.Certificate.rational
        refine ⟨rfl, ?_⟩
        let qchecked : ZPoly.CheckedIrreducible q :=
          ⟨positiveAssociate_irreducible p checked,
            positiveAssociate_degree_pos p checked⟩
        refine ⟨qchecked, ?_⟩
        sorry)
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
