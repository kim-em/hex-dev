/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Adjoin

public section

/-!
# Correctness of splitting towers

The input leading coefficient supplies the scalar omitted from the compact
runtime root array.  Thus the soundness predicate reconstructs nonmonic inputs
without adding redundant data to {name}`Hex.NumberTower.Splitting`.
-/

namespace Hex.NumberTower

namespace Roots

/-- Product of the recorded monic linear factors. The `.all` case denotes the
zero polynomial. -/
@[expose]
def linearProduct {T : NumberTower} : Roots T → Poly T
  | .all => 0
  | .finite roots =>
      roots.foldl
        (fun product entry =>
          product * Factorization.polyPow
            (DensePoly.ofCoeffs #[-entry.1, 1]) entry.2)
        1

/-- Every finite root entry has positive multiplicity. -/
def Positive {T : NumberTower} : Roots T → Prop
  | .all => True
  | .finite roots => ∀ entry ∈ roots.toList, 0 < entry.2

/-- A finite root array contains no duplicate tower values. -/
def NoDuplicates {T : NumberTower} : Roots T → Prop
  | .all => True
  | .finite roots =>
      roots.toList.Pairwise fun a b => a.1 ≠ b.1

end Roots

namespace Splitting

/-- Reconstruct the mapped input from its leading coefficient and returned
monic linear factors. -/
@[expose]
def reconstruct {T : NumberTower} {f : Poly T}
    (S : Splitting T f) : Poly S.extension.tower :=
  match S.roots with
  | .all => 0
  | .finite roots =>
      DensePoly.C (S.extension.embed f.leadingCoeff) *
        (Roots.linearProduct (.finite roots))

/-- Closure of the embedded base and returned roots under field operations. -/
inductive GeneratedBy {T : NumberTower} {f : Poly T}
    (S : Splitting T f) : Elem S.extension.tower → Prop
  | base (a : Elem T) : GeneratedBy S (S.extension.embed a)
  | root (entry : Elem S.extension.tower × Nat)
      (h : match S.roots with
        | .all => False
        | .finite roots => entry ∈ roots.toList) :
      GeneratedBy S entry.1
  | add {a b} : GeneratedBy S a → GeneratedBy S b → GeneratedBy S (a + b)
  | neg {a} : GeneratedBy S a → GeneratedBy S (-a)
  | mul {a b} : GeneratedBy S a → GeneratedBy S b → GeneratedBy S (a * b)
  | inv {a} : GeneratedBy S a → GeneratedBy S a⁻¹

/-- Mathematical meaning of a checked splitting result. -/
def Sound {T : NumberTower} {f : Poly T} (S : Splitting T f) : Prop :=
  S.extension.PreservesEmbedding ∧
    S.reconstruct = mapPoly S.extension.embed f ∧
    (S.roots = Roots.all ↔ T.toPolynomial f = 0) ∧
    S.roots.Positive ∧
    S.roots.NoDuplicates ∧
    (∀ entry, (match S.roots with
        | .all => False
        | .finite roots => entry ∈ roots.toList) →
      Polynomial.eval (S.extension.tower.toComplex entry.1)
        (S.extension.tower.toPolynomial
          (mapPoly S.extension.embed f)) = 0) ∧
    ∀ a : Elem S.extension.tower, GeneratedBy S a

end Splitting

/-- Every returned split payload reconstructs the input and generates the
result extension from the listed roots. -/
theorem split?_sound (T : NumberTower) (f : Poly T)
    {S : Splitting T f} (h : T.split? f = some S) :
    S.Sound := by
  sorry

/-- The bounded split/refactor loop succeeds for every tower polynomial. -/
theorem split?_isSome (T : NumberTower) (f : Poly T) :
    (T.split? f).isSome := by
  sorry

end Hex.NumberTower
