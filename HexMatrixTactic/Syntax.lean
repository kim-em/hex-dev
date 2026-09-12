/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Lean

public section

/-!
The syntax of the matrix frontends.  The term forms `det% A` and `char_poly A` return a
`Hex.MatrixTactic.Certified` record; the tactics `det` and `char_poly` close a
goal about the corresponding operation.  `det` is a non-reserved tactic
keyword, so importing a frontend leaves the ordinary `det` function
applications and identifiers untouched; the `%` distinguishes the
result-producing term form from those applications.  Rank tactics live with
their algorithm library, `HexRank`, not here.

Each syntax is declared once, here.  Frontends attach their own elaborators
to these kinds and answer `throwUnsupportedSyntax` outside their fragment, so
importing both the Hex and the Mathlib frontends registers each handler once
and lets the elaborator fall through to the other.
-/

namespace Hex.MatrixTactic

/-- `det% A` computes the determinant of a closed matrix `A` and returns a
`Hex.MatrixTactic.Certified` record with its value and proof. -/
syntax (name := detTerm) "det%" term:max : term

/-- `char_poly A` computes the characteristic polynomial of a closed square
matrix `A` and returns a `Hex.MatrixTactic.Certified` record with its value and proof. -/
syntax (name := charPolyTerm) "char_poly" term:max : term

/-- `det` closes a determinant equality on a closed matrix. -/
syntax (name := detTac) &"det" : tactic

/-- `char_poly` closes a characteristic-polynomial equality on a closed square
matrix. -/
syntax (name := charPolyTac) "char_poly" : tactic

/-- `char_poly A` introduces the computed polynomial as a `poly` let and the
equality `charPoly_eq`. -/
syntax (name := charPolyIntroTac) "char_poly" term:max : tactic

end Hex.MatrixTactic
