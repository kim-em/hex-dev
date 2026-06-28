module

public import HexGramSchmidtMathlib.Int.GramDet
public import HexGramSchmidtMathlib.Int.Augmented
public import HexGramSchmidtMathlib.Int.Swap
public import HexGramSchmidtMathlib.Int.RowAdd

public section

/-!
Mathlib correspondence for the integer Gram-determinant / scaled-coefficient
surface, split by subject across `HexGramSchmidtMathlib/Int/*`: the
`gramDet_eq_prod_normSq` helpers (`GramDet`), the augmented-Gram determinantal
identification (`Augmented`), the adjacent-swap pivot product (`Swap`), and the
row-add / scaledCoeffs-update / independence / singular-prefix lemmas
(`RowAdd`). This module re-exports them.
-/
