/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Produce
public import HexArith.ExactDiv

public section

/-!
The `Int` instantiation of the rank producer, through the GMP-backed exact
quotient `HexArith.Int.exactDiv`.
-/

namespace Hex.Matrix

variable {n m : Nat}

/-- Fraction-free Gauss-Jordan elimination over `Int`. -/
abbrev rowReduceFF (A : Matrix Int n m) : ReducedForm Int n m :=
  rowReduceWith HexArith.Int.exactDiv A

/-- The rank profile of an integer matrix. -/
abbrev rankProfile (A : Matrix Int n m) : RankProfile n m :=
  rankProfileWith HexArith.Int.exactDiv A

/-- The rank certificate of an integer matrix. -/
abbrev rankCert (A : Matrix Int n m) : RankCert Int n m :=
  rankCertWith HexArith.Int.exactDiv A

/-- The rank certificate of an integer matrix, checked. -/
abbrev certifyRank (A : Matrix Int n m) : Option (RankCert Int n m) :=
  certifyRankWith HexArith.Int.exactDiv A

/-- The rank of an integer matrix. -/
abbrev rank (A : Matrix Int n m) : Nat :=
  rankWith HexArith.Int.exactDiv A

end Hex.Matrix
