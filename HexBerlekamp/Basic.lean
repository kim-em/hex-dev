import HexMatrix
import HexPolyFp

/-!
Executable Berlekamp-matrix support for `hex-berlekamp`.

This module builds the Berlekamp matrix `Q_f` for a monic polynomial
`f : FpPoly p` by expressing the Frobenius image of each monomial basis vector
in the quotient basis `{1, X, ..., X^(n - 1)}`. It also exposes the fixed-space
matrix `Q_f - I` together with a kernel wrapper that reuses `HexMatrix`'s
nullspace API and converts basis vectors back into polynomial representatives.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- The basis size used for the Berlekamp matrix of `f`. -/
def basisSize (f : FpPoly p) : Nat :=
  f.degree?.getD 0

/-- Read a polynomial's first `degree f` coefficients as a vector. -/
def coeffVector (f g : FpPoly p) : Vector (ZMod64 p) (basisSize f) :=
  Vector.ofFn fun i => g.coeff i.val

/--
The `j`-th Berlekamp-matrix column, obtained by reducing
`(X^p mod f)^j` modulo `f` and reading the result in the monomial basis.
-/
def berlekampColumn (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (j : Fin (basisSize f)) : Vector (ZMod64 p) (basisSize f) :=
  let frobX := FpPoly.frobeniusXMod f hmonic
  let image := FpPoly.powModMonic frobX f hmonic j.val
  coeffVector f image

/-- The executable `j`-th Berlekamp column represents `X^(p*j)` modulo `f`. -/
theorem berlekampColumn_poly_mod_eq_linearPow_X
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (j : Fin (basisSize f)) :
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f =
      FpPoly.linearPow FpPoly.X (p * j.val) % f := by
  have hfrob :
      (FpPoly.frobeniusXMod f hmonic) % f =
        FpPoly.linearPow FpPoly.X p % f := by
    unfold FpPoly.frobeniusXMod
    exact FpPoly.powModMonic_mod_eq_linearPow FpPoly.X f hmonic p
  calc
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f
        = FpPoly.linearPow (FpPoly.frobeniusXMod f hmonic) j.val % f :=
            FpPoly.powModMonic_mod_eq_linearPow
              (FpPoly.frobeniusXMod f hmonic) f hmonic j.val
    _ = FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val % f :=
            FpPoly.linearPow_mod_eq_of_mod_eq_mod f
              (FpPoly.frobeniusXMod f hmonic) (FpPoly.linearPow FpPoly.X p)
              j.val hfrob
    _ = FpPoly.linearPow FpPoly.X (p * j.val) % f := by
            rw [FpPoly.linearPow_iterate_mul]

/--
Iteratively build the array of Berlekamp-matrix column polynomials
`[1, frobX, frobX^2, …, frobX^(n - 1)]`, each reduced modulo `f`.
Each step costs one polynomial product and one monic reduction, both
quadratic in `n`, so the array of `n` columns is built in `O(n^3)` total.
-/
private def berlekampColumnPolys (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (frobX : FpPoly p) : Nat → FpPoly p → Array (FpPoly p) → Array (FpPoly p)
  | 0, _, acc => acc
  | k + 1, current, acc =>
      berlekampColumnPolys f hmonic frobX k
        (FpPoly.modByMonic f (current * frobX) hmonic) (acc.push current)

private theorem berlekampColumnPolys_toList_eq_powModMonicLinear
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (frobX : FpPoly p)
    (fuel offset : Nat) (acc : Array (FpPoly p)) :
    (berlekampColumnPolys f hmonic frobX fuel
        (FpPoly.powModMonicLinear frobX f hmonic offset) acc).toList =
      acc.toList ++
        (List.range fuel).map fun k => FpPoly.powModMonicLinear frobX f hmonic (offset + k) := by
  induction fuel generalizing offset acc with
  | zero =>
      simp [berlekampColumnPolys]
  | succ fuel ih =>
      rw [berlekampColumnPolys]
      have hstep :
          FpPoly.modByMonic f
              (FpPoly.powModMonicLinear frobX f hmonic offset * frobX) hmonic =
            FpPoly.powModMonicLinear frobX f hmonic (offset + 1) := by
        change FpPoly.modByMonic f
              (FpPoly.powModMonicLinear frobX f hmonic offset * frobX) hmonic =
            FpPoly.powModMonicLinear frobX f hmonic (offset + 1)
        rw [show offset + 1 = Nat.succ offset by omega]
        rfl
      rw [hstep]
      rw [ih (offset + 1)]
      rw [Array.toList_push]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.append_assoc, List.append_cancel_left_eq]
      apply List.cons_eq_cons.mpr
      constructor
      · rfl
      · apply List.map_congr_left
        intro k _hk
        rw [show offset + 1 + k = offset + Nat.succ k by omega]
        rfl

private theorem array_toList_getD {α : Type}
    (xs : Array α) (i : Nat) (fallback : α) :
    xs.toList.getD i fallback = xs.getD i fallback := by
  cases xs with
  | mk data =>
      rw [List.getD_eq_getElem?_getD]
      unfold Array.getD Array.size Array.getInternal
      by_cases hlt : i < data.length
      · rw [dif_pos hlt]
        simp [List.getElem?_eq_getElem hlt]
      · rw [dif_neg hlt]
        simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hlt)]

private theorem list_getD_map_range
    {α : Type} [Zero α] (fuel n : Nat) (g : Nat → α) (hn : n < fuel) :
    ((List.range fuel).map g).getD n 0 = g n := by
  rw [List.getD_eq_getElem?_getD]
  have hlen : n < ((List.range fuel).map g).length := by
    simp [hn]
  rw [List.getElem?_eq_getElem hlen]
  simp [List.getElem_map, List.getElem_range]

private theorem berlekampColumnPolys_getD_eq_powModMonicLinear
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (frobX : FpPoly p)
    (j : Fin fuel) :
    (berlekampColumnPolys f hmonic frobX fuel
        (FpPoly.powModMonicLinear frobX f hmonic 0) #[]).getD j.val 0 =
      FpPoly.powModMonicLinear frobX f hmonic j.val := by
  have hlist := congrArg (fun xs : List (FpPoly p) => xs.getD j.val 0)
    (berlekampColumnPolys_toList_eq_powModMonicLinear f hmonic frobX fuel 0 #[])
  rw [← array_toList_getD
    (berlekampColumnPolys f hmonic frobX fuel
      (FpPoly.powModMonicLinear frobX f hmonic 0) #[]) j.val 0]
  simpa [list_getD_map_range fuel j.val
      (fun k => FpPoly.powModMonicLinear frobX f hmonic (0 + k)) j.isLt] using hlist

/--
The Berlekamp matrix `Q_f`, whose `j`-th column records the coordinates of
`X^(p * j) mod f` in the basis `{1, X, ..., X^(n - 1)}`. Columns are computed
iteratively from the recurrence `column (j + 1) = column j * (X^p mod f) mod f`
to avoid the per-column fast-exponentiation log factor.
-/
def berlekampMatrix (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Matrix (ZMod64 p) (basisSize f) (basisSize f) :=
  let frobX := FpPoly.frobeniusXMod f hmonic
  let polys := berlekampColumnPolys f hmonic frobX (basisSize f) 1 #[]
  Matrix.ofFn fun i j => (polys[j.val]?.getD 0).coeff i.val

/-- A Berlekamp matrix entry is the corresponding coefficient of the executable
column-polynomial array used by `berlekampMatrix`. -/
theorem berlekampMatrix_entry_eq_columnPolys_coeff
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (i j : Fin (basisSize f)) :
    (berlekampMatrix f hmonic)[i][j] =
      ((berlekampColumnPolys f hmonic (FpPoly.frobeniusXMod f hmonic)
        (basisSize f) 1 #[])[j.val]?.getD 0).coeff i.val := by
  simp [berlekampMatrix, Matrix.ofFn]

/-- A Berlekamp matrix entry is the corresponding coefficient of the public
`powModMonic` column representative. -/
theorem berlekampMatrix_entry_eq_powModMonic_coeff
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (i j : Fin (basisSize f)) :
    (berlekampMatrix f hmonic)[i][j] =
      (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).coeff i.val := by
  rw [berlekampMatrix_entry_eq_columnPolys_coeff]
  have hpoly :
      ((berlekampColumnPolys f hmonic (FpPoly.frobeniusXMod f hmonic)
        (basisSize f) 1 #[])[j.val]?.getD 0) =
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val := by
    rw [← Array.getD_eq_getD_getElem?]
    change (berlekampColumnPolys f hmonic (FpPoly.frobeniusXMod f hmonic)
        (basisSize f)
        (FpPoly.powModMonicLinear (FpPoly.frobeniusXMod f hmonic) f hmonic 0) #[]).getD
        j.val 0 =
      FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val
    rw [berlekampColumnPolys_getD_eq_powModMonicLinear]
    exact FpPoly.powModMonicLinear_eq_powModMonic
      (FpPoly.frobeniusXMod f hmonic) f hmonic j.val
  rw [hpoly]

/-- A public Berlekamp column entry is the corresponding coefficient of the
`powModMonic` column representative. -/
theorem berlekampColumn_entry_eq_powModMonic_coeff
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (i j : Fin (basisSize f)) :
    (berlekampColumn f hmonic j)[i] =
      (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).coeff i.val := by
  simp [berlekampColumn, coeffVector]

/-- The public Berlekamp column representative has the expected `X^(p*j)`
residue modulo `f`. -/
theorem berlekampColumn_powModMonic_mod_eq_linearPow_X
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (j : Fin (basisSize f)) :
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f =
      FpPoly.linearPow FpPoly.X (p * j.val) % f :=
  berlekampColumn_poly_mod_eq_linearPow_X f hmonic j

/-- The fixed-space matrix `Q_f - I` used in Berlekamp's kernel computation. -/
def fixedSpaceMatrix (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Ring (ZMod64 p)] :
    Matrix (ZMod64 p) (basisSize f) (basisSize f) :=
  let Q := berlekampMatrix f hmonic
  Matrix.ofFn fun i j =>
    @HSub.hSub (ZMod64 p) (ZMod64 p) (ZMod64 p)
      (@instHSub (ZMod64 p) inst.toSub) Q[i][j]
      (if i = j then
        @OfNat.ofNat (ZMod64 p) 1 (inst.toSemiring.ofNat 1)
      else
        @OfNat.ofNat (ZMod64 p) 0 (inst.toSemiring.ofNat 0))

/-- Convert a coefficient vector back to its polynomial representative. -/
def vectorToPoly {n : Nat} (v : Vector (ZMod64 p) n) : FpPoly p :=
  FpPoly.ofCoeffs v.toArray

/-- Re-reading the coefficients of a polynomial built from a Berlekamp-basis
coefficient vector recovers the original vector. -/
theorem coeffVector_vectorToPoly (f : FpPoly p) (v : Vector (ZMod64 p) (basisSize f)) :
    coeffVector f (vectorToPoly v) = v := by
  apply Vector.ext
  intro i hi
  simp [coeffVector, vectorToPoly, FpPoly.ofCoeffs]

/--
The fixed-space kernel of `Q_f - I`, reusing `HexMatrix.nullspace` instead of a
Berlekamp-local linear-algebra implementation.
-/
def fixedSpaceKernelVectors (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] :
    Vector (Vector (ZMod64 p) (basisSize f))
      (basisSize f - Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) :=
  Matrix.nullspace (fixedSpaceMatrix (inst := inst.toRing) f hmonic)

/-- The fixed-space kernel basis converted back to polynomial representatives. -/
def fixedSpaceKernel (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] :
    Vector (FpPoly p)
      (basisSize f - Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) :=
  Vector.ofFn fun i => vectorToPoly ((fixedSpaceKernelVectors f hmonic).get i)

/-- Vector-level executable Berlekamp kernel condition for the fixed-space
matrix `Q_f - I`. -/
def IsFixedSpaceKernelVector (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (v : Vector (ZMod64 p) (basisSize f)) [inst : Lean.Grind.Field (ZMod64 p)] : Prop :=
  @HMul.hMul (Matrix (ZMod64 p) (basisSize f) (basisSize f))
      (Vector (ZMod64 p) (basisSize f)) (Vector (ZMod64 p) (basisSize f))
      (@Matrix.instHMulVectorOfMulOfAddOfOfNatOfNatNat
        (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0))
      (fixedSpaceMatrix (inst := inst.toRing) f hmonic) v =
    @OfNat.ofNat (Vector (ZMod64 p) (basisSize f)) 0
      (@Zero.toOfNat0 (Vector (ZMod64 p) (basisSize f))
        (@Vector.instZero (ZMod64 p) (basisSize f)
          (@Zero.ofOfNat0 (ZMod64 p)
            (@Lean.Grind.Semiring.ofNat (ZMod64 p) inst.toCommSemiring.toSemiring 0))))

private theorem vector_sub_eq_zero_iff_eq [Lean.Grind.Ring R] (u v : Vector R n) :
    u - v = 0 ↔ u = v := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have hget := congrArg (fun w : Vector R n => w[i]) h
    grind
  · intro h
    rw [h]
    apply Vector.ext
    intro i hi
    grind

/-- The executable kernel predicate for `Q_f - I` is equivalent to the usual
fixed-space equation `Q_f * v = v`. -/
theorem isFixedSpaceKernelVector_iff_berlekampMatrix_mulVec_eq
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] (v : Vector (ZMod64 p) (basisSize f)) :
    IsFixedSpaceKernelVector f hmonic v ↔
      @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v = v := by
  unfold IsFixedSpaceKernelVector
  dsimp only [fixedSpaceMatrix]
  letI : Lean.Grind.Ring (ZMod64 p) := inst.toRing
  change
    @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0)
        (Matrix.ofFn fun i j =>
          @HSub.hSub (ZMod64 p) (ZMod64 p) (ZMod64 p)
            (@instHSub (ZMod64 p) inst.toSub) (berlekampMatrix f hmonic)[i][j]
            (if i = j then
              @OfNat.ofNat (ZMod64 p) 1 (inst.toCommSemiring.toSemiring.ofNat 1)
            else
              @OfNat.ofNat (ZMod64 p) 0 (inst.toCommSemiring.toSemiring.ofNat 0))) v =
      @OfNat.ofNat (Vector (ZMod64 p) (basisSize f)) 0
        (@Zero.toOfNat0 (Vector (ZMod64 p) (basisSize f))
          (@Vector.instZero (ZMod64 p) (basisSize f)
            (@Zero.ofOfNat0 (ZMod64 p)
              (@Lean.Grind.Semiring.ofNat (ZMod64 p) inst.toCommSemiring.toSemiring 0)))) ↔
    @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v = v
  have hsub :
      @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
          inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
          (inst.toCommSemiring.toSemiring.ofNat 0)
          (Matrix.ofFn fun i j =>
            @HSub.hSub (ZMod64 p) (ZMod64 p) (ZMod64 p)
              (@instHSub (ZMod64 p) inst.toSub) (berlekampMatrix f hmonic)[i][j]
              (if i = j then
                @OfNat.ofNat (ZMod64 p) 1 (inst.toCommSemiring.toSemiring.ofNat 1)
              else
                @OfNat.ofNat (ZMod64 p) 0 (inst.toCommSemiring.toSemiring.ofNat 0))) v =
        @HSub.hSub (Vector (ZMod64 p) (basisSize f))
          (Vector (ZMod64 p) (basisSize f)) (Vector (ZMod64 p) (basisSize f))
          (@instHSub (Vector (ZMod64 p) (basisSize f))
            (@Vector.instSub (ZMod64 p) (basisSize f) inst.toSub))
          (@Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
            inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
            (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v) v :=
    Matrix.sub_identity_mulVec (berlekampMatrix f hmonic) v
  rw [hsub]
  exact vector_sub_eq_zero_iff_eq
    (@Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
      inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
      (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v) v

/-- Polynomial-level executable Berlekamp kernel condition, by reading the
representative in the quotient basis used by `fixedSpaceMatrix`. -/
def IsFixedSpaceKernelPolynomial (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (g : FpPoly p) [Lean.Grind.Field (ZMod64 p)] : Prop :=
  IsFixedSpaceKernelVector f hmonic (coeffVector f g)

/-- Every vector returned by `fixedSpaceKernelVectors` satisfies the executable
fixed-space kernel condition. -/
theorem fixedSpaceKernelVectors_sound (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)]
    (k : Fin (basisSize f -
      Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))) :
    IsFixedSpaceKernelVector f hmonic ((fixedSpaceKernelVectors f hmonic).get k) := by
  unfold IsFixedSpaceKernelVector fixedSpaceKernelVectors
  exact Matrix.nullspace_sound (fixedSpaceMatrix (inst := inst.toRing) f hmonic) k

/-- Every polynomial representative returned by `fixedSpaceKernel` satisfies the
executable fixed-space kernel condition. -/
theorem fixedSpaceKernel_sound (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)]
    (k : Fin (basisSize f -
      Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))) :
    IsFixedSpaceKernelPolynomial f hmonic ((fixedSpaceKernel f hmonic).get k) := by
  unfold IsFixedSpaceKernelPolynomial fixedSpaceKernel
  rw [Vector.get_ofFn, coeffVector_vectorToPoly]
  exact fixedSpaceKernelVectors_sound f hmonic k

/-- Every vector satisfying the executable fixed-space kernel condition is a
linear combination of the public nullspace-basis matrix for `Q_f - I`. -/
theorem fixedSpaceKernelVectors_complete (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] (v : Vector (ZMod64 p) (basisSize f)) :
    IsFixedSpaceKernelVector f hmonic v →
      ∃ c : Vector (ZMod64 p)
          (basisSize f -
            Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)),
        @Matrix.mulVec (ZMod64 p) (basisSize f)
            (basisSize f -
              Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))
            inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
            (inst.toCommSemiring.toSemiring.ofNat 0)
            (Matrix.nullspaceBasisMatrix
              (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) c = v := by
  intro hv
  exact Matrix.nullspace_complete (fixedSpaceMatrix (inst := inst.toRing) f hmonic) v hv

/-- Polynomial representatives satisfying the executable fixed-space kernel
condition have coefficient vectors in the span of the nullspace basis. -/
theorem fixedSpaceKernelPolynomial_coeffVector_complete (f : FpPoly p)
    (hmonic : DensePoly.Monic f) [inst : Lean.Grind.Field (ZMod64 p)] (g : FpPoly p) :
    IsFixedSpaceKernelPolynomial f hmonic g →
      ∃ c : Vector (ZMod64 p)
          (basisSize f -
            Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)),
        @Matrix.mulVec (ZMod64 p) (basisSize f)
            (basisSize f -
              Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))
            inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
            (inst.toCommSemiring.toSemiring.ofNat 0)
            (Matrix.nullspaceBasisMatrix
              (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) c = coeffVector f g := by
  intro hg
  exact fixedSpaceKernelVectors_complete f hmonic (coeffVector f g) hg

end Berlekamp

end Hex
