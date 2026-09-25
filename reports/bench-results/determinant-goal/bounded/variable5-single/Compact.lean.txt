/-
Copyright (c) 2026 Paul Cadman, Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman, Kim Morrison
-/
import Mathlib.Tactic.Determinant.Bird.Cert
import Determinant.Steps
import Determinant.Coefficients
import Determinant.Division
import Determinant.Bounded

/-! Controlled adaptation of Mathlib's Bird certificate recurrence. Arithmetic
proofs use small congruence lemmas; an optional control combines recurrence
unfolding equalities. The recurrence, pruning and cache keys are unchanged. The optional
coefficient control changes scalar division normalization only. -/

open Lean Meta Qq Mathlib.Tactic.Ring Mathlib.Tactic.Determinant
namespace Determinant.Compact

section
variable {R : Type*} [CommRing R] {a b x y z : R}

theorem add_eq (ha : a = x) (hb : b = y) (h : x + y = z) : a + b = z := by
  rw [ha, hb, h]

theorem mul_eq (ha : a = x) (hb : b = y) (h : x * y = z) : a * b = z := by
  rw [ha, hb, h]

theorem neg_eq (ha : a = x) (h : -x = z) : -a = z := by
  rw [ha, h]
end

variable {u : Level} {α : Q(Type u)} {rα : Q(CommRing $α)}

meta def certAdd (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalAdd ctx.rc rcℕ a.val b.val
  have : $c.subject =Q $a.norm + $b.norm := ⟨⟩
  have hc : Q($a.norm + $b.norm = $c.norm) := c.proof
  return {
    subject := q($a.subject + $b.subject)
    isZero := c.isZero
    result := {
      expr := c.norm
      val := c.val
      proof := q(add_eq $a.proof $b.proof $hc) } }

meta def certMul (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalMul ctx.rc rcℕ a.val b.val
  have : $c.subject =Q $a.norm * $b.norm := ⟨⟩
  have hc : Q($a.norm * $b.norm = $c.norm) := c.proof
  return {
    subject := q($a.subject * $b.subject)
    isZero := c.isZero
    result := {
      expr := c.norm
      val := c.val
      proof := q(mul_eq $a.proof $b.proof $hc) } }

meta def certNeg (a : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalNeg ctx.rc rα a.val
  have : $c.subject =Q -$a.norm := ⟨⟩
  have hc : Q(-$a.norm = $c.norm) := c.proof
  return {
    subject := q(-$a.subject)
    isZero := c.isZero
    result := {
      expr := c.norm
      val := c.val
      proof := q(neg_eq $a.proof $hc) } }

meta section
/-- Certify the sign factor `(-1)^k` from `BirdDet.birdDet_eq`. -/
def certBirdSign (k : ℕ) : CertM rα (Cert rα) := do
  certEval q((-1 : $α) ^ $k)

/-- Certify the step branch of `BirdDet.sumFrom`.

This corresponds to the `lo < n` branch of:

```
sumFrom n lo f = if lo < n then f lo + sumFrom n (lo + 1) f else 0
```

Throws a meta-level error if called with `lo` such that `¬ lo < ctx.dimension`.
-/
def certSumFromStep
    (lo : ℕ) (f : Q(ℕ → $α))
    (headCert tailCert : CertM rα (Cert rα)) : CertM rα (Cert rα) := do
  let ctx ← read
  unless lo < ctx.dimension do
    throwError "certSumFromStep called with {lo} such that ¬ {lo} < {ctx.dimension}"
  have dim : Q(ℕ) := ctx.dimensionLit
  let hLt : Q($lo < $dim) ← mkDecideProofQ q($lo < $dim)
  let sumCert ← certAdd (← headCert) (← tailCert)
  return sumCert.chainProof q(BirdDet.sumFrom_step $dim $lo $f $hLt)

def coeffEntry (coeff division bounded : Bool) (i j : ℕ) : CertM rα (Cert rα) := do
  unless coeff do return ← certEntry i j
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr := A, arrayEntries, ..} := ctx
  let lhs : Q($α) := q(BirdDet.get $dimLit $A $i $j)
  -- The index of the matrix entry (i, j) in arrayEntries
  let idx := dim * i + j
  let entry := arrayEntries.getD idx q(0)
  let ce ← if bounded then toCert <$> Bounded.eval rcℕ ctx.rc ctx.cα entry
    else if division then toCert <$> Division.eval rcℕ ctx.rc ctx.cα entry
    else toCert <$> Coefficients.eval rcℕ ctx.rc ctx.cα entry
  let getD : Q($α) := q(Array.getD $A ($dimLit * $i + $j) 0)
  let hGet : Q($lhs = $getD) := q(BirdDet.get_eq $dimLit $A $i $j)
  have : $getD =Q $entry := ⟨⟩
  let hGetD : Q($getD = $entry) := q(rfl)
  let cert := ce.chainProof q(Eq.trans $hGet $hGetD)
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

mutual

/-- Certify an entry of `(BirdDet.stepEntry n A)^[t] (BirdDet.get n A)`. -/
partial def certIterStepEntry (fused coeff division bounded : Bool) (t i j : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).iterStepEntryCache[(t, i, j)]? then
    return c
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let cert ← match t with
    -- The `t = 0` branch of `Function.iterate`.
    | 0 => do
      let ce ← coeffEntry coeff division bounded i j
      if fused then
        pure (ce.chainProof q(Steps.iter_zero $dimLit $A $i $j))
      else do
        let hIter := q(Function.iterate_zero_apply
          (BirdDet.stepEntry $dimLit $A) (BirdDet.get $dimLit $A))
        let h := q(congrArg (fun F : ℕ → ℕ → $α => F $i $j) $hIter)
        pure (ce.chainProof h)
    -- The `t = t' + 1` branch of `Function.iterate`.
    | t' + 1 => do
      -- First summand in one `BirdDet.stepEntry` application:
      --   -(sumFrom n (i + 1) fun k => F_t k k) * get n A i j
      let diagSummand := q(fun k => $(ctx.iterStepEntry t') k k)
      let negDiagSum := q(-$(ctx.sumFrom (i + 1) diagSummand))
      let entryCert ← coeffEntry coeff division bounded i j
      let diagProdCert ←
        -- If `get n A i j = 0` then we can skip computation of
        --  `-(sumFrom n (i + 1) fun k => F_t k k)`
        if entryCert.isZero then
          zeroProdCert negDiagSum entryCert
        else do
          let diagSumCert ← certDiag fused coeff division bounded t' (i + 1)
          let negDiagSumCert ← certNeg diagSumCert
          certMul negDiagSumCert entryCert
      -- Second summand in one `BirdDet.stepEntry` application:
      --   sumFrom n (i + 1) fun k => F_t i k * get n A k j
      let tailSumCert ← certTail fused coeff division bounded t' i j (i + 1)
      let rhsCert ← certAdd diagProdCert tailSumCert
      if fused then
        pure (rhsCert.chainProof q(Steps.iter_step $dimLit $A $t' $i $j))
      else do
        let hStep := q(BirdDet.stepEntry_eq $dimLit $A $(ctx.iterStepEntry t') $i $j)
        let stepCert := rhsCert.chainProof hStep
        let hIter := q(Function.iterate_succ_apply'
          (BirdDet.stepEntry $dimLit $A) $t' (BirdDet.get $dimLit $A))
        let h := q(congrArg (fun F : ℕ → ℕ → $α ↦ F $i $j) $hIter)
        pure (stepCert.chainProof h)
  modify fun s =>
    {s with iterStepEntryCache := s.iterStepEntryCache.insert (t, i, j) cert}
  return cert


/-- Certify the diagonal tail sum in one `BirdDet.stepEntry` application:

```
sumFrom n (i + 1) fun k => (stepEntry n A)^[t] F k k)
```
-/
partial def certDiag (fused coeff division bounded : Bool) (t lo : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterStepEntry t) k k)
  let cert ←
    if lo < ctx.dimension
    then do
      let headCert := certIterStepEntry fused coeff division bounded t lo lo
      let tailCert := certDiag fused coeff division bounded t (lo + 1)
      certSumFromStep
        lo
        diagonalSummand
        headCert
        tailCert
    else
      certSumFromStop lo diagonalSummand
  modify fun s => {s with diagCache := s.diagCache.insert (t, lo) cert}
  return cert

/-- Certify the upper-tail sum in one `BirdDet.stepEntry` application:

```
sumFrom n (i + 1) fun k => (stepEntry n A)^[t] F i k * get n A k j
```
-/
partial def certTail (fused coeff division bounded : Bool) (t i j lo : ℕ) : CertM rα (Cert rα) := do
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let tailSummand :=
    q(fun k =>
      $(ctx.iterStepEntry t) $i k *
        BirdDet.get $dimLit $A k $j)
  if lo < ctx.dimension
  then do
    -- headCert certifies `(stepEntry n A)^[t] F i lo * get n A lo j`
    let headCert := do
      let entryCert ← coeffEntry coeff division bounded lo j
      -- If `get n A lo j = 0` then we can skip computation of
      --  `(stepEntry n A)^[t] F i lo`
      if entryCert.isZero
      then
        zeroProdCert
          q($(ctx.iterStepEntry t) $i $lo)
          entryCert
      else do
        let iterateCert ← certIterStepEntry fused coeff division bounded t i lo
        certMul iterateCert entryCert
    let tailCert := certTail fused coeff division bounded t i j (lo + 1)
    certSumFromStep
      lo
      tailSummand
      headCert
      tailCert
  else
    certSumFromStop lo tailSummand

end

/-- Certify a `BirdDet.birdDet n A` call. -/
def certBirdDet (fused : Bool := false) (coeff : Bool := false) (division : Bool := false) (bounded : Bool := false) : CertM rα (Cert rα) := do
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr, ..} := ctx
  if dim == 0
  then
    let ce ← certEval q(1 : $α)
    have : $dimLit =Q 0 := ⟨⟩
    have A : Q(Array $α) := arrayExpr
    let h := q(BirdDet.birdDet_zero $A)
    return ce.chainProof h
  else
    -- The non-zero `BirdDet.birdDet_eq` branch matches `k + 1`
    -- so we set k := `ctx.dimension - 1`.
    let k := dim - 1
    let cs ← certBirdSign k
    let ci ← certIterStepEntry fused coeff division bounded k 0 0
    let cm ← certMul cs ci
    have kLit := mkNatLitQ k
    have : $dimLit =Q $kLit + 1 := ⟨⟩
    let hn : Q($dimLit = $kLit + 1) := q(rfl)
    let h := q(BirdDet.birdDet_eq $dimLit $kLit $arrayExpr $hn)
    return cm.chainProof h

end
end Determinant.Compact
