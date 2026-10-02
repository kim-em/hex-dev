/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman, Kim Morrison
-/
import Determinant.Arithmetic
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness

/-! Experimental adaptation of Mathlib's Bird certificate evaluator. The same
recurrence and theorem applications build a shared expression without polynomial
normalization. A separate final equality check includes the supplied target.
The recurrence below is adapted from Mathlib/Tactic/Determinant/Bird/Cert.lean.
-/
open Lean Meta Elab Tactic Qq Mathlib.Tactic.Ring
open Mathlib.Tactic.Determinant (Ctx reifyBirdDet)

namespace Determinant.Deferred

section

variable {u : Level} {α : Q(Type u)} {rα : Q(CommRing $α)}

meta structure Cert (rα : Q(CommRing $α)) where
  {subject : Q($α)}
  norm : Q($α)
  proof : Q($subject = $norm)
  isZero : Bool := false

meta def Cert.chainProof {lhs rhs : Q($α)} (c : Cert rα)
    (h : Q($lhs = $rhs)) : Cert rα :=
  have : $rhs =Q $c.subject := ⟨⟩
  { subject := lhs, norm := c.norm, proof := q(Eq.trans $h $c.proof), isZero := c.isZero }

meta structure CertCache (rα : Q(CommRing $α)) where
  entryCache : Std.HashMap (Nat × Nat) (Cert rα) := {}
  iterStepEntryCache : Std.HashMap (Nat × Nat × Nat) (Cert rα) := {}
  diagCache : Std.HashMap (Nat × Nat) (Cert rα) := {}

meta abbrev CertM (rα : Q(CommRing $α)) :=
  StateT (CertCache rα) (ReaderT (Ctx rα) Mathlib.Tactic.AtomM)

meta def zeroCertOfProof {lhs : Q($α)} (h : Q($lhs = 0)) : Cert rα :=
  { subject := lhs, norm := q(0), proof := h, isZero := true }

meta def zeroProdCert (x : Q($α)) (c : Cert rα) : MetaM (Cert rα) := do
  have : $c.norm =Q (0 : $α) := ⟨⟩
  return zeroCertOfProof q(Eq.trans (congrArg (fun y => $x * y) $c.proof) (mul_zero $x))

meta def certEval (e : Q($α)) : CertM rα (Cert rα) :=
  pure { subject := e, norm := e, proof := q(Eq.refl $e), isZero := e == q(0 : $α) }

meta def certAdd (a b : Cert rα) : CertM rα (Cert rα) :=
  pure {
    subject := q($a.subject + $b.subject)
    norm := q($a.norm + $b.norm)
    proof := q(congr (congrArg (fun x y => x + y) $a.proof) $b.proof) }

meta def certMul (a b : Cert rα) : CertM rα (Cert rα) :=
  pure {
    subject := q($a.subject * $b.subject)
    norm := q($a.norm * $b.norm)
    proof := q(congr (congrArg (fun x y => x * y) $a.proof) $b.proof) }

meta def certNeg (a : Cert rα) : CertM rα (Cert rα) :=
  pure { subject := q(-$a.subject), norm := q(-$a.norm), proof := q(congrArg (fun x => -x) $a.proof) }

meta section
/-- Certify the sign factor `(-1)^k` from `BirdDet.birdDet_eq`. -/
def certBirdSign (k : ℕ) : CertM rα (Cert rα) := do
  certEval q((-1 : $α) ^ $k)

/-- Certify one matrix entry lookup `BirdDet.get n A i j`. -/
def certEntry (i j : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr := A, arrayEntries, ..} := ctx
  let lhs : Q($α) := q(BirdDet.get $dimLit $A $i $j)
  -- The index of the matrix entry (i, j) in arrayEntries
  let idx := dim * i + j
  let entry := arrayEntries.getD idx q(0)
  let ce ← certEval entry
  let getD : Q($α) := q(Array.getD $A ($dimLit * $i + $j) 0)
  let hGet : Q($lhs = $getD) := q(BirdDet.get_eq $dimLit $A $i $j)
  have : $getD =Q $entry := ⟨⟩
  let hGetD : Q($getD = $entry) := q(rfl)
  let cert := ce.chainProof q(Eq.trans $hGet $hGetD)
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

/-- Certify the stop branch of `BirdDet.sumFrom`.

This corresponds to the `else 0` branch of:

```
sumFrom n lo f = if lo < n then f lo + sumFrom n (lo + 1) f else 0
```

Throws a meta-level error if called with `lo` such that `lo < ctx.dimension`.
-/
def certSumFromStop (lo : ℕ) (f : Q(ℕ → $α)) : CertM rα (Cert rα) := do
  let ctx ← read
  if lo < ctx.dimension then
    throwError "certSumFromStop called with {lo} such that {lo} < {ctx.dimension}"
  have dimLit : Q(ℕ) := ctx.dimensionLit
  let hNot : Q(¬ $lo < $dimLit) ← mkDecideProofQ q(¬ $lo < $dimLit)
  return zeroCertOfProof q(BirdDet.sumFrom_stop $dimLit $lo $f $hNot)

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

mutual

/-- Certify an entry of `(BirdDet.stepEntry n A)^[t] (BirdDet.get n A)`. -/
partial def certIterStepEntry (t i j : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).iterStepEntryCache[(t, i, j)]? then
    return c
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let cert ← match t with
    -- The `t = 0` branch of `Function.iterate`.
    | 0 => do
      let ce ← certEntry i j
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
      let entryCert ← certEntry i j
      let diagProdCert ←
        -- If `get n A i j = 0` then we can skip computation of
        --  `-(sumFrom n (i + 1) fun k => F_t k k)`
        if entryCert.isZero then
          zeroProdCert negDiagSum entryCert
        else do
          let diagSumCert ← certDiag t' (i + 1)
          let negDiagSumCert ← certNeg diagSumCert
          certMul negDiagSumCert entryCert
      -- Second summand in one `BirdDet.stepEntry` application:
      --   sumFrom n (i + 1) fun k => F_t i k * get n A k j
      let tailSumCert ← certTail t' i j (i + 1)
      let rhsCert ← certAdd diagProdCert tailSumCert
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
partial def certDiag (t lo : ℕ) : CertM rα (Cert rα) := do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterStepEntry t) k k)
  let cert ←
    if lo < ctx.dimension
    then do
      let headCert := certIterStepEntry t lo lo
      let tailCert := certDiag t (lo + 1)
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
partial def certTail (t i j lo : ℕ) : CertM rα (Cert rα) := do
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
      let entryCert ← certEntry lo j
      -- If `get n A lo j = 0` then we can skip computation of
      --  `(stepEntry n A)^[t] F i lo`
      if entryCert.isZero
      then
        zeroProdCert
          q($(ctx.iterStepEntry t) $i $lo)
          entryCert
      else do
        let iterateCert ← certIterStepEntry t i lo
        certMul iterateCert entryCert
    let tailCert := certTail t i j (lo + 1)
    certSumFromStep
      lo
      tailSummand
      headCert
      tailCert
  else
    certSumFromStop lo tailSummand

end

/-- Certify a `BirdDet.birdDet n A` call. -/
def certBirdDet : CertM rα (Cert rα) := do
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
    let ci ← certIterStepEntry k 0 0
    let cm ← certMul cs ci
    have kLit := mkNatLitQ k
    have : $dimLit =Q $kLit + 1 := ⟨⟩
    let hn : Q($dimLit = $kLit + 1) := q(rfl)
    let h := q(BirdDet.birdDet_eq $dimLit $kLit $arrayExpr $hn)
    return cm.chainProof h

end
end

/-- Apply the universal Bird correctness theorem to a literal matrix, then
normalize the resulting expression and the supplied target in one atom context.
No determinant tactic or fallback is invoked. -/
meta def run (cache : Bool) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let some (_, left, right) := (← instantiateMVars (← g.getType)).eq?
    | throwError "expected an equality"
  let ⟨u, α, left⟩ ← inferTypeQ' left
  let ~q(@Matrix.det (Fin $n) _ _ _ $rα $matrix) := left
    | throwError "expected a determinant over Fin"
  let some dim ← getNatValue? n | throwError "expected a literal dimension"
  let ~q(Matrix.of $rows) := matrix | throwError "expected a literal matrix"
  let (matrixRows, _, _) ← Matrix.matchVecConsPrefix n rows
  unless matrixRows.length == dim do throwError "row count mismatch"
  let entries ← matrixRows.flatMapM fun row => do
    let (es, _, _) ← Matrix.matchVecConsPrefix n row
    unless es.length == dim do throwError "column count mismatch"
    pure es
  let xs ← mkListLit α entries
  have xs : Q(List $α) := xs
  have matrix : Q(Matrix (Fin $n) (Fin $n) $α) := matrix
  let arrayExpr : Q(Array $α) := q(List.toArray $xs)
  have : (List.ofFn fun k : Fin ($n * $n) ↦ $matrix k.divNat k.modNat) =Q $xs := ⟨⟩
  let hlist : Q(List.ofFn (fun k : Fin ($n * $n) ↦ $matrix k.divNat k.modNat) = $xs) := q(rfl)
  let hArray := q($hlist ▸ List.toArray_ofFn)
  let detEqBirdDet := q($hArray ▸ Matrix.ofArray_ofFn $matrix ▸ BirdDet.det_eq_birdDet
    (Array.ofFn fun k : Fin ($n * $n) ↦ $matrix k.divNat k.modNat) Array.size_ofFn)
  let reified ← reifyBirdDet q(BirdDet.birdDet $n $arrayExpr)
  let c ← certBirdDet (rα := reified.rα) |>.run' {} |>.run reified.ctx |>.run .reducible
  have norm : Q($α) := c.norm
  have cp : Q(BirdDet.birdDet $n $arrayExpr = $norm) := c.proof
  have p : Q(Matrix.det $matrix = $norm) := q(Eq.trans $detEqBirdDet $cp)
  have right : Q($α) := right
  let sub : Q($norm = $right) ← mkFreshExprSyntheticOpaqueMVar q($norm = $right)
  g.assign q(Eq.trans $p $sub)
  setGoals [sub.mvarId!]
  if cache then evalTactic (← `(tactic| cached_ring))
  else evalTactic (← `(tactic| plain_ring))

elab "deferred_bird" : tactic => run false
elab "shared_bird" : tactic => run true

end Determinant.Deferred
