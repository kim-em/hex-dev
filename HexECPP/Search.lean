/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.CM
public import HexPrimality.Construction

public section

/-!
# Bounded native ECPP search

One deterministic allocation survives every recursive failure and retry.
Factor work is reserved in bounded attempt packages: a leaf call reserves 64
attempts and an order call reserves four. The fixed profiles below also bound
trial division, subsets, worklists, witness sampling and per-attempt work;
unused reservations are never refunded. Root calls execute at most a quadratic
number of modular operations in the admitted bit size; scalar work counts the
maximum additions in the existing bit schedule. Exhaustion is not a verdict
of compositeness. Only raw subject-bound checked certificates are returned.
-/

namespace Hex.ECPP

inductive Resource where
  | inputBits | depth | candidates | roots | nonresidues | points
  | factorWork | scalarWork | outputBits | memo | portfolio
deriving Repr, BEq, DecidableEq

structure SearchBudget where
  maxBits : Nat := 256
  maxDepth : Nat := 32
  maxCandidates : Nat := 2048
  maxRoots : Nat := 8192
  maxNonresidues : Nat := 4096
  maxPoints : Nat := 4096
  maxFactorWork : Nat := 32768
  maxScalarWork : Nat := 1000000
  maxOutputBits : Nat := 2000000
  maxMemo : Nat := 128
  /-- Local retries are also charged to the shared allocations. -/
  pointRetries : Nat := 8
  nonresidueRetries : Nat := 64
deriving Repr

/-- Fixed per-attempt ceiling for terminal construction. It is deliberately
smaller than the full `primality?` route used by capability comparisons. -/
def leafBudget : Hex.Nat.ConstructionBudget := {
  maxBits := 256
  maxDepth := 8
  maxAttempts := 64
  maxSubsets := 32
  maxFactors := 16
  factor := {
    primeBudget := { rhoRestarts := 1, rhoSteps := 2048 }
    primeFuel := 8
    factorFuel := 16
    smoothBounds := [64, 512], smoothBases := [2] } }

/-- Fixed partial-factor package for one CM order. -/
def orderBudget : Hex.Nat.FactorSearchBudget := {
  primeBudget := { rhoRestarts := 1, rhoSteps := 2048 }
  primeFuel := 1
  factorFuel := 16
  attemptLimit := some 4
  smoothBounds := [64, 512]
  smoothBases := [2] }

structure SearchError where
  subject : Nat
  resource : Resource
deriving Repr

structure SearchStats where
  candidates : Nat := 0
  roots : Nat := 0
  nonresidues : Nat := 0
  points : Nat := 0
  factorWork : Nat := 0
  scalarWork : Nat := 0
  /-- Checked proposals rejected when their recursive child could not be built. -/
  backtracks : Nat := 0
  /-- First unresolved local branch, retained when the portfolio is exhausted. -/
  unresolved : Option SearchError := none
deriving Repr

structure SearchState where
  rand : Hex.Rand
  stats : SearchStats := {}
  /-- Only successes are cached; a failed branch may depend on remaining depth. -/
  memo : List Cert := []
deriving Repr

abbrev SearchM := ExceptT SearchError (StateM SearchState)

private def fail (n : Nat) (resource : Resource) : SearchM α := throw ⟨n, resource⟩

/-- Charge before running any work; no backtracking restores counters. -/
def charge (budget : SearchBudget) (n : Nat) (resource : Resource)
    (amount : Nat := 1) : SearchM Unit := do
  let s ← get
  let (used, limit) := match resource with
    | .candidates => (s.stats.candidates, budget.maxCandidates)
    | .roots => (s.stats.roots, budget.maxRoots)
    | .nonresidues => (s.stats.nonresidues, budget.maxNonresidues)
    | .points => (s.stats.points, budget.maxPoints)
    | .factorWork => (s.stats.factorWork, budget.maxFactorWork)
    | .scalarWork => (s.stats.scalarWork, budget.maxScalarWork)
    | _ => (0, 0)
  if used + amount > limit then fail n resource
  modify fun s => { s with stats := match resource with
    | .candidates => { s.stats with candidates := used + amount }
    | .roots => { s.stats with roots := used + amount }
    | .nonresidues => { s.stats with nonresidues := used + amount }
    | .points => { s.stats with points := used + amount }
    | .factorWork => { s.stats with factorWork := used + amount }
    | .scalarWork => { s.stats with scalarWork := used + amount }
    | _ => s.stats }

/-- Fixed-width draws need no rejection loop. This is proposal generation,
not a claim of uniform randomness. Every draw advances the shared stream. -/
private def draw (n : Nat) : SearchM Nat := do
  let s ← get
  let (x, r) := s.rand.words ((HexArith.bitLength n + 63) / 64)
  modify fun s => { s with rand := r }
  return x % n

private def nonresidue (budget : SearchBudget) (n : Nat) (sextic : Bool) :
    SearchM (Option Nat) := do
  for _ in [:budget.nonresidueRetries] do
    charge budget n .nonresidues
    let g ← draw n
    if (inverse? n g).isSome && CM.symbol g n == -1 &&
        HexArith.powMod g ((n - 1) / 2) n == n - 1 &&
        (!sextic || HexArith.powMod g ((n - 1) / 3) n != 1) then return some g
  return none

private def sqrt (budget : SearchBudget) (n z a : Nat) : SearchM (Option Nat) := do
  charge budget n .roots
  return CM.sqrt? n z a

private def scalar (budget : SearchBudget) (n a k : Nat) (P : Point) :
    SearchM (Option (Point × List Nat)) := do
  let work := 2 * HexArith.bitLength k
  charge budget n .scalarWork work
  return (proposeScalar { defaultImportBudget with
    maxScalarBits := budget.maxBits + 2, maxInverseOps := work } n a k P).toOption

private def leaf (budget : SearchBudget) (depth n : Nat) : SearchM (Option Cert) := do
  charge budget n .factorWork leafBudget.maxAttempts
  let r := (← get).rand
  match Hex.Nat.Construction.run n r
      { leafBudget with maxDepth := min leafBudget.maxDepth depth } with
  | .ok result =>
      modify fun s => { s with rand := result.rand }
      let c := Cert.base result.cert.raw
      return if checkAt n c then some c else none
  | .error error =>
      modify fun s => { s with rand := error.rand }
      return none

private def factors (budget : SearchBudget) (n m : Nat) : SearchM (List Nat) := do
  charge budget n .factorWork 4
  let result := Hex.Nat.Construction.factorSearch orderBudget m (← get).rand
  modify fun s => { s with rand := result.rand }
  let qs := result.raw.residual :: result.raw.factors.map Prod.fst
  return (qs.filter fun q => 2 ≤ q && q < n && m % q == 0 && sizeBound n q &&
    Hex.Nat.isProbablePrime q).mergeSort (· ≤ ·)

/-- Bit size of literal data, counting constructors as one bit as well.
This includes the entire embedded terminal certificate. -/
def primeBits : Nat → Hex.Nat.PrimeCert → Nat
  | 0, _ => 2000001
  | _ + 1, .small n => 1 + HexArith.bitLength n
  | fuel + 1, .pock n fs => 1 + HexArith.bitLength n +
      (fs.map fun (a, e, c) => HexArith.bitLength a + HexArith.bitLength e + primeBits fuel c).sum
  | fuel + 1, .pock3 n s r t fs => 1 + ([n, s, r, t].map HexArith.bitLength).sum +
      (fs.map fun (a, e, c) => HexArith.bitLength a + HexArith.bitLength e + primeBits fuel c).sum
  | fuel + 1, .pock3Sieve n s r t k fs => 1 + ([n, s, r, t, k].map HexArith.bitLength).sum +
      (fs.map fun (a, e, c) => HexArith.bitLength a + HexArith.bitLength e + primeBits fuel c).sum

def certBits : Cert → Nat
  | .base c => 1 + primeBits (leafBudget.maxDepth + 1) c
  | .step n a b x y d ws child => 1 + ([n, a, b, x, y, d].map HexArith.bitLength).sum +
      (ws.map fun w => 1 + HexArith.bitLength w).sum + certBits child

/-- Maximum scalar additions performed by a complete checker replay. -/
def replayWork : Cert → Nat
  | .base _ => 0
  | .step _ _ _ _ _ _ _ child => 2 * HexArith.bitLength child.subject + replayWork child

private def remember (budget : SearchBudget) (n : Nat) (c : Cert) : SearchM Cert := do
  if certBits c > budget.maxOutputBits then fail n .outputBits
  if (← get).memo.length >= budget.maxMemo then fail n .memo
  modify fun s => { s with memo := c :: s.memo }
  return c

private structure Proposal where
  a : Nat
  b : Nat
  x : Nat
  y : Nat
  discrInv : Nat
  inverses : List Nat

private def point (budget : SearchBudget) (n q cofactor z a b : Nat) :
    SearchM (Option Proposal) := do
  let some discrInv := inverse? n (4 * a * a * a + 27 * b * b) | return none
  for _ in [:budget.pointRetries] do
    charge budget n .points
    let x ← draw n
    let some y ← sqrt budget n z ((x * x * x + a * x + b) % n) | continue
    if !onCurve n a b x y then continue
    let some (.affine qx qy, _) ← scalar budget n a cofactor (.affine x y) | continue
    let some (.infinity, ws) ← scalar budget n a q (.affine qx qy) | continue
    charge budget n .scalarWork (2 * HexArith.bitLength q)
    if checkStep n a b qx qy discrInv ws q then
      return some ⟨a, b, qx, qy, discrInv, ws⟩
  return none

/-- Structurally bounded recursion; failure of a child resumes the parent's
remaining CM orders, without resetting any allocation or random state. -/
def search (budget : SearchBudget) : Nat → Nat → SearchM (Option Cert)
  | 0, n => do
      modify fun s => { s with stats := { s.stats with unresolved := some ⟨n, .depth⟩ } }
      return none
  | depth + 1, n => do
      if HexArith.bitLength n > budget.maxBits then fail n .inputBits
      if let some c := (← get).memo.find? (fun c => c.subject == n) then return some c
      if let some c ← leaf budget (depth + 1) n then return some (← remember budget n c)
      if n ≤ 3 || n % 2 == 0 || n % 3 == 0 || !Hex.Nat.isProbablePrime n then return none
      let some z ← nonresidue budget n false | return none
      for inv in CM.portfolio do
        charge budget n .candidates
        let k := if inv.d % 4 == 0 then inv.d / 4 else inv.d
        let some root ← sqrt budget n z (modSub n 0 k) | continue
        let norms := [CM.norm? n inv.d root, CM.norm? n inv.d (modSub n 0 root)]
        let some (t, v) := norms.findSome? id | continue
        let g ← if inv.d == 3 then nonresidue budget n true else pure (some z)
        let some g := g | continue
        for trace in CM.traces inv.d t v do
          charge budget n .candidates
          let m : Int := (n : Int) + 1 - trace
          if m ≤ 0 then continue
          let m := m.toNat
          for q in ← factors budget n m do
            let cofactor := m / q
            for (a, b) in CM.curves n inv g do
              let some proposal ← point budget n q cofactor z a b | continue
              if let some child ← search budget depth q then
                let c := Cert.step n a b proposal.x proposal.y proposal.discrInv
                  proposal.inverses child
                charge budget n .scalarWork (replayWork c)
                if checkAt n c then return some (← remember budget n c)
              modify fun s => { s with stats := { s.stats with backtracks := s.stats.backtracks + 1 } }
              -- Different points on this curve have the same child obligation.
              break
      modify fun s => { s with stats := { s.stats with
        unresolved := s.stats.unresolved.or (some ⟨n, .portfolio⟩) } }
      return none

structure SearchResult where
  result : Except SearchError Cert
  state : SearchState
deriving Repr

/-- Native production accepts only the subject, seed and resource allocation.
Every success is complete raw certificate data accepted by `checkAt`. -/
def produce (n seed : Nat) (budget : SearchBudget := {}) : SearchResult :=
  let computation : SearchM (Option Cert) := do
    let result ← search budget budget.maxDepth n
    if let some c := result then
      charge budget n .scalarWork (replayWork c)
    return result
  let (result, state) := computation.run.run { rand := Hex.Rand.ofSeed seed }
  let result := match result with
    | .error e => .error e
    | .ok (some c) => if checkAt n c then .ok c else .error ⟨n, .portfolio⟩
    | .ok none => .error (state.stats.unresolved.getD ⟨n, .portfolio⟩)
  ⟨result, state⟩

private def rows : Cert → List String
  | .base _ => []
  | .step n a _ x y _ _ child =>
      s!"[{n},{(n : Int) + 1 - child.subject},1,{a},[{x},{y}]]" :: rows child

/-- Freeze only replay inputs. Each row uses the already found q-order point
and cofactor one, so conversion need not repeat any CM or factor search. -/
def frozenRows (c : Cert) : String :=
  match rows c with
  | [] => toString c.subject
  | rows => "[" ++ String.intercalate "," rows ++ "]"

end Hex.ECPP
