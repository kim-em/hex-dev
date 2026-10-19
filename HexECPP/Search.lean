/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.CM.Roots
public import HexPrimality.Construction

public section

/-!
# Searching for elliptic curve primality certificates

`produce n seed` tries to construct a certificate proving `n` prime. It uses
complex multiplication to propose curves and orders, partially factors a
proposed order `m = s*q`, and tries to obtain a point of order `q` by multiplying
another point by `s`. It then recursively constructs a certificate for `q`.
Small-prime and Pocklington certificates can end the chain.

Search has finite limits shared across all attempted curves and recursive
calls. An unsuccessful branch does not refund its work. Failure to find a
certificate does not imply compositeness. Every successful result passes
`checkAt n`; a `Nat.Prime n` theorem additionally uses the soundness result
from `HexECPPTheory`. Proposed orders and random choices are not proof
assumptions.
-/

namespace Hex.ECPP

/-- The work limit or unsuccessful search stage reported when certificate
search cannot complete a primality proof. -/
inductive Resource where
  | inputBits | depth | candidates | roots | nonresidues | points
  | factorWork | scalarWork | outputBits | memo | portfolio
  | screening | nonresidueRetries | pointRetries | rows | nodes | factorPolicy
  | polynomialWork | rootWork
deriving Repr, BEq, DecidableEq

/-- Limits for finding an elliptic curve primality certificate. The counters
bound the entire search, including recursive proofs of auxiliary primes;
trying another curve does not restore work already spent. Retry limits also
bound the number of choices tried on each curve. Neither a bit-length limit
nor the other allowances guarantee that search succeeds for every prime. -/
structure SearchBudget where
  /-- Maximum subject bit length. -/
  maxBits : Nat := 256
  /-- Maximum recursive certificate depth. -/
  maxDepth : Nat := 32
  /-- Shared discriminant and order candidate allowance. -/
  maxCandidates : Nat := 2048
  /-- Shared modular-root call allowance. -/
  maxRoots : Nat := 8192
  /-- Shared nonresidue-draw allowance. -/
  maxNonresidues : Nat := 4096
  /-- Shared point-draw allowance. -/
  maxPoints : Nat := 4096
  /-- Shared reserved factor-attempt packages. -/
  maxFactorWork : Nat := 32768
  /-- Shared maximum scalar additions, including checker replays. -/
  maxScalarWork : Nat := 1000000
  /-- Maximum literal bits per retained certificate. -/
  maxOutputBits : Nat := 2000000
  /-- Maximum retained successful certificates. -/
  maxMemo : Nat := 128
  /-- Local retries are also charged to the shared allocations. -/
  pointRetries : Nat := 8
  /-- Local nonresidue draws, also charged to the shared allowance. -/
  nonresidueRetries : Nat := 64
  /-- Select a finite terminal package; omission retains the 256-bit policy. -/
  terminal : Option Hex.Nat.ConstructionBudget := none
  /-- Select a finite order package; its attempt limit must be explicit. -/
  order : Option Hex.Nat.FactorSearchBudget := none
  /-- Public output limits include ancestral rows and embedded terminal nodes. -/
  maxRows : Option Nat := none
  /-- Total nodes include the ECPP base wrapper. -/
  maxNodes : Option Nat := none
  /-- Reject oversized candidates locally, retaining all charged work. -/
  backtrackOutput : Bool := false
  /-- Opt in to the attributed fixed linear/quadratic class polynomial table. -/
  extendedCM : Bool := false
  /-- Shared reserved polynomial-root modular operations. -/
  maxPolynomialWork : Nat := 16777216
  /-- Per-call modular-operation ceiling; closed-form roots need no splits. -/
  maxRootWork : Nat := 1048576
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

/-- Larger search policy for integers through 512 bits, with additional
fixed complex multiplication class polynomials. Select it explicitly;
`produce` defaults to the 256-bit policy. Search can still fail within this
size range. Use `public512Budget` when the result must fit the public proof
commands' certificate limits. -/
def native512Budget : SearchBudget := {
  maxBits := 512, maxDepth := 32, maxCandidates := 8192, maxRoots := 32768
  maxNonresidues := 16384, maxPoints := 16384, maxFactorWork := 131072
  maxScalarWork := 8000000, maxOutputBits := 8000000
  terminal := some { leafBudget with maxBits := 512 }
  order := some orderBudget
  backtrackOutput := true, extendedCM := true }

/-- The 512-bit search policy used by the public tactic and export command.
It restricts output to 20 elliptic rows and 32 total certificate nodes,
including the wrapper and all nodes of the last HexPrimality certificate. -/
def public512Budget : SearchBudget := {
  native512Budget with maxDepth := 21, maxRows := some 20, maxNodes := some 32 }

/-- Explicit output-bounded 256-bit allocation for mixed factor completion.
The ordinary producer and existing Native 256-bit policy retain their defaults. -/
def public256Budget : SearchBudget := {
  maxDepth := 21, maxRows := some 20, maxNodes := some 32
  backtrackOutput := true }

/-- An integer whose primality certificate was not found, together with the
work limit or search stage that stopped the attempt. -/
structure SearchError where
  /-- Integer whose primality certificate remains unfound. -/
  subject : Nat
  /-- Work limit or search stage responsible for stopping the search. -/
  resource : Resource
deriving Repr

/-- Cumulative charged work and backtracking diagnostics. -/
structure SearchStats where
  /-- Charged discriminant and order candidates. -/
  candidates : Nat := 0
  /-- Charged modular-root calls. -/
  roots : Nat := 0
  /-- Charged nonresidue draws. -/
  nonresidues : Nat := 0
  /-- Charged point draws. -/
  points : Nat := 0
  /-- Reserved factor-work units, never refunded. -/
  factorWork : Nat := 0
  /-- Reserved scalar additions, never refunded. -/
  scalarWork : Nat := 0
  /-- Checked proposals rejected when their recursive child could not be built. -/
  backtracks : Nat := 0
  /-- Terminal package invocations and their checked successes. -/
  terminalCalls : Nat := 0
  terminalSuccesses : Nat := 0
  /-- Terminal calls outside the selected package's subject limit. -/
  terminalBitRejects : Nat := 0
  /-- Last unproved terminal obligation, distinct from CM child failures. -/
  terminalObligation : Option Nat := none
  /-- Successful norm equations, orders and eligible large prime factors. -/
  norms : Nat := 0
  orders : Nat := 0
  largeFactors : Nat := 0
  /-- Checked elliptic step proposals, before recursive child construction. -/
  proposals : Nat := 0
  /-- Output candidates rejected after their search work was charged. -/
  outputRejects : Nat := 0
  /-- Actual last literal-bit count; `none` records traversal exhaustion. -/
  outputBits : Option Nat := none
  /-- Reserved modular-operation bounds for class polynomial roots. -/
  polynomialWork : Nat := 0
  /-- Checked j-roots admitted from the class polynomial table. -/
  polynomialRoots : Nat := 0
  /-- Retained failure. Smaller unresolved children and complete portfolios supersede local retries. -/
  unresolved : Option SearchError := none
  /-- Last local retry exhaustion, retained even when the final diagnosis is portfolio exhaustion. -/
  lastRetry : Option SearchError := none
deriving Repr

/-- The advanced random stream, cumulative counters and checked success memo. -/
structure SearchState where
  /-- Advanced deterministic random stream. -/
  rand : Hex.Rand
  /-- Cumulative counters and diagnostics; stateful callers can reset them independently of the memo. -/
  stats : SearchStats := {}
  /-- Only successes are cached; a failed branch may depend on remaining depth. -/
  memo : List Cert := []
deriving Repr

/-- Search errors preserve the advanced random stream, memo and charged work. -/
abbrev SearchM := ExceptT SearchError (StateM SearchState)

/-- Abort on a shared allocation failure without rolling back state. -/
private def fail (n : Nat) (resource : Resource) : SearchM α := throw ⟨n, resource⟩

/-- Retain local retry diagnostics separately; a smaller unresolved child takes priority over a local retry. -/
private def unresolved (n : Nat) (resource : Resource) : SearchM Unit :=
  modify fun s => { s with stats := { s.stats with
    lastRetry := if resource == .pointRetries || resource == .nonresidueRetries then
        some ⟨n, resource⟩ else s.stats.lastRetry
    unresolved := match s.stats.unresolved with
      | some e => if (e.resource == .pointRetries || e.resource == .nonresidueRetries) &&
          (n < e.subject || (n == e.subject &&
            (resource == .depth || resource == .screening || resource == .portfolio))) then
            some ⟨n, resource⟩ else some e
      | none => some ⟨n, resource⟩ } }

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
    | .polynomialWork => (s.stats.polynomialWork, budget.maxPolynomialWork)
    | _ => (0, 0)
  if used + amount > limit then fail n resource
  modify fun s => { s with stats := match resource with
    | .candidates => { s.stats with candidates := used + amount }
    | .roots => { s.stats with roots := used + amount }
    | .nonresidues => { s.stats with nonresidues := used + amount }
    | .points => { s.stats with points := used + amount }
    | .factorWork => { s.stats with factorWork := used + amount }
    | .scalarWork => { s.stats with scalarWork := used + amount }
    | .polynomialWork => { s.stats with polynomialWork := used + amount }
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
  unresolved n .nonresidueRetries
  return none

private def sqrt (budget : SearchBudget) (n z a : Nat) : SearchM (Option Nat) := do
  charge budget n .roots
  return CM.sqrt? n z a

/-- Charge a finite root call before evaluating any class polynomial. -/
private def invariants (budget : SearchBudget) (n z : Nat) (p : CM.ClassPolynomial) :
    SearchM (List CM.Invariant) := do
  if !budget.extendedCM then
    return match p.coefficients with
      | [c, 1] => [⟨p.d, -c⟩]
      | _ => []
  let work := CM.rootWork n p
  if work > budget.maxRootWork then
    unresolved n .rootWork
    return []
  charge budget n .roots
  charge budget n .polynomialWork work
  let roots := CM.roots? n z p
  modify fun s => { s with stats := { s.stats with
    polynomialRoots := s.stats.polynomialRoots + roots.length } }
  return roots.map fun (j : Nat) => ⟨p.d, (j : Int)⟩

private def scalar (budget : SearchBudget) (n a k : Nat) (P : Point) :
    SearchM (Option (Point × List Nat)) := do
  let work := 2 * HexArith.bitLength k
  charge budget n .scalarWork work
  return (proposeScalar { defaultImportBudget with
    maxScalarBits := budget.maxBits + 2, maxInverseOps := work } n a k P).toOption

private def leaf (budget : SearchBudget) (depth n : Nat) : SearchM (Option Cert) := do
  let allocation := budget.terminal.getD leafBudget
  charge budget n .factorWork allocation.maxAttempts
  modify fun s => { s with stats := { s.stats with
    terminalCalls := s.stats.terminalCalls + 1
    terminalBitRejects := s.stats.terminalBitRejects +
      (if HexArith.bitLength n > allocation.maxBits then 1 else 0) } }
  let r := (← get).rand
  match Hex.Nat.Construction.runTraced n r
      { allocation with maxDepth := min allocation.maxDepth depth } with
  | .ok result =>
      modify fun s => { s with rand := result.rand }
      let c := Cert.base result.cert.raw
      modify fun s => { s with stats := { s.stats with
        terminalSuccesses := s.stats.terminalSuccesses + 1 } }
      return if checkAt n c then some c else none
  | .error error =>
      modify fun s => { s with rand := error.rand, stats := { s.stats with
        terminalObligation := error.obligation } }
      return none

private def factors (budget : SearchBudget) (n m : Nat) : SearchM (List Nat) := do
  let allocation := budget.order.getD orderBudget
  let some attempts := allocation.attemptLimit | fail n .factorPolicy
  charge budget n .factorWork attempts
  modify fun s => { s with stats := { s.stats with orders := s.stats.orders + 1 } }
  let result := Hex.Nat.Construction.factorSearch allocation m (← get).rand
  modify fun s => { s with rand := result.rand }
  let qs := result.raw.residual :: result.raw.factors.map Prod.fst
  let qs := (qs.filter fun q => 2 ≤ q && q < n && m % q == 0 && sizeBound n q &&
    Hex.Nat.isProbablePrime q).mergeSort (· ≤ ·)
  modify fun s => { s with stats := { s.stats with largeFactors := s.stats.largeFactors + qs.length } }
  return qs

/-- Count terminal literal bits under an explicit traversal fuel.
Exhaustion is explicit and cannot bypass a caller's larger output allocation. -/
def primeBits : Nat → Hex.Nat.PrimeCert → Option Nat
  | 0, _ => none
  | _ + 1, .small n => some (1 + HexArith.bitLength n)
  | fuel + 1, .pock n fs => do
      let bits ← fs.mapM fun (a, e, c) => do
        let child ← primeBits fuel c
        pure (HexArith.bitLength a + HexArith.bitLength e + child)
      pure (1 + HexArith.bitLength n + bits.sum)
  | fuel + 1, .pock3 n s r t fs => do
      let bits ← fs.mapM fun (a, e, c) => do
        let child ← primeBits fuel c
        pure (HexArith.bitLength a + HexArith.bitLength e + child)
      pure (1 + ([n, s, r, t].map HexArith.bitLength).sum + bits.sum)
  | fuel + 1, .pock3Sieve n s r t k fs => do
      let bits ← fs.mapM fun (a, e, c) => do
        let child ← primeBits fuel c
        pure (HexArith.bitLength a + HexArith.bitLength e + child)
      pure (1 + ([n, s, r, t, k].map HexArith.bitLength).sum + bits.sum)

/-- Count raw chain bits, including a terminal within the fixed leaf-depth
profile. Reject deeper supplied terminals instead of undercounting them. -/
def certBitsAt (terminalFuel : Nat) : Cert → Option Nat
  | .base c => (primeBits terminalFuel c).map (1 + ·)
  | .step n a b x y d ws child => do
      let bits ← certBitsAt terminalFuel child
      pure (1 + ([n, a, b, x, y, d].map HexArith.bitLength).sum +
        (ws.map fun w => 1 + HexArith.bitLength w).sum + bits)

/-- Literal bits under the original terminal profile. -/
def certBits (c : Cert) : Option Nat := certBitsAt (leafBudget.maxDepth + 1) c

/-- Embedded terminal node count and height; exhaustion rejects the candidate. -/
def primeShape : Nat → Hex.Nat.PrimeCert → Option (Nat × Nat)
  | 0, _ => none
  | _ + 1, .small _ => some (1, 1)
  | fuel + 1, .pock _ fs
  | fuel + 1, .pock3 _ _ _ _ fs
  | fuel + 1, .pock3Sieve _ _ _ _ _ fs => do
      let shapes ← fs.mapM fun (_, _, child) => primeShape fuel child
      pure (1 + (shapes.map Prod.fst).sum,
        1 + (shapes.map Prod.snd).foldl max 0)

/-- Rows, total nodes (including the base wrapper), and terminal height. -/
def certShape (terminalFuel : Nat) : Cert → Option (Nat × Nat × Nat)
  | .base c => do
      let (nodes, height) ← primeShape terminalFuel c
      pure (0, 1 + nodes, height)
  | .step _ _ _ _ _ _ _ child => do
      let (rows, nodes, height) ← certShape terminalFuel child
      pure (rows + 1, nodes + 1, height)

/-- Test remaining allowances before either retaining or reusing a success. -/
private def outputFailure (budget : SearchBudget) (depth : Nat) (c : Cert) : Option Resource := do
  let terminal := budget.terminal.getD leafBudget
  let some bits := certBitsAt (terminal.maxDepth + 1) c | return .outputBits
  if bits > budget.maxOutputBits then return .outputBits
  if !budget.backtrackOutput && budget.maxRows.isNone && budget.maxNodes.isNone then none else do
    let some (rows, nodes, height) := certShape (terminal.maxDepth + 1) c | return .nodes
    let ancestors := budget.maxDepth - depth
    if rows >= depth || height > min terminal.maxDepth (depth - rows) + 1 then return .depth
    if budget.maxRows.any (rows + ancestors > ·) then return .rows
    if budget.maxNodes.any (nodes + ancestors > ·) then return .nodes
    none

/-- Maximum scalar additions performed by a complete checker replay. -/
def replayWork : Cert → Nat
  | .base _ => 0
  | .step _ _ _ _ _ _ _ child => 2 * HexArith.bitLength child.subject + replayWork child

/-- Retain a checked success only within output-size and memo-entry allocations. -/
private def remember (budget : SearchBudget) (depth n : Nat) (c : Cert) :
    SearchM (Option Cert) := do
  let bits := certBitsAt ((budget.terminal.getD leafBudget).maxDepth + 1) c
  modify fun s => { s with stats := { s.stats with outputBits := bits } }
  if let some resource := outputFailure budget depth c then
    if !budget.backtrackOutput then fail n resource
    modify fun s => { s with stats := { s.stats with outputRejects := s.stats.outputRejects + 1 } }
    unresolved n resource
    return none
  if (← get).memo.length >= budget.maxMemo then fail n .memo
  modify fun s => { s with memo := c :: s.memo }
  return some c

/-- An affine child-order point with checked discriminant and inverse witnesses. -/
private structure Proposal where
  a : Nat
  b : Nat
  x : Nat
  y : Nat
  discrInv : Nat
  inverses : List Nat

/-- Try bounded point draws on one twist, leaving later twists available after local failure. -/
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
      modify fun s => { s with stats := { s.stats with proposals := s.stats.proposals + 1 } }
      return some ⟨a, b, qx, qy, discrInv, ws⟩
  -- Failed draws on a twist are rejected candidates. The caller still tries
  -- other twists and orders, so they do not diagnose overall exhaustion.
  unresolved n .pointRetries
  return none

/-- Structurally bounded recursion; failure of a child resumes the parent's
remaining CM orders, without resetting any allocation or random state.
This stateful worker requires a memo of previously checked successes admitted
under the same allocations and sufficient remaining depth. Caller-supplied
states are not validated here; `produce` starts fresh and checks its result. -/
def search (budget : SearchBudget) : Nat → Nat → SearchM (Option Cert)
  | 0, n => do
      unresolved n .depth
      return none
  | depth + 1, n => do
      if HexArith.bitLength n > budget.maxBits then fail n .inputBits
      if let some c := (← get).memo.find? (fun c => c.subject == n &&
          ((!budget.backtrackOutput && budget.maxRows.isNone && budget.maxNodes.isNone) ||
            (outputFailure budget (depth + 1) c).isNone)) then
        return some c
      if let some c ← leaf budget (depth + 1) n then
        if let some c ← remember budget (depth + 1) n c then return some c
      if n ≤ 3 || n % 2 == 0 || n % 3 == 0 || !Hex.Nat.isProbablePrime n then
        unresolved n .screening
        return none
      let some z ← nonresidue budget n false | return none
      let portfolio := CM.originalPolynomials ++
        (if budget.extendedCM then CM.classPolynomials else [])
      for polynomial in portfolio do
        charge budget n .candidates
        let k := if polynomial.d % 4 == 0 then polynomial.d / 4 else polynomial.d
        let some root ← sqrt budget n z (modSub n 0 k) | continue
        let norms := [CM.norm? n polynomial.d root, CM.norm? n polynomial.d (modSub n 0 root)]
        let some (t, v) := norms.findSome? id | continue
        modify fun s => { s with stats := { s.stats with norms := s.stats.norms + 1 } }
        let invs ← invariants budget n z polynomial
        if invs.isEmpty then continue
        let g ← if polynomial.d == 3 then nonresidue budget n true else pure (some z)
        let some g := g | continue
        for trace in CM.traces polynomial.d t v do
          charge budget n .candidates
          let m : Int := (n : Int) + 1 - trace
          if m ≤ 0 then continue
          let m := m.toNat
          for q in ← factors budget n m do
            let cofactor := m / q
            for inv in invs do
              for (a, b) in CM.curves n inv g do
                let some proposal ← point budget n q cofactor z a b | continue
                if let some child ← search budget depth q then
                  let c := Cert.step n a b proposal.x proposal.y proposal.discrInv
                    proposal.inverses child
                  -- The proposal checks this step and recursion supplies its
                  -- child. Replay the complete chain once at `produce`.
                  if let some c ← remember budget (depth + 1) n c then return some c
                modify fun s => { s with stats := { s.stats with backtracks := s.stats.backtracks + 1 } }
                -- Different points on this curve have the same child obligation.
                break
      unresolved n .portfolio
      return none

/-- The outcome of certificate search, together with its final random state
and statistics. An error reports an unsuccessful attempt, not a proof that
the input is composite. -/
structure SearchResult where
  /-- A complete checked primality certificate, or the integer and reason
  for which the search stopped. -/
  result : Except SearchError Cert
  /-- Final random stream, counters and successful memo. -/
  state : SearchState
deriving Repr

/-- Check complete raw data once at the production boundary. -/
private def finish (n : Nat) (result : Except SearchError (Option Cert))
    (state : SearchState) : Except SearchError Cert :=
  match result with
  | .error e => .error e
  | .ok (some c) => if checkAt n c then .ok c else .error ⟨n, .portfolio⟩
  | .ok none => .error (state.stats.unresolved.getD ⟨n, .portfolio⟩)

/-- Final production validation cannot return unchecked or substituted data. -/
private theorem finish_ok {n : Nat} {result : Except SearchError (Option Cert)}
    {state : SearchState} {c : Cert} (h : finish n result state = .ok c) :
    checkAt n c = true := by
  cases result with
  | error e => simp [finish] at h
  | ok option =>
    cases option with
    | none => simp [finish] at h
    | some candidate =>
      simp only [finish] at h
      split at h
      · cases h
        assumption
      · simp at h

/-- Search for a primality certificate for `n`, using `seed` to choose the
deterministic random sequence and `budget` to limit the work. Return a
certificate and search statistics, or an error explaining why search stopped.
Every `.ok c` result satisfies `checkAt n c = true`; failure to find a
certificate does not imply that `n` is composite.

The default policy admits inputs through 256 bits. `native512Budget` and
`public512Budget` explicitly select 512-bit search. For a theorem of
Mathlib's `Nat.Prime n`, use `HexECPPTheory.Native` or apply the companion's
soundness theorem to a kernel-checked checker equation. -/
def produce (n seed : Nat) (budget : SearchBudget := {}) : SearchResult :=
  let computation : SearchM (Option Cert) := do
    let result ← search budget budget.maxDepth n
    if let some c := result then
      charge budget n .scalarWork (replayWork c)
    return result
  let (result, state) := computation.run.run { rand := Hex.Rand.ofSeed seed }
  ⟨finish n result state, state⟩

/-- Every successful production result is accepted at the requested subject,
independently of seed, allocation and arithmetic proposals. -/
theorem produce_ok {n seed : Nat} {budget : SearchBudget} {c : Cert}
    (h : (produce n seed budget).result = .ok c) : checkAt n c = true := by
  exact finish_ok h

/-- Encode ECPP points with cofactor one; terminal data is supplied separately. -/
private def rows : Cert → List String
  | .base _ => []
  | .step n a _ x y _ _ child =>
      s!"[{n},{(n : Int) + 1 - child.subject},1,{a},[{x},{y}]]" :: rows child

/-- Freeze only replay inputs. Each row uses the already found q-order point
and cofactor one, so conversion need not repeat any CM or factor search.
The stored `t = n + 1 - q` is an encoding field, not a Frobenius trace. -/
def frozenRows (c : Cert) : String :=
  match rows c with
  | [] => toString c.subject
  | rows => "[" ++ String.intercalate "," rows ++ "]"

end Hex.ECPP
