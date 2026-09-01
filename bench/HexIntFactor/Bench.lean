/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor
import LeanBench

/-! Native benchmark families for integer factorization and replay. -/

namespace Hex.IntFactorBench

open Hex.Nat

-- Proof-producing benchmark inputs walk the committed primality table.
set_option maxRecDepth 100000

def runFactorCount (n : Nat) : Nat :=
  match factor? n (Hex.Rand.ofSeed n) with
  | .ok (F, _) => F.raw.factors.length
  | .error f => f.attempts

private def leastFactor (n : Nat) (factors : List PrimePower) : Nat :=
  factors.foldl (fun least entry => min least entry.prime) n

private def encodeFactors (factors : List PrimePower) : List Nat :=
  factors.flatMap fun entry => [entry.prime, entry.exponent]

private def factorFull (n seed : Nat) : List Nat :=
  match factor? n (Hex.Rand.ofSeed seed) with
  | .ok (F, _) => encodeFactors F.raw.factors
  | .error _ => []

private def rhoLeast (n seed : Nat) : Nat :=
  let budget := defaultPrimeCertBudget
  match Internal.rhoSplitCountedWith? n (Hex.Rand.ofSeed seed)
      budget.rhoRestarts budget.rhoSteps with
  | .ok success => min success.factor (n / success.factor)
  | .error _ => 0

def runPMinusOne (n : Nat) : Nat :=
  match pMinusOneFactor n 2 10000 with
  | .factor d => d
  | .noFactor => 1
  | .whole => n

def runEcm (n : Nat) : Nat :=
  match ecmStage1 n 7 1000 with
  | .factor d => d
  | .noFactor => 1
  | .whole => n

def runCyclotomic (n : Nat) : Nat :=
  match cyclotomicSplit? 2 n .minus with
  | some parts => parts.foldl (fun acc part => acc + part.value % 65536) 0
  | none => 0

def replayInput (e : Nat) : Factorization :=
  ⟨2 ^ e, [⟨e, .small 2⟩]⟩

def runReplay (e : Nat) : Nat :=
  if checkFactorization (replayInput e) then 1 else 0

@[noinline]
private def runOrderOnce (p : Nat) : Nat := orderOf 3 p

def runOrder (p : Nat) : Nat :=
  (List.range 512).foldl (fun total _ => total + runOrderOnce p) 0

private def balancedInput : Nat → Nat
  | 32 => 64553 * 66553
  | 40 => 1047587 * 1049599
  | 48 => 16776217 * 16778227
  | 56 => 268434461 * 268436507
  | 64 => 4294966297 * 4294968317
  | 72 => 68719475767 * 68719477789
  | 80 => 1099511626781 * 1099511628781
  | _ => 64553 * 66553

/- Multiple fixed seeds average randomized cycle length without changing the
family. An empty encoding is a failed search and is rejected by
`control-audit`; successful encodings are canonical complete factorizations. -/
private opaque balancedSeeds : Array Nat := #[0, 1, 2, 3, 4]

def runBalancedFactor (bits : Nat) : Array (List Nat) :=
  let n := balancedInput bits
  balancedSeeds.map fun salt => factorFull n (n + 104729 * salt)

/- Raw rho intentionally returns only the normalized split factor. It is a
scaling/profile target, not the denominator for full public factorization. -/
def runBalancedRho (bits : Nat) : Array Nat :=
  let n := balancedInput bits
  balancedSeeds.map fun salt => rhoLeast n (n + 104729 * salt)

structure CompletionInput where
  target : Nat
  factor : Nat
  randState : UInt64

private def completeSplit (input : CompletionInput) : List Nat :=
  let r : Hex.Rand := ⟨input.randState⟩
  match factor? input.factor r with
  | .error _ => []
  | .ok (left, r') =>
      match factor? (input.target / input.factor) r' with
      | .error _ => []
      | .ok (right, _) =>
          let factors := Internal.mergePowers
            left.raw.factors right.raw.factors
          let raw : Factorization := ⟨input.target, factors⟩
          if checkFactorization raw then encodeFactors factors else []

/- These fixtures are the successful direct-rho outputs for the exact balanced
targets and five seeds above. Storing the normalized split and advanced state
makes the completion target time only recursive factorization, certificate
construction, canonical merging, and final checker acceptance. -/
private opaque completion32 : Array CompletionInput := #[
  ⟨4296195809, 64553, 4354685569233041163⟩,
  ⟨4296195809, 66553, 4354685569233145892⟩,
  ⟨4296195809, 66553, 4354685569233250621⟩,
  ⟨4296195809, 66553, 4354685569233355350⟩,
  ⟨4296195809, 64553, 4354685569233460079⟩]
private opaque completion40 : Array CompletionInput := #[
  ⟨1099546267613, 1047587, 4354686664483112967⟩,
  ⟨1099546267613, 1049599, 4354686664483217696⟩,
  ⟨1099546267613, 1047587, 4354686664483322425⟩,
  ⟨1099546267613, 1049599, 4354686664483427154⟩,
  ⟨1099546267613, 1049599, 4354686664483531883⟩]
private opaque completion48 : Array CompletionInput := #[
  ⟨281475177027259, 16778227, 4354967040113872613⟩,
  ⟨281475177027259, 16776217, 4354967040113977342⟩,
  ⟨281475177027259, 16778227, 4354967040114082071⟩,
  ⟨281475177027259, 16776217, 4354967040114186800⟩,
  ⟨281475177027259, 16776217, 4354967040114291529⟩]
private opaque completion56 : Array CompletionInput := #[
  ⟨72057609069267727, 268434461, 4426743174006113081⟩,
  ⟨72057609069267727, 268434461, 4426743174006217810⟩,
  ⟨72057609069267727, 268434461, 4426743174006322539⟩,
  ⟨72057609069267727, 268434461, 4426743174006427268⟩,
  ⟨72057609069267727, 268436507, 4426743174006531997⟩]
private opaque completion64 : Array CompletionInput := #[
  ⟨18446744168197812149, 4294968317, 8709371224361951241⟩,
  ⟨18446744168197812149, 4294966297, 8709371224362055970⟩,
  ⟨18446744168197812149, 4294966297, 8709371224362160699⟩,
  ⟨18446744168197812149, 4294966297, 8709371224362265428⟩,
  ⟨18446744168197812149, 4294968317, 8709371224362370157⟩]
private opaque completion72 : Array CompletionInput := #[
  ⟨4722366488642080239163, 68719477789, 8709376902308716175⟩,
  ⟨4722366488642080239163, 68719475767, 8709376902308820904⟩,
  ⟨4722366488642080239163, 68719475767, 8709376902308925633⟩,
  ⟨4722366488642080239163, 68719475767, 8709376902309030362⟩,
  ⟨4722366488642080239163, 68719477789, 8709376902309135091⟩]
private opaque completion80 : Array CompletionInput := #[
  ⟨1208925819625624289983961, 1099511628781, 8709382124988968493⟩,
  ⟨1208925819625624289983961, 1099511628781, 8709382124989073222⟩,
  ⟨1208925819625624289983961, 1099511628781, 8709382124989177951⟩,
  ⟨1208925819625624289983961, 1099511628781, 8709382124989282680⟩,
  ⟨1208925819625624289983961, 1099511628781, 8709382124989387409⟩]

initialize completion32Ref : IO.Ref (Array CompletionInput) ← IO.mkRef completion32
initialize completion40Ref : IO.Ref (Array CompletionInput) ← IO.mkRef completion40
initialize completion48Ref : IO.Ref (Array CompletionInput) ← IO.mkRef completion48
initialize completion56Ref : IO.Ref (Array CompletionInput) ← IO.mkRef completion56
initialize completion64Ref : IO.Ref (Array CompletionInput) ← IO.mkRef completion64
initialize completion72Ref : IO.Ref (Array CompletionInput) ← IO.mkRef completion72
initialize completion80Ref : IO.Ref (Array CompletionInput) ← IO.mkRef completion80

private def readCompletion (ref : IO.Ref (Array CompletionInput))
    (_ : Unit) : IO (Array (List Nat)) := do
  return (← ref.get).map completeSplit

@[noinline] def runBalancedCompletion32 := readCompletion completion32Ref
@[noinline] def runBalancedCompletion40 := readCompletion completion40Ref
@[noinline] def runBalancedCompletion48 := readCompletion completion48Ref
@[noinline] def runBalancedCompletion56 := readCompletion completion56Ref
@[noinline] def runBalancedCompletion64 := readCompletion completion64Ref
@[noinline] def runBalancedCompletion72 := readCompletion completion72Ref
@[noinline] def runBalancedCompletion80 := readCompletion completion80Ref

private def completionInputs : Nat → Array CompletionInput
  | 32 => completion32
  | 40 => completion40
  | 48 => completion48
  | 56 => completion56
  | 64 => completion64
  | 72 => completion72
  | 80 => completion80
  | _ => #[]

private def completionMatchesRho (bits : Nat) : Bool :=
  let n := balancedInput bits
  (balancedSeeds.toList.zip (completionInputs bits).toList).all fun (salt, input) =>
    let budget := defaultPrimeCertBudget
    match Internal.rhoSplitCountedWith? n
        (Hex.Rand.ofSeed (n + 104729 * salt))
        budget.rhoRestarts budget.rhoSteps with
    | .ok success =>
        input.target == n && input.factor == success.factor &&
          input.randState == success.rand.state
    | .error _ => false

def reportSplits : IO UInt32 := do
  for bits in #[32, 40, 48, 56, 64, 72, 80] do
    let n := balancedInput bits
    for salt in #[0, 1, 2, 3, 4] do
      let seed := n + 104729 * salt
      let budget := defaultPrimeCertBudget
      match Internal.rhoSplitCountedWith? n (Hex.Rand.ofSeed seed)
          budget.rhoRestarts budget.rhoSteps with
      | .ok success =>
          IO.println s!"{bits},{salt},{n},{success.factor},{success.rand.state.toNat}"
      | .error _ => IO.println s!"{bits},{salt},{n},failure,failure"
  return 0

private def smoothInput : Nat → Nat
  | 32 => 65537 * 65521
  | 40 => 65537 * 8400967
  | 48 => 65537 * 2147496017
  | 56 => 65537 * 549755826233
  | 64 => 65537 * 140737488367699
  | 72 => 65537 * 36028797018976327
  | 76 => 65537 * 576460752303435851
  | 80 => 65537 * 9223372036854788173
  | _ => 65537 * 65521

/- The word cases have least factor 1000003. The direct-`Nat` cases reuse the
same 34-bit successful ECM factor against 39-, 43-, and 47-bit cofactors. Its
predecessor is not 1000-smooth, while the fixed Suyama curve succeeds. This is
an honestly unbalanced ECM family and not a disguised p-1 success family. -/
private def ecmInput : Nat → Nat
  | 48 => 1000003 * 268435579
  | 56 => 1000003 * 68719476901
  | 64 => 1000003 * 17592186044591
  | 72 => 8593846213 * 274877919317
  | 76 => 8593846213 * 4398046523483
  | 80 => 8593846213 * 70368744190051
  | _ => 1000003 * 268435579

def runEcmAt (bits : Nat) : Nat :=
  runEcm (ecmInput bits)

def runEcmRho (bits : Nat) : Nat :=
  let n := ecmInput bits
  rhoLeast n n

@[noinline]
def runPowerSplit (e : Nat) : List Nat :=
  let target := powerTarget 2 e .minus
  match factorPower? 2 e .minus (Hex.Rand.ofSeed target) with
  | .ok (F, _) => encodeFactors F.raw.factors
  | .error _ => []

@[noinline]
def runPowerGeneric (e : Nat) : List Nat :=
  let target := powerTarget 2 e .minus
  factorFull target target

def runPrimitiveRoot (p : Nat) : Nat :=
  match primeCert? p (Hex.Rand.ofSeed p) (defaultFuel p) with
  | .error failure => failure.attempts
  | .ok (pc, r) =>
      match factor? (p - 1) r with
      | .error failure => failure.attempts
      | .ok (F, _) =>
          match primitiveRoot? pc F p with
          | none => 0
          | some (g, _) => g

/- Sixteen table-smooth composites form an approximately uniform six-million
grid below `10^8`. Every prime factor is in the committed table, so direct
trial division and the public dispatcher have the same semantic result. Opaque
storage prevents the fixed-target bodies from becoming module-init constants. -/
private opaque tableInputs : Array Nat := #[
  5999953, 11999921, 17999983, 23999947,
  30000013, 35999987, 41999597, 47999209,
  53999863, 59999501, 66000017, 71999951,
  77999983, 84000193, 89999939, 95999257
]

initialize tableInputsRef : IO.Ref (Array Nat) ← IO.mkRef tableInputs

private def tableDispatch : IO (Array (List Nat)) := do
  let inputs ← tableInputsRef.get
  return inputs.map fun n =>
    match factor? n (Hex.Rand.ofSeed n) with
    | .ok (F, _) => encodeFactors F.raw.factors
    | .error _ => []

private def tableTrial : IO (Array (List Nat)) := do
  let inputs ← tableInputsRef.get
  return inputs.map fun n =>
    let out := trialFactors n
    if out.2 = 1 then encodeFactors out.1 else []

@[noinline]
def runTableDispatch (_ : Unit) : IO (Array (List Nat)) := do
  tableDispatch

@[noinline]
def runTableTrial (_ : Unit) : IO (Array (List Nat)) := do
  tableTrial

private opaque balancedBits : Array Nat := #[32, 40, 48, 56, 64, 72, 80]
private opaque smoothBits : Array Nat := #[32, 40, 48, 56, 64, 72, 76, 80]
private opaque ecmBits : Array Nat := #[48, 56, 64, 72, 76, 80]
private opaque powerExponents : Array Nat :=
  #[12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 72, 80]

initialize powerExponentsRef : IO.Ref (Array Nat) ← IO.mkRef powerExponents
initialize smoothBitsRef : IO.Ref (Array Nat) ← IO.mkRef smoothBits
initialize ecmBitsRef : IO.Ref (Array Nat) ← IO.mkRef ecmBits

initialize balanced32Ref : IO.Ref Nat ← IO.mkRef 32
initialize balanced40Ref : IO.Ref Nat ← IO.mkRef 40
initialize balanced48Ref : IO.Ref Nat ← IO.mkRef 48
initialize balanced56Ref : IO.Ref Nat ← IO.mkRef 56
initialize balanced64Ref : IO.Ref Nat ← IO.mkRef 64
initialize balanced72Ref : IO.Ref Nat ← IO.mkRef 72
initialize balanced80Ref : IO.Ref Nat ← IO.mkRef 80

initialize ecm48Ref : IO.Ref Nat ← IO.mkRef 48
initialize ecm56Ref : IO.Ref Nat ← IO.mkRef 56
initialize ecm64Ref : IO.Ref Nat ← IO.mkRef 64
initialize ecm72Ref : IO.Ref Nat ← IO.mkRef 72
initialize ecm76Ref : IO.Ref Nat ← IO.mkRef 76
initialize ecm80Ref : IO.Ref Nat ← IO.mkRef 80

private def readBalanced (ref : IO.Ref Nat)
    (run : Nat → α) (_ : Unit) : IO α := do
  return run (← ref.get)

@[noinline] def runBalancedFactor32 :=
  readBalanced balanced32Ref runBalancedFactor
@[noinline] def runBalancedFactor40 :=
  readBalanced balanced40Ref runBalancedFactor
@[noinline] def runBalancedFactor48 :=
  readBalanced balanced48Ref runBalancedFactor
@[noinline] def runBalancedFactor56 :=
  readBalanced balanced56Ref runBalancedFactor
@[noinline] def runBalancedFactor64 :=
  readBalanced balanced64Ref runBalancedFactor
@[noinline] def runBalancedFactor72 :=
  readBalanced balanced72Ref runBalancedFactor
@[noinline] def runBalancedFactor80 :=
  readBalanced balanced80Ref runBalancedFactor

private def readEcm (ref : IO.Ref Nat) (_ : Unit) : IO Nat := do
  return runEcm (ecmInput (← ref.get))

@[noinline] def runEcm48 := readEcm ecm48Ref
@[noinline] def runEcm56 := readEcm ecm56Ref
@[noinline] def runEcm64 := readEcm ecm64Ref
@[noinline] def runEcm72 := readEcm ecm72Ref
@[noinline] def runEcm76 := readEcm ecm76Ref
@[noinline] def runEcm80 := readEcm ecm80Ref

@[noinline]
def runPMinusOneBatch (_ : Unit) : IO (Array Nat) :=
  return (← smoothBitsRef.get).map fun bits => runPMinusOne (smoothInput bits)

@[noinline]
def runEcmBatch (_ : Unit) : IO (Array Nat) :=
  return (← ecmBitsRef.get).map fun bits => runEcm (ecmInput bits)

@[noinline]
def runEcmRhoBatch (_ : Unit) : IO (Array Nat) :=
  return (← ecmBitsRef.get).map fun bits => rhoLeast (ecmInput bits) (ecmInput bits)

@[noinline]
def runCyclotomicBatch (_ : Unit) : IO (Array Nat) := do
  return (← powerExponentsRef.get).map runCyclotomic

@[noinline]
def runPowerGenericBatch (_ : Unit) : IO (Array (List Nat)) := do
  return (← powerExponentsRef.get).map runPowerGeneric

@[noinline]
def runPowerSplitBatch (_ : Unit) : IO (Array (List Nat)) := do
  return (← powerExponentsRef.get).map runPowerSplit

private def defaultFuelInputs : Array Nat :=
  tableInputs ++
  balancedBits.map balancedInput ++
  smoothBits.map smoothInput ++
  ecmBits.map ecmInput ++
  powerExponents.map fun e => powerTarget 2 e .minus

initialize defaultFuelInputsRef : IO.Ref (Array Nat) ←
  IO.mkRef defaultFuelInputs

@[noinline]
def runDefaultFuelSchedule (_ : Unit) : IO (Array Nat) :=
  return (← defaultFuelInputsRef.get).map fun n =>
    match Internal.factorCounted? n (Hex.Rand.ofSeed n) with
    | .ok success => 2 * success.attempts + 1
    | .error failure => 2 * failure.attempts

def reportDefaultFuel : IO UInt32 := do
  for n in defaultFuelInputs do
    match Internal.factorCounted? n (Hex.Rand.ofSeed n) with
    | .ok success =>
        IO.println s!"{n},{defaultFuel n},success,{success.attempts}"
    | .error failure =>
        IO.println s!"{n},{defaultFuel n},failure,{failure.attempts}"
  return 0

def probeEcm (values : List String) : IO UInt32 := do
  for value in values do
    match value.toNat? with
    | none => IO.eprintln s!"invalid natural: {value}"
    | some n => IO.println s!"{n},{runEcm n}"
  return 0

private def orderLadder : Array Nat :=
  #[257, 1013, 4073, 16363, 65537, 262193, 524309, 1048589]

#guard orderLadder.all fun p => orderOf 3 p == p - 1

/- These 50- and 61-bit primes divide `3^64 - 1` and `3^176 - 1`,
respectively. They exercise downstream-sized operands while keeping the
otherwise linear reference order scan bounded. -/
private opaque downstreamOrderPrimes : Array Nat := #[
  926510094425921,
  1363620137403810529
]

initialize downstreamOrderPrimesRef : IO.Ref (Array Nat) ←
  IO.mkRef downstreamOrderPrimes

@[noinline]
def runDownstreamOrder (_ : Unit) : IO (Array Nat) := do
  return (← downstreamOrderPrimesRef.get).map (orderOf 3)

@[noinline]
def runDownstreamPrimitiveRoot (_ : Unit) : IO (Array Nat) := do
  return (← downstreamOrderPrimesRef.get).map runPrimitiveRoot

def reportControls : IO UInt32 := do
  let dispatchedTable ← tableDispatch
  let trialTable ← tableTrial
  let mut ok := dispatchedTable == trialTable && dispatchedTable.all (!·.isEmpty)
  let tableStatus := if ok then "success" else "failure"
  IO.println s!"table,{tableStatus}"
  for bits in balancedBits do
    let dispatched := runBalancedFactor bits
    let completed := (completionInputs bits).map completeSplit
    let success := dispatched == completed && dispatched.all (!·.isEmpty) &&
      completionMatchesRho bits
    ok := ok && success
    let status := if success then "success" else "failure"
    IO.println s!"balanced-{bits},{status}"
  let genericPower := powerExponents.map runPowerGeneric
  let splitPower := powerExponents.map runPowerSplit
  let powerSuccess := genericPower == splitPower && genericPower.all (!·.isEmpty)
  ok := ok && powerSuccess
  let powerStatus := if powerSuccess then "success" else "failure"
  IO.println s!"power,{powerStatus}"
  return if ok then 0 else 1

private theorem boundedPowMul_exact (q acc : Nat) (hq : 0 < q)
    (hacc : 0 < acc) : ∀ e : Nat,
    boundedPowMul (acc * q ^ e) q acc e = some (acc * q ^ e)
  | 0 => by simp [boundedPowMul]
  | e + 1 => by
      have hpow : 0 < q ^ e := Nat.pow_pos hq
      have hle : q ≤ q ^ e * q := Nat.le_mul_of_pos_left q hpow
      have hmul : acc * q ≤ acc * q ^ (e + 1) := by
        simpa only [Nat.pow_succ] using Nat.mul_le_mul_left acc hle
      rw [boundedPowMul, ite_eq_right (Nat.ne_of_gt hacc),
        ite_eq_right (Nat.ne_of_gt hq),
        ite_eq_left ((Nat.le_div_iff_mul_le hq).2 hmul)]
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using
        boundedPowMul_exact q (acc * q) hq (Nat.mul_pos hacc hq) e

private def sigmaExponentInput (e : Nat) : CheckedFactorization (3 ^ (e + 1)) :=
  ⟨⟨3 ^ (e + 1), [⟨e + 1, .small 3⟩]⟩, rfl, by
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨Nat.pow_pos (by decide), ?_⟩, ?_⟩
    · simp [checkEntries, show checkPrime (.small 3) = true by decide]
    · simp only [factorProduct, PrimePower.prime, PrimeCert.subject]
      have h : boundedPowMul (3 ^ (e + 1)) 3 1 (e + 1) =
          some (3 ^ (e + 1)) := by
        simpa using boundedPowMul_exact 3 1 (by decide) (by decide) (e + 1)
      rw [h]⟩

structure SigmaExponentInput where
  subject : Nat
  checked : CheckedFactorization subject

instance : Hashable SigmaExponentInput where
  hash input := hash input.subject

def prepSigmaExponent (e : Nat) : SigmaExponentInput :=
  ⟨_, sigmaExponentInput e⟩

@[noinline]
private def runSigmaExponentOnce (input : SigmaExponentInput) : Nat :=
  sigma input.checked 1

def runSigmaExponent (input : SigmaExponentInput) : Nat :=
  (List.range 512).foldl
    (fun total _ => total + runSigmaExponentOnce input) 0

private def sigmaEntries : List PrimePower :=
  primeTable.toList.map fun p => ⟨32, .small p⟩

private def sigmaSubject (count : Nat) : Nat :=
  ((sigmaEntries.take count).map fun entry => entry.prime ^ entry.exponent).prod

private def sigmaInput (count : Nat) (h : checkFactorization
    ⟨sigmaSubject count, sigmaEntries.take count⟩ = true) :
    CheckedFactorization (sigmaSubject count) :=
  ⟨⟨sigmaSubject count, sigmaEntries.take count⟩, rfl, h⟩

structure SigmaInput where
  subject : Nat
  checked : CheckedFactorization subject

instance : Hashable SigmaInput where
  hash input := hash input.subject

private opaque sigmaInputDefault : SigmaInput :=
  ⟨_, sigmaInput 0 (by decide)⟩
private opaque sigmaInput32 : SigmaInput :=
  ⟨_, sigmaInput 32 (by decide)⟩
private opaque sigmaInput64 : SigmaInput :=
  ⟨_, sigmaInput 64 (by decide)⟩
private opaque sigmaInput128 : SigmaInput :=
  ⟨_, sigmaInput 128 (by decide)⟩
private opaque sigmaInput256 : SigmaInput :=
  ⟨_, sigmaInput 256 (by decide)⟩
private opaque sigmaInput512 : SigmaInput :=
  ⟨_, sigmaInput 512 (by decide)⟩
set_option maxHeartbeats 1000000 in
private opaque sigmaInput1024 : SigmaInput :=
  ⟨_, sigmaInput 1024 (by decide)⟩

@[noinline]
def sigmaInputForCount : Nat → SigmaInput
  | 32 => sigmaInput32
  | 64 => sigmaInput64
  | 128 => sigmaInput128
  | 256 => sigmaInput256
  | 512 => sigmaInput512
  | 1024 => sigmaInput1024
  | _ => sigmaInputDefault

@[noinline]
private def runSigmaFactorCountOnce (input : SigmaInput) : Nat :=
  sigma input.checked 1

def runSigmaFactorCount (input : SigmaInput) : Nat :=
  (List.range 512).foldl
    (fun total _ => total + runSigmaFactorCountOnce input) 0

@[noinline]
private def runSquareOnce (input : SigmaInput) : Nat :=
  squareDivisor input.checked + squarefreePart input.checked

def runSquareFactorCount (input : SigmaInput) : Nat :=
  (List.range 16384).foldl (fun total _ => total + runSquareOnce input) 0

@[noinline]
private def runTotientFactorCountOnce (input : SigmaInput) : Nat :=
  totient input.checked

def runTotientFactorCount (input : SigmaInput) : Nat × Nat :=
  (List.range 512).foldl (fun total _ =>
    let value := runTotientFactorCountOnce input
    (total.1 + value, total.2 + value % 4294967291)) (0, 0)

/- The matched direct arm runs Brent rho with the public dispatcher's restart
and cycle-step allocation. Each balanced least factor has `bits / 2` bits, so
the fixed five-seed batch has `Theta(2^(bits/4))` expected cycle work. -/
setup_benchmark runBalancedRho n => 2 ^ (n / 4)
  where {
    paramFloor := 32
    paramCeiling := 80
    paramSchedule := .custom #[32, 40, 48, 56, 64, 72, 80]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 1000000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- `boundedPowMul` replays the single exponent one guarded multiplication at a
time. The accumulator grows throughout the replay, so the sum of widening
guarded multiplications and divisions has a `Theta(n²)` native-cost model. The
multi-order-of-magnitude exponent schedule makes this a two-sided claim. -/
setup_benchmark runReplay n => n * n
  where {
    paramFloor := 1024
    paramCeiling := 262144
    paramSchedule := .custom
      #[1024, 16384, 65536, 131072, 196608, 229376, 262144]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 1000000000
    outerTrials := 3
  }

/- `orderOf` carries one bounded residue and performs one modular multiplication
per candidate exponent. On every prime in this ladder, `3` has order `p - 1`,
so each run exercises `p - 1` scan steps and the declared arithmetic-operation
model is linear. A fixed 512-run hot loop raises three upper rungs above the
single-spawn resolution floor without changing that model. -/
setup_benchmark runOrder n => n
  where {
    paramFloor := 257
    paramCeiling := 1048589
    paramSchedule := .custom orderLadder
    maxSecondsPerCall := 5.0
    targetInnerNanos := 2500000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- For the certified input `3^(e+1)` at `k = 1`, `sigma` computes a nontrivial
exact geometric quotient with `Theta(e)` output bits. Preparation hoists the
unused certified subject out of the timed loop. The quotient divisor is the
single-limb value `2`, so exponentiation dominates with the declared
quasi-linear `n log n` surrogate. A fixed 512-run hot loop raises the upper
three rungs above the single-spawn resolution floor without changing the
model; Lean's `Nat` result hash is constant-time. -/
setup_benchmark runSigmaExponent n => n * n.log2
  with prep := prepSigmaExponent
  where {
    paramFloor := 16384
    paramCeiling := 4194304
    paramSchedule := .custom #[16384, 65536, 262144, 1048576, 4194304]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 1000000000
    signalFloorMultiplier := 1.0
    -- The multi-million-bit ladder crosses native multiplication regimes;
    -- 0.20 admits that finite-range transition without changing the model.
    slopeTolerance := 0.20
    outerTrials := 3
  }

/- Each certified entry has exponent 32. The `i`th sequential product step
multiplies a linearly growing accumulator by one bounded-size table-prime
entry sum. Its cost is `Theta(i)` limbs, whose sum is the declared
`Theta(n²)` native-cost model. A fixed 512-run hot loop clears the single-spawn
resolution floor without changing the model. Preparation selects a prechecked
input once per child spawn, outside the timed loop. -/
setup_benchmark runSigmaFactorCount n => n * n
  with prep := sigmaInputForCount
  where {
    paramFloor := 32
    paramCeiling := 1024
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 3000000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Each prepared certificate has `n` entries of fixed exponent 32. The
square-divisor accumulator grows linearly in limbs, so its sequential
multiplication has the declared `Theta(n²)` native-cost model; the parity
product is identically one and contributes only a linear pass. A fixed 16384-run
hot loop preserves that model while raising the operation above the child
spawn-resolution floor. Preparation hoists the enormous certified subject out
of the timed loop, so an input-range scan would be immediately observable
rather than hidden in setup. -/
setup_benchmark runSquareFactorCount n => n * n
  with prep := sigmaInputForCount
  where {
    paramFloor := 32
    paramCeiling := 1024
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 1000000000
    -- At 32..512 the early accumulator-width regimes gave an inconclusive
    -- slope. Extending to 1024 exposes convergence toward the n² model.
    slopeTolerance := 0.20
    outerTrials := 3
  }

/- Each prepared certificate has `n` fixed-exponent prime-power entries.
`totient` builds one bounded-size contribution per entry, then sequentially
multiplies an accumulator whose limb count grows linearly, giving the declared
`Theta(n²)` native-cost model. A fixed 512-run hot loop clears the single-spawn
resolution floor without changing the model. The paired modular checksum
prevents the low word of these highly even results from making every harness
hash zero; its single division per repeat is lower-order. Preparation hoists
the enormous subject out of the timed loop; scanning residues below it would
not terminate on these subjects. -/
setup_benchmark runTotientFactorCount n => n * n
  with prep := sigmaInputForCount
  where {
    paramFloor := 32
    paramCeiling := 1024
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 1000000000
    signalFloorMultiplier := 1.0
    -- The ladder crosses accumulator-width regimes; 0.20 admits that
    -- finite-range transition without changing the model.
    slopeTolerance := 0.20
    outerTrials := 3
  }

private def fixedConfig (bodySeconds : Float) (expected : UInt64) :
    LeanBench.FixedBenchmarkConfig where
  repeats := 3
  -- The scientific collector owns median budget assertions. This deliberately
  -- generous process timeout keeps CI `verify` a correctness/bitrot gate.
  maxSecondsPerCall := 10.0 + 5.0 * bodySeconds
  expectedHash := some expected

private def powerConfig (expected : UInt64) :
    LeanBench.FixedBenchmarkConfig where
  repeats := 7
  maxSecondsPerCall := 10.1
  expectedHash := some expected

/- Protocol anchor, not performance evidence: the exact public `defaultFuel`
schedule over every committed table, balanced, smooth, ECM, and power-form
input. The odd/even encoding retains success/failure and charged attempts. -/
setup_fixed_benchmark runDefaultFuelSchedule where
  fixedConfig 2.0 0xdeec635db1873394

/- Mode 3 for balanced dispatch. Its attempted five-seed 32--80-bit
`2^(bits/4)` registration was inconclusive because certificate construction
and primality checks dominate different lower rungs; the raw-rho registration
above retains the stable asymptotic check. One fixed public-factor target per
rung records the full pipeline, while the matched completion targets below
start from precomputed rho outputs and isolate post-split work. -/
setup_fixed_benchmark runBalancedFactor32 where
  fixedConfig 0.01 0x1bf8f79828d53905
setup_fixed_benchmark runBalancedFactor40 where
  fixedConfig 0.05 0x73341ad461f040fb
setup_fixed_benchmark runBalancedFactor48 where
  fixedConfig 0.1 0xae563f6ab52a4a8b
setup_fixed_benchmark runBalancedFactor56 where
  fixedConfig 0.2 0x386194db34d47118
setup_fixed_benchmark runBalancedFactor64 where
  fixedConfig 0.75 0x6dc7828c846f9e2b
setup_fixed_benchmark runBalancedFactor72 where
  fixedConfig 2.0 0x2c5ab36c63d8144e
setup_fixed_benchmark runBalancedFactor80 where
  fixedConfig 6.0 0x62b9a8e4f8df37af

setup_fixed_benchmark runBalancedCompletion32 where
  fixedConfig 0.01 0x1bf8f79828d53905
setup_fixed_benchmark runBalancedCompletion40 where
  fixedConfig 0.01 0x73341ad461f040fb
setup_fixed_benchmark runBalancedCompletion48 where
  fixedConfig 0.01 0xae563f6ab52a4a8b
setup_fixed_benchmark runBalancedCompletion56 where
  fixedConfig 0.01 0x386194db34d47118
setup_fixed_benchmark runBalancedCompletion64 where
  fixedConfig 0.01 0x6dc7828c846f9e2b
setup_fixed_benchmark runBalancedCompletion72 where
  fixedConfig 0.01 0x2c5ab36c63d8144e
setup_fixed_benchmark runBalancedCompletion80 where
  fixedConfig 0.01 0x62b9a8e4f8df37af
/- Mode 3 for table dispatch: parameterising by integer value mixes unrelated
factor shapes, so the deterministic uniform batch is the canonical workload.
The headline report records the attempted mixed ladder and the batch's absolute
budget. `runTableTrial` is the output-agreeing direct-route timing anchor. -/
setup_fixed_benchmark runTableDispatch where
  fixedConfig 0.01 0x2e89d71edc0211cb
setup_fixed_benchmark runTableTrial where
  fixedConfig 0.01 0x2e89d71edc0211cb

/- Mode 3 for fixed-bound p-1: its word/direct-`Nat` transition and limb
plateaus defeated a stable one-parameter wall-time model. The canonical batch
covers every committed 32--80-bit success case under one reported budget. -/
setup_fixed_benchmark runPMinusOneBatch where
  fixedConfig 0.1 0xf15e2d694e366d3a

/- Mode 3 for fixed-bound ECM: a three-point word ladder and a three-point
direct-`Nat` ladder cannot distinguish constant, linear, and multiplication
costs. The canonical batch carries the absolute budget; the matched rho batch
is an output-agreeing route-policy timing anchor, not separate coverage. -/
setup_fixed_benchmark runEcmBatch where
  fixedConfig 0.1 0x32066d5482493644
setup_fixed_benchmark runEcmRhoBatch where
  fixedConfig 0.5 0x32066d5482493644
setup_fixed_benchmark runEcm48 where
  fixedConfig 0.02 0x00000000000f4243
setup_fixed_benchmark runEcm56 where
  fixedConfig 0.02 0x00000000000f4243
setup_fixed_benchmark runEcm64 where
  fixedConfig 0.02 0x00000000000f4243
setup_fixed_benchmark runEcm72 where
  fixedConfig 0.02 0x00000002003bafc5
setup_fixed_benchmark runEcm76 where
  fixedConfig 0.02 0x00000002003bafc5
setup_fixed_benchmark runEcm80 where
  fixedConfig 0.02 0x00000002003bafc5

/- Mode 3 for cyclotomic construction and power-form search: divisor shape and
the deterministic factor-search route make exponent-only slopes unstable. The
fixed 12--80-bit exponent batch is the canonical workload, and the generic/
split pair uses identical seeds and returns matching canonical complete
factorizations. Their operation-specific budgets live in the report. -/
setup_fixed_benchmark runCyclotomicBatch where
  fixedConfig 0.01 0x6338245641c4c84e
setup_fixed_benchmark runPowerGenericBatch where
  powerConfig 0x681a285cd74ea124
setup_fixed_benchmark runPowerSplitBatch where
  powerConfig 0x681a285cd74ea124

/- Mode 3 downstream cases. The exact 50- and 61-bit primes have short base-3
orders, so they test realistic operand sizes without pretending that the
reference linear scan is feasible for arbitrary 64-bit order. Opaque inputs
and noinline bodies prevent closed-term lifting; the report records separate
absolute budgets for order and primitive-root search. -/
setup_fixed_benchmark runDownstreamOrder where
  fixedConfig 0.01 0x748bc67983cb604e
setup_fixed_benchmark runDownstreamPrimitiveRoot where
  fixedConfig 0.02 0xf53a7f8b2ec1ebc6

end Hex.IntFactorBench

/- Attribution-only runners for representative mode-3 families whose
scientific targets are fixed batches.  The parameter is an honest repetition
count of one committed representative, so these registrations make the timed
region available to the compiled profiler without inventing an asymptotic
claim about the operand family. -/
namespace Hex.IntFactorProfile

@[noinline]
private def runSmoothOnce (salt : Nat) : Nat :=
  Hex.IntFactorBench.runEcmAt (80 + salt - salt)

def runSmooth (repeats : Nat) : Array Nat :=
  (List.range repeats).toArray.map runSmoothOnce

@[noinline]
private def runPowerOnce (salt : Nat) : List Nat :=
  Hex.IntFactorBench.runPowerSplit (80 + salt - salt)

def runPower (repeats : Nat) : Array (List Nat) :=
  (List.range repeats).toArray.map runPowerOnce

/- Cost model: each array entry performs the same committed 80-bit unbalanced
ECM stage-1 call, so `n` entries perform exactly `n` copies of fixed work.
The runtime salt blocks closed-term lifting while cancelling arithmetically. -/
setup_benchmark runSmooth n => n where {
  paramFloor := 1
  paramCeiling := 4
  paramSchedule := .custom #[1, 2, 3, 4]
  maxSecondsPerCall := 30.0
  targetInnerNanos := 1000000000
  outerTrials := 3
}

/- Cost model: each array entry performs the same committed exponent-80 power
factorization, so `n` entries perform exactly `n` copies of fixed work. -/
setup_benchmark runPower n => n where {
  paramFloor := 1
  paramCeiling := 4
  paramSchedule := .custom #[1, 2, 3, 4]
  maxSecondsPerCall := 30.0
  targetInnerNanos := 1000000000
  outerTrials := 3
}

end Hex.IntFactorProfile

def main (args : List String) : IO UInt32 :=
  match args with
  | ["default-fuel"] => Hex.IntFactorBench.reportDefaultFuel
  | ["control-audit"] => Hex.IntFactorBench.reportControls
  | ["split-probe"] => Hex.IntFactorBench.reportSplits
  | "ecm-probe" :: values => Hex.IntFactorBench.probeEcm values
  | _ => LeanBench.Cli.dispatch args
