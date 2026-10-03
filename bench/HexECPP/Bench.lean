/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Search
import HexECPP.Fixture65
import HexECPP.Fixture256
import HexECPP.Fixture512
import HexECPP.ImportConformance
import HexECPP.PariFixtures
import LeanBench

/-!
Mathlib-free compiled ECPP measurements. Conversion, checking, and raw
certificate size have separate registrations; kernel replay is measured in
fresh bridge proof modules.

The complete accepted-certificate and native endpoint registrations use
mode 3. Subject-bit ladders vary witness counts, recursive leaves and search
branches independently; the frozen corpus has both success and exhaustion
at each size. Those ladders therefore do not have a tight scalar wall-time
model, and a published bound on scalar replay does not cover factor search
or terminal construction. Asymptotic detection for these complete endpoints
is replaced by operation-specific regression budgets in `ecpp_audit.py`,
derived before measurement from twice the retained endpoint medians. Parser
and scalar primitives instead use the independently derived ladders below.
`runSize*` remain observation/hash anchors without budgets.
-/

open Hex.ECPP

private instance : Inhabited Cert := ⟨.base (.small 2)⟩

initialize cert65Ref : IO.Ref Cert ← IO.mkRef Fixture65.cert
initialize cert256Ref : IO.Ref Cert ← IO.mkRef Fixture256.cert
initialize cert512Ref : IO.Ref Cert ← IO.mkRef Fixture512.cert
initialize pari65Ref : IO.Ref String ← IO.mkRef ImportConformance.pari65
initialize pari256Ref : IO.Ref String ← IO.mkRef PariFixtures.pari256
initialize pari512Ref : IO.Ref String ← IO.mkRef PariFixtures.pari512

def runCheck65 (_ : Unit) : IO Nat := do
  return if checkAt 18446744073709551629 (← cert65Ref.get) then 1 else 0

def runCheck256 (_ : Unit) : IO Nat := do
  return if check (← cert256Ref.get) then 1 else 0

def runCheck512 (_ : Unit) : IO Nat := do
  return if check (← cert512Ref.get) then 1 else 0

def runConvert65 (_ : Unit) : IO Nat := do
  return match convertText ImportConformance.budget (← pari65Ref.get)
      Fixture65.child with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runConvert256 (_ : Unit) : IO Nat := do
  return match convertText defaultImportBudget (← pari256Ref.get)
      PariFixtures.leaf256 with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runConvert512 (_ : Unit) : IO Nat := do
  return match convertText defaultImportBudget (← pari512Ref.get)
      PariFixtures.leaf512 with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runParse512 (_ : Unit) : IO Nat := do
  return match parsePari defaultImportBudget (← pari512Ref.get) with
  | .ok c => c.rows.length
  | .error _ => 0

private partial def certSize : Cert → Nat
  | .base _ => 1
  | .step _ _ _ _ _ _ ws child => 1 + ws.length + certSize child

def runSize65 (_ : Unit) : IO Nat := return certSize (← cert65Ref.get)
def runSize256 (_ : Unit) : IO Nat := return certSize (← cert256Ref.get)
def runSize512 (_ : Unit) : IO Nat := return certSize (← cert512Ref.get)

setup_fixed_benchmark runCheck65 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runCheck256 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runCheck512 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert65 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert256 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert512 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runParse512 where {
  repeats := 3
  expectedHash := some (hash (17 : Nat))
}
setup_fixed_benchmark runSize65 where { repeats := 3 }
setup_fixed_benchmark runSize256 where { repeats := 3 }
setup_fixed_benchmark runSize512 where { repeats := 3 }

private def terminal : Cert → Hex.Nat.PrimeCert
  | .base c => c
  | .step _ _ _ _ _ _ _ c => terminal c

initialize native128Ref : IO.Ref Nat ← IO.mkRef 177080666831933235355717939809840315427
initialize native256Ref : IO.Ref Nat ← IO.mkRef 69199437377629051939477864552334532767081794053034238723740032946332041487367
initialize nativeHardRef : IO.Ref Nat ← IO.mkRef 96590133568377947488922651108406533027621815589740576200326951544495709460191
initialize nativeCertRef : IO.Ref (Option Cert) ← IO.mkRef none

/-- Warm the fixed replay input outside measurement; ordinary scalar/parser
children need no native search during startup. Failure cannot become a leaf. -/
def nativeCert : IO Cert := do
  if let some c ← nativeCertRef.get then return c
  let n ← native256Ref.get
  let .ok c := (produce n 0).result | throw (IO.userError "native fixture exhausted")
  nativeCertRef.set (some c)
  return c

@[noinline] def runNative128 (_ : Unit) : IO Nat := do
  let n ← native128Ref.get
  return if (produce n 0).result.toOption.any (checkAt n) then 1 else 0

@[noinline] def runNative256 (_ : Unit) : IO Nat := do
  let n ← native256Ref.get
  return if (produce n 0).result.toOption.any (checkAt n) then 1 else 0

/-- Frozen validation-256-7, seed seven: the longest retained native chain.
Its 3.3-second per-call ceiling is twice the retained 1.638-second observation
rounded upward, not the harness timeout. -/
@[noinline] def runNativeHard (_ : Unit) : IO Nat := do
  let n ← nativeHardRef.get
  return if (produce n 7).result.toOption.any (checkAt n) then 1 else 0

@[noinline] def runNativeCheck (_ : Unit) : IO Nat := do
  return if checkAt (← native256Ref.get) (← nativeCert) then 1 else 0

@[noinline] def runNativeConvert (_ : Unit) : IO Nat := do
  let c ← nativeCert
  return if (convertText defaultImportBudget (frozenRows c) (terminal c)).toOption.any
    (checkAt c.subject) then 1 else 0

setup_fixed_benchmark runNative128 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNative256 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeHard where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeCheck where {
  repeats := 5, warmupFirstIter := true, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeConvert where {
  repeats := 5, warmupFirstIter := true, expectedHash := some (hash (1 : Nat)) }

initialize native512Ref : IO.Ref Nat ← IO.mkRef 12655077169514309177840953837335225568096061334897322610772679501937608896257370675750838605329022124937902809437637812352386386288931562255682923262789457
initialize native512CertRef : IO.Ref (Option Cert) ← IO.mkRef none

private def native512Cert : IO Cert := do
  if let some c ← native512CertRef.get then return c
  let n ← native512Ref.get
  let .ok c := (produce n 0 public512Budget).result
    | throw (IO.userError "native 512-bit fixture exhausted")
  native512CertRef.set (some c)
  return c

/-- Fixed heldout-512-ordinary-0, seed zero. Mode 3: search branches and
terminal shape do not admit a tight subject-width wall-time model. The
five-second ceiling is declared before bench collection, above twice the
retained whole-route search measurements. -/
@[noinline] def runNative512 (_ : Unit) : IO Nat := do
  let n ← native512Ref.get
  return if (produce n 0 public512Budget).result.toOption.any (checkAt n) then 1 else 0

/-- Warmed native 512-bit checking; 80 ms is above twice the retained
29.5 ms checking observation and is distinct from the subprocess cap. -/
@[noinline] def runNative512Check (_ : Unit) : IO Nat := do
  return if checkAt (← native512Ref.get) (← native512Cert) then 1 else 0

/-- Warmed native 512-bit conversion; 300 ms is above twice the retained
112.4 ms observation. Production stays outside this timed operation. -/
@[noinline] def runNative512Convert (_ : Unit) : IO Nat := do
  let c ← native512Cert
  return if (convertText defaultImportBudget (frozenRows c) (terminal c)).toOption.any
    (checkAt c.subject) then 1 else 0

setup_fixed_benchmark runNative512 where {
  repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNative512Check where {
  repeats := 5, warmupFirstIter := true, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNative512Convert where {
  repeats := 5, warmupFirstIter := true, expectedHash := some (hash (1 : Nat)) }

/-- Square root, Cornacchia norm and the complete exceptional twist portfolio,
checked by their integer equations on runtime inputs. -/
private def cmProposals (n d : Nat) : Bool := Id.run do
  let k := if d % 4 == 0 then d / 4 else d
  let a := modSub n 0 k
  let some r := CM.sqrt? n 3 a | return false
  let some (t, v) := CM.norm? n d r | return false
  let curves := CM.portfolio.flatMap (fun inv => CM.curves n inv 3)
  return CM.rootValid n a r && CM.normValid n d t v &&
    (CM.traces d t v).length == (if d == 3 then 6 else 4) &&
    curves.length == 24 && curves.all (fun (a, b) =>
      a < n && b < n && (4 * a * a * a + 27 * b * b) % n != 0)

initialize cm128Ref : IO.Ref Nat ← IO.mkRef 305927751028606010005614597858307057793
initialize exhaustedRef : IO.Ref Nat ← IO.mkRef 86906364443826889462434168665794151905575430136092680752789091262591140309013

@[noinline] def runCM128 (_ : Unit) : IO Nat := do
  return if cmProposals (← cm128Ref.get) 4 then 1 else 0

@[noinline] def runCM256 (_ : Unit) : IO Nat := do
  return if cmProposals (← nativeHardRef.get) 3 then 1 else 0

@[noinline] def runCountedConvert65 (_ : Unit) : IO Nat := do
  return match parsePari defaultImportBudget (← pari65Ref.get) with
  | .error _ => 0
  | .ok input => if (convertCounted defaultImportBudget Hex.Nat.defaultPrimeCertBudget
      (Hex.Rand.ofSeed 1) 200 input).toOption.any (fun result => checkAt input.subject result.1) then 1 else 0

/-- Frozen tuning-256-3 exercises the complete root portfolio without an
accepted point; its resource result is content checked. -/
@[noinline] def runNativeExhaust (_ : Unit) : IO Nat := do
  let n ← exhaustedRef.get
  return match (produce n 3).result with
  | .error e => if e.resource == .portfolio && e.subject == n then 1 else 0
  | .ok _ => 0

setup_fixed_benchmark runCM128 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runCM256 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runCountedConvert65 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeExhaust where { repeats := 5, expectedHash := some (hash (1 : Nat)) }

/-!
# Controlled ECPP input families

Scalar length varies with a fixed small modulus and a nonidentity point of
order thirteen. Parsing varies the number of fixed-width rows, independently
of primality and certificate generation. Setup remains outside timed regions.
-/

namespace Hex.ECPPBench
open Hex.ECPP

private instance : Hashable ImportBudget := ⟨fun b => hash (reprStr b)⟩
private instance : Hashable PariCertificate := ⟨fun c => hash (reprStr c)⟩

def scalarInput (bits : Nat) : Nat × List Nat :=
  let q := 13 * (2 ^ (max 1 bits) - 1)
  let b := { defaultImportBudget with
    maxScalarBits := bits + 4, maxInverseOps := 2 * (bits + 4) }
  let ws := match proposeScalar b 7 0 q (.affine 1 2) with
    | .ok (_, ws) => ws
    | .error _ => []
  (q, ws)

@[noinline] def runReplay (input : Nat × List Nat) : Bool :=
  replayDone 7 0 3 input.1 (.affine 1 2) input.2

@[noinline] def runProposal (input : Nat × List Nat) : Bool :=
  (proposeScalar { defaultImportBudget with
    maxScalarBits := HexArith.bitLength input.1,
    maxInverseOps := 2 * HexArith.bitLength input.1 }
    7 0 input.1 (.affine 1 2)).toOption.any fun (p, ws) =>
      p == .infinity && ws == input.2

-- Derivation: dense scalars 13*(2^k-1) have k+O(1) bits. The SPEC
-- prescribes Nat.testBit, defined in Lean 4.35 as 1 &&& (q >>> i) != 0.
-- For a bignum q, each shift materializes its remaining suffix: summing
-- k-i bits over the k positions costs Theta(k^2 / wordBits). The affine
-- operations modulo seven and witness traversal contribute Theta(k).
-- Thus the compiled large-scalar family is quadratic, while the SPEC's
-- separate O(L) modular-ring-operation count remains linear. These
-- sizes expose the bignum regime.
setup_benchmark runReplay k => k * k with prep := scalarInput where {
  paramFloor := 262144, paramCeiling := 4194304, outerTrials := 3
  targetInnerNanos := 5000000000, maxSecondsPerCall := 1200.0
}

-- Derivation: the identical bit extraction has Theta(k^2 / wordBits)
-- suffix-copy cost. Fixed-modulus extended GCD, witness reversal and
-- comparison contribute only Theta(k). This is a compiled-time claim,
-- not a replacement for the SPEC's modular-operation bound.
setup_benchmark runProposal k => k * k with prep := scalarInput where {
  paramFloor := 262144, paramCeiling := 4194304, outerTrials := 3
  targetInnerNanos := 5000000000, maxSecondsPerCall := 1200.0
}

def rowBudget (rows : Nat) : ImportBudget :=
  { defaultImportBudget with maxInputBytes := 64 * rows + 64, maxRows := rows }

def textInput (rows : Nat) : ImportBudget × String :=
  (rowBudget rows, "[" ++ String.intercalate ","
    (List.replicate (max 1 rows) "[7,-5,1,0,[1,2]]") ++ "]")

@[noinline] def runParse (input : ImportBudget × String) : Nat :=
  match parsePari input.1 input.2 with
  | .ok c => c.rows.length
  | .error _ => 0

def parsedInput (rows : Nat) : ImportBudget × PariCertificate :=
  (rowBudget rows, ⟨List.replicate rows ⟨7, -5, 1, 0, ⟨1, 2, 1⟩⟩, 13⟩)

@[noinline] def runPreflight (input : ImportBudget × PariCertificate) : Bool :=
  (preflight input.1 input.2).isOk

-- Derivation: r fixed-width row tokens contain Theta(r) bytes and integers.
-- Digit scanning, JSON parsing, decoding and the terminal-row lookup each
-- traverse them once. Bounded integer arithmetic has constant cost here.
setup_benchmark runParse r => r with prep := textInput where {
  paramFloor := 1, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 8.0
}

-- Derivation: list length, seven fixed-width bit checks per row and original
-- index traversal each cost Theta(r); no endpoint construction is timed.
setup_benchmark runPreflight r => r with prep := parsedInput where {
  paramFloor := 1, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 8.0
}

/-- Prime moduli at the actual requested widths. The generator and complete
output are retained in `reports/ecpp/audit/sized-primes.json`. -/
def sizedPrimes : List (Nat × Nat) := [
  (64, 9223372036854775907),
  (128, 170141183460469231731687303715884105979),
  (256, 57896044618658097711785492504343953926634992332820282019728792003956564820243),
  (512, 6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042857),
  (1024, 89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112069763),
  (2048, 16158503035655503650357438344334975980222051334857742016065172713762327569433945446598600705761456731844358980460949009747059779575245460547544076193224141560315438683650498045875098875194826053398028819192033784138396109321309878080919047169238085235290822926018152521443787945770532904303776199561965192760957166694834171210342487393282284747428088017663161029038902829665513096354230157075129296432088558362971801859230928678799175576150822952201848806616643615613562842355410104862578550863465661734839271290328348967522998634176499319107762583194718667771801067716614802322659239302476074096777926805529798117439),
  (4096, 522194440706576253345876355358312191289982124523691890192116741641976953985778728424413405967498779170445053357219631418993786719092896803631618043925682638972978488271854999170180795067191859157214035005927973113188159419698856372836167342172293308748403954352901852035642024370059304557233988891799014503343469488440893892973452815095130470299789726716411734651513348221529512507986199933857107770846917779942645743159118957217248367043905936319748237550094520674504208530837546834166925275516486044134775384991808184705966507606898412918594045916828375610659246423184062775112999150206172392431297837246097308511903252956622805412865917690043804311051417135098849101156584508839003337597742539960818209685142687562392007453579567729991395256699805775897135553415567045292136442139895777424891477161767258532611634530697452993846501061481697843891439474220308003706472837459911525285821188577408160690315522951458068463354171428220365223949985950890732881736611925133626529949897998045399734600887312408859224933727829625089164535236559716582775403784110923285873186648442456409760158728501220463308455437074192539205964902261490928669488824051563042951500651206733594863336608245755565801460390869016718045121902354170201577101317)]


/-- Runtime residues and a complete expected scalar result at real modulus widths. -/
structure SizedCase where
  n : Nat
  b : Nat
  q : Nat
  point : Point
  result : Point
  inverses : List Nat
  deriving Repr

private instance : Hashable SizedCase := ⟨fun input => hash (reprStr input)⟩

/-- Use independently generated primes and full-width nontrivial coordinates.
Dense scalar and modulus widths grow together; setup is outside measurement. -/
private def sizedCase (n bits : Nat) : SizedCase := Id.run do
  let x := n / 3 + 1
  let y := n / 7 + 1
  let b := modSub n (y * y % n) ((x * x * x + 5 * x) % n)
  let q := 2 ^ bits - 1
  let point := Point.affine x y
  let budget := { defaultImportBudget with maxScalarBits := bits, maxInverseOps := 2 * bits }
  let result := (proposeScalar budget n 5 q point).toOption.getD (.infinity, [])
  return ⟨n, b, q, point, result.1, result.2⟩

/-- Grow scalar and modulus widths together, including downstream sizes. -/
def sizedInput (bits : Nat) : SizedCase :=
  sizedCase ((sizedPrimes.find? (fun row => row.1 == bits)).getD (sizedPrimes.head!) |>.2) bits

/-- Vary scalar width independently at a supplied-certificate modulus. -/
def scalarWidthInput (bits : Nat) : SizedCase :=
  sizedCase 18446744073709551629 bits

/-- Vary modulus width independently at the 65-bit vector's 47-bit cofactor. -/
def modulusWidthInput (bits : Nat) : SizedCase :=
  sizedCase ((sizedPrimes.find? (fun row => row.1 == bits)).getD (sizedPrimes.head!) |>.2) 47

@[noinline] def runSizedReplay (input : SizedCase) : Bool :=
  onCurve input.n 5 input.b (input.n / 3 + 1) (input.n / 7 + 1) &&
  (replay input.n 5 input.b input.q input.point input.inverses).any
    (fun result => result.1 == input.result && result.2.isEmpty)

@[noinline] def runSizedProposal (input : SizedCase) : Bool :=
  let bits := HexArith.bitLength input.q
  (proposeScalar { defaultImportBudget with maxScalarBits := bits, maxInverseOps := 2 * bits }
    input.n 5 input.q input.point).toOption.any fun result =>
      result.1 == input.result && result.2 == input.inverses

-- Mode 2. Both scalar and modulus have k bits, including the real 64..512
-- caller range. Replay performs at most 2*k affine additions. GMP's documented
-- basecase multiply/divide bound is quadratic in operand bits; faster regimes
-- improve that bound. Nat.testBit copies contribute O(k^2), so O(k^3) bounds
-- this compiled workload. No tight monomial spans GMP's changing algorithms.
-- Sources: gmplib.org/manual/Basecase-Multiplication and Basecase-Division.
setup_benchmark runSizedReplay k => k * k * k with prep := sizedInput where {
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 5000000000, maxSecondsPerCall := 120.0
}

-- Mode 2. Classical extended Euclid costs O(k^2): quotient bit lengths
-- sum to O(k), and each division/coefficient update costs at most its quotient
-- width times k. At most 2*k inverse proposals give O(k^3). The compiled
-- Nat recurrence uses these operations, rather than a direct GMP GCDEXT call.
-- Source: Brent/Zimmermann, Modern Computer Arithmetic, sections 1.6/1.6.2/2.5,
-- https://maths-people.anu.edu.au/~brent/pd/mca-cup-0.5.9.pdf.
setup_benchmark runSizedProposal k => k * k * k
  with prep := sizedInput where {
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 5000000000, maxSecondsPerCall := 120.0
}

-- Independent axes. With fixed modulus, k scalar bits cost O(k^2) in
-- prescribed bit extraction and O(k) bounded-width affine/inverse work.
-- With fixed scalar, only a constant number of additions and inverses occur;
-- quadratic basecase arithmetic/classical Euclid bounds k-bit moduli.
-- These registrations measure wrappers around the identical timed callbacks.
@[noinline] def runScalarReplay (input : SizedCase) : Bool := runSizedReplay input
@[noinline] def runScalarProposal (input : SizedCase) : Bool := runSizedProposal input
@[noinline] def runModulusReplay (input : SizedCase) : Bool := runSizedReplay input
@[noinline] def runModulusProposal (input : SizedCase) : Bool := runSizedProposal input

-- Linear bounded-width regime: at most eight limbs per scalar bit extraction,
-- with a fixed 65-bit modulus and at most 2*bits bounded-width additions.
setup_benchmark runScalarReplay bits => bits with prep := scalarWidthInput where {
  paramFloor := 32, paramCeiling := 512, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 120.0
}
-- Linear bounded-width regime: the same scalar copies and at most 2*bits
-- inverses on fixed 65-bit operands; Euclid coefficients remain bounded.
setup_benchmark runScalarProposal bits => bits with prep := scalarWidthInput where {
  paramFloor := 32, paramCeiling := 512, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 120.0
}
-- Quadratic upper bound: a fixed 47-bit scalar performs boundedly many ring operations.
setup_benchmark runModulusReplay bits => bits * bits with prep := modulusWidthInput where {
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 120.0
}
-- Quadratic upper bound: boundedly many classical extended Euclid calls.
setup_benchmark runModulusProposal bits => bits * bits with prep := modulusWidthInput where {
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 120.0
}

end Hex.ECPPBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
