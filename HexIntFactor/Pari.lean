/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Import
public import HexIntFactor.Factor

public section

/-! Explicit optional PARI factor discovery. Direct executable invocation and
bounded output reading follow HexECPPMathlib.Pari, without that dependency. -/

namespace Hex.Nat.Pari

/-- Parsing allocations are independent of process and certificate allocations. -/
structure ParseBudget where
  maxBytes : Nat := 16448
  maxBits : Nat := 256
  maxEntries : Nat := 64
  maxDigits : Nat := 78
  maxExponent : Nat := 256
deriving Repr

/-- Narrow framing, number grammar and allocation diagnostics. -/
inductive ParseError where
  | bounds | framing | number | exponent | subjectMismatch
deriving Repr, BEq

private def decimal (b : ParseBudget) (text : String) : Except ParseError Nat := do
  if text.isEmpty || text.utf8ByteSize > b.maxDigits then throw .bounds
  unless text.toList.all (fun c => '0' ≤ c && c ≤ '9') do throw .number
  let some n := text.toNat? | throw .number
  if HexArith.bitLength n > b.maxBits then throw .bounds
  return n

/-- Parse only bounded ASCII decimal lines; no arithmetic or primality is trusted. -/
def parse (b : ParseBudget) (n : Nat) (text : String) : Except ParseError FactorProposal := do
  if text.utf8ByteSize > b.maxBytes then throw .bounds
  let text := if text.endsWith "\n" then (text.dropEnd 1).toString else text
  let lines := text.splitOn "\n"
  unless lines.head? == some "HEX_FACTOR_BEGIN" && lines.getLast? == some "HEX_FACTOR_END" do
    throw .framing
  let payload := lines.drop 1 |>.dropLast
  let subject :: entries := payload | throw .framing
  if entries.length > b.maxEntries then throw .bounds
  unless (← decimal b subject) == n do throw .subjectMismatch
  let entries ← entries.mapM fun line => do
    let [p, e] := line.splitOn " " | throw ParseError.number
    let p ← decimal b p
    let e ← decimal b e
    if e == 0 || e > b.maxExponent then throw .exponent
    return ((p : Int), (e : Int), none)
  return ⟨n, entries⟩

/-- Finite process limits; request stack size is fixed and startup files disabled. -/
structure ProcessBudget where
  timeoutMs : Nat := 30000
  maxOutputBytes : Nat := 16448
  maxErrorBytes : Nat := 4096
deriving Repr

/-- Process failure never says anything about the factorization subject. -/
inductive ProcessError where
  | missing
  | start (detail : String)
  | failed (exitCode : UInt32) (stderr : String)
  | timeout | cancelled | stdoutLimit | stderrLimit | utf8 | unsupported
  | pipe (detail : String)
  | subjectBounds | zero
deriving Repr, BEq

private def readBounded (handle : IO.FS.Handle) (limit : Nat) (overflow : ProcessError) :
    IO (Except ProcessError String) := do
  let mut data := ByteArray.empty
  repeat
    let chunk ← handle.read 4096
    if chunk.isEmpty then
      return match String.fromUTF8? data with
        | some text => .ok text
        | none => .error .utf8
    if data.size + chunk.size > limit then return .error overflow
    data := data ++ chunk

private def reader (t : Task (Except IO.Error (Except ProcessError String))) :
    Except ProcessError String :=
  match t.get with
  | .ok result => result
  | .error err => .error (.pipe err.toString)

private def requestFile (n : Nat) : IO System.FilePath := do
  let (handle, path) ← IO.FS.createTempFile
  try
    handle.putStr s!"default(nbthreads,1); f=factor({n}); print(\"HEX_FACTOR_BEGIN\"); print({n}); for(i=1,matsize(f)[1],print(f[i,1],\" \",f[i,2])); print(\"HEX_FACTOR_END\"); quit\n"
    handle.flush
    return path
  catch err =>
    IO.FS.removeFile path
    throw err

private def runFile (request : System.FilePath) (b : ProcessBudget)
    (executable : String) (cancel : Option IO.CancelToken) :
    IO (Except ProcessError String) := do
  let child ← try
    IO.Process.spawn {
      cmd := executable
      args := #["-q", "-f", "-s", "64000000", request.toString]
      stdin := .null
      stdout := .piped
      stderr := .piped
      setsid := true }
  catch err => return .error (.start err.toString)
  let stdout ← IO.asTask (readBounded child.stdout b.maxOutputBytes .stdoutLimit) .dedicated
  let stderr ← IO.asTask (readBounded child.stderr b.maxErrorBytes .stderrLimit) .dedicated
  let start ← IO.monoMsNow
  let reaped ← IO.mkRef false
  try
    repeat
      if let some token := cancel then
        if ← token.isSet then return .error .cancelled
      if (← IO.monoMsNow) - start ≥ b.timeoutMs then return .error .timeout
      let outDone ← IO.hasFinished stdout
      let errDone ← IO.hasFinished stderr
      if outDone then
        if let .error err := reader stdout then return .error err
      if errDone then
        if let .error err := reader stderr then return .error err
      if outDone && errDone then
        discard <| IO.wait stdout
        discard <| IO.wait stderr
        if let some status ← child.tryWait then
          reaped.set true
          let .ok output := reader stdout | return reader stdout
          let .ok errors := reader stderr | return reader stderr
          if status == 255 && (errors.splitOn "could not execute external process").length > 1 then
            return .error .missing
          if status != 0 || !errors.isEmpty then return .error (.failed status errors)
          return .ok output
      IO.sleep 25
  finally
    unless ← reaped.get do
      try child.kill catch _ => pure ()
      discard <| IO.wait stdout
      discard <| IO.wait stderr
      try discard <| child.wait catch _ => pure ()
      reaped.set true

/-- Direct executable invocation with bounded numeral input; never uses a shell.
The request file is removed on success and failure. This producer supports
POSIX platforms. -/
def run (n : Nat) (b : ProcessBudget := {}) (executable : String := "gp")
    (cancel : Option IO.CancelToken := none) (parser : ParseBudget := {}) :
    IO (Except ProcessError String) := do
  if n == 0 then return .error .zero
  if System.Platform.isWindows then return .error .unsupported
  if HexArith.bitLength n > parser.maxBits then return .error .subjectBounds
  if (toString n).utf8ByteSize > parser.maxDigits then return .error .subjectBounds
  if let some token := cancel then
    if ← token.isSet then return .error .cancelled
  if n == 1 then return .ok "HEX_FACTOR_BEGIN\n1\nHEX_FACTOR_END\n"
  let request ← try requestFile n catch err => return .error (.start err.toString)
  try runFile request b executable cancel
  finally IO.FS.removeFile request

/-- Discovery and parsing failures have different diagnostic types. -/
inductive ProducerError where
  | process (error : ProcessError)
  | parse (error : ParseError)
deriving Repr

/-- Produce untrusted proposals explicitly, without certification or native search. -/
def produce (n : Nat) (process : ProcessBudget := {}) (parser : ParseBudget := {})
    (executable : String := "gp") (cancel : Option IO.CancelToken := none) :
    IO (Except ProducerError FactorProposal) := do
  match ← run n process executable cancel parser with
  | .error err => return .error (.process err)
  | .ok text => return (parse parser n text).mapError ProducerError.parse

/-- Independent finite allocation for each eligible native fallback piece. -/
structure NativeBudget where
  factorFuel : Nat := 4
  primeFuel : Nat := 8
  primeBudget : PrimeCertBudget := ⟨2, 65536, .off⟩
deriving Repr

/-- Backend history survives eventual native completion or exhaustion. -/
inductive Diagnostic where
  | producer (error : ProducerError)
  | importer (error : ImportError)
  | completion (piece : ResidualPiece)
  | native (subject : Nat) (stop : FactorStop)
  | mergeError (subject : Nat) (error : ImportError)
  | cancelled
deriving Repr

/-- Optional production result; incomplete native progress remains checked data.
`imported` retains the original validated residual pieces, not current hints.
Native rejected candidates and their recovery snapshots are retained separately. -/
structure Result (n : Nat) where
  value : Option (CheckedFactors n) := none
  rand : Hex.Rand
  diagnostics : List Diagnostic := []
  imported : Option (ImportResult n) := none
  nativeFailures : List (Nat × FactorFailure) := []

private def isCancelled (cancel : Option IO.CancelToken) : IO Bool := do
  match cancel with
  | none => return false
  | some token => token.isSet

/-- Native fallback is one finite stage: at most one call per validated composite
piece and one for the unlisted quotient. Exhausted prime construction is retained,
never retried with the weaker ordinary native allocation. -/
def fallback (b : ImportBudget) (native : NativeBudget) (n : Nat)
    (saved : ImportResult n) (diagnostics : List Diagnostic := [])
    (cancel : Option IO.CancelToken := none) : IO (Result n) := do
  let mut value := saved.value
  let mut rand := saved.rand
  let mut diagnostics := diagnostics ++ saved.unresolved.map Diagnostic.completion
  let mut failures := []
  let pieces := (if saved.unlisted > 1 then [(saved.unlisted, 1)] else []) ++
    (saved.unresolved.filterMap fun p =>
      if p.stop == .composite then some (p.base, p.exponent) else none)
  for (base, exponent) in pieces do
    if ← isCancelled cancel then
      return ⟨some value, rand, diagnostics ++ [.cancelled], some saved, failures⟩
    let found := Internal.factorCountedWith? native.primeBudget native.primeFuel
      base rand native.factorFuel false .off
    let powers ← match found with
      | .ok success =>
          rand := success.rand
          pure success.factorization.raw.factors
      | .error failure =>
          rand := failure.rand
          diagnostics := diagnostics ++ [.native base failure.stop]
          failures := failures ++ [(base, failure)]
          -- Preserve previous checked data on rejection; retain the candidate.
          if failure.stop == .rejected then continue
          pure ((failure.snapshot.map (·.raw.factors)).getD [])
    let powers := powers.map fun e => { e with exponent := e.exponent * exponent }
    let combined := Internal.mergePowers powers value.raw.factors
    -- Supplied native evidence and aggregate multiplicities pass import bounds.
    let proposal : FactorProposal := ⟨n, combined.map fun e =>
      ((e.prime : Int), (e.exponent : Int), some e.cert)⟩
    match importFactors { b with completion := { b.completion with maxAttempts := 0 } }
        n proposal rand with
    | .ok progress => value := progress.value
    | .error err => diagnostics := diagnostics ++ [.mergeError base err]
  if ← isCancelled cancel then diagnostics := diagnostics ++ [.cancelled]
  return ⟨some value, rand, diagnostics, some saved, failures⟩

/-- Explicit external assistance with bounded native fallback. Ordinary native
APIs and pure FactorSearch callbacks are unchanged and never invoke this route. -/
def factor (n : Nat) (r : Hex.Rand) (b : ImportBudget := {})
    (process : ProcessBudget := {}) (parser : ParseBudget := {}) (native : NativeBudget := {})
    (executable : String := "gp") (cancel : Option IO.CancelToken := none) : IO (Result n) := do
  let empty ← match importFactors b n ⟨n, []⟩ r with
    | .error err => return ⟨none, r, [.importer err], none, []⟩
    | .ok progress => pure progress
  if ← isCancelled cancel then return ⟨some empty.value, r, [.cancelled], none, []⟩
  if n == 1 then return ⟨some empty.value, r, [], none, []⟩
  match ← produce n process parser executable cancel with
  | .error (.process .cancelled) => return ⟨some empty.value, r, [.cancelled], none, []⟩
  | .error err => fallback b native n empty [.producer err] cancel
  | .ok proposal =>
      match importFactors b n proposal r with
      | .error err => fallback b native n empty [.importer err] cancel
      | .ok saved =>
          match saved.value with
          | .complete _ =>
              if ← isCancelled cancel then
                return ⟨some saved.value, saved.rand, [.cancelled], some saved, []⟩
              return ⟨some saved.value, saved.rand, [], some saved, []⟩
          | .partialResult _ => fallback b native n saved [] cancel

end Hex.Nat.Pari
