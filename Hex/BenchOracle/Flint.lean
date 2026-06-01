import Lean.Data.Json
import Lean.Data.Json.FromToJson

/-!
# Shared FLINT persistent-subprocess bench driver helper

This module is the Lean-side companion to
`scripts/oracle/flint_bench_driver.py`. Per
`SPEC/benchmarking.md` (post-#3657) §"External comparators"
§"Process call", FLINT comparators with non-negligible per-call
overhead are wired as a persistent subprocess: the driver loops on
stdin (one JSON request per line, see the driver's docstring for the
framing protocol), and the bench harness reuses one driver process
across every measured call inside a single
`lake exe hexfoo_bench run` invocation.

This module owns:

* `PersistentComparator` — wraps the post-`takeStdin` Lean
  `IO.Process.Child` plus its persistent stdin handle (so the
  process is not reaped while the bench process holds a reference).
* `flintDriverRef` — module-level `IO.Ref` caching the running
  driver across calls inside one bench process.
* `runRequest`, `runOp` — high-level helpers that build a JSON
  request, send it through the driver, parse the reply, and surface
  driver-side errors as `IO.userError`. On stream errors the cached
  child is dropped, a fresh driver is spawned, and the request is
  retried once.

## Per-library wiring

Each consuming library (HexPoly, HexPolyZ, HexHensel, HexMatrix,
HexBerlekamp, HexGFqRing) calls `Hex.BenchOracle.Flint.runOp` from
its `Bench.lean` and parses the returned `Json` per its family's
result schema. Example (sketch — actual wiring lands in the
per-library HOs, HO-21..HO-26)::

  open Lean (Json)
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "mul"
    #[("a", coeffsToJson a), ("b", coeffsToJson b)]
  let coeffs ← jsonToCoeffs result

## Configuration

* `HEX_FLINT_BENCH_DRIVER` — absolute path to the driver script,
  overriding the default `scripts/oracle/flint_bench_driver.py`
  (relative to the bench process's cwd, which is the repo root
  under `lake exe`).
* `HEX_FLINT_BENCH_PYTHON` — interpreter command (default
  `python3`). Useful in CI when only `python` is on `PATH`.
-/

namespace Hex.BenchOracle.Flint

open Lean (Json JsonNumber)
open IO.FS (Handle)
open IO.Process

/-- Persistent child process for a comparator that loops on
stdin / stdout.

* `stdin` is the writable handle returned by
  `Child.takeStdin`.
* `child` is the post-`takeStdin` `Child` (so its `stdin` field is
  `Stdio.null`); we keep it so the process is not reaped while the
  benchmark holds the comparator.
-/
structure PersistentComparator where
  stdin : Handle
  child : Child { stdin := .null, stdout := .piped, stderr := .piped }

namespace PersistentComparator

/-- Spawn a child process with piped stdin/stdout/stderr and detach
its stdin handle via `Child.takeStdin` so the bench harness can
write requests without blocking on the child's exit. -/
def spawn (cmd : String) (args : Array String := #[])
    (cwd : Option System.FilePath := none) : IO PersistentComparator := do
  let raw ← IO.Process.spawn
    { cmd := cmd, args := args, cwd := cwd,
      stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← raw.takeStdin
  return { stdin := stdin, child := child }

/-- Write one request line and read one reply line. The caller
embeds any framing into `request`; this helper appends `'\n'`,
flushes stdin, then blocks on `getLine`. Raises `IO.userError` if
the child closes stdout before replying (the empty-line case). -/
def requestLine (c : PersistentComparator) (request : String) : IO String := do
  c.stdin.putStr (request ++ "\n")
  c.stdin.flush
  let reply ← c.child.stdout.getLine
  if reply.isEmpty then
    throw <| IO.userError "flint_bench_driver closed stdout before replying"
  return reply

end PersistentComparator

/-- Module-level cache of the running FLINT bench driver. Populated
lazily on first request; reset to `none` on stream error so the next
request re-spawns the driver. -/
initialize flintDriverRef : IO.Ref (Option PersistentComparator) ←
  IO.mkRef none

private def envOr (name : String) (default : String) : IO String := do
  match (← IO.getEnv name) with
  | some v => return v
  | none => return default

private def driverPath : IO String :=
  envOr "HEX_FLINT_BENCH_DRIVER" "scripts/oracle/flint_bench_driver.py"

private def pythonCommand : IO String :=
  envOr "HEX_FLINT_BENCH_PYTHON" "python3"

/-- Lazily spawn the persistent FLINT driver, or return the cached
handle. The driver is invoked as `<python> <driver-script>`. -/
def resolveDriver : IO PersistentComparator := do
  if let some ch ← flintDriverRef.get then
    return ch
  let py ← pythonCommand
  let script ← driverPath
  let ch ← PersistentComparator.spawn py #[script]
  flintDriverRef.set (some ch)
  return ch

/-- Send a single JSON request line and return the parsed JSON
reply. On any `IO` error from the stream (driver crash, pipe close)
the cached child handle is dropped, a fresh driver is spawned, and
the request is retried once. Persistent failure surfaces as an
`IO.userError` from the retry path. -/
def sendRequest (request : Json) : IO Json := do
  let line := request.compress
  let reply ←
    try
      (← resolveDriver).requestLine line
    catch _ =>
      flintDriverRef.set none
      (← resolveDriver).requestLine line
  match Json.parse reply with
  | .ok j => return j
  | .error err =>
    throw <| IO.userError s!"flint_bench_driver reply not valid JSON: {err}; reply: {reply}"

/-- Build the request JSON object from `family`, `op`, and a list of
extra fields, send it through the driver, and return the unwrapped
`result` field on success. Raises `IO.userError` on a driver-side
error frame (`{"ok": false, "error": ...}`) or on a reply that does
not match either the success or failure shape. -/
def runOp (family : String) (op : String) (fields : Array (String × Json))
    : IO Json := do
  let mut obj : Array (String × Json) := #[("family", Json.str family), ("op", Json.str op)]
  for kv in fields do
    obj := obj.push kv
  let reply ← sendRequest (Json.mkObj obj.toList)
  match reply.getObjValAs? Bool "ok" with
  | Except.ok true =>
    match reply.getObjVal? "result" with
    | Except.ok r => return r
    | Except.error msg =>
      throw (IO.userError
        s!"flint_bench_driver: missing 'result' in success reply: {msg}; reply: {reply.compress}")
  | Except.ok false =>
    let err := (reply.getObjValAs? String "error").toOption.getD "(no error message)"
    throw (IO.userError s!"flint_bench_driver: {family}/{op}: {err}")
  | Except.error msg =>
    throw (IO.userError
      s!"flint_bench_driver: reply missing/non-bool 'ok' field: {msg}; reply: {reply.compress}")

/-- Helper: encode an `Int` list (e.g. polynomial coefficient list,
ascending degree) as a JSON array suitable for a `runOp` field. -/
def intsToJson (xs : List Int) : Json :=
  Json.arr (xs.map fun n => Json.num (JsonNumber.fromInt n)).toArray

/-- Helper: decode a JSON array of integers (e.g. a coefficient list
returned by `fmpz_poly` ops) back into a Lean `List Int`. Raises
`IO.userError` if the JSON is not an array of ints. -/
def jsonToInts (j : Json) : IO (List Int) := do
  match j.getArr? with
  | Except.ok arr => do
    let mut out : Array Int := Array.mkEmpty arr.size
    for elt in arr do
      match elt.getInt? with
      | Except.ok n => out := out.push n
      | Except.error msg =>
        throw (IO.userError
          s!"flint_bench_driver: element not an integer: {msg}; element: {elt.compress}")
    return out.toList
  | Except.error msg =>
    throw (IO.userError
      s!"flint_bench_driver: expected JSON array, got: {msg}; value: {j.compress}")

end Hex.BenchOracle.Flint
