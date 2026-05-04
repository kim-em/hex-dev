/-!
JSONL fixture/result emission helper for the Hex conformance suite.

External oracles (python-flint, cypari2, fpylll, ...) consume one JSONL
record per line — see `scripts/oracle/common.py` for the schema.  This
module provides minimal `IO` helpers that build the records as JSON
strings and write them to either stdout or the file named by the
`HEX_FIXTURE_OUTPUT` environment variable.

The helpers intentionally avoid pulling in any third-party JSON
library: every record we need to emit is a flat object whose values
are strings, integers, lists of integers, or `null`, so a hand-rolled
serializer is small enough to read at a glance and keeps `Hex` (the
library hosting this module) dependency-free.

Per-library emit drivers (e.g. `HexPoly/EmitFixtures.lean`) define a
`main` that walks a fixture list and calls these helpers; a `lean_exe`
target in the `lakefile.lean` makes them runnable via
`lake exe hexpoly_emit_fixtures > poly.jsonl`.
-/

namespace Hex.Conformance.Emit

/-- Append a JSON-escaped form of `s` to `acc`. -/
private def escapeStringInto (acc : String) (s : String) : String := Id.run do
  let mut out := acc.push '"'
  for c in s.toList do
    match c with
    | '\\' => out := out.push '\\' |>.push '\\'
    | '"'  => out := out.push '\\' |>.push '"'
    | '\n' => out := out.push '\\' |>.push 'n'
    | '\r' => out := out.push '\\' |>.push 'r'
    | '\t' => out := out.push '\\' |>.push 't'
    | _    =>
      if c.toNat < 0x20 then
        let hex := Nat.toDigits 16 c.toNat
        let pad := List.replicate (4 - hex.length) '0'
        out := out.push '\\' |>.push 'u'
        for d in pad ++ hex do
          out := out.push d
      else
        out := out.push c
  out.push '"'

private def jsonString (s : String) : String :=
  escapeStringInto "" s

private def jsonInt (n : Int) : String :=
  toString n

private def jsonIntList (xs : List Int) : String := Id.run do
  let mut out := "["
  let mut first := true
  for x in xs do
    if first then
      first := false
    else
      out := out.push ','
    out := out ++ jsonInt x
  out.push ']'

private def jsonIntMatrix (rows : List (List Int)) : String := Id.run do
  let mut out := "["
  let mut first := true
  for row in rows do
    if first then
      first := false
    else
      out := out.push ','
    out := out ++ jsonIntList row
  out.push ']'

private def jsonOptionalInt : Option Int → String
  | none   => "null"
  | some n => jsonInt n

/-- A field of a JSON object as `(key, raw-JSON-value)`. -/
private abbrev Field := String × String

private def jsonObject (fields : List Field) : String := Id.run do
  let mut out := "{"
  let mut first := true
  for (k, v) in fields do
    if first then
      first := false
    else
      out := out.push ','
    out := out ++ jsonString k |>.push ':' |>.append v
  out.push '}'

/-- Write a single JSONL record (the trailing newline) either to
`stdout` or, when set, to the file named by `HEX_FIXTURE_OUTPUT`. -/
private def emitLine (record : String) : IO Unit := do
  let line := record.push '\n'
  match (← IO.getEnv "HEX_FIXTURE_OUTPUT") with
  | none      => IO.print line
  | some path =>
    let h ← IO.FS.Handle.mk path IO.FS.Mode.append
    h.putStr line

/-- Emit a `poly` fixture record (Lean-side input). -/
def emitPolyFixture (lib case : String) (coeffs : List Int)
    (modulus : Option Int := none) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",    jsonString "poly"),
    ("lib",     jsonString lib),
    ("case",    jsonString case),
    ("coeffs",  jsonIntList coeffs),
    ("modulus", jsonOptionalInt modulus)
  ]

/-- Emit a `matrix` fixture record. -/
def emitMatrixFixture (lib case : String) (rows : List (List Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "matrix"),
    ("lib",  jsonString lib),
    ("case", jsonString case),
    ("rows", jsonIntMatrix rows)
  ]

/-- Emit a `lattice` fixture record (basis as row vectors). -/
def emitLatticeFixture (lib case : String) (basis : List (List Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",  jsonString "lattice"),
    ("lib",   jsonString lib),
    ("case",  jsonString case),
    ("basis", jsonIntMatrix basis)
  ]

/-- Emit a `prime` fixture record (`p`, `n` describe `GF(p^n)`). -/
def emitPrimeFixture (lib case : String) (p n : Int) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "prime"),
    ("lib",  jsonString lib),
    ("case", jsonString case),
    ("p",    jsonInt p),
    ("n",    jsonInt n)
  ]

/-- Emit a `gfqfield` fixture record carrying the prime `p`, the
modulus polynomial coefficients, two reduced operands `a` / `b`
(with `b` nonzero so `a / b` is well-defined), and the integer
exponent `zexp` used by the `zpow` op. -/
def emitGfqFieldFixture (lib case : String) (p : Int)
    (modulus a b : List Int) (zexp : Int) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",    jsonString "gfqfield"),
    ("lib",     jsonString lib),
    ("case",    jsonString case),
    ("p",       jsonInt p),
    ("modulus", jsonIntList modulus),
    ("a",       jsonIntList a),
    ("b",       jsonIntList b),
    ("zexp",    jsonInt zexp)
  ]

/-- Emit a `result` record carrying Lean's computed answer for one op
on a previously-emitted case.  `value` must be a valid raw JSON
fragment; helpers below build the common shapes. -/
def emitResult (lib case op : String) (value : String) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",  jsonString "result"),
    ("lib",   jsonString lib),
    ("case",  jsonString case),
    ("op",    jsonString op),
    ("value", value)
  ]

/-- Polynomial-shaped result value: a coefficient list. -/
def polyValue (coeffs : List Int) : String := jsonIntList coeffs

/-- Integer-list result value (e.g. a vector of leading determinants). -/
def intListValue (xs : List Int) : String := jsonIntList xs

/-- Integer-matrix result value (rows of integers). -/
def intMatrixValue (rows : List (List Int)) : String := jsonIntMatrix rows

/-- `divmod`-shaped result value: a `[quotient, remainder]` coefficient pair. -/
def divModValue (quot rem : List Int) : String :=
  "[" ++ jsonIntList quot ++ "," ++ jsonIntList rem ++ "]"

/-- Q-coefficient polynomial result value: parallel `num` / `den` lists.

The oracle compares Lean's gcd to `flint.fmpq_poly`'s gcd by normalising
both to the monic associate, which is meaningful because `Hex.DensePoly`
gcd over `Rat` is only determined up to a (rational) scalar associate. -/
def polyRatValue (coeffs : List Rat) : String :=
  let nums := coeffs.map (·.num)
  let dens := coeffs.map fun r => (r.den : Int)
  "{" ++ jsonString "num" ++ ":" ++ jsonIntList nums ++
  "," ++ jsonString "den" ++ ":" ++ jsonIntList dens ++ "}"

/-- Lattice-shaped result value: a basis as a list of integer rows. -/
def latticeValue (basis : List (List Int)) : String := jsonIntMatrix basis

end Hex.Conformance.Emit
