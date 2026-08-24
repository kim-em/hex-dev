/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
JSONL fixture/result emission helper for the Hex conformance suite.

External oracles (python-flint, cypari2, fpylll, ...) consume one JSONL
record per line — see `scripts/oracle/common.py` for the schema.  This
module provides minimal `IO` helpers that build the records as JSON
strings and write them to either stdout or the file named by the
`HEX_FIXTURE_OUTPUT` environment variable.

The helpers intentionally avoid pulling in any third-party JSON
library. Most records are flat objects whose values are strings,
integers, lists of integers, or `null`; the one recursive RCF sentence
fixture uses a closed typed wire AST below. The resulting hand-rolled
serializer remains small enough to audit and keeps `Hex` (the library
hosting this module) dependency-free.

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

private def jsonRatList (xs : List Rat) : String :=
  let nums := xs.map (·.num)
  let dens := xs.map fun r => (r.den : Int)
  "{" ++ jsonString "num" ++ ":" ++ jsonIntList nums ++
  "," ++ jsonString "den" ++ ":" ++ jsonIntList dens ++ "}"

private def jsonMvPolyTerms (terms : List (List Nat × Int)) : String := Id.run do
  let mut out := "["
  let mut first := true
  for (exponents, coeff) in terms do
    if first then
      first := false
    else
      out := out.push ','
    out := out ++ "[" ++
      jsonIntList (exponents.map Int.ofNat) ++ "," ++ jsonInt coeff ++ "]"
  out.push ']'

private def jsonOptionalInt : Option Int → String
  | none   => "null"
  | some n => jsonInt n

private def jsonSparseTerms (terms : List (Nat × Int × Int)) : String := Id.run do
  let mut out := "["
  let mut first := true
  for (e, num, den) in terms do
    if first then
      first := false
    else
      out := out.push ','
    out := out ++ "[" ++ jsonInt (Int.ofNat e) ++ "," ++ jsonInt num ++ ","
      ++ jsonInt den ++ "]"
  out.push ']'

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

/-- Emit a `poly` fixture record with optional metadata naming a pinned
modular factorization split expected by an external oracle.  The integer
fixture itself remains non-modular; `modFactorPrime` and
`modFactorDegrees` describe the independent factorization check for
`coeffs` reduced modulo `p`. -/
def emitPolyFixtureWithModFactorDegrees (lib case : String) (coeffs : List Int)
    (p : Int) (degrees : List Int) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",             jsonString "poly"),
    ("lib",              jsonString lib),
    ("case",             jsonString case),
    ("coeffs",           jsonIntList coeffs),
    ("modulus",          jsonOptionalInt none),
    ("modFactorPrime",   jsonInt p),
    ("modFactorDegrees", jsonIntList degrees)
  ]

/-- Emit a `matrix` fixture record. -/
def emitMatrixFixture (lib case : String) (rows : List (List Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "matrix"),
    ("lib",  jsonString lib),
    ("case", jsonString case),
    ("rows", jsonIntMatrix rows)
  ]

/-- Emit a canonical or pre-normalization `mvpoly` fixture. Each term is an
exponent vector paired with its integer coefficient. -/
def emitMvPolyFixture (lib case : String) (arity : Nat) (order : String)
    (terms : List (List Nat × Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",  jsonString "mvpoly"),
    ("lib",   jsonString lib),
    ("case",  jsonString case),
    ("arity", toString arity),
    ("order", jsonString order),
    ("terms", jsonMvPolyTerms terms)
  ]

/-- Emit a fixed-precision univariate-series fixture. Coefficients use a
parallel numerator/denominator encoding for both `ZZ` and `QQ`; the domain
field tells the oracle which coefficient ring contract applies. -/
def emitSeriesFixture (lib case domain : String) (precision : Nat)
    (coeffs : List Rat) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "series"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("domain", jsonString domain),
    ("precision", toString precision),
    ("coeffs", jsonRatList coeffs)
  ]

/-- Emit a multivariate-gcd fixture over the named coefficient domain. -/
def emitMvGcdFixture (lib case : String) (arity : Nat) (order domain : String)
    (modulus : Option Int) (left right : List (List Nat × Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "mvgcd"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("arity", toString arity),
    ("order", jsonString order),
    ("domain", jsonString domain),
    ("mod", jsonOptionalInt modulus),
    ("left", jsonMvPolyTerms left),
    ("right", jsonMvPolyTerms right)
  ]

/-- Emit a characteristic-zero multivariate squarefree-decomposition fixture. -/
def emitMvSqfFixture (lib case : String) (arity : Nat) (order domain : String)
    (terms : List (List Nat × Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "mvsqf"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("arity", toString arity),
    ("order", jsonString order),
    ("domain", jsonString domain),
    ("terms", jsonMvPolyTerms terms)
  ]

/-- Emit a finite-characteristic multivariate squarefree-decision fixture. -/
def emitMvSquarefreeFixture (lib case : String) (arity : Nat) (order : String)
    (modulus : Nat) (terms : List (List Nat × Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "mvsquarefree"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("arity", toString arity),
    ("order", jsonString order),
    ("domain", jsonString "zmod"),
    ("mod", toString modulus),
    ("terms", jsonMvPolyTerms terms)
  ]

/-- Emit a `sparsepoly` fixture record: a sparse univariate polynomial as
`(exponent, numerator, denominator)` terms in ascending exponent order
(`den = 1` outside the `"rat"` domain), over the domain `"int"`, `"rat"`,
or `"zmod"` (with `mod` the modulus, `null` otherwise). Exponents may be
large (`10^6`); nothing here materialises a coefficient vector. -/
def emitSparsePolyFixture (lib case dom : String) (mod? : Option Int)
    (terms : List (Nat × Int × Int)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",   jsonString "sparsepoly"),
    ("lib",    jsonString lib),
    ("case",   jsonString case),
    ("domain", jsonString dom),
    ("mod",    jsonOptionalInt mod?),
    ("terms",  jsonSparseTerms terms)
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

/-- Emit a symmetric-representative fixture. -/
def emitSymModFixture (lib case : String) (a : Int) (m : Nat) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "symmod"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("a", jsonInt a),
    ("m", toString m)
  ]

/-- Emit an incremental CRT fixture as parallel residue and modulus lists. -/
def emitCrtFixture (lib case : String) (steps : List (Int × Nat)) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "crt"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("residues", jsonIntList (steps.map Prod.fst)),
    ("moduli", jsonIntList (steps.map fun step => Int.ofNat step.2))
  ]

/-- Emit one bounded rational-reconstruction fixture. -/
def emitRatReconFixture (lib case : String) (a : Int) (m : Nat)
    (p q : Int) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "ratrecon"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("a", jsonInt a),
    ("m", toString m),
    ("p", jsonInt p),
    ("q", jsonInt q)
  ]

/-- Emit a `conway` fixture record identifying a committed `C(p, n)` entry. -/
def emitConwayFixture (lib case : String) (p n : Int) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "conway"),
    ("lib",  jsonString lib),
    ("case", jsonString case),
    ("p",    jsonInt p),
    ("n",    jsonInt n)
  ]

/-- Emit a `gfqring` fixture record carrying the prime `p`, the
modulus polynomial coefficients, two reduced operands `a` / `b`, an
unreduced polynomial `c` (for the `reduce` op), and a scalar `n` (for
the `nsmul` op). -/
def emitGfqRingFixture (lib case : String) (p : Int)
    (modulus a b c : List Int) (n : Int) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",    jsonString "gfqring"),
    ("lib",     jsonString lib),
    ("case",    jsonString case),
    ("p",       jsonInt p),
    ("modulus", jsonIntList modulus),
    ("a",       jsonIntList a),
    ("b",       jsonIntList b),
    ("c",       jsonIntList c),
    ("n",       jsonInt n)
  ]

/-- Emit a `gfq_bridge` fixture record carrying the prime `p`, the
modulus polynomial coefficients (ascending), and two reduced operands
`a` / `b` as ascending coefficient lists.  The operands are the input
the oracle consumes; both Lean rep paths (packed `GF2n` and generic
`GFqField.FiniteField`) emit per-op result records describing the
same `(a, b)` pair, and the oracle cross-checks each rep path against
python-flint's canonical answer. -/
def emitGfqBridgeFixture (lib case : String) (p : Int)
    (modulus a b : List Int) : IO Unit := do
  emitLine <| jsonObject [
    ("kind",    jsonString "gfq_bridge"),
    ("lib",     jsonString lib),
    ("case",    jsonString case),
    ("p",       jsonInt p),
    ("modulus", jsonIntList modulus),
    ("a",       jsonIntList a),
    ("b",       jsonIntList b)
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

/-! # Real-closed-field sentence fixtures -/

/- Typed wire representation for the RCF sentence fixture.  Keeping this
small AST in the dependency-free conformance helper prevents per-library
emitters from hand-rolling nested JSON or accidentally serialising internal
certificate evidence. -/
namespace Rcf

/-- A comparison tag in the RCF fixture schema. -/
inductive Cmp where
  | lt | le | eq | ge | gt | ne

/-- A Boolean formula over ascending-coefficient integer polynomials. -/
inductive Formula where
  | atom (coeffs : List Int) (cmp : Cmp)
  | tt
  | ff
  | not (arg : Formula)
  | and (left right : Formula)
  | or (left right : Formula)
  | imp (left right : Formula)

/-- A dyadic number as `(numerator, denominator exponent)`, denoting
`numerator * 2^(-exponent)`. -/
abbrev Dyadic := Int × Int

/-- One quantified RCF sentence.  The constructors enforce that only bounded
quantifiers carry endpoints. -/
inductive Sentence where
  | forallReal (formula : Formula)
  | existsReal (formula : Formula)
  | forallIoc (lower upper : Dyadic) (formula : Formula)
  | existsIoc (lower upper : Dyadic) (formula : Formula)

end Rcf

private def rcfCmpValue : Rcf.Cmp → String
  | .lt => jsonString "lt"
  | .le => jsonString "le"
  | .eq => jsonString "eq"
  | .ge => jsonString "ge"
  | .gt => jsonString "gt"
  | .ne => jsonString "ne"

private def rcfFormulaValue : Rcf.Formula → String
  | .atom coeffs cmp => jsonObject [
      ("tag", jsonString "atom"),
      ("coeffs", jsonIntList coeffs),
      ("cmp", rcfCmpValue cmp)
    ]
  | .tt => jsonObject [("tag", jsonString "tt")]
  | .ff => jsonObject [("tag", jsonString "ff")]
  | .not arg => jsonObject [
      ("tag", jsonString "not"),
      ("arg", rcfFormulaValue arg)
    ]
  | .and left right => jsonObject [
      ("tag", jsonString "and"),
      ("left", rcfFormulaValue left),
      ("right", rcfFormulaValue right)
    ]
  | .or left right => jsonObject [
      ("tag", jsonString "or"),
      ("left", rcfFormulaValue left),
      ("right", rcfFormulaValue right)
    ]
  | .imp left right => jsonObject [
      ("tag", jsonString "imp"),
      ("left", rcfFormulaValue left),
      ("right", rcfFormulaValue right)
    ]

private def rcfDyadicValue (d : Rcf.Dyadic) : String :=
  jsonIntList [d.1, d.2]

private def rcfBoundsValue (lower upper : Rcf.Dyadic) : String :=
  jsonObject [
    ("lower", rcfDyadicValue lower),
    ("upper", rcfDyadicValue upper)
  ]

private def rcfSentenceValue : Rcf.Sentence → String
  | .forallReal formula => jsonObject [
      ("quantifier", jsonString "forall_real"),
      ("bounds", "null"),
      ("formula", rcfFormulaValue formula)
    ]
  | .existsReal formula => jsonObject [
      ("quantifier", jsonString "exists_real"),
      ("bounds", "null"),
      ("formula", rcfFormulaValue formula)
    ]
  | .forallIoc lower upper formula => jsonObject [
      ("quantifier", jsonString "forall_ioc"),
      ("bounds", rcfBoundsValue lower upper),
      ("formula", rcfFormulaValue formula)
    ]
  | .existsIoc lower upper formula => jsonObject [
      ("quantifier", jsonString "exists_ioc"),
      ("bounds", rcfBoundsValue lower upper),
      ("formula", rcfFormulaValue formula)
    ]

/-- Emit a version-1 `rcf_sentence` fixture containing only the original
reflected input sentence. -/
def emitRcfFixture (lib case : String) (sentence : Rcf.Sentence) : IO Unit := do
  emitLine <| jsonObject [
    ("kind", jsonString "rcf_sentence"),
    ("lib", jsonString lib),
    ("case", jsonString case),
    ("schema", "1"),
    ("sentence", rcfSentenceValue sentence)
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

/-- Sparse-polynomial-shaped result value: ascending
`(exponent, numerator, denominator)` terms. -/
def sparsePolyValue (terms : List (Nat × Int × Int)) : String :=
  jsonSparseTerms terms

/-- Integer-list result value (e.g. a vector of leading determinants). -/
def intListValue (xs : List Int) : String := jsonIntList xs

/-- Integer-matrix result value (rows of integers). -/
def intMatrixValue (rows : List (List Int)) : String := jsonIntMatrix rows

/-- Multivariate-polynomial result value: exponent/coefficient term pairs. -/
def mvPolyValue (terms : List (List Nat × Int)) : String :=
  jsonMvPolyTerms terms

/-- `divmod`-shaped result value: a `[quotient, remainder]` coefficient pair. -/
def divModValue (quot rem : List Int) : String :=
  "[" ++ jsonIntList quot ++ "," ++ jsonIntList rem ++ "]"

/-- Q-coefficient polynomial result value: parallel `num` / `den` lists.

The oracle compares Lean's gcd to `flint.fmpq_poly`'s gcd by normalising
both to the monic associate, which is meaningful because `Hex.DensePoly`
gcd over `Rat` is only determined up to a (rational) scalar associate. -/
def polyRatValue (coeffs : List Rat) : String :=
  jsonRatList coeffs

/-- Rational coefficient-list value used by truncated-series results. -/
def seriesValue (coeffs : List Rat) : String :=
  jsonRatList coeffs

/-- Optional rational coefficient-list value used by partial series
operations. -/
def optionSeriesValue (coeffs : Option (List Rat)) : String :=
  match coeffs with
  | none => "null"
  | some xs => jsonRatList xs

/-- Lattice-shaped result value: a basis as a list of integer rows. -/
def latticeValue (basis : List (List Int)) : String := jsonIntMatrix basis

end Hex.Conformance.Emit
