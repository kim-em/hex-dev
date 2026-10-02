/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Cert
public import HexArith.ExtGcd
public import HexPrimality.Search
public import Lean.Data.Json

public section

/-!
# Bounded conversion of supplied PARI ECPP rows

Conversion constructs proposals and inverse transcripts. Every returned
certificate is checked again by `checkAt`; no proposal is a proof dependency.
-/

namespace Hex.ECPP

/-- Finite allocations for parsing, conversion and terminal construction. -/
structure ImportBudget where
  /-- Maximum UTF-8 bytes before parsing. -/
  maxInputBytes : Nat
  /-- Maximum consecutive decimal digits before integer allocation. -/
  maxDigits : Nat
  /-- Maximum supplied rows. -/
  maxRows : Nat
  /-- Maximum bit length of any supplied integer magnitude. -/
  maxIntegerBits : Nat
  /-- Maximum bit length of either scalar replay. -/
  maxScalarBits : Nat
  /-- Maximum inverse operations per scalar replay. -/
  maxInverseOps : Nat
  /-- Maximum caller-supplied terminal search fuel. -/
  maxEndpointFuel : Nat
deriving Repr

/-- A finite conversion policy admitting the frozen 512-bit PARI vector.
Callers can use smaller explicit budgets for shorter certificates. -/
def defaultImportBudget : ImportBudget :=
  ⟨16384, 170, 20, 512, 512, 1200, 200⟩

/-- Conversion failures distinguish allocation, format and arithmetic errors. -/
inductive ImportErrorKind where
  | malformed
  | exhausted
  | unsupported
  | invalidArithmetic
  | nonunitProjective
  | subjectMismatch
  | invalidEndpoint
deriving Repr, BEq

/-- A conversion diagnostic with an original row index; the endpoint follows the rows. -/
structure ImportError where
  /-- Original zero-based vector index; input-wide text errors use zero and may carry parser details. -/
  row : Nat
  /-- The allocation, format or arithmetic failure. -/
  kind : ImportErrorKind
  /-- Zero-based ASCII offset for a text preflight failure, when available. -/
  offset : Option Nat := none
  /-- Generic parser diagnostic, including its source location. -/
  detail : Option String := none
deriving Repr

/-- Supplied signed homogeneous coordinates; normalization requires a unit denominator. -/
structure Projective where
  /-- Signed first homogeneous coordinate. -/
  x : Int
  /-- Signed second homogeneous coordinate. -/
  y : Int
  /-- Signed denominator, checked as a unit before normalization. -/
  z : Int
deriving Repr

/-- One supplied PARI row: subject, trace encoding, cofactor, curve coefficient and point. -/
structure PariRow where
  /-- Claimed subject of this row. -/
  n : Nat
  /-- Signed order encoding: the proposed order is `n + 1 - t`. -/
  t : Int
  /-- Positive exact cofactor dividing the proposed order. -/
  s : Int
  /-- Signed short Weierstrass coefficient. -/
  a : Int
  /-- Supplied affine or homogeneous point. -/
  point : Projective
deriving Repr

/-- Parsed rows and the terminal subject to replace with a checked Hex certificate. -/
structure PariCertificate where
  /-- Rows in parent-to-child order. -/
  rows : List PariRow
  /-- Terminal subject requiring an accepted Hex primality certificate. -/
  endpoint : Nat
deriving Repr

/-- Subject represented by the outer row, or by the endpoint for an empty vector. -/
def PariCertificate.subject (input : PariCertificate) : Nat :=
  (input.rows.head?.map PariRow.n).getD input.endpoint

/-- Reduce a supplied signed integer to a natural residue. -/
def residue (n : Nat) (z : Int) : Nat := (z % (n : Int)).toNat

/-- Conversion may search for inverses, unlike the proof checker. Each
proposal is still verified before it enters the raw certificate. -/
def inverse? (n d : Nat) : Option Nat :=
  let (g, s, _) := HexArith.extGcd d n
  if g != 1 then none
  else
    let u := residue n s
    if u < n && d * u % n == 1 then some u else none

/-- Normalize homogeneous coordinates only after checking a unit inverse of `z`. -/
def normalizeProjective (n : Nat) (P : Projective) :
    Except ImportErrorKind Point := do
  let z := residue n P.z
  let some u := inverse? n z | throw .nonunitProjective
  if z * u % n != 1 then throw .nonunitProjective
  pure (.affine (residue n P.x * u % n) (residue n P.y * u % n))

/-- Compute and check the inverse for one affine division branch. -/
def proposeWithInverse (n a : Nat) (P Q : Point) (d : Nat) :
    Except ImportErrorKind (Point × Option Nat) := do
  let some u := inverse? n d | throw .invalidArithmetic
  let some (R, rest) := add? n a P Q [u] | throw .invalidArithmetic
  if !rest.isEmpty then throw .invalidArithmetic
  pure (R, some u)

/-- Untrusted affine addition used only while converting supplied rows. -/
def proposeAdd (n a : Nat) (P Q : Point) :
    Except ImportErrorKind (Point × Option Nat) := do
  match P, Q with
  | .infinity, Q => pure (Q, none)
  | P, .infinity => pure (P, none)
  | .affine x₁ y₁, .affine x₂ y₂ =>
      if x₁ == x₂ then
        if (y₁ + y₂) % n == 0 then pure (.infinity, none)
        else if y₁ == y₂ then
          proposeWithInverse n a P Q (2 * y₁ % n)
        else throw .invalidArithmetic
      else proposeWithInverse n a P Q (modSub n x₂ x₁)

/-- Accumulate used inverses in reverse scalar-schedule order. -/
private def pushWitness (acc : List Nat) (w : Option Nat) : List Nat :=
  match w with
  | none => acc
  | some u => u :: acc

/-- Whether the next affine branch requires a checked inverse witness. -/
private def needsInverse (n : Nat) : Point → Point → Bool
  | .infinity, _ | _, .infinity => false
  | .affine x₁ y₁, .affine x₂ y₂ =>
      if x₁ == x₂ then (y₁ + y₂) % n != 0 && y₁ == y₂
      else true

/-- Generate a canonical proposal and its inverse transcript. The structural
recursor visits the same scalar bits as the proof checker. -/
def proposeBits (budget : ImportBudget) (n a q : Nat) (Q : Point) :
    Nat → Point → List Nat → Nat → Except ImportErrorKind (Point × List Nat)
  | 0, R, acc, _ => pure (R, acc.reverse)
  | bits + 1, R, acc, used => do
      if needsInverse n R R && used >= budget.maxInverseOps then throw .exhausted
      let (D, ud) ← proposeAdd n a R R
      let used := used + (if ud.isSome then 1 else 0)
      let (S, us) ←
        if q.testBit bits then
          if needsInverse n D Q && used >= budget.maxInverseOps then throw .exhausted
          proposeAdd n a D Q
        else pure (D, none)
      let acc := pushWitness (pushWitness acc ud) us
      proposeBits budget n a q Q bits S acc (used + (if us.isSome then 1 else 0))

/-- Generate a bounded scalar proposal and its complete inverse transcript. -/
def proposeScalar (budget : ImportBudget) (n a q : Nat) (Q : Point) :
    Except ImportErrorKind (Point × List Nat) := do
  if HexArith.bitLength q > budget.maxScalarBits then throw .exhausted
  proposeBits budget n a q Q (HexArith.bitLength q) .infinity [] 0

/-- Check every supplied integer before arithmetic or endpoint construction. -/
def checkRowLimits (budget : ImportBudget) (row : PariRow) :
    Except ImportErrorKind Unit := do
  if [row.n, row.t.natAbs, row.s.natAbs, row.a.natAbs,
      row.point.x.natAbs, row.point.y.natAbs, row.point.z.natAbs].any
      (fun z => HexArith.bitLength z > budget.maxIntegerBits) then
    throw .exhausted

/-- Preflight parsed input before checking or searching for a terminal
certificate. Row errors retain their original vector index; the endpoint
uses the index immediately after the last row. Text byte and digit limits
are enforced separately by `parsePari`. -/
def preflight (budget : ImportBudget) (input : PariCertificate) :
    Except ImportError Unit := do
  if input.rows.length > budget.maxRows then throw { row := 0, kind := .exhausted }
  if HexArith.bitLength input.endpoint > budget.maxIntegerBits then
    throw { row := input.rows.length, kind := .exhausted }
  for (row, index) in input.rows.zipIdx do
    match checkRowLimits budget row with
    | .ok () => pure ()
    | .error kind => throw { row := index, kind := kind }

/-- Convert one row against its supplied child and check the local step.
The complete child chain is checked at the public conversion boundary. -/
def convertRow (budget : ImportBudget) (row : PariRow) (child : Cert) :
    Except ImportErrorKind Cert := do
  checkRowLimits budget row
  let n := row.n
  if n ≤ 3 then throw .invalidArithmetic
  let m : Int := (n : Int) + 1 - row.t
  if m ≤ 0 || row.s ≤ 0 then throw .invalidArithmetic
  if m % row.s != 0 then throw .invalidArithmetic
  let q := (m / row.s).toNat
  if q != child.subject then throw .subjectMismatch
  let a := residue n row.a
  let P ← normalizeProjective n row.point
  let .affine px py := P | throw .nonunitProjective
  let b := modSub n (py * py % n) ((px * px * px + a * px) % n)
  if !onCurve n a b px py then throw .invalidArithmetic
  let (Q, _) ← proposeScalar budget n a row.s.toNat P
  let .affine x y := Q | throw .invalidArithmetic
  let (result, inverses) ← proposeScalar budget n a q Q
  if result != .infinity then throw .invalidArithmetic
  let some discrInv := inverse? n (4 * a * a * a + 27 * b * b) |
    throw .invalidArithmetic
  let cert := Cert.step n a b x y discrInv inverses child
  if !checkStep n a b x y discrInv inverses child.subject then throw .invalidArithmetic
  pure cert

/-- Convert from the terminal row outward, preserving original row indices on failure. -/
def convertRows (budget : ImportBudget) :
    Nat → List PariRow → Cert → Except ImportError Cert
  | _, [], child => pure child
  | rowIndex, row :: rows, child => do
      let child ← convertRows budget (rowIndex + 1) rows child
      match convertRow budget row child with
      | .ok cert => pure cert
      | .error kind => throw { row := rowIndex, kind := kind }

/-- Convert a parsed PARI vector with a supplied accepted Hex terminal
certificate. The terminal subject must match exactly. -/
def convert (budget : ImportBudget) (input : PariCertificate)
    (leaf : Hex.Nat.PrimeCert) : Except ImportError Cert := do
  preflight budget input
  if leaf.subject != input.endpoint then throw { row := input.rows.length, kind := .subjectMismatch }
  if !Hex.Nat.checkPrime leaf then throw { row := input.rows.length, kind := .invalidEndpoint }
  let cert ← convertRows budget 0 input.rows (.base leaf)
  if !checkAt input.subject cert then throw { row := 0, kind := .invalidArithmetic }
  pure cert

/-- Scan integer digits and bracket nesting before JSON allocation. Commas
at the outer vector level retain the failing row; text offsets locate lexical
failures. The permitted PARI format uses at most three bracket levels. -/
private def scanInput (budget : ImportBudget) :
    List Char → Nat → Nat → Nat → Nat → Except ImportError Unit
  | [], _, depth, row, offset =>
      if depth == 0 then pure () else
        throw { row := row, kind := .malformed, offset := some offset }
  | c :: cs, digits, depth, row, offset => do
      if '0' ≤ c && c ≤ '9' then
        if digits + 1 > budget.maxDigits then
          throw { row := row, kind := .exhausted, offset := some offset }
        scanInput budget cs (digits + 1) depth row (offset + 1)
      else if c == '[' then
        if depth >= 3 then
          throw { row := row, kind := .unsupported, offset := some offset }
        scanInput budget cs 0 (depth + 1) row (offset + 1)
      else if c == ']' then
        if depth == 0 then
          throw { row := row, kind := .malformed, offset := some offset }
        scanInput budget cs 0 (depth - 1) row (offset + 1)
      else if c == ',' || c == '-' || c == ' ' ||
          c == '\n' || c == '\r' || c == '\t' then
        let row := if c == ',' && depth == 1 then row + 1 else row
        scanInput budget cs 0 depth row (offset + 1)
      else throw { row := row, kind := .unsupported, offset := some offset }

/-- Accept only a JSON integer, preserving its sign. -/
private def jsonInt (j : Lean.Json) : Except ImportErrorKind Int :=
  match j.getInt? with
  | .ok z => pure z
  | .error _ => throw .malformed

/-- Accept only a nonnegative JSON integer. -/
private def jsonNat (j : Lean.Json) : Except ImportErrorKind Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw .malformed

/-- Reject non-vector JSON values. -/
private def jsonArray (j : Lean.Json) : Except ImportErrorKind (Array Lean.Json) :=
  match j.getArr? with
  | .ok xs => pure xs
  | .error _ => throw .malformed

/-- Accept two affine or three homogeneous integer coordinates. -/
private def parsePoint (j : Lean.Json) : Except ImportErrorKind Projective := do
  let xs ← jsonArray j
  if xs.size != 2 && xs.size != 3 then throw .malformed
  let x ← jsonInt xs[0]!
  let y ← jsonInt xs[1]!
  let z ← if xs.size == 3 then jsonInt xs[2]! else pure 1
  pure ⟨x, y, z⟩

/-- Decode the five fields of a PARI row without trusting its arithmetic. -/
private def parseRow (j : Lean.Json) : Except ImportErrorKind PariRow := do
  let xs ← jsonArray j
  if xs.size != 5 then throw .malformed
  let n ← jsonNat xs[0]!
  let t ← jsonInt xs[1]!
  let s ← jsonInt xs[2]!
  let a ← jsonInt xs[3]!
  let point ← parsePoint xs[4]!
  pure ⟨n, t, s, a, point⟩

/-- Decode a bounded vector while retaining each original row's location. -/
private def parseLocated (budget : ImportBudget) (source : String) :
    Except ImportError PariCertificate := do
  if source.utf8ByteSize > budget.maxInputBytes then throw { row := 0, kind := .exhausted }
  scanInput budget source.toList 0 0 0 0
  let json ← match Lean.Json.parse source with
    | .ok j => pure j
    | .error detail => throw { row := 0, kind := .malformed, detail := some detail }
  let input ← match json with
  | .num _ =>
      let n ← (jsonNat json).mapError (fun kind => { row := 0, kind := kind })
      pure ⟨[], n⟩
  | .arr xs =>
      if xs.size == 0 then throw { row := 0, kind := .malformed }
      if xs.size > budget.maxRows then throw { row := 0, kind := .exhausted }
      let rows ← xs.toList.zipIdx.mapM fun (j, index) => do
        let row ← (parseRow j).mapError (fun kind => { row := index, kind := kind })
        (checkRowLimits budget row).mapError (fun kind => { row := index, kind := kind })
        pure row
      let some last := rows.getLast? | throw { row := 0, kind := .malformed }
      let m : Int := (last.n : Int) + 1 - last.t
      if m ≤ 0 || last.s ≤ 0 || m % last.s != 0 then
        throw { row := rows.length - 1, kind := .invalidArithmetic }
      pure ⟨rows, (m / last.s).toNat⟩
  | _ => throw { row := 0, kind := .unsupported }
  preflight budget input
  pure input

/-- Parse a PARI integer or a vector of `[n,t,s,a,P]` rows. An affine `P`
has two coordinates; the three-coordinate form is also accepted so its
projective `z` is checked as a unit. `convertText` retains row locations. -/
def parsePari (budget : ImportBudget) (source : String) :
    Except ImportErrorKind PariCertificate :=
  (parseLocated budget source).mapError ImportError.kind

/-- Parse and convert a supplied PARI certificate under explicit limits. -/
def convertText (budget : ImportBudget) (source : String)
    (leaf : Hex.Nat.PrimeCert) : Except ImportError Cert := do
  let input ← parseLocated budget source
  convert budget input leaf

/-- Complete a partial PARI endpoint with Hex's bounded, checked terminal
certificate search. Supplied `fuel` above the conversion allocation is rejected. -/
def convertCounted (budget : ImportBudget)
    (primeBudget : Hex.Nat.PrimeCertBudget) (rand : Hex.Rand)
    (fuel : Nat) (input : PariCertificate) :
    Except ImportError (Cert × Hex.Rand) := do
  preflight budget input
  if fuel > budget.maxEndpointFuel then throw { row := input.rows.length, kind := .exhausted }
  let result ← match Hex.Nat.Internal.primeCertCountedWith?
      primeBudget input.endpoint rand fuel with
    | .ok result => pure result
    | .error failure =>
        match failure.stop with
        | .composite => throw { row := input.rows.length, kind := .invalidEndpoint }
        | .exhausted => throw { row := input.rows.length, kind := .exhausted }
  let cert ← convert budget input result.cert.raw
  pure (cert, result.rand)

/-- Supplied conversion returns only certificates accepted by the raw
checker; parsing and proposal generation are outside the proof boundary. -/
theorem convert_ok {budget : ImportBudget} {input : PariCertificate}
    {leaf : Hex.Nat.PrimeCert} {c : Cert}
    (h : convert budget input leaf = .ok c) : checkAt input.subject c = true := by
  unfold convert at h
  cases hp : preflight budget input with
  | error e => simp [hp, bind, Except.bind] at h
  | ok value =>
    simp only [hp, bind, Except.bind] at h
    split at h
    · simp [throw] at h
    · split at h
      · simp [throw] at h
      · cases hr : convertRows budget 0 input.rows (.base leaf) with
        | error e => simp [hr] at h
        | ok candidate =>
          simp only [hr] at h
          split at h
          · simp [throw] at h
          · simp only [pure, Except.pure] at h
            cases h
            simpa using ‹(!checkAt input.subject c) ≠ true›

end Hex.ECPP
