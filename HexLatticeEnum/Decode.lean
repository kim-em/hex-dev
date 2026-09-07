/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Cert

@[expose] public section

namespace Hex.LatticeEnum

/-- Independent limits for decoding untrusted certificate text.
Byte size is checked before tokenization; dimensions and counts before allocation. -/
structure DecodeLimits where
  /-- Maximum UTF-8 input size, including numeric digits and separators. -/
  bytes : Nat := 8388608
  /-- Maximum rank and ambient dimension. -/
  dimension : Nat := 256
  /-- Maximum total number of tree nodes, shared across all siblings. -/
  nodes : Nat := 1000000
  /-- Maximum number of claimed output points. -/
  points : Nat := 100000
  /-- Maximum decimal token length, including a possible minus sign. -/
  digits : Nat := 4096
  deriving Repr

namespace Codec

/-- Decoder state, including the single global tree-node allowance. -/
structure State where
  tokens : List String
  nodes : Nat

/-- Parsing never assumes arithmetic validity or certificate soundness. -/
abbrev Reader := StateT State (Except String)

/-- Consume one token. -/
def token : Reader String := do
  let s ← get
  match s.tokens with
  | [] => throw "truncated certificate"
  | value :: rest =>
    set { s with tokens := rest }
    return value

/-- Read a bounded unsigned decimal token. -/
def natural (limits : DecodeLimits) : Reader Nat := do
  let value ← token
  if value.utf8ByteSize > limits.digits then throw "numeric token limit exceeded"
  match value.toNat? with
  | some value => return value
  | none => throw "expected a natural number"

/-- Read a bounded signed decimal token. -/
def integer (limits : DecodeLimits) : Reader Int := do
  let value ← token
  if value.utf8ByteSize > limits.digits then throw "numeric token limit exceeded"
  match value.toInt? with
  | some value => return value
  | none => throw "expected an integer"

/-- Rational tokens contain a numerator and a strictly positive denominator. -/
def rational (limits : DecodeLimits) : Reader Rat := do
  let num ← integer limits
  let den ← natural limits
  if den = 0 then throw "zero denominator"
  return mkRat num den

/-- Decode a vector of the externally checked dimension. -/
def vector (size : Nat) (read : Reader α) : Reader (Vector α size) := do
  let mut values := #[]
  for _ in [:size] do
    values := values.push (← read)
  if h : values.size = size then return ⟨values, h⟩
  else throw "invalid vector length"

/-- Matrices are serialized row by row, with dimensions supplied by the header. -/
def matrix (n m : Nat) (read : Reader α) : Reader (Matrix α n m) :=
  Matrix.ofRows <$> vector n (vector m read)

/-- Read a reported point, retaining its claims for independent replay. -/
def point (limits : DecodeLimits) (n m : Nat) : Reader (Point n m) := do
  return ⟨← vector n (integer limits), ← vector m (integer limits), ← rational limits⟩

/-- Prefix tree decoding is bounded both by rank and by a global node count. -/
def tree (limits : DecodeLimits) : (depth : Nat) → Reader Tree
  | depth => do
    let state ← get
    if state.nodes = 0 then throw "tree node limit exceeded"
    set { state with nodes := state.nodes - 1 }
    match ← token with
    | "E" => return .empty
    | "L" =>
      if depth = 0 then return .leaf else throw "leaf above dimension zero"
    | "N" =>
      match _hd : depth with
      | 0 => throw "tree depth exceeds rank"
      | depth + 1 =>
        let lo ← integer limits
        let hi ← integer limits
        let count ← natural limits
        if count > (← get).nodes then throw "tree node limit exceeded"
        let mut children := #[]
        for _ in [:count] do
          let label ← integer limits
          let child ← tree limits depth
          children := children.push (label, child)
        return .node ⟨lo, hi⟩ children.toList
    | _ => throw "unknown tree tag"
termination_by depth => depth
decreasing_by omega

/-- Parse a versioned local certificate, checking dimensions before reading matrix entries. -/
def certificate (limits : DecodeLimits) (n m : Nat) : Reader (Certificate n m) := do
  if (← token) != "hex-lattice-enum-1" then throw "unsupported certificate version"
  let rank ← natural limits
  let ambient ← natural limits
  if rank != n || ambient != m then throw "certificate dimension mismatch"
  if n > limits.dimension || m > limits.dimension then throw "dimension limit exceeded"
  let rows ← matrix n m (integer limits)
  let forward ← matrix n n (integer limits)
  let reverse ← matrix n n (integer limits)
  let mu ← matrix n n (rational limits)
  let orthogonal ← matrix n m (rational limits)
  let norms ← vector n (rational limits)
  let projection ← vector n (rational limits)
  let residual ← vector m (rational limits)
  let tree ← tree limits n
  let count ← natural limits
  if count > limits.points then throw "point limit exceeded"
  let points ← vector count (point limits n m)
  return ⟨rows, forward, reverse, ⟨mu, orthogonal, norms, projection, residual⟩, tree, points.toList⟩

/-- Encode vectors and matrices without introducing a second certificate representation. -/
def vectorTokens (encode : α → List String) (v : Vector α n) : List String :=
  v.toList.flatMap encode

def matrixTokens (encode : α → List String) (a : Matrix α n m) : List String :=
  vectorTokens (vectorTokens encode) a.rows

def intTokens (z : Int) : List String := [toString z]

def ratTokens (q : Rat) : List String := [toString q.num, toString q.den]

def pointTokens (p : Point n m) : List String :=
  vectorTokens intTokens p.coefficients ++ vectorTokens intTokens p.ambient ++ ratTokens p.distanceSq

/-- The prefix grammar records every child label and exact interval endpoint. -/
def treeTokens : Tree → List String
  | .empty => ["E"]
  | .leaf => ["L"]
  | .node interval children =>
    ["N", toString interval.lo, toString interval.hi, toString children.length] ++
      children.attach.flatMap (fun child => toString child.val.1 :: treeTokens child.val.2)
termination_by tree => sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem child.property
  have hp : sizeOf child.val = 1 + sizeOf child.val.1 + sizeOf child.val.2 := by
    cases child.val
    rfl
  simp_all
  omega

end Codec

/-- Decode bounded certificate text. A successful parse still requires `checkEnumeration`.
The format is a space-separated prefix stream: version, dimensions, row-major integer
matrices, rational data as numerator/positive-denominator pairs, tree, and point list.
Tree tags are `E`, `L`, and `N lo hi childCount (label subtree)*`. -/
def decodeCertificate (limits : DecodeLimits) (n m : Nat) (text : String) :
    Except String (Certificate n m) := do
  if text.utf8ByteSize > limits.bytes then throw "certificate byte limit exceeded"
  let (cert, state) ← (Codec.certificate limits n m).run ⟨text.splitOn " ", limits.nodes⟩
  if !state.tokens.isEmpty then throw "trailing certificate tokens"
  return cert

/-- Serialize a certificate in the bounded decoder's versioned local format. -/
def encodeCertificate (cert : Certificate n m) : String :=
  String.intercalate " " <|
    ["hex-lattice-enum-1", toString n, toString m] ++
    Codec.matrixTokens Codec.intTokens cert.rows ++
    Codec.matrixTokens Codec.intTokens cert.forward ++
    Codec.matrixTokens Codec.intTokens cert.reverse ++
    Codec.matrixTokens Codec.ratTokens cert.data.mu ++
    Codec.matrixTokens Codec.ratTokens cert.data.orthogonal ++
    Codec.vectorTokens Codec.ratTokens cert.data.norms ++
    Codec.vectorTokens Codec.ratTokens cert.data.projection ++
    Codec.vectorTokens Codec.ratTokens cert.data.residual ++
    Codec.treeTokens cert.tree ++ [toString cert.points.length] ++
    cert.points.flatMap Codec.pointTokens

/-- Decode an optimum certificate with the same independent byte, dimension and node limits. -/
def decodeOptimumCertificate (limits : DecodeLimits) (n m : Nat) (text : String) :
    Except String (OptimumCertificate n m) := do
  if text.utf8ByteSize > limits.bytes then throw "certificate byte limit exceeded"
  let read : Codec.Reader (OptimumCertificate n m) := do
    if (← Codec.token) != "hex-lattice-optimum-1" then throw "unsupported optimum version"
    let cert ← Codec.certificate limits n m
    let candidate ← Codec.point limits n m
    return ⟨candidate, cert⟩
  let (cert, state) ← read.run ⟨text.splitOn " ", limits.nodes⟩
  if !state.tokens.isEmpty then throw "trailing certificate tokens"
  return cert

/-- Serialize the complete ball and attained candidate of an optimum certificate. -/
def encodeOptimumCertificate (cert : OptimumCertificate n m) : String :=
  "hex-lattice-optimum-1 " ++ encodeCertificate cert.enumeration ++ " " ++
    String.intercalate " " (Codec.pointTokens cert.candidate)

end Hex.LatticeEnum
