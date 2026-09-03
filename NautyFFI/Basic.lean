/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
# Dense nauty 2.9.3 bindings

This module exposes the deliberately narrow dense-nauty configuration used by
`hex-graph-iso`: canonical labelling for vertex-coloured undirected simple
graphs, and the isomorphism test derived from two canonical labellings.

The implementation is an unverified native FFI. Callers that need trusted
results must validate them independently.
-/

namespace NautyFFI

/-- A finite vertex-coloured graph. Vertex `i` has colour `colors[i]`, colours
are the ordered indices below `colorCount`, and `adjacency[i][j]` records an
undirected edge. `canonicalize` checks that the matrix is square, symmetric,
and loopless, and that every declared colour is used. -/
structure Graph where
  /-- The number of ordered colour cells. -/
  colorCount : Nat
  /-- One ordered colour index per vertex. -/
  colors : Array Nat
  /-- The symmetric, loopless Boolean adjacency matrix. -/
  adjacency : Array (Array Bool)
  deriving Repr, BEq

/-- A canonical form: ordered colour-cell sizes followed by the upper
triangle of the canonical adjacency matrix in row-major order. If there are
`n` vertices, `adjacency` has `n * (n - 1) / 2` entries. -/
structure CanonicalForm where
  /-- Sizes of the ordered colour cells. -/
  cellSizes : Array Nat
  /-- Canonical upper-triangle adjacency bits in row-major order. -/
  adjacency : Array Bool
  deriving Repr, BEq

/-- The result of canonical labelling. `labelling[new]` is the original
vertex placed at canonical position `new`. -/
structure CanonResult where
  /-- Nauty's canonical labelling, mapping new positions to old vertices. -/
  labelling : Array Nat
  /-- The canonical form produced by the labelling. -/
  form : CanonicalForm
  deriving Repr, BEq

/-- Raw native call into the vendored nauty 2.9.3. Inputs and outputs use
little-endian 32-bit vertex indices; canonical adjacency entries are bytes.
The checked `canonicalize` wrapper is the public entry point. -/
@[extern "lean_nauty_canonicalize"]
private opaque canonicalizeRaw
    (n colorCount : USize) (colors adjacency : @& ByteArray) : ByteArray

private def pushUInt32 (bytes : ByteArray) (value : Nat) : ByteArray :=
  bytes
    |>.push (value &&& 0xff).toUInt8
    |>.push ((value >>> 8) &&& 0xff).toUInt8
    |>.push ((value >>> 16) &&& 0xff).toUInt8
    |>.push ((value >>> 24) &&& 0xff).toUInt8

private def getUInt32 (bytes : ByteArray) (offset : Nat) : Nat :=
  (bytes.get! offset).toNat |||
    ((bytes.get! (offset + 1)).toNat <<< 8) |||
    ((bytes.get! (offset + 2)).toNat <<< 16) |||
    ((bytes.get! (offset + 3)).toNat <<< 24)

private def validate (graph : Graph) : Except String Unit := do
  let n := graph.colors.size
  if n > 2147483647 then
    throw s!"nauty: vertex count {n} exceeds the C interface limit"
  if graph.colorCount > 2147483647 then
    throw s!"nauty: colour count {graph.colorCount} exceeds the C interface limit"
  if graph.adjacency.size != n then
    throw s!"nauty: expected {n} adjacency rows, got {graph.adjacency.size}"
  if n == 0 then
    if graph.colorCount != 0 then
      throw "nauty: the empty graph must have no colour cells"
    return
  if graph.colorCount == 0 || graph.colorCount > n then
    throw s!"nauty: expected between 1 and {n} colour cells"
  let mut seen := Array.replicate graph.colorCount false
  for i in [0:n] do
    let color := graph.colors[i]!
    if color >= graph.colorCount then
      throw s!"nauty: colour {color} at vertex {i} is out of range"
    seen := seen.set! color true
    let row := graph.adjacency[i]!
    if row.size != n then
      throw s!"nauty: adjacency row {i} has length {row.size}, expected {n}"
    if row[i]! then
      throw s!"nauty: adjacency matrix has a loop at vertex {i}"
  for color in [0:graph.colorCount] do
    if !seen[color]! then
      throw s!"nauty: colour cell {color} is empty"
  for i in [0:n] do
    for j in [i + 1:n] do
      if graph.adjacency[i]![j]! != graph.adjacency[j]![i]! then
        throw s!"nauty: adjacency matrix is not symmetric at ({i}, {j})"

private def cellSizes (graph : Graph) : Array Nat := Id.run do
  let mut sizes := Array.replicate graph.colorCount 0
  for color in graph.colors do
    sizes := sizes.set! color (sizes[color]! + 1)
  return sizes

private def isLabelling (n : Nat) (labelling : Array Nat) : Bool := Id.run do
  if labelling.size != n then return false
  let mut seen := Array.replicate n false
  for vertex in labelling do
    if vertex >= n || seen[vertex]! then return false
    seen := seen.set! vertex true
  return true

/-- Canonically label a vertex-coloured undirected simple graph with the
pinned dense-nauty configuration. The result contains both nauty's labelling
and the canonical form (ordered colour-cell sizes and canonical adjacency).
Malformed inputs are rejected before entering native code. -/
def canonicalize (graph : Graph) : Except String CanonResult := do
  validate graph
  let n := graph.colors.size
  let sizes := cellSizes graph
  if n == 0 then
    return { labelling := #[], form := { cellSizes := sizes, adjacency := #[] } }
  let mut colorBytes := ByteArray.emptyWithCapacity (4 * n)
  for color in graph.colors do
    colorBytes := pushUInt32 colorBytes color
  let mut adjacencyBytes := ByteArray.emptyWithCapacity (n * n)
  for row in graph.adjacency do
    for adjacent in row do
      adjacencyBytes := adjacencyBytes.push (if adjacent then 1 else 0)
  let output := canonicalizeRaw n.toUSize graph.colorCount.toUSize
    colorBytes adjacencyBytes
  let triSize := n * (n - 1) / 2
  let expectedSize := 4 * n + triSize
  if output.size != expectedSize then
    throw s!"nauty: native result has {output.size} bytes, expected {expectedSize}"
  let labelling := (Array.range n).map fun i => getUInt32 output (4 * i)
  if !isLabelling n labelling then
    throw "nauty: native result contains an invalid canonical labelling"
  let adjacency := (Array.range triSize).map fun i => output.get! (4 * n + i) != 0
  return { labelling, form := { cellSizes := sizes, adjacency } }

/-- Find an isomorphism between two valid coloured graphs. The result is
`none` when their canonical forms differ. For `some transporter`,
`transporter[oldA]` is the corresponding vertex of the second graph; it is
obtained by composing the two canonical labellings. -/
def findIso (left right : Graph) : Except String (Option (Array Nat)) := do
  validate left
  validate right
  if left.colors.size != right.colors.size || left.colorCount != right.colorCount then
    return none
  let leftCanon ← canonicalize left
  let rightCanon ← canonicalize right
  if leftCanon.form != rightCanon.form then
    return none
  let n := left.colors.size
  let mut transporter := Array.replicate n 0
  for i in [0:n] do
    transporter := transporter.set! leftCanon.labelling[i]! rightCanon.labelling[i]!
  return some transporter

/-- Decide coloured-graph isomorphism by equality of the two canonical forms.
Malformed inputs are reported as errors. -/
def isIso (left right : Graph) : Except String Bool := do
  return (← findIso left right).isSome

end NautyFFI
