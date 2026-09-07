/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# nauty FFI bench comparator

Lean binding for `Hex/BenchOracle/ffi/nauty_canon.c`, which links the
vendored nauty 2.9.3 source in `vendor/nauty-2.9.3` (unmodified files
from the pinned archive; provenance in that directory's README) through
the static library `hexnautyffi`. The C side runs the same pinned
densenauty configuration as the conformance oracle shim
`scripts/oracle/graphiso_nauty_shim.c`.

Development-monorepo tooling only: the vendored nauty and this
comparator support conformance and benchmarking here and are not part
of any released Hex library.

## Keeping marshalling out of the measurement

This binding exists to be *timed against*, so anything it does that
nauty does not must stay outside the timed region. Two things here are
`O(n²)` and have nothing to do with the search:

* building the `n * n` adjacency byte array the C side reads, and
* reading the canonical form back out.

So the call is split. `prepare` does the marshalling and is meant to run
once, before the timer starts; `canonPrepared` is the timed call, and
decodes only the `O(n)` labelling and the node count. The canonical form
comes back as packed bits inside `CanonResult.raw` and is never
materialized unless something asks: `sameForm` compares two results
without building anything, and `tri` renders the `0`/`1` string the
conformance oracle emits, at `O(n²)`, for callers outside a timed
region.

`canon` is the unsplit convenience wrapper, and charges the caller for
the marshalling; do not use it inside a timing loop.
-/

namespace Hex.BenchOracle.Nauty

/-- One canonical-labelling answer from the pinned nauty 2.9.3.

`raw` is the FFI reply verbatim: `n` little-endian `UInt32` labelling
entries, then `⌈n(n-1)/2 / 8⌉` bytes of the canonical upper triangle
packed row-major and least-significant bit first, then the visited-node
count as 8 little-endian bytes. Reading the canonical form out of it is
`O(n²)`, so it is left packed. -/
structure CanonResult where
  /-- The FFI reply verbatim. -/
  raw : ByteArray
  /-- The number of vertices. -/
  n : Nat
  /-- The canonical labelling. -/
  lab : Array Nat
  /-- The visited-node count. -/
  nodes : Nat

/-- A graph already marshalled into the comparator's wire format.
Building one is `O(n²)` and is not part of what nauty does, so a timing
loop builds it once and calls `canonPrepared` inside. -/
structure Prepared where
  /-- The number of vertices. -/
  n : Nat
  /-- The number of ordered colour cells. -/
  k : Nat
  /-- `n` little-endian `UInt32` colours. -/
  colors : ByteArray
  /-- `n * n` row-major `0`/`1` adjacency bytes. -/
  adj : ByteArray

/-- Raw FFI call. Marshalling contract (kept in sync with
`hex_nauty_canon` in `nauty_canon.c`): `colors` holds `n` little-endian
`UInt32` colours, `adj` holds `n * n` row-major `0`/`1` bytes, and the
result is the `CanonResult.raw` layout above. `prepare` validates the
preconditions (`1 ≤ n`, `k ≤ n`, colours below `k`). Labels and colours
are four bytes wide so that the comparator is not capped at 255
vertices. -/
@[extern "hex_nauty_canon"]
private opaque canonFFI (n k : USize) (colors adj : @& ByteArray) : ByteArray

private def pushU32 (b : ByteArray) (v : Nat) : ByteArray :=
  b |>.push (UInt8.ofNat (v % 256))
    |>.push (UInt8.ofNat (v >>> 8 % 256))
    |>.push (UInt8.ofNat (v >>> 16 % 256))
    |>.push (UInt8.ofNat (v >>> 24 % 256))

private def getU32 (b : ByteArray) (off : Nat) : Nat :=
  (b.get! off).toNat ||| ((b.get! (off + 1)).toNat <<< 8) |||
    ((b.get! (off + 2)).toNat <<< 16) ||| ((b.get! (off + 3)).toNat <<< 24)

/-- Marshal a coloured graph into the comparator's wire format. `adj`
lists each vertex's adjacency row as a `0`/`1` string. `O(n²)`: call it
outside any timed region. Pure, so a benchmark can hold its prepared
input in a top-level definition and time nothing but the call. -/
def prepare? (n k : Nat) (colors : List Nat) (adj : List String) :
    Except String Prepared := do
  unless 1 ≤ n do
    throw s!"nauty canon: n = {n} out of range"
  unless k ≤ n do
    throw s!"nauty canon: k = {k} exceeds n = {n}"
  unless colors.length == n && colors.all (· < k) do
    throw "nauty canon: bad colour list"
  unless adj.length == n && adj.all (·.length == n) do
    throw "nauty canon: bad adjacency rows"
  let mut colorBytes := ByteArray.emptyWithCapacity (4 * n)
  for c in colors do
    colorBytes := pushU32 colorBytes c
  let mut adjBytes := ByteArray.emptyWithCapacity (n * n)
  for row in adj do
    for c in row.toList do
      adjBytes := adjBytes.push (if c == '1' then 1 else 0)
  return { n, k, colors := colorBytes, adj := adjBytes }

/-- `prepare?` in `IO`. -/
def prepare (n k : Nat) (colors : List Nat) (adj : List String) :
    IO Prepared :=
  IO.ofExcept (prepare? n k colors adj)

/-- The number of bytes of packed canonical form for `n` vertices. -/
private def triBytes (n : Nat) : Nat := (n * (n - 1) / 2 + 7) / 8

/-- Canonicalize a marshalled graph. This is the call to time: it enters
nauty and decodes the `O(n)` labelling and the node count, leaving the
canonical form packed. -/
def canonPrepared (p : Prepared) : IO CanonResult := do
  let out := canonFFI p.n.toUSize p.k.toUSize p.colors p.adj
  let want := 4 * p.n + triBytes p.n + 8
  unless out.size == want do
    throw <| IO.userError
      s!"nauty canon: FFI reply has {out.size} bytes, expected {want}"
  let lab := (Array.range p.n).map fun i => getU32 out (4 * i)
  let base := 4 * p.n + triBytes p.n
  let mut nodes := 0
  for b in [0:8] do
    nodes := nodes + (out.get! (base + b)).toNat <<< (8 * b)
  return { raw := out, n := p.n, lab, nodes }

/-- Canonicalize one coloured graph, marshalling included. Convenience
for callers outside a timing loop; inside one, use `prepare` and then
`canonPrepared`. -/
def canon (n k : Nat) (colors : List Nat) (adj : List String) :
    IO CanonResult := do
  canonPrepared (← prepare n k colors adj)

namespace CanonResult

/-- Bit `t` of the packed canonical upper triangle. -/
def triBit (r : CanonResult) (t : Nat) : Bool :=
  (r.raw.get! (4 * r.n + t / 8) >>> UInt8.ofNat (t % 8)) &&& 1 == 1

/-- Do two results have the same canonical form? A comparison over the
packed bytes, allocating nothing. -/
def sameForm (a b : CanonResult) : Bool := Id.run do
  if a.n != b.n then return false
  let bytes := triBytes a.n
  for t in [0:bytes] do
    if a.raw.get! (4 * a.n + t) != b.raw.get! (4 * b.n + t) then
      return false
  return true

/-- The canonical upper-triangle adjacency bits in row-major order as a
`0`/`1` string, the form the conformance oracle emits. `O(n²)`: call it
outside any timed region. -/
def tri (r : CanonResult) : String :=
  String.ofList <| (List.range (r.n * (r.n - 1) / 2)).map fun t =>
    if r.triBit t then '1' else '0'

end CanonResult

end Hex.BenchOracle.Nauty
