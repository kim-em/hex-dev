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
-/

namespace Hex.BenchOracle.Nauty

/-- One canonical-labelling answer from the pinned nauty 2.9.3:
the canonical labelling, the canonical upper-triangle adjacency bits in
row-major order as a `0`/`1` string, and the visited-node count. -/
structure CanonResult where
  lab : Array Nat
  tri : String
  nodes : Nat
  deriving Repr

/-- Raw FFI call. Marshalling contract (kept in sync with
`hex_nauty_canon` in `nauty_canon.c`): `colors` holds `n` colour bytes,
`adj` holds `n * n` row-major `0`/`1` bytes, and the result packs `n`
lab bytes, `n*(n-1)/2` upper-triangle `0`/`1` bytes, and the
visited-node count as 8 little-endian bytes. `canon` validates the
preconditions (`1 ≤ n ≤ 255`, `k ≤ n`, colour bytes below `k`). -/
@[extern "hex_nauty_canon"]
private opaque canonFFI (n k : USize) (colors adj : @& ByteArray) : ByteArray

/-- Canonicalize one coloured graph through the pinned nauty
comparator. `adj` lists each vertex's adjacency row as a `0`/`1`
string. -/
def canon (n k : Nat) (colors : List Nat) (adj : List String) :
    IO CanonResult := do
  unless 1 ≤ n && n ≤ 255 do
    throw <| IO.userError s!"nauty canon: n = {n} out of range"
  unless k ≤ n do
    throw <| IO.userError s!"nauty canon: k = {k} exceeds n = {n}"
  unless colors.length == n && colors.all (· < k) do
    throw <| IO.userError "nauty canon: bad colour list"
  unless adj.length == n && adj.all (·.length == n) do
    throw <| IO.userError "nauty canon: bad adjacency rows"
  let colorBytes := ByteArray.mk <| (colors.map (·.toUInt8)).toArray
  let mut adjBytes := ByteArray.emptyWithCapacity (n * n)
  for row in adj do
    for c in row.toList do
      adjBytes := adjBytes.push (if c == '1' then 1 else 0)
  let out := canonFFI n.toUSize k.toUSize colorBytes adjBytes
  let triLen := n * (n - 1) / 2
  unless out.size == n + triLen + 8 do
    throw <| IO.userError
      s!"nauty canon: FFI reply has {out.size} bytes, expected {n + triLen + 8}"
  let lab := (Array.range n).map fun i => (out.get! i).toNat
  let tri := String.ofList <| (List.range triLen).map fun i =>
    if out.get! (n + i) == 1 then '1' else '0'
  let mut nodes := 0
  for b in [0:8] do
    nodes := nodes + (out.get! (n + triLen + b)).toNat <<< (8 * b)
  return { lab, tri, nodes }

end Hex.BenchOracle.Nauty
