/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic

@[expose] public section

/-!
# D2 interval-representation experiment

These declarations are measurement candidates, not the public
`Hex.Interval` representation.  They place the same normalized `Raw` value in
the two layouts required by the D2 experiment:

* `Bundled` carries a proof of cut consistency;
* `Checked` is plain raw data, revalidated at a replay boundary.

Both candidates use `Raw.normalizeUnchecked` after constructing small trusted
inputs. The deterministic arena workload includes empty, whole, one-sided
unbounded, proper finite, reversed, open-singleton, and closed-singleton inputs.
The shared checksum makes timing comparisons detect semantic disagreement
rather than merely forcing weak-head evaluation.
-/

namespace Hex.Interval.Experiment

/-- Candidate that stores cut consistency with every interval value. -/
structure Bundled where
  raw : Raw
  isConsistent : raw.CutConsistent

namespace Bundled

/-- Construct a bundled candidate from a trusted experiment input. Production
planner boundaries must call `Raw.normalizeWithin` before exact comparison. -/
def ofTrustedRaw (raw : Raw) : Bundled :=
  ⟨raw.normalizeUnchecked, Raw.consistent_normalizeUnchecked raw⟩

/-- Observable raw view.  This is deliberately the operation whose generated
C representation is inspected by the D2 harness. -/
def view (interval : Bundled) : Raw := interval.raw

end Bundled

/-- Candidate that stores only canonical raw data.  Its consistency Boolean
is checked when a trace crosses the replay boundary. -/
abbrev Checked := Raw

namespace Checked

/-- Construct a plain candidate from a trusted experiment input. Production
planner boundaries must call `Raw.normalizeWithin` before exact comparison. -/
def ofTrustedRaw (raw : Raw) : Checked := raw.normalizeUnchecked

/-- Revalidate a plain candidate at a trust boundary. -/
def valid (interval : Checked) : Bool := interval.consistent

end Checked

/-- Deterministic raw input family covering all endpoint shapes and both
canonical and noncanonical finite pairs. -/
def sample (i : Nat) : Raw :=
  let precision : Int := Int.ofNat (i % 19) - 9
  let lower := Dyadic.ofIntWithPrec (Int.ofNat (2 * i + 1)) precision
  let step := Dyadic.ofIntWithPrec (Int.ofNat (2 * (i % 5) + 1)) precision
  let upper := lower + step
  let strict := i % 2 = 0
  match i % 8 with
  | 0 => .empty
  | 1 => .bounds .unbounded .unbounded
  | 2 => .bounds .unbounded (.finite upper strict)
  | 3 => .bounds (.finite lower strict) .unbounded
  | 4 => .bounds (.finite lower strict) (.finite upper (!strict))
  | 5 => .bounds (.finite upper false) (.finite lower false)
  | 6 => .bounds (.finite lower true) (.finite lower false)
  | _ => .bounds (.finite lower false) (.finite lower false)

/-- Build the append-only arena shape for the bundled candidate. -/
def bundledArena (n : Nat) : Array Bundled :=
  (Array.range n).map fun i => Bundled.ofTrustedRaw (sample i)

/-- Build the append-only arena shape for the externally checked candidate. -/
def checkedArena (n : Nat) : Array Checked :=
  (Array.range n).map fun i => Checked.ofTrustedRaw (sample i)

/-- Mix one word into a deterministic checksum. -/
def mix (acc value : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + value + 0xBF58476D1CE4E5B9

/-- Encode a signed integer without routing through a platform-sized type. -/
def intWord (value : Int) : UInt64 :=
  mix (UInt64.ofNat value.natAbs) (if value < 0 then 1 else 0)

/-- Checksum one canonical dyadic representation. -/
def dyadicWord : Dyadic → UInt64
  | .zero => 0
  | .ofOdd numerator precision _ =>
      mix (mix 1 (intWord numerator)) (intWord precision)

/-- Checksum a lower cut, including its shape and strictness. -/
def lowerWord : Lower → UInt64
  | .unbounded => 2
  | .finite value strict =>
      mix (mix 3 (dyadicWord value)) (if strict then 1 else 0)

/-- Checksum an upper cut, including its shape and strictness. -/
def upperWord : Upper → UInt64
  | .finite value strict =>
      mix (mix 5 (dyadicWord value)) (if strict then 1 else 0)
  | .unbounded => 7

/-- Checksum raw interval data. -/
def rawWord : Raw → UInt64
  | .empty => 11
  | .bounds lower upper => mix (lowerWord lower) (upperWord upper)

/-- Common checksum fold over raw views. -/
def checksum (arena : Array Raw) : UInt64 :=
  arena.foldl (fun acc raw => mix acc (rawWord raw)) 0

/-- Compiled-search workload for the bundled candidate. -/
def bundledWork (n : Nat) : UInt64 :=
  checksum ((bundledArena n).map Bundled.view)

/-- Compiled-search workload for the plain candidate, excluding the boundary
validation pass. -/
def checkedWork (n : Nat) : UInt64 :=
  checksum (checkedArena n)

/-- Replay-boundary workload for the plain candidate.  A failed consistency
check returns a deliberately distinct checksum. -/
def checkedBoundaryWork (n : Nat) : UInt64 :=
  let arena := checkedArena n
  if arena.all Checked.valid then checksum arena else UInt64.ofNat (UInt64.size - 1)

/-- Replay-boundary workload for the bundled candidate.  Consistency is
already represented by `Bundled.isConsistent`, so no Boolean scan is needed. -/
def bundledBoundaryWork (n : Nat) : UInt64 := bundledWork n

/-! The ordinary-kernel probes intentionally use a separate, transparent
`List`/`Nat` encoding.  Compiled search uses arrays and machine words above;
replaying those implementation details through a downstream module would tie
the proof format to core array internals. -/

/-- Small exact encoding of a signed integer for kernel replay. -/
def replayInt (value : Int) : Nat :=
  2 * value.natAbs + if value < 0 then 1 else 0

/-- Small exact encoding of a dyadic's canonical constructor fields. -/
def replayDyadic : Dyadic → Nat
  | .zero => 0
  | .ofOdd numerator precision _ =>
      1 + 3 * replayInt numerator + 5 * replayInt precision

/-- Encode one lower cut for the transparent replay fold. -/
def replayLower : Lower → Nat
  | .unbounded => 2
  | .finite value strict =>
      3 + 7 * replayDyadic value + if strict then 1 else 0

/-- Encode one upper cut for the transparent replay fold. -/
def replayUpper : Upper → Nat
  | .finite value strict =>
      5 + 11 * replayDyadic value + if strict then 1 else 0
  | .unbounded => 7

/-- Encode raw data for the transparent replay fold. -/
def replayRaw : Raw → Nat
  | .empty => 11
  | .bounds lower upper => 13 + replayLower lower + replayUpper upper

/-- Ordinary-kernel workload for the bundled representation. -/
def replayBundledWork (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => acc + replayRaw (Bundled.ofTrustedRaw (sample i)).view) 0

/-- Ordinary-kernel workload for the externally checked representation.  The
Boolean validation is performed on each retained value before its encoding is
accepted. -/
def replayCheckedWork (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i =>
      let interval := Checked.ofTrustedRaw (sample i)
      if interval.valid then acc + replayRaw interval else acc)
    0

end Hex.Interval.Experiment
