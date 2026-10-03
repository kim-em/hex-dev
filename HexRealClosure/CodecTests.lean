/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext
public meta import HexRealClosure.TowerContext
public import HexSignDet.Codec.Bytes
public meta import HexSignDet.Codec.Bytes

public section

namespace Hex.RealClosure.Tower.CodecTests
open SignDet
open SignDet.Codec (Json)

structure Observation where
  name : String
  bytes : Nat
  digest : UInt64
  accepted : Bool
  deriving Repr

private def signature (name : String) (value : Json) (roots keys : Nat) : Observation :=
  let bytes := value.writeBytes
  let accepted := match Signature.codec.decodeBytes bytes with
    | .error _ => false
    | .ok result => result.roots.length == roots && result.base.constants.length == keys &&
      result.literal == value && hash result.literal == hash value
  ⟨name, bytes.size, hash value, accepted⟩

private def payload (n : Nat) : Observation :=
  let q : Json := .arr #[.number 0, .number 1, .number 1]
  let value : Json := .arr #[.number 1, .arr (Array.replicate n q), .arr #[q]]
  let bytes := value.writeBytes
  let accepted := match Codec.parse {} bytes with
    | .error _ => false
    | .ok parsed => match BaseContext.Syntax.ofLiteral parsed with
      | some result@(.fraction p q) => p.length == n && q.length == 1 && result.literal == value
      | _ => false
  ⟨"fraction-payload", bytes.size, hash value, accepted⟩

/-- These are literal decoding/hash probes, not validated million-level towers
or semantic coefficient facts. Wide invalid literals are also untrusted input. -/
def run (n : Nat) : Array Observation :=
  let roots : Json := .arr #[.arr #[], .number 0, .arr (Array.replicate n (.number 0))]
  let key : Json := .arr #[.string "k", .number 0]
  let keys : Json := .arr #[.arr (Array.replicate (n / 4) key), .number 0, .arr #[]]
  #[signature "root-literals" roots n 0, signature "context-keys" keys 0 (n / 4), payload (n / 2)]

#guard (run 1000).all (·.accepted)

end Hex.RealClosure.Tower.CodecTests
