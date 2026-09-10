/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Derived

public section

namespace Hex.PermGroup.Derived

/-- Replay starts from a supplied complete chain for the forced commutator
array, so the checker never reruns the chain producer. -/
structure Certificate (n : Nat) where
  seed : Chain n
  trace : List (Normal.Step n)

@[expose] def check (G K : Group n) (c : Certificate n) : Bool :=
  if hc : checkChain (seeds G) c.seed = true then
    Normal.checkClosure G ⟨seeds G, c.seed, hc⟩ K c.trace
  else false

theorem check_spec {G K : Group n} {c : Certificate n} (h : check G K c = true) :
    SameGroup K G.derived := by
  unfold check at h
  split at h
  · rename_i hc
    let H : Group n := ⟨seeds G, c.seed, hc⟩
    have he : SameGroup H (seedGroup G) := fun _ => Iff.rfl
    have hH : H.IsSubgroup G := fun p hp => seed_inside G p ((he p).mp hp)
    have hh := Normal.checkClosure_spec hH h
    have hK : K.IsSubgroup G.derived := hh.2.2.2 G.derived
      (fun p hp => G.derivedCert.contains p ((he p).mp hp)) G.derivedCert.normal
    have hd : G.derived.IsSubgroup K := (G.derived_le K).mpr
      (Normal.comm_generated G K hh.2.2.1 (by
        intro p hp q hq
        exact hh.2.1 _ ((he _).mpr (seed_comm G p hp q hq))))
    exact fun p => ⟨hK p, hd p⟩
  · contradiction

/-- Extract independent replay data from the deterministic producer. -/
@[expose] def certificate (G : Group n) : Certificate n :=
  ⟨(seedGroup G).chain, G.derivedCert.trace⟩

theorem checked (G : Group n) : check G G.derived (certificate G) = true := by
  have hc : checkChain (seeds G) (seedGroup G).chain = true := (seedGroup G).valid
  unfold check
  split
  · exact G.derivedCert.checked
  · rename_i hn
    exact False.elim (hn hc)

/-- Keep the output group and its certificate together so callers computing a
series do not rebuild the same normal closure to extract its trace. -/
structure Result (G : Group n) where
  group : Group n
  certificate : Certificate n
  checked : check G group certificate = true

theorem Result.inside {G : Group n} (r : Result G) : r.group.IsSubgroup G :=
  fun p hp => G.derived_inside p ((check_spec r.checked p).mp hp)

@[expose] def build (G : Group n) : Result G :=
  let d := G.derivedCert
  ⟨d.group, ⟨(seedGroup G).chain, d.trace⟩, checked G⟩

end Hex.PermGroup.Derived
