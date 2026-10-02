/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Root
public import HexGraphIso.Nauty.Sparse.MaxResult
public import HexGraphIso.Sparse.Run

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Untrusted sparse certificate data, including the production search's
literal canonical label. The key and every tree record must pass replay. -/
structure CertCandidate (n : Nat) where
  tree : CertNode
  key : Key n
  lab : Array Nat

/-- Run the optimized search once, then expand proof subtrees against its
installed key. The native label and tie order are retained literally. -/
@[expose] def produceCand (G : GraphIso.Sparse.Colored n k) : Option (CertCandidate n) :=
  let s := runColored G
  let best := if n = 0 then some (⟨[codeSentinel], G.graph⟩ : Key n)
    else State.best G.graph s
  best.map fun B => ⟨produceRoot G B, B, s.canonlab⟩

/-- The unlimited producer succeeds with the actual production label and
the proved canonical maximum. This uses unconditional production correctness. -/
theorem produceCand_eq (G : GraphIso.Sparse.Colored n k) :
    produceCand G = some ⟨produceRoot G (canonSpecKey G), canonSpecKey G,
      (runColored G).canonlab⟩ := by
  by_cases hn : n = 0
  · simp only [produceCand, hn, ite_true, canonSpecKey_zero hn, Option.map_some]
  · have hb : State.best G.graph (runColored G) = some (canonSpecKey G) :=
      run_max G (by omega)
    simp only [produceCand, hn, ite_false, hb, Option.map_some]

theorem produceCand_isSome (G : GraphIso.Sparse.Colored n k) : (produceCand G).isSome := by
  rw [produceCand_eq]
  rfl

theorem produceCand_replays {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    (h : produceCand G = some c) : checkKey G c.tree c.key = true := by
  rw [produceCand_eq] at h
  cases Option.some.inj h
  exact produceRoot_replays G

theorem produceCand_key {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    (h : produceCand G = some c) : c.key = canonSpecKey G := by
  rw [produceCand_eq] at h
  cases Option.some.inj h
  rfl

theorem produceCand_label {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    (h : produceCand G = some c) : c.lab = (runColored G).canonlab := by
  rw [produceCand_eq] at h
  cases Option.some.inj h
  rfl

/-- Validate an untrusted candidate through a single native sparse replay. -/
@[expose] def validateKey? (G : GraphIso.Sparse.Colored n k) (c : CertCandidate n) : Option (Key n) :=
  if checkKey G c.tree c.key then some c.key else none

theorem validateKey?_sound {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n} {B : Key n}
    (h : validateKey? G c = some B) : canonSpecKey G = B := by
  rw [validateKey?] at h
  split at h
  · rename_i hc
    cases Option.some.inj h
    exact checkKey_sound hc
  · cases h

/-- Produce and check a sparse key. No-limit failure is excluded by the
producer completeness theorem, independently of any trust in compiled code. -/
@[expose] def certifyKey? (G : GraphIso.Sparse.Colored n k) : Option (Key n) :=
  (produceCand G).bind (validateKey? G)

theorem certifyKey?_eq (G : GraphIso.Sparse.Colored n k) :
    certifyKey? G = some (canonSpecKey G) := by
  simp only [certifyKey?, produceCand_eq, Option.bind_some, validateKey?, produceRoot_replays, ite_true]

end Hex.GraphIso.Nauty.Sparse
