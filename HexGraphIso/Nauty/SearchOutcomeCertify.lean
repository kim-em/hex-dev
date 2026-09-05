/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeOtherTotal
public import HexGraphIso.Nauty.SearchOutcomeFirstNode
public import HexGraphIso.Nauty.SearchOutcomeRoot

public section

/-!
Totality of the certified canonicalization.

The two node statements are proved together by induction on the
executable recursion fuel; the root instance identifies the specification
key with the traced key, and the certificate check then succeeds.
`certifyCanon` is the resulting total, certificate-checked canonical
form, and the transcription `canonicalize?` is total because it agrees
with it.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Every node of both kinds is total at every executable fuel. -/
theorem totalAll (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat) :
    ∀ runFuel, OtherTotal G ctx inf tcLevel runFuel ∧
      FirstTotal G ctx inf tcLevel runFuel
  | 0 => ⟨OtherTotal.zero G ctx inf tcLevel, FirstTotal.zero G ctx inf tcLevel⟩
  | runFuel + 1 =>
      ⟨OtherTotal.succ G ctx inf tcLevel runFuel
          (totalAll G ctx inf tcLevel runFuel).1,
        FirstTotal.succ G ctx inf tcLevel runFuel
          (totalAll G ctx inf tcLevel runFuel).1
          (totalAll G ctx inf tcLevel runFuel).2⟩

/-- The unpruned specification key is the key the transcription installs. -/
theorem canonSpecKey_eq_tracedKey (G : Colored n k) (hn0 : 0 < n) :
    canonSpecKey G = tracedKey G :=
  keyEq_of_firstTotal G hn0
    (totalAll G { g := rowsOf G } (n + 2) 100 (n + 2)).2

/-- The certified canonicalization always succeeds. -/
theorem certifyCanon?_isSome (G : Colored n k) : (certifyCanon? G).isSome := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    exact certifyCanon?_isSome_zero G
  · exact certifyCanon?_isSome_of_keyEq G (canonSpecKey_eq_tracedKey G hn0)

/-! # Total certificate-checked canonicalization -/

/-- Certificate-checked canonicalization: the transcribed search's
answer, accepted through the single trusted `checkCanon` replay, which
always succeeds. -/
@[expose] def certifyCanon (G : Colored n k) : CanonResult n k :=
  (certifyCanon? G).get (certifyCanon?_isSome G)

theorem certifyCanon?_eq (G : Colored n k) :
    certifyCanon? G = some (certifyCanon G) :=
  (Option.some_get (certifyCanon?_isSome G)).symm

theorem certifyCanon_form (G : Colored n k) :
    (certifyCanon G).form = specCanon G := by
  have h := certifyCanon?_eq G
  rw [certifyCanon?] at h
  split at h
  · cases h
  · exact checkCanon_form h

theorem certifyCanon_relabel (G : Colored n k) :
    G.relabel (certifyCanon G).label = (certifyCanon G).form := by
  have h := certifyCanon?_eq G
  rw [certifyCanon?] at h
  split at h
  · cases h
  · exact (checkCanon_sound h).2.1.symm

/-- The transcription agrees with the certificate-checked answer on
every input. -/
theorem canonicalize?_eq (G : Colored n k) :
    canonicalize? G = some (certifyCanon G) :=
  canonicalize?_eq_of_certifyCanon (certifyCanon?_eq G)

/-- The transcription always answers. -/
theorem canonicalize?_isSome (G : Colored n k) :
    (canonicalize? G).isSome := by
  rw [canonicalize?_eq]
  rfl

end Hex.GraphIso.Nauty
