/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Group

public section

namespace Hex.PermGroup.Chain

/-- Mixed-radix encoding, with the top-level orbit digit most significant. -/
@[expose] def encode : (c : Chain n) → c.Choice → Fin c.orbitProduct
  | .leaf _ _, _ => ⟨0, Nat.zero_lt_one⟩
  | .cons level tail, digits =>
    let rest := tail.encode digits.2
    ⟨digits.1.val * tail.orbitProduct + rest.val, by
      have h := Nat.mul_le_mul_right tail.orbitProduct digits.1.isLt
      change _ < level.orbit.points.size * tail.orbitProduct
      have := rest.isLt
      simp only [Nat.succ_mul] at h
      omega⟩

/-- Exact division and remainder recover the mixed-radix digits. An in-range
index itself proves that every radix encountered on its path is positive. -/
@[expose] def decode : (c : Chain n) → Fin c.orbitProduct → c.Choice
  | .leaf _ _, _ => PUnit.unit
  | .cons level tail, k =>
    have hp : 0 < tail.orbitProduct := by
      have hk := k.isLt
      change k.val < level.orbit.points.size * tail.orbitProduct at hk
      by_cases he : tail.orbitProduct = 0
      · simp [he] at hk
      · omega
    (⟨k.val / tail.orbitProduct, by
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      exact k.isLt⟩,
      tail.decode ⟨k.val % tail.orbitProduct, Nat.mod_lt _ hp⟩)

theorem encode_decode (c : Chain n) (k : Fin c.orbitProduct) : c.encode (c.decode k) = k := by
  induction c with
  | leaf S words =>
    apply Fin.ext
    have := k.isLt
    change k.val < 1 at this
    simp only [encode]
    omega
  | cons level tail ih =>
    apply Fin.ext
    simp only [decode, encode, ih]
    simpa only [Nat.mul_comm] using Nat.div_add_mod k.val tail.orbitProduct

theorem decode_encode (c : Chain n) (digits : c.Choice) : c.decode (c.encode digits) = digits := by
  induction c with
  | leaf S words => cases digits; rfl
  | cons level tail ih =>
    have hr := (tail.encode digits.2).isLt
    have hp : 0 < tail.orbitProduct := by omega
    apply Prod.ext
    · apply Fin.ext
      change (digits.1.val * tail.orbitProduct + (tail.encode digits.2).val) /
        tail.orbitProduct = digits.1.val
      rw [Nat.mul_comm digits.1.val, Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.add_zero]
    · simpa [encode, decode, Nat.add_mod, Nat.mod_eq_of_lt hr] using ih digits.2

/-- Sifting with bounded orbit digits. Failures carry no choice and cannot be
used as a rank; membership still comes from the complete-chain checker. -/
@[expose] def choose : (c : Chain n) → Nat → Perm n → Option c.Choice
  | .leaf _ _, _, p => if p = Perm.id n then some PUnit.unit else none
  | .cons level tail, base, p =>
    if hb : base < n then
      match level.orbit.lookup[(p.get ⟨base, hb⟩).val] with
      | none => none
      | some x => (tail.choose (base + 1) (level.orbit.reps[x.val].inv.comp p)).map (x, ·)
    else none

theorem choose_isSome (c : Chain n) (base : Nat) (p : Perm n) :
    (c.choose base p).isSome = c.accepts base p := by
  induction c generalizing base p with
  | leaf S words =>
    simp only [choose, accepts_leaf, Choice]
    split <;> simp_all
  | cons level tail ih =>
    rw [choose, accepts_cons]
    simp only [Choice]
    split
    · split <;> simp_all
    · rfl

theorem choose_sound {c : Chain n} {base : Nat} {p : Perm n} {digits : c.Choice}
    (h : c.choose base p = some digits) : c.value digits = p := by
  induction c generalizing base p with
  | leaf S words =>
    simp only [choose] at h
    split at h
    · rename_i he
      exact he.symm
    · simp at h
  | cons level tail ih =>
    simp only [choose] at h
    split at h
    · split at h
      · simp at h
      · rename_i x hx
        obtain ⟨rest, hr, he⟩ := Option.map_eq_some_iff.mp h
        subst digits
        have hv := ih hr
        simp only [value, hv]
        apply Perm.ext
        intro i
        simp
    · simp at h

/-- Obtain a choice from a known successful sift, without repeating membership
checks or searching through possible choices. -/
@[expose] def choice (c : Chain n) (base : Nat) (p : Perm n) (h : c.accepts base p = true) : c.Choice :=
  (c.choose base p).get (by simpa only [choose_isSome] using h)

theorem value_choice (c : Chain n) (base : Nat) (p : Perm n) (h : c.accepts base p = true) :
    c.value (c.choice base p h) = p :=
  choose_sound (Option.some_get _).symm

end Hex.PermGroup.Chain

namespace Hex.PermGroup.Group

theorem checked (G : Group n) : G.chain.checkFrom 0 = true :=
  (of_decide_eq_true G.valid).2.2

/-- The position of an element in the stored chain's mixed-radix ordering. -/
@[expose] def rank (G : Group n) (p : Element G) : Fin G.order :=
  G.chain.encode (G.chain.choice 0 p.val ((G.contains_iff p.val).mpr p.property))

/-- Recover an element by exact digit extraction and representative multiplication. -/
@[expose] def unrank (G : Group n) (k : Fin G.order) : Element G :=
  ⟨G.chain.value (G.chain.decode k),
    checkWords_sound (of_decide_eq_true G.valid).2.1
      (Chain.value_generated (checked G) _)⟩

theorem unrank_rank (G : Group n) (p : Element G) : G.unrank (G.rank p) = p := by
  apply Subtype.ext
  simp only [rank, unrank, Chain.decode_encode]
  exact Chain.value_choice ..

theorem rank_unrank (G : Group n) (k : Fin G.order) : G.rank (G.unrank k) = k := by
  have he : G.chain.choice 0 (G.unrank k).val
      ((G.contains_iff _).mpr (G.unrank k).property) = G.chain.decode k := by
    apply Chain.value_injective (checked G)
    exact Chain.value_choice ..
  simp only [rank, he]
  exact Chain.encode_decode ..

/-- Raw permutations are ranked only after a complete membership check. -/
@[expose] def rank? (G : Group n) (p : Perm n) : Option (Fin G.order) :=
  (G.chain.choose 0 p).map G.chain.encode

/-- Reject out-of-range indices before digit extraction. -/
@[expose] def unrank? (G : Group n) (k : Nat) : Option (Element G) :=
  if h : k < G.order then some (G.unrank ⟨k, h⟩) else none

theorem rank?_isSome (G : Group n) (p : Perm n) : (G.rank? p).isSome = G.contains p := by
  change ((G.chain.choose 0 p).map G.chain.encode).isSome = G.chain.accepts 0 p
  rw [Option.isSome_map, Chain.choose_isSome]

theorem rank?_rank (G : Group n) (p : Element G) : G.rank? p.val = some (G.rank p) := by
  have hc : G.chain.choose 0 p.val =
      some (G.chain.choice 0 p.val ((G.contains_iff _).mpr p.property)) :=
    (Option.some_get _).symm
  change (G.chain.choose 0 p.val).map G.chain.encode =
    some (G.chain.encode (G.chain.choice 0 p.val ((G.contains_iff _).mpr p.property)))
  rw [hc]
  rfl

theorem unrank?_unrank (G : Group n) (k : Fin G.order) : G.unrank? k.val = some (G.unrank k) := by
  simp [unrank?, k.isLt]

theorem unrank?_isSome (G : Group n) (k : Nat) :
    (G.unrank? k).isSome = decide (k < G.order) := by
  unfold unrank?
  split <;> simp_all

/-- Apply unranking to one index from the supplied source. The source receives
the positive exact order; its effects and failures are preserved by `map`. -/
@[expose] def sampleWith {m : Type → Type} [Functor m]
    (draw : (bound : Nat) → 0 < bound → m (Fin bound)) (G : Group n) : m (Element G) :=
  G.unrank <$> draw G.order G.order_pos

theorem sampleWith_error {ε : Type} (error : ε) (G : Group n) :
    sampleWith (m := Except ε) (fun _ _ => Except.error error) G = Except.error error := rfl

end Hex.PermGroup.Group
