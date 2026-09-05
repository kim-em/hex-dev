/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Bits
public import HexGraphIso.IsoLit

public section

/-!
Kernel-priced primitives for the certificate replay.

The kernel has no support for `Array` and reduces `List` access by
walking the spine, so every indexed read of the replay's labelling
and partition state costs the index. It does have GMP-accelerated
`Nat` arithmetic and bit operations, each one reduction step whatever
the operand size. This file packs a list of small naturals into one
`Nat` of fixed-width fields, so that a read is a shift and a mask and
a write is a handful of arithmetic steps, and states the
correspondence `Rep` between a packed number and the list it encodes
that the replay clones in `HexGraphIso.NodePacked` thread through
their equalities.

Every definition here that the kernel evaluates is spelled with the
raw `Nat.add`, `Nat.beq`, `Nat.land`, ... functions the kernel
accelerates and with `cond` on their `Bool` results, so no typeclass
instance or `Decidable` wrapper stands between the term and the
accelerated step; the `if`/`==`/`&&&` spellings unfold to these by
`rfl`, which is how the proofs connect the two. The same treatment
gives `popCountK` and `lowBitK`, byte-table forms of the per-bit
recursions that the kernel otherwise pays one step per bit for.
-/

namespace Hex.GraphIso.Nauty

/-! # Raw operation spellings -/

@[simp] theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
@[simp] theorem lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
@[simp] theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
@[simp] theorem shiftRight_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
@[simp] theorem shiftLeft_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
@[simp] theorem mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
@[simp] theorem add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[simp] theorem sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[simp] theorem div_eq (a b : Nat) : Nat.div a b = a / b := rfl
@[simp] theorem mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

theorem cond_beq {α : Type} (a b : Nat) (x y : α) :
    cond (Nat.beq a b) x y = if a = b then x else y := by
  rcases hb : Nat.beq a b with _ | _
  · rw [ite_eq_right (Nat.ne_of_beq_eq_false hb)]
    rfl
  · rw [ite_eq_left (Nat.eq_of_beq_eq_true hb)]
    rfl

theorem cond_blt {α : Type} (a b : Nat) (x y : α) :
    cond (Nat.blt a b) x y = if a < b then x else y := by
  rcases Decidable.em (a < b) with h | h
  · simp [h, Nat.blt_eq]
  · simp [h, Nat.blt_eq]

theorem cond_ble {α : Type} (a b : Nat) (x y : α) :
    cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  rcases Decidable.em (a ≤ b) with h | h
  · simp [h, Nat.ble_eq]
  · simp [h, Nat.ble_eq]

theorem beq_eq_beq (a b : Nat) : Nat.beq a b = (a == b) := by
  rcases hb : Nat.beq a b with _ | _
  · exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_beq_eq_false hb)).symm
  · exact (beq_iff_eq.mpr (Nat.eq_of_beq_eq_true hb)).symm

theorem blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rcases Decidable.em (a < b) with h | h
  · rw [decide_eq_true h]
    exact Nat.blt_eq.mpr h
  · rw [decide_eq_false h]
    rcases hb : Nat.blt a b with _ | _
    · rfl
    · exact absurd (Nat.blt_eq.mp hb) h

theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rcases Decidable.em (a ≤ b) with h | h
  · rw [decide_eq_true h]
    exact Nat.ble_eq.mpr h
  · rw [decide_eq_false h]
    rcases hb : Nat.ble a b with _ | _
    · rfl
    · exact absurd (Nat.ble_eq.mp hb) h

theorem beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rcases Decidable.em (a = b) with h | h
  · rw [decide_eq_true h]
    exact Nat.beq_eq.mpr h
  · rw [decide_eq_false h]
    rcases hb : Nat.beq a b with _ | _
    · rfl
    · exact absurd (Nat.beq_eq.mp hb) h

theorem cond_beq_true {α : Type} (a : Bool) (x y : α) :
    cond a x y = if a = true then x else y := by
  cases a <;> rfl

/-! # Bit-set operations, raw -/

/-- `elem` with the accelerated steps only. -/
@[expose] def elemK (s v : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight s v) 1) 1

theorem elemK_eq (s v : Nat) : elemK s v = elem s v := by
  rw [elemK, elem, Nat.testBit, land_eq, shiftRight_eq, Nat.and_one_is_mod,
    Nat.and_comm, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (s >>> v) with h | h <;> simp [h] <;> rfl

/-- `insert`, raw. -/
@[expose] def insertK (s v : Nat) : Nat :=
  Nat.lor s (Nat.shiftLeft 1 v)

theorem insertK_eq (s v : Nat) : insertK s v = insert s v := rfl

/-- `erase`, raw. -/
@[expose] def eraseK (s v : Nat) : Nat :=
  cond (elemK s v) (Nat.xor s (Nat.shiftLeft 1 v)) s

theorem eraseK_eq (s v : Nat) : eraseK s v = erase s v := by
  rw [eraseK, erase, elemK_eq, cond_beq_true]
  rfl

/-- `mash`, raw. -/
@[expose] def mashK (l i : Nat) : Nat :=
  Nat.land (Nat.add (Nat.xor l 0o65435) i) 0o77777

theorem mashK_eq (l i : Nat) : mashK l i = mash l i := rfl

/-- `cleanup`, raw. -/
@[expose] def cleanupK (l : Nat) : Nat := Nat.mod l 0o77777

theorem cleanupK_eq (l : Nat) : cleanupK l = cleanup l := rfl

/-! # Byte-table `popCount` and `lowBit`

The per-bit recursions cost the kernel about forty reduction steps
per bit (each iteration a `Nat` decision, a modulus, a division, an
addition, all through their instances). One byte per iteration, the
byte's answer read from a 256-entry table packed four bits per entry
into one literal, is one shift and one mask per byte. -/

/-- `popCount` of every byte, four bits per entry. -/
@[expose] def popCountTable : Nat :=
  0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110

/-- `lowBit` of every nonzero byte (and `0` for the zero byte), four
bits per entry. -/
@[expose] def lowBitTable : Nat :=
  0x102010301020104010201030102010501020103010201040102010301020106010201030102010401020103010201050102010301020104010201030102010701020103010201040102010301020105010201030102010401020103010201060102010301020104010201030102010501020103010201040102010301020100

/-- The table entry of byte `b`. -/
@[expose] def byteEntry (table b : Nat) : Nat :=
  Nat.land (Nat.shiftRight table (Nat.mul 4 b)) 15

theorem popCountTable_spec :
    ∀ b, b < 256 → byteEntry popCountTable b = popCount b := by
  decide +kernel

theorem lowBitTable_spec :
    ∀ b, b < 256 → byteEntry lowBitTable b = lowBit b := by
  decide +kernel

/-- `popCount` by bytes, raw. -/
@[expose] def popCountK (s : Nat) : Nat :=
  go (s + 1) s 0
where
  go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | fuel + 1, s, acc =>
      cond (Nat.beq s 0) acc
        (go fuel (Nat.shiftRight s 8)
          (Nat.add acc (byteEntry popCountTable (Nat.land s 255))))

theorem popCountK_go_eq :
    ∀ (fuel s acc : Nat), s < fuel →
      popCountK.go fuel s acc = acc + popCount s
  | fuel + 1, s, acc, h => by
    rw [popCountK.go, cond_beq]
    rcases Decidable.em (s = 0) with rfl | hs
    · simp
    · rw [ite_eq_right hs]
      simp only [shiftRight_eq, land_eq, add_eq]
      have h255 : s &&& 255 = s % 256 := Nat.and_two_pow_sub_one_eq_mod s 8
      have hlt : s >>> 8 < fuel := by
        rw [Nat.shiftRight_eq_div_pow]
        have := Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by decide : 1 < 2 ^ 8)
        omega
      rw [popCountK_go_eq fuel _ _ hlt, h255,
        popCountTable_spec _ (Nat.mod_lt _ (by decide)), popCount_split s]
      omega

theorem popCountK_eq (s : Nat) : popCountK s = popCount s := by
  rw [popCountK, popCountK_go_eq (s + 1) s 0 (Nat.lt_succ_self s), Nat.zero_add]

/-- `lowBit` by bytes, raw. -/
@[expose] def lowBitK (s : Nat) : Nat :=
  go (s + 1) s 0
where
  go : Nat → Nat → Nat → Nat
    | 0, _, _ => 0
    | fuel + 1, s, shift =>
      cond (Nat.beq s 0) 0
        (cond (Nat.beq (Nat.land s 255) 0)
          (go fuel (Nat.shiftRight s 8) (Nat.add shift 8))
          (Nat.add shift (byteEntry lowBitTable (Nat.land s 255))))

theorem lowBitK_go_eq :
    ∀ (fuel s shift : Nat), s < fuel →
      lowBitK.go fuel s shift = if s = 0 then 0 else shift + lowBit s
  | fuel + 1, s, shift, h => by
    rw [lowBitK.go, cond_beq]
    rcases Decidable.em (s = 0) with rfl | hs
    · simp
    · rw [ite_eq_right hs, ite_eq_right hs, cond_beq]
      simp only [shiftRight_eq, land_eq, add_eq]
      have h255 : s &&& 255 = s % 256 := Nat.and_two_pow_sub_one_eq_mod s 8
      have hp : (2 : Nat) ^ 8 = 256 := rfl
      rw [h255]
      rcases Decidable.em (s % 256 = 0) with hb | hb
      · rw [ite_eq_left hb]
        have hlt : s >>> 8 < fuel := by
          rw [Nat.shiftRight_eq_div_pow]
          have := Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by decide : 1 < 2 ^ 8)
          omega
        rw [lowBitK_go_eq fuel _ _ hlt, Nat.shiftRight_eq_div_pow, hp]
        have hge : s / 256 ≠ 0 := by
          have : 256 ∣ s := Nat.dvd_of_mod_eq_zero hb
          rcases this with ⟨c, rfl⟩
          simp only [Nat.mul_div_cancel_left _ (by omega : 0 < 256)]
          omega
        have hsplit : lowBit s = 8 + lowBit (s / 256) := by
          rw [lowBit_shift_pow 8 hs (by rw [hp]; exact hb), hp]
        rw [ite_eq_right hge, hsplit]
        omega
      · rw [ite_eq_right hb, lowBitTable_spec _ (Nat.mod_lt _ (by omega))]
        have := lowBit_mod_pow 8 (s := s) (by rw [hp]; exact hb)
        rw [hp] at this
        rw [← this]

theorem lowBitK_eq (s : Nat) : lowBitK s = lowBit s := by
  rw [lowBitK, lowBitK_go_eq (s + 1) s 0 (Nat.lt_succ_self s)]
  rcases Decidable.em (s = 0) with rfl | hs
  · simp
  · rw [ite_eq_right hs, Nat.zero_add]

/-- `nextElem`, raw. -/
@[expose] def nextElemK (s : Nat) (pos : Option Nat) : Option Nat :=
  let s' :=
    match pos with
    | none => s
    | some p => Nat.shiftLeft (Nat.shiftRight s (Nat.add p 1)) (Nat.add p 1)
  cond (Nat.beq s' 0) none (some (lowBitK s'))

theorem nextElemK_eq (s : Nat) (pos : Option Nat) :
    nextElemK s pos = nextElem s pos := by
  unfold nextElemK nextElem
  cases pos <;> simp only [cond_beq, lowBitK_eq, shiftLeft_eq, shiftRight_eq,
    add_eq]

/-! # Packed vectors

A list of naturals below `2 ^ w` is one number whose field `i` holds
the `i`-th entry in bits `[w * i, w * (i + 1))`. -/

/-- The packed number of a list, low field first. -/
@[expose] def pack (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => Nat.add x (Nat.shiftLeft (pack w l) w)

/-- The kernel-facing read of field `i`; `m = 2 ^ w - 1` is the field
mask, passed rather than recomputed. Fields beyond the list read as
`0`, matching `atD`. -/
@[expose] def pget (w m a i : Nat) : Nat :=
  Nat.land (Nat.shiftRight a (Nat.mul w i)) m

/-- The kernel-facing write of field `i` below `len`; a write at or
beyond `len` is the identity, matching `List.set`. -/
@[expose] def pset (w m len a i v : Nat) : Nat :=
  cond (Nat.blt i len)
    (Nat.add
      (Nat.sub a (Nat.shiftLeft (pget w m a i) (Nat.mul w i)))
      (Nat.shiftLeft v (Nat.mul w i)))
    a

/-- Every entry below `2 ^ w`. -/
@[expose] def Small (w : Nat) (l : List Nat) : Prop := ∀ x, x ∈ l → x < 2 ^ w

theorem pack_cons (w x : Nat) (l : List Nat) :
    pack w (x :: l) = x + 2 ^ w * pack w l := by
  rw [pack, add_eq, shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_comm]

theorem pack_lt (w : Nat) : ∀ (l : List Nat), Small w l →
    pack w l < 2 ^ (w * l.length)
  | [], _ => by simp [pack]
  | x :: l, h => by
    rw [pack_cons, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have hx : x < 2 ^ w := h x (List.mem_cons_self ..)
    have hl := pack_lt w l fun y hy => h y (List.mem_cons_of_mem _ hy)
    have : 2 ^ w * pack w l + 2 ^ w ≤ 2 ^ w * 2 ^ (w * l.length) := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hl
    rw [Nat.mul_comm (2 ^ (w * l.length))]
    omega

theorem pack_append (w : Nat) : ∀ (l : List Nat) (v : Nat),
    pack w (l ++ [v]) = pack w l + 2 ^ (w * l.length) * v
  | [], v => by simp [pack, pack_cons]
  | x :: l, v => by
    rw [List.cons_append, pack_cons, pack_cons, pack_append w l v,
      List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_add,
      Nat.add_assoc]
    ac_rfl

theorem pack_replicate (w : Nat) : ∀ (n : Nat),
    pack w (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, pack_cons, pack_replicate w n]; simp

/-- The arithmetic form of a field read. -/
theorem pget_eq (w a i : Nat) :
    pget w (2 ^ w - 1) a i = a / 2 ^ (w * i) % 2 ^ w := by
  rw [pget, land_eq, shiftRight_eq, mul_eq, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

theorem pget_lt (w a i : Nat) : pget w (2 ^ w - 1) a i < 2 ^ w := by
  rw [pget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem pget_pack (w : Nat) : ∀ (l : List Nat) (i : Nat), Small w l →
    pget w (2 ^ w - 1) (pack w l) i = atD l i 0
  | [], i, _ => by
    rw [pget_eq, pack]
    simp [atD]
  | x :: l, 0, h => by
    rw [pget_eq, pack_cons, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h x (List.mem_cons_self ..))]
    rfl
  | x :: l, i + 1, h => by
    have hl : Small w l := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [atD, ← pget_pack w l i hl, pget_eq, pget_eq, pack_cons,
      Nat.mul_succ, Nat.add_comm (w * i) w, Nat.pow_add,
      ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos w),
      Nat.div_eq_of_lt (h x (List.mem_cons_self ..)), Nat.add_zero]

theorem pset_pack (w : Nat) : ∀ (l : List Nat) (i v : Nat), Small w l →
    v < 2 ^ w →
    pset w (2 ^ w - 1) l.length (pack w l) i v = pack w (l.set i v)
  | [], i, v, _, _ => by
    rw [pset, List.length_nil, cond_blt, ite_eq_right (Nat.not_lt_zero i)]
    rfl
  | x :: l, 0, v, h, hv => by
    rw [pset, cond_blt, ite_eq_left (by simp), pget_pack w _ 0 h,
      List.set_cons_zero, pack_cons, pack_cons, atD]
    simp only [mul_eq, shiftLeft_eq, add_eq, sub_eq, Nat.mul_zero,
      Nat.shiftLeft_zero]
    omega
  | x :: l, i + 1, v, h, hv => by
    have hl : Small w l := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.set_cons_succ, pack_cons w x (l.set i v), ← pset_pack w l i v hl hv,
      List.length_cons, pset, pset, cond_blt, cond_blt]
    rcases Decidable.em (i < l.length) with hi | hi
    · rw [ite_eq_left (by omega), ite_eq_left hi]
      have hg : pget w (2 ^ w - 1) (pack w (x :: l)) (i + 1) =
          pget w (2 ^ w - 1) (pack w l) i := by
        rw [pget_pack w _ _ h, pget_pack w l i hl]
        rfl
      rw [hg]
      simp only [shiftLeft_eq, add_eq, sub_eq, mul_eq, Nat.shiftLeft_eq, pack_cons]
      have hle : pget w (2 ^ w - 1) (pack w l) i * 2 ^ (w * i) ≤ pack w l := by
        rw [pget_eq]
        exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _))
          (Nat.div_mul_le_self _ _)
      have hle' : 2 ^ w * (pget w (2 ^ w - 1) (pack w l) i * 2 ^ (w * i)) ≤
          2 ^ w * pack w l := Nat.mul_le_mul_left _ hle
      rw [Nat.mul_succ, Nat.pow_add]
      have e1 : pget w (2 ^ w - 1) (pack w l) i * (2 ^ (w * i) * 2 ^ w) =
          2 ^ w * (pget w (2 ^ w - 1) (pack w l) i * 2 ^ (w * i)) := by ac_rfl
      have e2 : v * (2 ^ (w * i) * 2 ^ w) = 2 ^ w * (v * 2 ^ (w * i)) := by ac_rfl
      rw [e1, e2, Nat.mul_add, Nat.mul_sub]
      omega
    · rw [ite_eq_right (by omega), ite_eq_right hi]
      exact pack_cons w x l

theorem pack_injective (w : Nat) : ∀ (l₁ l₂ : List Nat), Small w l₁ → Small w l₂ →
    l₁.length = l₂.length → pack w l₁ = pack w l₂ → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | x :: l₁, y :: l₂, h₁, h₂, hlen, heq => by
    rw [pack_cons, pack_cons] at heq
    have hx : x = y := by
      have := congrArg (· % 2 ^ w) heq
      simp only [Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (h₁ x (List.mem_cons_self ..)),
        Nat.mod_eq_of_lt (h₂ y (List.mem_cons_self ..))] at this
      exact this
    subst hx
    have hp : pack w l₁ = pack w l₂ :=
      Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos w) (Nat.add_left_cancel heq)
    rw [pack_injective w l₁ l₂ (fun z hz => h₁ z (List.mem_cons_of_mem _ hz))
      (fun z hz => h₂ z (List.mem_cons_of_mem _ hz)) (by simpa using hlen) hp]

theorem Small.set {w : Nat} {l : List Nat} (h : Small w l) {v : Nat}
    (hv : v < 2 ^ w) (i : Nat) : Small w (l.set i v) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h x hx
  · exact hv

theorem Small.append {w : Nat} {l : List Nat} (h : Small w l) {v : Nat}
    (hv : v < 2 ^ w) : Small w (l ++ [v]) := by
  intro x hx
  rw [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h x hx
  · exact hv

theorem Small.replicate (w n : Nat) : Small w (List.replicate n 0) := by
  intro x hx
  rw [List.mem_replicate] at hx
  rw [hx.2]
  exact Nat.two_pow_pos w

theorem Small.nil (w : Nat) : Small w [] := fun _ h => absurd h (List.not_mem_nil)

theorem Small.atD {w : Nat} : ∀ {l : List Nat}, Small w l → ∀ (i : Nat),
    atD l i 0 < 2 ^ w
  | [], _, i => by
    rw [Hex.GraphIso.atD]
    exact Nat.two_pow_pos w
  | x :: _, h, 0 => h x (List.mem_cons_self ..)
  | _ :: l, h, i + 1 => Small.atD (fun y hy => h y (List.mem_cons_of_mem _ hy)) i

/-- The correspondence between a packed number and a list of `n`
entries below `2 ^ w`. -/
structure Rep (w n a : Nat) (l : List Nat) : Prop where
  len : l.length = n
  small : Small w l
  eq : a = pack w l

theorem Rep.get {w n a : Nat} {l : List Nat} (h : Rep w n a l) (i : Nat) :
    pget w (2 ^ w - 1) a i = atD l i 0 := by
  rw [h.eq, pget_pack w l i h.small]

theorem Rep.get_lt {w n a : Nat} {l : List Nat} (_ : Rep w n a l) (i : Nat) :
    pget w (2 ^ w - 1) a i < 2 ^ w := pget_lt w a i

theorem Rep.set {w n a : Nat} {l : List Nat} (h : Rep w n a l) (i : Nat)
    {v : Nat} (hv : v < 2 ^ w) :
    Rep w n (pset w (2 ^ w - 1) n a i v) (l.set i v) where
  len := by rw [List.length_set, h.len]
  small := h.small.set hv i
  eq := by rw [h.eq, ← h.len, pset_pack w l i v h.small hv]

theorem Rep.push {w n a : Nat} {l : List Nat} (h : Rep w n a l) {v : Nat}
    (hv : v < 2 ^ w) :
    Rep w (n + 1) (Nat.add a (Nat.shiftLeft v (Nat.mul w n))) (l ++ [v]) where
  len := by rw [List.length_append, List.length_singleton, h.len]
  small := h.small.append hv
  eq := by
    rw [h.eq, pack_append, add_eq, shiftLeft_eq, mul_eq, Nat.shiftLeft_eq,
      h.len, Nat.mul_comm v]

theorem Rep.nil (w : Nat) : Rep w 0 0 [] where
  len := rfl
  small := Small.nil w
  eq := rfl

theorem Rep.replicate (w n : Nat) : Rep w n 0 (List.replicate n 0) where
  len := List.length_replicate
  small := Small.replicate w n
  eq := (pack_replicate w n).symm

theorem Rep.ofList {w : Nat} {l : List Nat} (h : Small w l) :
    Rep w l.length (pack w l) l where
  len := rfl
  small := h
  eq := rfl

end Hex.GraphIso.Nauty
