import HexArith.ExtGcd
import HexArith.Nat.ModArith
import HexArith.UInt64.Wide

/-!
Core `ZMod64` definitions for `hex-mod-arith`.

This module introduces the `UInt64`-backed residue type `Hex.ZMod64 p`
together with a project-local modulus-bounds typeclass, smart construction by
reduction mod `p`, the initial additive and multiplicative API, executable
exponentiation and inversion helpers, and the default extern-backed
multiplication contract.
-/
namespace Hex

namespace ZMod64

/-- `ZMod64 p` is only valid when `p` is positive and fits in one machine word. -/
class Bounds (p : Nat) : Prop where
  pPos : 0 < p
  pLeR : p ≤ UInt64.word

end ZMod64

/-- Residues mod `p` stored in a single machine word, with a proof of reduction. -/
structure ZMod64 (p : Nat) [ZMod64.Bounds p] where
  val : UInt64
  isLt : val.toNat < p

namespace ZMod64

variable {p : Nat} [Bounds p]

/-- View a residue as its reduced Nat representative. -/
def toNat (a : ZMod64 p) : Nat :=
  a.val.toNat

/-- View a residue as its underlying `UInt64` word. -/
def toUInt64 (a : ZMod64 p) : UInt64 :=
  a.val

instance : CoeOut (ZMod64 p) UInt64 where
  coe := toUInt64

instance : CoeOut (ZMod64 p) Nat where
  coe := toNat

/-- Converting a residue to `UInt64` exposes exactly the stored word. -/
@[simp, grind =] theorem toUInt64_eq_val (a : ZMod64 p) : a.toUInt64 = a.val := rfl

/-- Converting a residue to `Nat` reads the stored word as its canonical representative. -/
@[simp, grind =] theorem toNat_eq_val (a : ZMod64 p) : a.toNat = a.val.toNat := rfl

/-- The Nat view of a residue is always the canonical representative below the modulus. -/
@[simp] theorem toNat_lt (a : ZMod64 p) : a.toNat < p := a.isLt

/-- Extensionality for residues via equality of their stored machine words. -/
@[ext] theorem ext {a b : ZMod64 p} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Extensionality for residues via their canonical Nat representatives. -/
@[grind .]
theorem ext_toNat {a b : ZMod64 p} (h : a.toNat = b.toNat) : a = b :=
  ext (UInt64.toNat_inj.mp h)

/-- Reduce a Nat representative modulo `p`. -/
def normalize (p n : Nat) : Nat :=
  n % p

/-- Normalization always returns a canonical representative below the modulus. -/
theorem normalize_lt (p n : Nat) [Bounds p] : normalize p n < p :=
  Nat.mod_lt _ (Bounds.pPos (p := p))

/-- Normalizing an already canonical representative leaves it unchanged. -/
@[simp, grind =] theorem normalize_of_lt {q n : Nat} (hn : n < q) : normalize q n = n := by
  rw [normalize, Nat.mod_eq_of_lt hn]

/-- Normalizing a residue's canonical representative leaves it unchanged. -/
@[simp, grind =] theorem normalize_toNat (a : ZMod64 p) : normalize p a.toNat = a.toNat :=
  normalize_of_lt a.toNat_lt

/--
Build a reduced residue by taking the Nat representative mod `p`.

The bound `p ≤ 2^64` ensures the reduced representative is stored faithfully in
the backing `UInt64`.
-/
def ofNat (p n : Nat) [Bounds p] : ZMod64 p := by
  let reduced := normalize p n
  have hred : reduced < p := normalize_lt p n
  have hword : reduced < UInt64.word := Nat.lt_of_lt_of_le hred (Bounds.pLeR (p := p))
  refine ⟨UInt64.ofNatLT reduced hword, ?_⟩
  simpa [reduced, UInt64.toNat_ofNatLT] using hred

/-- The Nat representative of `ofNat p n` is `n` reduced modulo `p`. -/
@[simp, grind =] theorem toNat_ofNat (n : Nat) : (ofNat p n).toNat = n % p := by
  have hred : n % p < p := Nat.mod_lt _ (Bounds.pPos (p := p))
  have hword : n % p < UInt64.word := Nat.lt_of_lt_of_le hred (Bounds.pLeR (p := p))
  simp [ofNat, normalize, UInt64.toNat_ofNatLT]

/-- The stored word of `ofNat p n`, viewed as a Nat, is `n` reduced modulo `p`. -/
@[simp, grind =] theorem val_toNat_ofNat (n : Nat) : (ofNat p n).val.toNat = n % p := by
  simpa using toNat_ofNat (p := p) n

/-- Constructing a residue from its canonical representative is the identity. -/
@[simp, grind =] theorem ofNat_toNat (a : ZMod64 p) : ofNat p a.toNat = a := by
  apply ext
  apply UInt64.toNat_inj.mp
  rw [val_toNat_ofNat]
  exact Nat.mod_eq_of_lt a.toNat_lt

/-- Two residues are equal exactly when their canonical representatives agree. -/
@[grind ←]
theorem eq_iff_toNat_eq (a b : ZMod64 p) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, ext_toNat⟩

/-- A reduced representative constructs the same residue as the original representative. -/
@[simp, grind =] theorem ofNat_mod (n : Nat) : ofNat p (n % p) = ofNat p n := by
  rw [eq_iff_toNat_eq, toNat_ofNat, toNat_ofNat, Nat.mod_mod]

/-- Normalizing before constructing a residue does not change the residue. -/
@[simp, grind =] theorem ofNat_normalize (n : Nat) : ofNat p (normalize p n) = ofNat p n := by
  simp [normalize]

/-- Characterise when an arbitrary representative builds a given residue. -/
@[grind ←]
theorem ofNat_eq_iff_toNat_eq (n : Nat) (a : ZMod64 p) :
    ofNat p n = a ↔ n % p = a.toNat := by
  rw [eq_iff_toNat_eq, toNat_ofNat]

/-- Characterise when a residue is built from an arbitrary representative. -/
@[grind ←]
theorem eq_ofNat_iff_toNat_eq (a : ZMod64 p) (n : Nat) :
    a = ofNat p n ↔ a.toNat = n % p := by
  rw [eq_iff_toNat_eq, toNat_ofNat]

/-- Equality of residues built from arbitrary Nat representatives is equality modulo `p`. -/
@[grind ←]
theorem ofNat_eq_ofNat_iff_mod_eq (x y : Nat) :
    ofNat p x = ofNat p y ↔ x % p = y % p := by
  rw [eq_iff_toNat_eq, toNat_ofNat, toNat_ofNat]

/-- All canonical residues modulo `p`, listed in representative order. -/
def values (p : Nat) [Bounds p] : List (ZMod64 p) :=
  (List.range p).map fun n => ofNat p n

/-- The canonical list of residues modulo `p` has one entry for each representative. -/
@[simp, grind =] theorem values_length : (values p).length = p := by
  simp [values]

/-- Every residue appears in `values`. -/
theorem mem_values (a : ZMod64 p) : a ∈ values p := by
  unfold values
  apply List.mem_map.mpr
  refine ⟨a.toNat, List.mem_range.mpr a.toNat_lt, ?_⟩
  apply ext
  apply UInt64.toNat_inj.mp
  rw [val_toNat_ofNat]
  exact (Nat.mod_eq_of_lt a.toNat_lt).trans (by rfl)

/-- Membership in the canonical residue list is automatic for every residue. -/
@[simp, grind =] theorem mem_values_iff (a : ZMod64 p) : a ∈ values p ↔ True :=
  iff_true_intro (mem_values a)

/-- Reduced representatives below `p` construct the same residue exactly when
the representatives are equal. -/
theorem ofNat_eq_ofNat_iff_of_lt {x y : Nat} (hx : x < p) (hy : y < p) :
    ofNat p x = ofNat p y ↔ x = y := by
  constructor
  · intro h
    have hnat := congrArg ZMod64.toNat h
    rw [toNat_ofNat, toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hnat
    exact hnat
  · intro h
    subst y
    rfl

private theorem nodup_map_of_injective_on
    {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hxy' : x = y := hinj x (by simp) y (by simp [hy]) hxy.symm
        exact hxs.1 (hxy' ▸ hy)
      · apply ih hxs.2
        intro a ha b hb hab
        exact hinj a (by simp [ha]) b (by simp [hb]) hab

/-- The canonical residue list has no duplicate entries. -/
@[grind .]
theorem values_nodup : (values p).Nodup := by
  unfold values
  apply nodup_map_of_injective_on (List.nodup_range : (List.range p).Nodup)
  intro x hx y hy hxy
  exact
    (ofNat_eq_ofNat_iff_of_lt
      (List.mem_range.mp hx) (List.mem_range.mp hy)).mp hxy

/-- The zero residue class. -/
protected def zero : ZMod64 p :=
  ofNat p 0

/-- The residue class of one. -/
protected def one : ZMod64 p :=
  ofNat p 1

/-- The modulus as a `UInt64` word when `p < 2^64`. -/
def modulusWord (p : Nat) (hp : p < UInt64.word) : UInt64 :=
  UInt64.ofNatLT p hp

/-- The correction word `2^64 - p` used when `p < 2^64`. -/
def complementWord (p : Nat) [Bounds p] (_hp : p < UInt64.word) : UInt64 :=
  UInt64.ofNatLT (UInt64.word - p) <| by
    exact Nat.sub_lt (by decide : 0 < 2 ^ 64) (Bounds.pPos (p := p))

/-- Carry branch of `add`: when the unreduced sum `a.toNat + b.toNat`
reaches the word size `2^64` (`hcarry`), the wrapped machine sum plus
the complement word `2^64 - p` has representative `a.toNat + b.toNat - p`.
Requires `p < 2^64` (`hpLt`) for the complement word to exist. -/
private theorem add_carry_toNat (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hcarry : UInt64.word ≤ a.toNat + b.toNat) :
    ((a.val + b.val) + complementWord p hpLt).toNat = a.toNat + b.toNat - p := by
  have ha : a.toNat < p := a.isLt
  have hb : b.toNat < p := b.isLt
  have hpLe : p ≤ UInt64.word := Bounds.pLeR (p := p)
  have hsum_lt : a.toNat + b.toNat - UInt64.word < UInt64.word := by omega
  have hsum_toNat : (a.val + b.val).toNat = a.toNat + b.toNat - UInt64.word := by
    rw [UInt64.toNat_add]
    simpa [toNat_eq_val, UInt64.word] using
      (by rw [Nat.mod_eq_sub_mod hcarry, Nat.mod_eq_of_lt hsum_lt] :
        (a.toNat + b.toNat) % UInt64.word = a.toNat + b.toNat - UInt64.word)
  have hcorr_lt : (a.toNat + b.toNat - UInt64.word) + (UInt64.word - p) < UInt64.word := by
    omega
  rw [UInt64.toNat_add, hsum_toNat]
  simp [complementWord, UInt64.toNat_ofNatLT]
  rw [Nat.mod_eq_of_lt (by simpa [toNat_eq_val, UInt64.word] using hcorr_lt)]
  have hfinal :
      (a.toNat + b.toNat - UInt64.word) + (UInt64.word - p) =
        a.toNat + b.toNat - p := by
    omega
  simpa [toNat_eq_val] using hfinal

/-- Carry branch of `add`: the corrected representative `a.toNat + b.toNat - p`
stays in canonical range `< p`, so the result is a valid `ZMod64 p`. -/
private theorem add_carry_lt (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hcarry : UInt64.word ≤ a.toNat + b.toNat) :
    ((a.val + b.val) + complementWord p hpLt).toNat < p := by
  rw [add_carry_toNat a b hcarry]
  have ha : a.toNat < p := a.isLt
  have hb : b.toNat < p := b.isLt
  omega

/-- No-carry-with-reduce branch of `add`: the unreduced sum fits in a
word (`hcarry`) but is at least the modulus (`hreduce`), so subtracting
the modulus word `p` gives the representative `a.toNat + b.toNat - p`.
Requires `p < 2^64` (`hpLt`) for the modulus word to exist. -/
private theorem add_noCarry_reduce_toNat (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hcarry : ¬ UInt64.word ≤ a.toNat + b.toNat)
    (hreduce : modulusWord p hpLt ≤ a.val + b.val) :
    ((a.val + b.val) - modulusWord p hpLt).toNat = a.toNat + b.toNat - p := by
  have hsum_lt : a.toNat + b.toNat < UInt64.word := by omega
  have hsum_toNat : (a.val + b.val).toNat = a.toNat + b.toNat := by
    rw [UInt64.toNat_add]
    simpa [toNat_eq_val, UInt64.word] using
      (by rw [Nat.mod_eq_of_lt hsum_lt] :
        (a.toNat + b.toNat) % UInt64.word = a.toNat + b.toNat)
  have hreduceNat : p ≤ a.toNat + b.toNat := by
    have := UInt64.le_iff_toNat_le.mp hreduce
    simpa [hsum_toNat, modulusWord, UInt64.toNat_ofNatLT] using this
  have hge : UInt64.word ≤ UInt64.word - p + (a.toNat + b.toNat) := by omega
  have hlt : UInt64.word - p + (a.toNat + b.toNat) - UInt64.word < UInt64.word := by
    omega
  rw [UInt64.toNat_sub, hsum_toNat]
  simp [modulusWord, UInt64.toNat_ofNatLT]
  rw [Nat.mod_eq_sub_mod (by simpa [toNat_eq_val, UInt64.word] using hge),
    Nat.mod_eq_of_lt (by simpa [toNat_eq_val, UInt64.word] using hlt)]
  have hfinal :
      UInt64.word - p + (a.toNat + b.toNat) - UInt64.word =
        a.toNat + b.toNat - p := by
    omega
  simpa [toNat_eq_val] using hfinal

/-- No-carry-with-reduce branch of `add`: the reduced representative
`a.toNat + b.toNat - p` stays in canonical range `< p`. -/
private theorem add_noCarry_reduce_lt (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hcarry : ¬ UInt64.word ≤ a.toNat + b.toNat)
    (hreduce : modulusWord p hpLt ≤ a.val + b.val) :
    ((a.val + b.val) - modulusWord p hpLt).toNat < p := by
  rw [add_noCarry_reduce_toNat a b hcarry hreduce]
  have ha : a.toNat < p := a.isLt
  have hb : b.toNat < p := b.isLt
  omega

/-- No-carry, no-reduce branch of `add`: the unreduced sum fits in a word
(`hcarry`) and is already below the modulus (`_hreduce`), so its `toNat`
is exactly `a.toNat + b.toNat` with no correction applied. -/
private theorem add_noCarry_noReduce_toNat (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hcarry : ¬ UInt64.word ≤ a.toNat + b.toNat)
    (_hreduce : ¬ modulusWord p hpLt ≤ a.val + b.val) :
    (a.val + b.val).toNat = a.toNat + b.toNat := by
  have hsum_lt : a.toNat + b.toNat < UInt64.word := by omega
  rw [UInt64.toNat_add]
  simpa [toNat_eq_val, UInt64.word] using
    (by rw [Nat.mod_eq_of_lt hsum_lt] :
      (a.toNat + b.toNat) % UInt64.word = a.toNat + b.toNat)

/-- No-carry, no-reduce branch of `add`: the uncorrected sum is already
in canonical range `< p`. -/
private theorem add_noCarry_noReduce_lt (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hcarry : ¬ UInt64.word ≤ a.toNat + b.toNat)
    (hreduce : ¬ modulusWord p hpLt ≤ a.val + b.val) :
    (a.val + b.val).toNat < p := by
  have hsum_toNat := add_noCarry_noReduce_toNat a b hcarry hreduce
  have hreduceNat : ¬ p ≤ a.toNat + b.toNat := by
    intro hpSum
    apply hreduce
    apply UInt64.le_iff_toNat_le.mpr
    simpa [hsum_toNat, modulusWord, UInt64.toNat_ofNatLT] using hpSum
  omega

/-- No-borrow branch of `sub`: when `b.val ≤ a.val` (`hba`) the
machine-word difference does not wrap, so its `toNat` is exactly
`a.toNat - b.toNat`. -/
private theorem sub_noBorrow_toNat (a b : ZMod64 p)
    (hba : b.val ≤ a.val) :
    (a.val - b.val).toNat = a.toNat - b.toNat := by
  have hbaNat : b.toNat ≤ a.toNat := by
    simpa [toNat_eq_val] using UInt64.le_iff_toNat_le.mp hba
  have hge : UInt64.word ≤ UInt64.word - b.toNat + a.toNat := by omega
  have hlt : UInt64.word - b.toNat + a.toNat - UInt64.word < UInt64.word := by
    have haWord : a.toNat < UInt64.word := by
      simpa [toNat_eq_val, UInt64.word, UInt64.size] using UInt64.toNat_lt_size a.val
    omega
  rw [UInt64.toNat_sub]
  rw [Nat.mod_eq_sub_mod (by simpa [toNat_eq_val, UInt64.word] using hge),
    Nat.mod_eq_of_lt (by simpa [toNat_eq_val, UInt64.word] using hlt)]
  have hbWord : b.toNat ≤ UInt64.word := by
    have hbSize : b.toNat < UInt64.word := by
      simpa [toNat_eq_val, UInt64.word, UInt64.size] using UInt64.toNat_lt_size b.val
    exact Nat.le_of_lt hbSize
  have hsum :
      UInt64.word - b.toNat + a.toNat = UInt64.word + (a.toNat - b.toNat) := by
    rw [← Nat.sub_add_comm hbWord, Nat.add_sub_assoc hbaNat]
  have hfinal : UInt64.word - b.toNat + a.toNat - UInt64.word = a.toNat - b.toNat := by
    rw [hsum, Nat.add_sub_cancel_left]
  simpa [toNat_eq_val] using hfinal

/-- No-borrow branch of `sub`: the difference `a.toNat - b.toNat` is
bounded by `a.toNat < p`, so it stays in canonical range `< p`. -/
private theorem sub_noBorrow_lt (a b : ZMod64 p)
    (hba : b.val ≤ a.val) :
    (a.val - b.val).toNat < p := by
  rw [sub_noBorrow_toNat a b hba]
  have ha : a.toNat < p := a.isLt
  omega

/-- Borrow branch of `sub`: when `b.val > a.val` (`hba`) the machine-word
difference wraps; subtracting the complement word `2^64 - p` and wrapping
again recovers the representative `p - b.toNat + a.toNat`. Requires
`p < 2^64` (`hpLt`) for the complement word to exist. -/
private theorem sub_borrow_toNat (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hba : ¬ b.val ≤ a.val) :
    ((a.val - b.val) - complementWord p hpLt).toNat = p - b.toNat + a.toNat := by
  have hbaNat : ¬ b.toNat ≤ a.toNat := by
    intro h
    apply hba
    apply UInt64.le_iff_toNat_le.mpr
    simpa [toNat_eq_val] using h
  have hbLe : b.toNat ≤ p := Nat.le_of_lt b.isLt
  have hdiff_lt : UInt64.word - b.toNat + a.toNat < UInt64.word := by
    have : a.toNat < b.toNat := by omega
    omega
  have hdiff_toNat : (a.val - b.val).toNat = UInt64.word - b.toNat + a.toNat := by
    rw [UInt64.toNat_sub]
    simpa [toNat_eq_val, UInt64.word] using
      (by rw [Nat.mod_eq_of_lt hdiff_lt] :
        (UInt64.word - b.toNat + a.toNat) % UInt64.word =
          UInt64.word - b.toNat + a.toNat)
  have hge :
      UInt64.word ≤ UInt64.word - (UInt64.word - p) + (UInt64.word - b.toNat + a.toNat) := by
    omega
  have hlt :
      UInt64.word - (UInt64.word - p) + (UInt64.word - b.toNat + a.toNat) -
          UInt64.word < UInt64.word := by
    have ha : a.toNat < p := a.isLt
    omega
  rw [UInt64.toNat_sub, hdiff_toNat]
  simp [complementWord, UInt64.toNat_ofNatLT]
  rw [Nat.mod_eq_sub_mod (by simpa [toNat_eq_val, UInt64.word] using hge),
    Nat.mod_eq_of_lt (by simpa [toNat_eq_val, UInt64.word] using hlt)]
  have hfinal :
      UInt64.word - (UInt64.word - p) + (UInt64.word - b.toNat + a.toNat) -
          UInt64.word =
        p - b.toNat + a.toNat := by
    omega
  simpa [toNat_eq_val] using hfinal

/-- Borrow branch of `sub`: the corrected representative
`p - b.toNat + a.toNat` stays in canonical range `< p`, since the borrow
hypothesis forces `a.toNat < b.toNat`. -/
private theorem sub_borrow_lt (a b : ZMod64 p) {hpLt : p < UInt64.word}
    (hba : ¬ b.val ≤ a.val) :
    ((a.val - b.val) - complementWord p hpLt).toNat < p := by
  rw [sub_borrow_toNat a b hba]
  have ha : a.toNat < p := a.isLt
  have hbaNat : ¬ b.toNat ≤ a.toNat := by
    intro h
    apply hba
    apply UInt64.le_iff_toNat_le.mpr
    simpa [toNat_eq_val] using h
  omega

/--
Add two reduced residues using wrapped machine-word addition plus one
correction step when `p < 2^64`.
-/
def add (a b : ZMod64 p) : ZMod64 p := by
  by_cases hp : p = UInt64.word
  · refine ⟨a.val + b.val, ?_⟩
    simpa [hp] using (UInt64.toNat_lt_size (a.val + b.val))
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    let p64 := modulusWord p hpLt
    let c64 := complementWord p hpLt
    let sum := a.val + b.val
    by_cases hcarry : UInt64.word ≤ a.toNat + b.toNat
    · exact ⟨sum + c64, by simpa [sum, c64] using add_carry_lt a b hcarry⟩
    · by_cases hreduce : p64 ≤ sum
      · exact ⟨sum - p64, by simpa [sum, p64] using add_noCarry_reduce_lt a b hcarry hreduce⟩
      · exact ⟨sum, by simpa [sum] using add_noCarry_noReduce_lt a b hcarry hreduce⟩

/--
Subtract two residues by adding the modular complement of the second and
reducing mod `p`.
-/
def sub (a b : ZMod64 p) : ZMod64 p := by
  by_cases hp : p = UInt64.word
  · refine ⟨a.val - b.val, ?_⟩
    simpa [hp] using (UInt64.toNat_lt_size (a.val - b.val))
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    let c64 := complementWord p hpLt
    let diff := a.val - b.val
    by_cases hba : b.val ≤ a.val
    · exact ⟨diff, by simpa [diff] using sub_noBorrow_lt a b hba⟩
    · exact ⟨diff - c64, by simpa [diff, c64] using sub_borrow_lt a b hba⟩

/--
Multiply two reduced residues and reduce the product mod `p`.

The trusted runtime contract is the `lean_hex_zmod64_mul` extern, whose C body
must agree with this pure Lean fallback.
-/
@[extern "lean_hex_zmod64_mul"]
def mul (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat * b.toNat)

/--
Raise a residue to a natural power using exponentiation by squaring.

The accumulator form keeps the executable path close to the intended downstream
runtime usage while preserving a simple semantic contract.
-/
@[extern "lean_hex_zmod64_pow"]
def pow (a : ZMod64 p) (n : Nat) : ZMod64 p :=
  let rec go (base acc : ZMod64 p) (k : Nat) : ZMod64 p :=
    match k with
    | 0 => acc
    | m + 1 =>
        let acc' := if (m + 1) % 2 = 0 then acc else mul acc base
        go (mul base base) acc' ((m + 1) / 2)
  termination_by k
  decreasing_by
    simpa using Nat.div_lt_self (Nat.succ_pos m) (by decide : 1 < 2)
  go a ZMod64.one n

/--
Compute a modular inverse candidate via the integer extended-GCD helper from
`hex-arith`.

When `a` is coprime to `p`, this is the canonical inverse mod `p`; otherwise it
still exposes the executable Bezout-derived residue needed by later algebraic
layers.
-/
def inv (a : ZMod64 p) : ZMod64 p :=
  let (_, s, _) := HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat p)
  ofNat p (Int.toNat (s % Int.ofNat p))

instance : Zero (ZMod64 p) where
  zero := ZMod64.zero

instance : One (ZMod64 p) where
  one := ZMod64.one

instance : Add (ZMod64 p) where
  add := ZMod64.add

instance : Sub (ZMod64 p) where
  sub := ZMod64.sub

instance : Mul (ZMod64 p) where
  mul := ZMod64.mul

instance : Pow (ZMod64 p) Nat where
  pow := ZMod64.pow

instance : Inv (ZMod64 p) where
  inv := ZMod64.inv

/-- The canonical representative of the zero residue is `0`. -/
@[simp, grind =] theorem toNat_zero : (ZMod64.zero : ZMod64 p).toNat = 0 := by
  rw [ZMod64.zero, toNat_ofNat]
  exact Nat.zero_mod _

/-- The canonical representative of the one residue is `1 % p`. -/
@[simp, grind =] theorem toNat_one : (ZMod64.one : ZMod64 p).toNat = 1 % p := by
  rw [ZMod64.one, toNat_ofNat]

/-- Addition agrees with addition of canonical representatives modulo `p`. -/
@[simp, grind =] theorem toNat_add (a b : ZMod64 p) :
    (add a b).toNat = (a.toNat + b.toNat) % p := by
  unfold add
  by_cases hp : p = UInt64.word
  · rw [dif_pos hp]
    simp [toNat_eq_val, UInt64.toNat_add, hp, UInt64.word]
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    rw [dif_neg hp]
    by_cases hcarry : UInt64.word ≤ a.toNat + b.toNat
    · rw [dif_pos hcarry]
      change ((a.val + b.val) + complementWord p hpLt).toNat = (a.toNat + b.toNat) % p
      rw [add_carry_toNat a b hcarry]
      have ha : a.toNat < p := a.isLt
      have hb : b.toNat < p := b.isLt
      have hpSum : p ≤ a.toNat + b.toNat := by omega
      have hlt : a.toNat + b.toNat - p < p := by omega
      rw [Nat.mod_eq_sub_mod hpSum, Nat.mod_eq_of_lt hlt]
    · rw [dif_neg hcarry]
      let p64 := modulusWord p hpLt
      let sum := a.val + b.val
      by_cases hreduce : p64 ≤ sum
      · rw [dif_pos hreduce]
        change ((a.val + b.val) - modulusWord p hpLt).toNat = (a.toNat + b.toNat) % p
        rw [add_noCarry_reduce_toNat a b hcarry hreduce]
        have ha : a.toNat < p := a.isLt
        have hb : b.toNat < p := b.isLt
        have hsum_lt : a.toNat + b.toNat < UInt64.word := by omega
        have hsum_toNat : (a.val + b.val).toNat = a.toNat + b.toNat := by
          rw [UInt64.toNat_add]
          simpa [toNat_eq_val, UInt64.word] using
            (by rw [Nat.mod_eq_of_lt hsum_lt] :
              (a.toNat + b.toNat) % UInt64.word = a.toNat + b.toNat)
        have hreduceNat : p ≤ a.toNat + b.toNat := by
          have := UInt64.le_iff_toNat_le.mp hreduce
          simpa [p64, sum, hsum_toNat, modulusWord, UInt64.toNat_ofNatLT] using this
        have hlt : a.toNat + b.toNat - p < p := by omega
        rw [Nat.mod_eq_sub_mod hreduceNat, Nat.mod_eq_of_lt hlt]
      · rw [dif_neg hreduce]
        change (a.val + b.val).toNat = (a.toNat + b.toNat) % p
        rw [add_noCarry_noReduce_toNat a b hcarry hreduce]
        have hnot : ¬ p ≤ a.toNat + b.toNat := by
          intro hpSum
          apply hreduce
          apply UInt64.le_iff_toNat_le.mpr
          have hsum_toNat := add_noCarry_noReduce_toNat (p := p) a b hcarry hreduce
          change (modulusWord p hpLt).toNat ≤ (a.val + b.val).toNat
          simpa [modulusWord, UInt64.toNat_ofNatLT, hsum_toNat] using hpSum
        rw [Nat.mod_eq_of_lt (by omega)]

/-- Addition is the residue built from the sum of canonical representatives. -/
theorem add_eq_ofNat (a b : ZMod64 p) :
    add a b = ofNat p (a.toNat + b.toNat) := by
  rw [eq_iff_toNat_eq, toNat_add, toNat_ofNat]

/-- Operator-level form of `add_eq_ofNat`. -/
theorem add_op_eq_ofNat (a b : ZMod64 p) :
    a + b = ofNat p (a.toNat + b.toNat) := by
  simpa using add_eq_ofNat a b

/-- Subtraction agrees with modular subtraction of canonical representatives. -/
@[simp, grind =] theorem toNat_sub (a b : ZMod64 p) :
    (sub a b).toNat = (a.toNat + (p - b.toNat)) % p := by
  unfold sub
  by_cases hp : p = UInt64.word
  · rw [dif_pos hp]
    change (a.val - b.val).toNat = (a.toNat + (p - b.toNat)) % p
    rw [UInt64.toNat_sub]
    simp [toNat_eq_val, hp, UInt64.word, Nat.add_comm]
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    rw [dif_neg hp]
    let c64 := complementWord p hpLt
    let diff := a.val - b.val
    by_cases hba : b.val ≤ a.val
    · rw [dif_pos hba]
      change (a.val - b.val).toNat = (a.toNat + (p - b.toNat)) % p
      rw [sub_noBorrow_toNat a b hba]
      have hbaNat : b.toNat ≤ a.toNat := by
        simpa [toNat_eq_val] using UInt64.le_iff_toNat_le.mp hba
      have hbLe : b.toNat ≤ p := Nat.le_of_lt b.isLt
      have ha : a.toNat < p := a.isLt
      have hge : p ≤ a.toNat + (p - b.toNat) := by omega
      have hlt : a.toNat + (p - b.toNat) - p < p := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
      omega
    · rw [dif_neg hba]
      change ((a.val - b.val) - complementWord p hpLt).toNat =
        (a.toNat + (p - b.toNat)) % p
      rw [sub_borrow_toNat a b hba]
      have hbaNat : ¬ b.toNat ≤ a.toNat := by
        intro h
        apply hba
        apply UInt64.le_iff_toNat_le.mpr
        simpa [toNat_eq_val] using h
      have hbLe : b.toNat ≤ p := Nat.le_of_lt b.isLt
      have ha : a.toNat < p := a.isLt
      have hlt : a.toNat + (p - b.toNat) < p := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega

/-- Subtraction is the residue built from the modular difference of representatives. -/
theorem sub_eq_ofNat (a b : ZMod64 p) :
    sub a b = ofNat p (a.toNat + (p - b.toNat)) := by
  rw [eq_iff_toNat_eq, toNat_sub, toNat_ofNat]

/-- Operator-level form of `sub_eq_ofNat`. -/
theorem sub_op_eq_ofNat (a b : ZMod64 p) :
    a - b = ofNat p (a.toNat + (p - b.toNat)) := by
  simpa using sub_eq_ofNat a b

/-- Multiplication agrees with multiplication of canonical representatives modulo `p`. -/
@[simp, grind =] theorem toNat_mul (a b : ZMod64 p) :
    (mul a b).toNat = (a.toNat * b.toNat) % p := by
  rw [mul, toNat_ofNat]

/-- Multiplication is the residue built from the product of canonical representatives. -/
theorem mul_eq_ofNat (a b : ZMod64 p) :
    mul a b = ofNat p (a.toNat * b.toNat) := by
  rw [eq_iff_toNat_eq, toNat_mul, toNat_ofNat]

/-- Operator-level form of `mul_eq_ofNat`. -/
theorem mul_op_eq_ofNat (a b : ZMod64 p) :
    a * b = ofNat p (a.toNat * b.toNat) := by
  simpa using mul_eq_ofNat a b

/--
Definition-level representative equation for the extended-GCD inverse candidate.

Most callers should prefer `inv_mul_eq_one_of_coprime`; this lemma exposes the
exact executable residue produced by `inv`. It is intentionally not tagged as a
default simplification rule, since unfolding `inv` exposes the extended-GCD
implementation body.
-/
theorem toNat_inv_def (a : ZMod64 p) :
    (inv a).toNat =
      (Int.toNat ((let (_, s, _) := HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat p); s)
        % Int.ofNat p)) % p := by
  rw [inv, toNat_ofNat]

/-- Inversion is the residue built from the extended-GCD inverse representative. -/
theorem inv_eq_ofNat (a : ZMod64 p) :
    inv a =
      ofNat p
        (Int.toNat
          ((let (_, s, _) :=
              HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat p); s)
            % Int.ofNat p)) := by
  rw [eq_iff_toNat_eq, toNat_inv_def, toNat_ofNat]

/-- Operator-level form of `inv_eq_ofNat`. -/
theorem inv_op_eq_ofNat (a : ZMod64 p) :
    a⁻¹ =
      ofNat p
        (Int.toNat
          ((let (_, s, _) :=
              HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat p); s)
            % Int.ofNat p)) := by
  simpa using inv_eq_ofNat a

/-- A Bézout cofactor for `gcd a p = 1` reduces to a modular inverse of `a`:
given `s * a + t * p = 1`, the centered representative `s % p` satisfies
`(s % p) * a ≡ 1 (mod p)`. This is the step turning the extended-GCD output
(`HexArith.Int.extGcd`, consumed by `inv`) into the modular-inverse
correctness spec. -/
private theorem invBezout_mul_mod_eq_one {a p : Nat} (hp : 0 < p)
    {s t : Int} (hbez : s * Int.ofNat a + t * Int.ofNat p = 1) :
    (Int.toNat (s % Int.ofNat p) * a) % p = 1 % p := by
  have hpInt : (Int.ofNat p) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hp)
  have hs_nonneg : 0 ≤ s % Int.ofNat p := Int.emod_nonneg _ hpInt
  have hs_cast : Int.ofNat (Int.toNat (s % Int.ofNat p)) = s % Int.ofNat p :=
    Int.toNat_of_nonneg hs_nonneg
  have hs_congr :
      (Int.ofNat (Int.toNat (s % Int.ofNat p)) * Int.ofNat a -
          s * Int.ofNat a) % Int.ofNat p = 0 := by
    rw [hs_cast]
    have hdiv :
        Int.ofNat p ∣
          (s % Int.ofNat p * Int.ofNat a - s * Int.ofNat a) := by
      have hbase : Int.ofNat p ∣ s % Int.ofNat p - s :=
        Int.dvd_sub_self_of_emod_eq rfl
      rcases hbase with ⟨k, hk⟩
      refine ⟨k * Int.ofNat a, ?_⟩
      rw [← Int.sub_mul, hk, Int.mul_assoc]
    exact Int.emod_eq_zero_of_dvd hdiv
  have hbez_congr : (s * Int.ofNat a - 1) % Int.ofNat p = 0 := by
    have hdiv : Int.ofNat p ∣ s * Int.ofNat a - 1 := by
      refine ⟨-t, ?_⟩
      calc
        s * Int.ofNat a - 1 = -(t * Int.ofNat p) := by omega
        _ = Int.ofNat p * -t := by
          rw [Int.mul_comm]
          exact Int.neg_mul_eq_mul_neg (Int.ofNat p) t
    exact Int.emod_eq_zero_of_dvd hdiv
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.natCast_emod]
  have htarget :
      (Int.ofNat (Int.toNat (s % Int.ofNat p) * a) - 1) % Int.ofNat p = 0 := by
    have hdiv₁ : Int.ofNat p ∣
        Int.ofNat (Int.toNat (s % Int.ofNat p)) * Int.ofNat a -
          s * Int.ofNat a :=
      Int.dvd_of_emod_eq_zero hs_congr
    have hdiv₂ : Int.ofNat p ∣ s * Int.ofNat a - 1 :=
      Int.dvd_of_emod_eq_zero hbez_congr
    have hdiv : Int.ofNat p ∣ Int.ofNat (Int.toNat (s % Int.ofNat p) * a) - 1 := by
      rcases hdiv₁ with ⟨k₁, hk₁⟩
      rcases hdiv₂ with ⟨k₂, hk₂⟩
      refine ⟨k₁ + k₂, ?_⟩
      calc
        Int.ofNat (Int.toNat (s % Int.ofNat p) * a) - 1 =
            (Int.ofNat (Int.toNat (s % Int.ofNat p)) * Int.ofNat a -
                s * Int.ofNat a) +
              (s * Int.ofNat a - 1) := by
          rw [show Int.ofNat (Int.toNat (s % Int.ofNat p) * a) =
              Int.ofNat (Int.toNat (s % Int.ofNat p)) * Int.ofNat a by
            simp [Int.ofNat_eq_natCast]]
          omega
        _ = Int.ofNat p * k₁ + Int.ofNat p * k₂ := by
          rw [hk₁, hk₂]
        _ = Int.ofNat p * (k₁ + k₂) := by
          rw [Int.mul_add]
    exact Int.emod_eq_zero_of_dvd hdiv
  have hleft :
      (Int.ofNat (Int.toNat (s % Int.ofNat p) * a) % Int.ofNat p) =
        (1 : Int) % Int.ofNat p := by
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr htarget
  simpa using hleft

/-- Even case of one square-and-multiply step: when `k` is even, replacing
`base ^ k` by `(base * base) ^ (k / 2)` under modular reduction leaves the
accumulator unchanged mod `p`. Used by `pow_go_toNat` to discharge the even
branch of the `pow.go` recursion. -/
private theorem nat_mod_mul_pow_square_even (acc base k p : Nat) (heven : k % 2 = 0) :
    (acc * ((base * base) % p) ^ (k / 2)) % p = (acc * base ^ k) % p := by
  have hk : 2 * (k / 2) = k := by
    have h := Nat.mod_add_div k 2
    omega
  have hsquare : (base * base) ^ (k / 2) = base ^ (2 * (k / 2)) := by
    rw [Nat.mul_pow, ← Nat.pow_add]
    congr
    omega
  calc
    (acc * ((base * base) % p) ^ (k / 2)) % p =
        (acc * (base * base) ^ (k / 2)) % p := by
      rw [Nat.mul_mod]
      rw [show ((base * base) % p) ^ (k / 2) % p = (base * base) ^ (k / 2) % p by
        exact (Nat.pow_mod (base * base) (k / 2) p).symm]
      rw [← Nat.mul_mod]
    _ = (acc * base ^ (2 * (k / 2))) % p := by rw [hsquare]
    _ = (acc * base ^ k) % p := by rw [hk]

/-- Odd case of one square-and-multiply step: when `k` is odd, folding one
factor of `base` into the accumulator and replacing `base ^ k` by
`(base * base) ^ (k / 2)` under modular reduction reproduces `acc * base ^ k`
mod `p`. Used by `pow_go_toNat` for the odd branch of the `pow.go` recursion. -/
private theorem nat_mod_mul_pow_square_odd (acc base k p : Nat) (hodd : k % 2 ≠ 0) :
    ((acc * base) % p * ((base * base) % p) ^ (k / 2)) % p =
      (acc * base ^ k) % p := by
  have hmod : k % 2 = 1 := by
    have h := Nat.mod_two_eq_zero_or_one k
    omega
  have hk : 1 + 2 * (k / 2) = k := by
    have h := Nat.mod_add_div k 2
    omega
  have hsquare : (base * base) ^ (k / 2) = base ^ (2 * (k / 2)) := by
    rw [Nat.mul_pow, ← Nat.pow_add]
    congr
    omega
  calc
    ((acc * base) % p * ((base * base) % p) ^ (k / 2)) % p =
        (acc * base * (base * base) ^ (k / 2)) % p := by
      rw [Nat.mul_mod]
      rw [Nat.mod_mod]
      rw [show ((base * base) % p) ^ (k / 2) % p = (base * base) ^ (k / 2) % p by
        exact (Nat.pow_mod (base * base) (k / 2) p).symm]
      rw [← Nat.mul_mod]
    _ = (acc * (base * base ^ (2 * (k / 2)))) % p := by
      rw [hsquare]
      grind
    _ = (acc * base ^ (1 + 2 * (k / 2))) % p := by
      simp [Nat.pow_add]
    _ = (acc * base ^ k) % p := by rw [hk]

/-- Loop invariant of the `pow.go` tail recursion: the canonical representative
of `pow.go base acc k` is `(acc.toNat * base.toNat ^ k) % p`, linking the
tail-recursive accumulator to `base ^ k` mod `p`. This is the workhorse behind
`toNat_pow`. -/
private theorem pow_go_toNat (base acc : ZMod64 p) (k : Nat) :
    (pow.go base acc k).toNat = (acc.toNat * base.toNat ^ k) % p := by
  revert base acc
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro base acc
      cases k with
      | zero =>
          simp [pow.go, Nat.mod_eq_of_lt acc.isLt]
      | succ m =>
          have hlt : (m + 1) / 2 < m + 1 :=
            Nat.div_lt_self (Nat.succ_pos m) (by decide : 1 < 2)
          simp [pow.go]
          by_cases heven : (m + 1) % 2 = 0
          · rw [if_pos heven]
            have hrec := ih ((m + 1) / 2) hlt (mul base base) acc
            change (pow.go (mul base base) acc ((m + 1) / 2)).toNat =
              acc.toNat * base.toNat ^ (m + 1) % p
            rw [hrec]
            rw [toNat_mul]
            exact nat_mod_mul_pow_square_even acc.toNat base.toNat (m + 1) p heven
          · rw [if_neg heven]
            have hrec := ih ((m + 1) / 2) hlt (mul base base) (mul acc base)
            change (pow.go (mul base base) (mul acc base) ((m + 1) / 2)).toNat =
              acc.toNat * base.toNat ^ (m + 1) % p
            rw [hrec]
            rw [toNat_mul, toNat_mul]
            exact nat_mod_mul_pow_square_odd acc.toNat base.toNat (m + 1) p heven

/-- Exponentiation agrees with natural-power reduction of the canonical representative. -/
@[simp, grind =] theorem toNat_pow (a : ZMod64 p) (n : Nat) :
    (pow a n).toNat = a.toNat ^ n % p := by
  rw [pow]
  rw [pow_go_toNat]
  rw [toNat_one]
  rw [← Nat.mod_mul_mod]
  simp

/-- Exponentiation is the residue built from the representative's natural power. -/
theorem pow_eq_ofNat (a : ZMod64 p) (n : Nat) :
    pow a n = ofNat p (a.toNat ^ n) := by
  rw [eq_iff_toNat_eq, toNat_pow, toNat_ofNat]

/-- Operator-level form of `pow_eq_ofNat`. -/
theorem pow_op_eq_ofNat (a : ZMod64 p) (n : Nat) :
    a ^ n = ofNat p (a.toNat ^ n) := by
  simpa using pow_eq_ofNat a n

/--
The extended-GCD inverse candidate is a left inverse whenever the representative
is coprime to the modulus.
-/
@[grind =]
theorem inv_mul_eq_one (a : ZMod64 p) (hcop : Nat.Coprime a.toNat p) :
    (mul (inv a) a).toNat = 1 % p := by
  rw [toNat_mul, toNat_inv_def]
  generalize hgcd : HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat p) = triple
  obtain ⟨g, s, t⟩ := triple
  have hbez :
      s * Int.ofNat a.toNat + t * Int.ofNat p = 1 := by
    have hspec := HexArith.Int.extGcd_bezout (Int.ofNat a.toNat) (Int.ofNat p)
    have hfst := HexArith.Int.extGcd_fst (Int.ofNat a.toNat) (Int.ofNat p)
    rw [hgcd] at hspec
    rw [hgcd] at hfst
    simp at hfst
    have hg : g = 1 := by
      rw [hfst]
      simpa [Int.gcd_eq_natAbs_gcd_natAbs, hcop]
    rw [hg] at hspec
    simp at hspec
    exact hspec
  simpa [Nat.mod_mod] using
    invBezout_mul_mod_eq_one (a := a.toNat) (p := p) (Bounds.pPos (p := p))
      (s := s) (t := t) hbez

/-- Coprime residues multiply by their computed inverse to the unit residue. -/
@[grind =]
theorem inv_mul_eq_one_of_coprime (a : ZMod64 p) (hcop : Nat.Coprime a.toNat p) :
    mul (inv a) a = ZMod64.one := by
  rw [eq_iff_toNat_eq, inv_mul_eq_one a hcop, toNat_one]

/-- Operator-level form of `inv_mul_eq_one_of_coprime`. -/
@[grind =]
theorem inv_op_mul_eq_one_of_coprime (a : ZMod64 p) (hcop : Nat.Coprime a.toNat p) :
    a⁻¹ * a = 1 := by
  simpa using inv_mul_eq_one_of_coprime a hcop

/-- Addition produces a canonical representative below the modulus. -/
theorem add_lt_modulus (a b : ZMod64 p) : (add a b).toNat < p := by
  exact (add a b).isLt

/-- Subtraction produces a canonical representative below the modulus. -/
theorem sub_lt_modulus (a b : ZMod64 p) : (sub a b).toNat < p := by
  exact (sub a b).isLt

/-- Multiplication produces a canonical representative below the modulus. -/
theorem mul_lt_modulus (a b : ZMod64 p) : (mul a b).toNat < p := by
  simpa [toNat_mul] using normalize_lt p (a.toNat * b.toNat)

/-- Exponentiation produces a canonical representative below the modulus. -/
theorem pow_lt_modulus (a : ZMod64 p) (n : Nat) : (pow a n).toNat < p := by
  exact (pow a n).isLt

/-- Inversion produces a canonical representative below the modulus. -/
theorem inv_lt_modulus (a : ZMod64 p) : (inv a).toNat < p := by
  exact (inv a).isLt

end ZMod64
end Hex
