import HexPolyFp.Enumeration

/-!
Project-side quotient API for `F_p[X] / (g)`.

The executable representation keeps canonical representatives reduced by the
existing `FpPoly.modByMonic` path.  The API is intentionally small: it exposes
the quotient operations needed by Rabin-style finite-field arguments while
leaving the deepest irreducible-gcd fact as a narrow helper theorem.
-/

namespace Hex
namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

local instance : DensePoly.DivModLaws (ZMod64 p) :=
  ZMod64.instDivModLawsZMod64Fp p

/-- Canonical representatives for the quotient `F_p[X] / (g)`, reduced modulo
a monic positive-degree modulus. -/
structure Quotient (g : FpPoly p) (hmonic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) where
  val : FpPoly p
  reduced : val.degree?.getD 0 < g.degree?.getD 0

namespace Quotient

variable {g : FpPoly p} {hmonic : DensePoly.Monic g}
variable {hg_pos : 0 < g.degree?.getD 0}

omit [ZMod64.PrimeModulus p] in
@[ext] theorem ext {a b : Quotient g hmonic hg_pos} (h : a.val = b.val) :
    a = b := by
  cases a
  cases b
  simp at h
  subst h
  rfl

/-- Reduce a polynomial to its canonical quotient representative. -/
def reduce (f : FpPoly p) : Quotient g hmonic hg_pos :=
  ⟨FpPoly.modByMonic g f hmonic, by
    rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    exact DensePoly.mod_degree_lt_of_pos_degree f g hg_pos⟩

@[simp] theorem reduce_val (f : FpPoly p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val =
      FpPoly.modByMonic g f hmonic :=
  rfl

theorem reduce_val_eq_mod (f : FpPoly p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val = f % g := by
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]

/-- Polynomial congruence modulo the defining quotient polynomial. -/
def Congr (f h : FpPoly p) : Prop :=
  DensePoly.Congr f h g

theorem reduce_eq_reduce_of_congr {f h : FpPoly p} (hc : Congr (g := g) f h) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p) f h g hc

theorem congr_of_reduce_eq_reduce {f h : FpPoly p}
    (heq :
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h) :
    Congr (g := g) f h := by
  unfold Congr
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  apply @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p) f h g
  have hval := congrArg Quotient.val heq
  have hf := reduce_val_eq_mod (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f
  have hh := reduce_val_eq_mod (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h
  rw [hf, hh] at hval
  exact hval

theorem reduce_eq_reduce_iff_congr (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h ↔
      Congr (g := g) f h :=
  ⟨congr_of_reduce_eq_reduce, reduce_eq_reduce_of_congr⟩

private theorem nodup_map_of_injective
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
        have hyx : y = x := hinj y (by simp [hy]) x (by simp) hxy
        exact hxs.1 (by simpa [hyx] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

/-- All canonical quotient representatives, enumerated via bounded-degree
polynomials. -/
def elements : List (Quotient g hmonic hg_pos) :=
  (Enumeration.polysBelowDegree p (g.degree?.getD 0)).map
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos))

@[simp] theorem elements_length :
    (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).length =
      p ^ g.degree?.getD 0 := by
  simp [elements]

/-- Every quotient element appears in `elements`. -/
theorem mem_elements (a : Quotient g hmonic hg_pos) :
    a ∈ elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos) := by
  unfold elements
  apply List.mem_map.mpr
  refine ⟨a.val, Enumeration.mem_polysBelowDegree_of_degree_getD_lt a.reduced, ?_⟩
  apply ext
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  exact DensePoly.mod_eq_self_of_degree_lt a.val g a.reduced

/-- The quotient enumeration has no duplicate elements. -/
theorem elements_nodup :
    (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).Nodup := by
  unfold elements
  apply nodup_map_of_injective
  · exact Enumeration.polysBelowDegree_nodup (p := p) (g.degree?.getD 0)
  · intro a ha b hb hab
    have hval := congrArg Quotient.val hab
    rw [reduce_val, reduce_val, FpPoly.modByMonic, FpPoly.modByMonic,
      DensePoly.modByMonic_eq_mod, DensePoly.modByMonic_eq_mod] at hval
    have ha_deg : a.degree?.getD 0 < g.degree?.getD 0 :=
      Enumeration.degree_getD_lt_of_mem_polysBelowDegree hg_pos ha
    have hb_deg : b.degree?.getD 0 < g.degree?.getD 0 :=
      Enumeration.degree_getD_lt_of_mem_polysBelowDegree hg_pos hb
    rw [DensePoly.mod_eq_self_of_degree_lt a g ha_deg,
      DensePoly.mod_eq_self_of_degree_lt b g hb_deg] at hval
    exact hval

/-- The quotient has `p ^ deg(g)` canonical representatives in the executable
list-cardinality sense. -/
theorem elements_card :
    (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).length =
      p ^ g.degree?.getD 0 :=
  elements_length (g := g) (hmonic := hmonic) (hg_pos := hg_pos)

omit [ZMod64.PrimeModulus p] in
/-- Equality of quotient elements is equality of canonical remainders. -/
theorem eq_iff_val_eq {a b : Quotient g hmonic hg_pos} :
    a = b ↔ a.val = b.val :=
  ⟨fun h => by cases h; rfl, ext⟩

/-- Zero in the quotient. -/
def zero : Quotient g hmonic hg_pos :=
  reduce 0

instance : Zero (Quotient g hmonic hg_pos) where
  zero := zero

/-- One in the quotient. -/
def one : Quotient g hmonic hg_pos :=
  reduce 1

instance : One (Quotient g hmonic hg_pos) where
  one := one

/-- The class of the polynomial indeterminate. -/
def X : Quotient g hmonic hg_pos :=
  reduce FpPoly.X

/-- Addition of canonical quotient representatives. -/
def add (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val + b.val)

instance : Add (Quotient g hmonic hg_pos) where
  add := add

/-- Negation of canonical quotient representatives. -/
def neg (a : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (-a.val)

instance : Neg (Quotient g hmonic hg_pos) where
  neg := neg

/-- Subtraction of canonical quotient representatives. -/
def sub (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val - b.val)

instance : Sub (Quotient g hmonic hg_pos) where
  sub := sub

/-- Multiplication of canonical quotient representatives. -/
def mul (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val * b.val)

instance : Mul (Quotient g hmonic hg_pos) where
  mul := mul

/-- Natural-number powers in the quotient. -/
def pow (a : Quotient g hmonic hg_pos) : Nat → Quotient g hmonic hg_pos
  | 0 => 1
  | n + 1 => pow a n * a

instance : Pow (Quotient g hmonic hg_pos) Nat where
  pow := pow

@[simp] theorem zero_val :
    (0 : Quotient g hmonic hg_pos).val = FpPoly.modByMonic g 0 hmonic :=
  rfl

@[simp] theorem one_val :
    (1 : Quotient g hmonic hg_pos).val = FpPoly.modByMonic g 1 hmonic :=
  rfl

@[simp] theorem X_val :
    (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).val =
      FpPoly.modByMonic g FpPoly.X hmonic :=
  rfl

@[simp] theorem add_val (a b : Quotient g hmonic hg_pos) :
    (a + b).val = FpPoly.modByMonic g (a.val + b.val) hmonic :=
  rfl

@[simp] theorem neg_val (a : Quotient g hmonic hg_pos) :
    (-a).val = FpPoly.modByMonic g (-a.val) hmonic :=
  rfl

@[simp] theorem sub_val (a b : Quotient g hmonic hg_pos) :
    (a - b).val = FpPoly.modByMonic g (a.val - b.val) hmonic :=
  rfl

@[simp] theorem mul_val (a b : Quotient g hmonic hg_pos) :
    (a * b).val = FpPoly.modByMonic g (a.val * b.val) hmonic :=
  rfl

@[simp] theorem pow_zero (a : Quotient g hmonic hg_pos) :
    a ^ (0 : Nat) = 1 := by
  rfl

@[simp] theorem pow_succ (a : Quotient g hmonic hg_pos) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := by
  rfl

theorem reduce_add_eq (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) =
      reduce
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        ((reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val +
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h).val) := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_add_mod (ZMod64 p) inferInstance inferInstance inferInstance
    (ZMod64.instDivModLawsZMod64Fp p) f h g

theorem reduce_mul_eq (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f * h) =
      reduce
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        ((reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val *
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h).val) := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
    (ZMod64.instDivModLawsZMod64Fp p) f h g

/-- Reducing an already-canonical quotient representative leaves it unchanged. -/
theorem reduce_val_self (a : Quotient g hmonic hg_pos) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val = a := by
  apply ext
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  exact DensePoly.mod_eq_self_of_degree_lt a.val g a.reduced

/-- The canonical quotient representative of `1` is the polynomial `1`. -/
theorem one_val_eq_one :
    (1 : Quotient g hmonic hg_pos).val = (1 : FpPoly p) := by
  rw [one_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  have hone_deg : (1 : FpPoly p).degree?.getD 0 < g.degree?.getD 0 := by
    change (DensePoly.C (1 : ZMod64 p)).degree?.getD 0 < g.degree?.getD 0
    simpa using hg_pos
  exact DensePoly.mod_eq_self_of_degree_lt (1 : FpPoly p) g hone_deg

/-- `1` is a left identity for quotient multiplication. -/
@[simp] theorem one_mul (a : Quotient g hmonic hg_pos) :
    (1 : Quotient g hmonic hg_pos) * a = a := by
  calc
    (1 : Quotient g hmonic hg_pos) * a =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((1 : Quotient g hmonic hg_pos).val * a.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((1 : FpPoly p) * a.val) := by rw [one_val_eq_one]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val := by
          rw [FpPoly.one_mul]
    _ = a := reduce_val_self a

/-- `1` is a right identity for quotient multiplication. -/
@[simp] theorem mul_one (a : Quotient g hmonic hg_pos) :
    a * (1 : Quotient g hmonic hg_pos) = a := by
  calc
    a * (1 : Quotient g hmonic hg_pos) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (1 : Quotient g hmonic hg_pos).val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (1 : FpPoly p)) := by rw [one_val_eq_one]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val := by
          rw [FpPoly.mul_one]
    _ = a := reduce_val_self a

/-- Quotient multiplication is associative. -/
theorem mul_assoc (a b c : Quotient g hmonic hg_pos) :
    (a * b) * c = a * (b * c) := by
  calc
    (a * b) * c =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a * b).val * c.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a.val * b.val) * c.val) := by
          have hmul := reduce_mul_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (a.val * b.val) c.val
          rw [reduce_val_self c] at hmul
          exact hmul.symm
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (b.val * c.val)) := by rw [FpPoly.mul_assoc]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (b * c).val) := by
          have hmul := reduce_mul_eq (g := g) (hmonic := hmonic)
            (hg_pos := hg_pos) a.val (b.val * c.val)
          rw [reduce_val_self a] at hmul
          exact hmul
    _ = a * (b * c) := rfl

/-- Quotient multiplication is commutative. -/
theorem mul_comm (a b : Quotient g hmonic hg_pos) :
    a * b = b * a := by
  calc
    a * b =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * b.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (b.val * a.val) := by rw [FpPoly.mul_comm]
    _ = b * a := rfl

/-- Quotient powers turn addition of exponents into multiplication. -/
theorem pow_add (a : Quotient g hmonic hg_pos) (m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
      simp [Nat.add_zero]
  | succ n ih =>
      calc
        a ^ (m + (n + 1)) = a ^ ((m + n) + 1) := by rw [Nat.add_succ]
        _ = a ^ (m + n) * a := by rfl
        _ = (a ^ m * a ^ n) * a := by rw [ih]
        _ = a ^ m * (a ^ n * a) := by rw [mul_assoc]
        _ = a ^ m * a ^ (n + 1) := by rfl

/-- Quotient powers turn multiplication of exponents into iterated powering. -/
theorem pow_mul (a : Quotient g hmonic hg_pos) (m n : Nat) :
    (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (a ^ m) ^ (n + 1) = (a ^ m) ^ n * a ^ m := by rfl
        _ = a ^ (m * n) * a ^ m := by rw [ih]
        _ = a ^ (m * n + m) := by
          exact (pow_add a (m * n) m).symm
        _ = a ^ (m * (n + 1)) := by rw [Nat.mul_succ]

/--
Reducing an executable polynomial power agrees with powering its quotient
class.
-/
theorem reduce_linearPow_eq_pow (f : FpPoly p) (n : Nat) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (FpPoly.linearPow f n) =
      (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) ^ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (FpPoly.linearPow f (n + 1)) =
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (FpPoly.linearPow f n * f) := by
              rw [FpPoly.linearPow_succ]
        _ =
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (FpPoly.linearPow f n) *
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f := by
              exact reduce_mul_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (FpPoly.linearPow f n) f
        _ =
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) ^ n *
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f := by
              rw [ih]
        _ =
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) ^ (n + 1) := by
              rfl

/-- The xgcd-based inverse candidate, normalized by the leading coefficient of
the computed gcd. -/
def inverseCandidate (a : FpPoly p) : FpPoly p :=
  DensePoly.scale (DensePoly.leadingCoeff (DensePoly.gcd a g))⁻¹
    (DensePoly.xgcd a g).left

/--
Narrow Euclidean obligation for quotient inversion.

For a nonzero canonical representative modulo a monic irreducible positive-degree
polynomial, the normalized left Bezout coefficient is a multiplicative inverse
modulo `g`.
-/
theorem mul_mod_inverseCandidate_eq_one_of_irreducible
    (hg_irr : FpPoly.Irreducible g) {a : FpPoly p}
    (ha_ne : a ≠ 0) (ha_reduced : a.degree?.getD 0 < g.degree?.getD 0) :
    (a * inverseCandidate (g := g) a) % g = (1 : FpPoly p) % g := by
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  -- Bezout identity from the executable extended gcd.
  let xres : DensePoly.XGCDResult (ZMod64 p) := DensePoly.xgcd a g
  let d : FpPoly p := DensePoly.gcd a g
  have hbezout : xres.left * a + xres.right * g = d := by
    have hb := DensePoly.xgcd_bezout a g
    simpa [xres, d, DensePoly.gcd] using hb
  -- The gcd divides both inputs.
  have hda : d ∣ a := DensePoly.gcd_dvd_left a g
  have hdg : d ∣ g := DensePoly.gcd_dvd_right a g
  have hg_ne : g ≠ 0 := hg_irr.1
  have hd_ne : d ≠ 0 := by
    intro hzero
    obtain ⟨s, hs⟩ := hda
    apply ha_ne
    rw [hs, hzero, FpPoly.zero_mul]
  -- Irreducibility forces the gcd to be a unit constant.
  obtain ⟨r, hr⟩ := hdg
  have hr_ne : r ≠ 0 := by
    intro hzero
    apply hg_ne
    rw [hr, hzero, FpPoly.mul_zero]
  have hd_deg : d.degree? = some 0 := by
    rcases hg_irr.2 _ _ hr.symm with hd_deg_zero | hr_deg_zero
    · exact hd_deg_zero
    · exfalso
      have hsum : g.degree?.getD 0 = d.degree?.getD 0 + r.degree?.getD 0 := by
        rw [hr]
        exact FpPoly.degree?_mul_eq_add_degree? d r hd_ne hr_ne
      have hr_deg_zero' : r.degree?.getD 0 = 0 := by simp [hr_deg_zero]
      obtain ⟨s, hs⟩ := hda
      have hs_ne : s ≠ 0 := by
        intro hzero
        apply ha_ne
        rw [hs, hzero, FpPoly.mul_zero]
      have hsum_a : a.degree?.getD 0 = d.degree?.getD 0 + s.degree?.getD 0 := by
        rw [hs]
        exact FpPoly.degree?_mul_eq_add_degree? d s hd_ne hs_ne
      omega
  -- Extract the leading coefficient and verify it is invertible.
  let dlc : ZMod64 p := DensePoly.leadingCoeff d
  have hd_size : d.size = 1 := by
    unfold DensePoly.degree? at hd_deg
    by_cases hsize : d.size = 0
    · simp [hsize] at hd_deg
    · simp [hsize] at hd_deg
      omega
  have hd_size_pos : 0 < d.size := by omega
  have hdlc_ne : dlc ≠ 0 := by
    show DensePoly.leadingCoeff d ≠ 0
    rw [FpPoly.leadingCoeff_eq_coeff_pred d hd_size_pos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size d hd_size_pos
  -- Scale Bezout by `dlc⁻¹` so the gcd becomes the unit `1`.
  let R : FpPoly p := DensePoly.scale dlc⁻¹ xres.right
  let L : FpPoly p := DensePoly.scale dlc⁻¹ xres.left
  have hbezout_scaled : L * a + R * g = DensePoly.scale dlc⁻¹ d := by
    show DensePoly.scale dlc⁻¹ xres.left * a +
        DensePoly.scale dlc⁻¹ xres.right * g = DensePoly.scale dlc⁻¹ d
    rw [← FpPoly.scale_mul_left, ← FpPoly.scale_mul_left,
        ← FpPoly.scale_add, hbezout]
  have hscale_d : DensePoly.scale dlc⁻¹ d = (1 : FpPoly p) := by
    apply DensePoly.ext_coeff
    intro n
    have hzero_mul : (dlc⁻¹ : ZMod64 p) * 0 = 0 := by grind
    rw [DensePoly.coeff_scale dlc⁻¹ d n hzero_mul]
    change dlc⁻¹ * d.coeff n = (DensePoly.C (1 : ZMod64 p)).coeff n
    rw [DensePoly.coeff_C]
    cases n with
    | zero =>
        have hd_coeff : d.coeff 0 = dlc := by
          show d.coeff 0 = DensePoly.leadingCoeff d
          rw [FpPoly.leadingCoeff_eq_coeff_pred d hd_size_pos]
          congr 1
          omega
        rw [hd_coeff]
        simp
        exact ZMod64.inv_mul_eq_one_of_prime
          (ZMod64.PrimeModulus.prime (p := p)) hdlc_ne
    | succ k =>
        have hd_coeff : d.coeff (k + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le d (by omega)
        rw [hd_coeff]
        have hkne : k + 1 ≠ 0 := Nat.succ_ne_zero k
        rw [if_neg hkne]
        exact hzero_mul
  have hkey : L * a + R * g = (1 : FpPoly p) := by
    show DensePoly.scale dlc⁻¹ xres.left * a +
        DensePoly.scale dlc⁻¹ xres.right * g = (1 : FpPoly p)
    rw [hbezout_scaled, hscale_d]
  -- Convert to the required modular identity using mod_add_mod and mod_mul_self.
  have hRg_mod : (R * g) % g = 0 := by
    show (DensePoly.scale dlc⁻¹ xres.right * g) % g = 0
    rw [FpPoly.mul_comm (DensePoly.scale dlc⁻¹ xres.right) g]
    exact DensePoly.mod_eq_zero_of_dvd (g * DensePoly.scale dlc⁻¹ xres.right) g ⟨_, rfl⟩
  have hL_eq : inverseCandidate (g := g) a = L := rfl
  rw [hL_eq, FpPoly.mul_comm a L]
  -- Goal: L * a % g = 1 % g
  have hmm : L * a % g % g = L * a % g :=
    @DensePoly.mod_mod (ZMod64 p) inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) (L * a) g
  have hadd : (L * a + R * g) % g = (L * a % g + R * g % g) % g :=
    @DensePoly.mod_add_mod (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) (L * a) (R * g) g
  calc L * a % g
      = L * a % g % g := hmm.symm
    _ = (L * a % g + 0) % g := by rw [FpPoly.add_zero]
    _ = (L * a % g + R * g % g) % g := by rw [hRg_mod]
    _ = (L * a + R * g) % g := hadd.symm
    _ = 1 % g := by rw [hkey]

/-- Multiplicative inverse candidate in the quotient, with the conventional
junk value `0⁻¹ = 0`.  The cancellation theorem below requires irreducibility. -/
def inv (a : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  if a.val = 0 then
    0
  else
    reduce (inverseCandidate (g := g) a.val)

instance : Inv (Quotient g hmonic hg_pos) where
  inv := inv

theorem inv_zero :
    (0 : Quotient g hmonic hg_pos)⁻¹ = 0 := by
  have hzero_val : (0 : Quotient g hmonic hg_pos).val = 0 := by
    rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
  change inv (0 : Quotient g hmonic hg_pos) = 0
  unfold inv
  change (if (0 : Quotient g hmonic hg_pos).val = 0 then 0
    else reduce (inverseCandidate (g := g) (0 : Quotient g hmonic hg_pos).val)) = 0
  rw [hzero_val]
  simp

theorem mul_inv_cancel (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have ha_val_ne : a.val ≠ 0 := by
    intro hval
    apply ha
    apply ext
    change a.val = (0 : Quotient g hmonic hg_pos).val
    simpa [zero, reduce_val_eq_mod, hval] using
      (DensePoly.modByMonic_zero g hmonic).symm
  apply ext
  change (a * inv (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a).val =
    (1 : Quotient g hmonic hg_pos).val
  unfold inv
  simp [ha_val_ne]
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  change FpPoly.modByMonic g
      (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic)
      hmonic =
    FpPoly.modByMonic g 1 hmonic
  calc
    FpPoly.modByMonic g
        (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic)
        hmonic =
        (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic) % g := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    _ = (a.val * ((inverseCandidate (g := g) a.val) % g)) % g := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    _ = (a.val * inverseCandidate (g := g) a.val) % g := by
          have ha_mod : a.val % g = a.val :=
            DensePoly.mod_eq_self_of_degree_lt a.val g a.reduced
          have hmul_mod :=
            @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
              (ZMod64.instDivModLawsZMod64Fp p) a.val
              (inverseCandidate (g := g) a.val) g
          calc
            (a.val * ((inverseCandidate (g := g) a.val) % g)) % g =
                ((a.val % g) * ((inverseCandidate (g := g) a.val) % g)) % g := by
                  simp [ha_mod]
            _ = (a.val * inverseCandidate (g := g) a.val) % g := hmul_mod.symm
    _ = (1 : FpPoly p) % g :=
          mul_mod_inverseCandidate_eq_one_of_irreducible
            (g := g) hg_irr ha_val_ne a.reduced
    _ = FpPoly.modByMonic g 1 hmonic := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]

/-- The inverse candidate also cancels on the left for nonzero quotient
elements modulo an irreducible polynomial. -/
theorem inv_mul_cancel (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0) :
    a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr ha

end Quotient
end FpPoly
end Hex
