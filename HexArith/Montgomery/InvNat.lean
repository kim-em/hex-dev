import HexArith.Montgomery.RedcNat

/-!
Montgomery inverses for `HexArith`.

The runtime inverse is computed in wrapping `UInt64` arithmetic by Newton-style
doubling from the standard odd-modulus seed. The proof surface records the
resulting modular-inverse properties.
-/

/-- One Newton/Hensel refinement step for the positive Montgomery inverse. -/
private def montPosInvStep (p x : UInt64) : UInt64 :=
  x * (2 - p * x)

/-- The executable wrapping Newton step lifts a 3-bit inverse to 6 bits. -/
private theorem montPosInvStep_mod_3_to_6 (p x : UInt64)
    (hx : p * x % 8 = 1) :
    p * montPosInvStep p x % 64 = 1 := by
  unfold montPosInvStep
  bv_decide (config := { timeout := 120 })

/-- The executable wrapping Newton step lifts a 6-bit inverse to 12 bits. -/
private theorem montPosInvStep_mod_6_to_12 (p x : UInt64)
    (hx : p * x % 64 = 1) :
    p * montPosInvStep p x % 4096 = 1 := by
  unfold montPosInvStep
  bv_decide (config := { timeout := 120 })

private theorem two_pow_dvd_uint64_word {t : Nat} (ht : t ≤ 64) :
    2 ^ t ∣ UInt64.word := by
  refine ⟨2 ^ (64 - t), ?_⟩
  calc
    UInt64.word = 2 ^ 64 := rfl
    _ = 2 ^ (t + (64 - t)) := by rw [Nat.add_sub_of_le ht]
    _ = 2 ^ t * 2 ^ (64 - t) := by rw [Nat.pow_add]

private theorem mod_uint64_word_mod_two_pow (n t : Nat) (ht : t ≤ 64) :
    n % UInt64.word % 2 ^ t = n % 2 ^ t := by
  exact Nat.mod_mod_of_dvd n (two_pow_dvd_uint64_word ht)

/-- Multiplication wrap at `2^64` is invisible when reducing modulo fewer bits. -/
private theorem UInt64.toNat_mul_mod_two_pow (a b : UInt64) {t : Nat}
    (ht : t ≤ 64) :
    (a * b).toNat % 2 ^ t = (a.toNat * b.toNat) % 2 ^ t := by
  simpa [UInt64.toNat_mul] using
    mod_uint64_word_mod_two_pow (a.toNat * b.toNat) t ht

/-- Subtraction wrap at `2^64` is invisible when reducing modulo fewer bits. -/
private theorem UInt64.toNat_sub_mod_two_pow (a b : UInt64) {t : Nat}
    (ht : t ≤ 64) :
    (a - b).toNat % 2 ^ t =
      (2 ^ 64 - b.toNat + a.toNat) % 2 ^ t := by
  simpa [UInt64.toNat_sub] using
    mod_uint64_word_mod_two_pow (2 ^ 64 - b.toNat + a.toNat) t ht

private theorem int_newton_refine_dvd (m y : Int) (hm : m ∣ y - 1) :
    m * m ∣ y * (2 - y) - 1 := by
  rcases hm with ⟨q, hq⟩
  have hy : y = 1 + m * q := by omega
  subst y
  refine ⟨-(q * q), ?_⟩
  grind

private theorem nat_newton_refine_dvd (y k : Nat) (h : y % 2 ^ k = 1) :
    ((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int) ∣
      (y : Int) * (2 - (y : Int)) - 1 := by
  have hy : y = 1 + 2 ^ k * (y / 2 ^ k) := by
    have hdecomp := Nat.mod_add_div y (2 ^ k)
    rw [h] at hdecomp
    omega
  apply int_newton_refine_dvd
  refine ⟨((y / 2 ^ k : Nat) : Int), ?_⟩
  have hyInt := congrArg (fun n : Nat => (n : Int)) hy
  simp only [Int.natCast_add, Int.ofNat_one, Int.natCast_mul] at hyInt
  omega

private theorem int_dvd_of_nat_dvd {a b : Nat} (h : a ∣ b) :
    (a : Int) ∣ (b : Int) := by
  rcases h with ⟨q, hq⟩
  refine ⟨(q : Int), ?_⟩
  rw [← Int.natCast_mul, hq]

/--
Newton/Hensel refinement over powers of two, phrased with the `2^64 - z + 2`
wrapping-subtraction shape produced by `UInt64.toNat_sub_mod_two_pow`.
-/
private theorem nat_newton_refine_wrapped_dvd (y z k t : Nat)
    (h : y % 2 ^ k = 1) (hz : z = y % 2 ^ 64)
    (ht : t ≤ 2 * k) (ht64 : t ≤ 64) :
    ((2 ^ t : Nat) : Int) ∣
      (y : Int) * (((2 ^ 64 - z + 2 : Nat) : Int)) - 1 := by
  let T : Nat := 2 ^ t
  let W : Nat := 2 ^ 64
  have hT_dvd_kk_nat : T ∣ (2 ^ k) * (2 ^ k) := by
    have ht' : t ≤ k + k := by omega
    rw [← Nat.pow_add]
    exact Nat.pow_dvd_pow 2 ht'
  have hT_dvd_kk : (T : Int) ∣ (((2 ^ k) * (2 ^ k) : Nat) : Int) :=
    int_dvd_of_nat_dvd hT_dvd_kk_nat
  have hstd_big := nat_newton_refine_dvd y k h
  have hstd : (T : Int) ∣ (y : Int) * (2 - (y : Int)) - 1 := by
    rcases hT_dvd_kk with ⟨a, ha⟩
    rcases hstd_big with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    simp only [T, Int.natCast_mul] at ha ⊢
    rw [hb, ha]
    grind
  have hT_dvd_W_nat : T ∣ W := by
    exact Nat.pow_dvd_pow 2 ht64
  have hT_dvd_W : (T : Int) ∣ (W : Int) := int_dvd_of_nat_dvd hT_dvd_W_nat
  have hdecomp : z + W * (y / W) = y := by
    have h0 := Nat.mod_add_div y W
    rw [← hz] at h0
    exact h0
  have hWbase : (W : Int) ∣ (W : Int) + (y : Int) - (z : Int) := by
    refine ⟨1 + ((y / W : Nat) : Int), ?_⟩
    have hdecompInt := congrArg (fun n : Nat => (n : Int)) hdecomp
    simp only [Int.natCast_add, Int.natCast_mul] at hdecompInt
    simp only [W] at hdecompInt ⊢
    omega
  have hbase : (T : Int) ∣ (W : Int) + (y : Int) - (z : Int) := by
    rcases hT_dvd_W with ⟨a, ha⟩
    rcases hWbase with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    simp only [T] at ha ⊢
    rw [hb, ha]
    grind
  have hwrapDiff :
      (((2 ^ 64 - z + 2 : Nat) : Int) - (2 - (y : Int))) =
        (W : Int) + (y : Int) - (z : Int) := by
    have hzle : z ≤ W := by
      rw [hz]
      exact Nat.le_of_lt (Nat.mod_lt y (Nat.two_pow_pos 64))
    simp only [W]
    omega
  have hdelta : (T : Int) ∣
      (y : Int) * ((((2 ^ 64 - z + 2 : Nat) : Int) - (2 - (y : Int)))) := by
    rcases hbase with ⟨a, ha⟩
    refine ⟨(y : Int) * a, ?_⟩
    rw [hwrapDiff, ha]
    grind
  have hsum : (T : Int) ∣
      ((y : Int) * ((((2 ^ 64 - z + 2 : Nat) : Int) - (2 - (y : Int)))) +
        ((y : Int) * (2 - (y : Int)) - 1)) :=
    Int.dvd_add hdelta hstd
  rcases hsum with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [← hq]
  grind

private theorem nat_mod_eq_one_of_int_dvd_sub_one {T n : Nat} (hT : 1 < T)
    (h : (T : Int) ∣ (n : Int) - 1) :
    n % T = 1 := by
  rcases h with ⟨q, hq⟩
  have hq_nonneg : 0 ≤ q := by
    by_cases hq_nonneg : 0 ≤ q
    · exact hq_nonneg
    · have hqneg : q < 0 := by omega
      have hprod_le : (T : Int) * q ≤ 2 * q :=
        Int.mul_le_mul_of_nonpos_right (by omega : (2 : Int) ≤ (T : Int)) (by omega)
      have hprod : (T : Int) * q ≤ -2 := by omega
      have hlower : -1 ≤ (n : Int) - 1 := by omega
      rw [hq] at hlower
      omega
  have hn_eq : n = T * q.toNat + 1 := by
    have hcast : ((n : Int) - 1) = (T * q.toNat : Nat) := by
      rw [hq, ← Int.toNat_of_nonneg hq_nonneg]
      simp
    omega
  rw [hn_eq]
  simp [Nat.mod_eq_of_lt hT]

private theorem int_dvd_sub_one_of_nat_mod_eq_one {T n : Nat} (h : n % T = 1) :
    (T : Int) ∣ (n : Int) - 1 := by
  have hdecomp := Nat.mod_add_div n T
  rw [h] at hdecomp
  refine ⟨((n / T : Nat) : Int), ?_⟩
  have hdecompInt := congrArg (fun m : Nat => (m : Int)) hdecomp
  simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] at hdecompInt
  omega

private theorem nat_mod_eq_pred_of_int_dvd_add_one {T n : Nat} (hT : 1 < T)
    (h : (T : Int) ∣ (n : Int) + 1) :
    n % T = T - 1 := by
  rcases h with ⟨q, hq⟩
  have hq_pos : 0 < q := by
    by_cases hqpos : 0 < q
    · exact hqpos
    · have hqnonpos : q ≤ 0 := by omega
      have hprodnonpos : (T : Int) * q ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hqnonpos
      omega
  have hn_eq : n + 1 = T * q.toNat := by
    have hcast : ((n : Int) + 1) = (T * q.toNat : Nat) := by
      rw [hq, ← Int.toNat_of_nonneg (by omega : 0 ≤ q)]
      simp
    omega
  have hq_nat_pos : 0 < q.toNat := by omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q.toNat ≠ 0)
  rw [hr] at hn_eq
  have hn_split : n = T * r + (T - 1) := by grind
  rw [hn_split]
  rw [Nat.add_mod]
  simp [Nat.mod_eq_of_lt (by omega : T - 1 < T)]

private theorem odd_square_mod_eight (n : Nat) (hodd : n % 2 = 1) :
    n * n % 8 = 1 := by
  obtain ⟨q, hq⟩ : ∃ q, n = 2 * q + 1 := by
    refine ⟨n / 2, ?_⟩
    have h := Nat.mod_add_div n 2
    rw [hodd] at h
    omega
  subst n
  have hqmod : q % 2 = 0 ∨ q % 2 = 1 := by
    have hlt := Nat.mod_lt q (by omega : 0 < 2)
    omega
  rcases hqmod with hqmod | hqmod
  · obtain ⟨r, hr⟩ : ∃ r, q = 2 * r := by
      refine ⟨q / 2, ?_⟩
      have h := Nat.mod_add_div q 2
      rw [hqmod] at h
      omega
    subst q
    have hsq : (2 * (2 * r) + 1) * (2 * (2 * r) + 1) =
        8 * (2 * r * r + r) + 1 := by
      grind
    rw [hsq]
    simp
  · obtain ⟨r, hr⟩ : ∃ r, q = 2 * r + 1 := by
      refine ⟨q / 2, ?_⟩
      have h := Nat.mod_add_div q 2
      rw [hqmod] at h
      omega
    subst q
    have hsq : (2 * (2 * r + 1) + 1) * (2 * (2 * r + 1) + 1) =
        8 * (2 * r * r + 3 * r + 1) + 1 := by
      grind
    rw [hsq]
    simp

private theorem montPosInvStep_mod_refine (p x : UInt64) {k t : Nat}
    (hx : p.toNat * x.toNat % 2 ^ k = 1)
    (htpos : 0 < t) (ht : t ≤ 2 * k) (ht64 : t ≤ 64) :
    p.toNat * (montPosInvStep p x).toNat % 2 ^ t = 1 := by
  unfold montPosInvStep
  let y := p.toNat * x.toNat
  let z := (p * x).toNat
  have hz_mod : z % 2 ^ 64 = y % 2 ^ 64 := by
    change (p * x).toNat % 2 ^ 64 = (p.toNat * x.toNat) % 2 ^ 64
    exact UInt64.toNat_mul_mod_two_pow (a := p) (b := x) (t := 64) (by omega)
  have hz : z = y % 2 ^ 64 := by
    rw [← hz_mod]
    have hzlt : z < 2 ^ 64 := by
      simpa [z, UInt64.size, UInt64.word] using UInt64.toNat_lt_size (p * x)
    exact (Nat.mod_eq_of_lt hzlt).symm
  have hsub :
      (2 - p * x).toNat % 2 ^ t =
        (2 ^ 64 - z + 2) % 2 ^ t := by
    simpa [z, Nat.add_comm] using
      UInt64.toNat_sub_mod_two_pow (a := 2) (b := p * x) ht64
  have hmul :
      p.toNat * (x * (2 - p * x)).toNat % 2 ^ t =
        (y * (2 ^ 64 - z + 2)) % 2 ^ t := by
    calc
      p.toNat * (x * (2 - p * x)).toNat % 2 ^ t
          = p.toNat * ((x * (2 - p * x)).toNat % 2 ^ t) % 2 ^ t := by
            rw [Nat.mul_mod_mod]
      _ = p.toNat * ((x.toNat * (2 - p * x).toNat) % 2 ^ t) % 2 ^ t := by
            rw [UInt64.toNat_mul_mod_two_pow (a := x) (b := 2 - p * x) ht64]
      _ = p.toNat * (x.toNat * (2 - p * x).toNat) % 2 ^ t := by
            rw [Nat.mul_mod_mod]
      _ = y * (2 - p * x).toNat % 2 ^ t := by
            simp [y, Nat.mul_assoc]
      _ = y * ((2 - p * x).toNat % 2 ^ t) % 2 ^ t := by
            rw [Nat.mul_mod_mod]
      _ = y * ((2 ^ 64 - z + 2) % 2 ^ t) % 2 ^ t := by
            rw [hsub]
      _ = y * (2 ^ 64 - z + 2) % 2 ^ t := by
            rw [Nat.mul_mod_mod]
  rw [hmul]
  apply nat_mod_eq_one_of_int_dvd_sub_one
  · exact Nat.one_lt_pow (by omega : t ≠ 0) (by omega : 1 < 2)
  · simpa only [Int.natCast_mul] using
      nat_newton_refine_wrapped_dvd y z k t hx hz ht ht64

/--
Starting from the odd-modulus seed `x = p`, five refinement steps lift the
inverse from mod `2^3` to mod `2^96 ≥ 2^64`.
-/
def montPosInv (p : UInt64) : UInt64 :=
  let x1 := montPosInvStep p p
  let x2 := montPosInvStep p x1
  let x3 := montPosInvStep p x2
  let x4 := montPosInvStep p x3
  montPosInvStep p x4

/-- The user-facing Montgomery inverse is the negated positive inverse. -/
def montInv (p : UInt64) : UInt64 :=
  0 - montPosInv p

/-- The positive Montgomery inverse satisfies `p * x ≡ 1 (mod 2^64)`. -/
theorem montPosInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montPosInv p).toNat % UInt64.word = 1 := by
  let x1 := montPosInvStep p p
  let x2 := montPosInvStep p x1
  let x3 := montPosInvStep p x2
  let x4 := montPosInvStep p x3
  have hx0 : p.toNat * p.toNat % 2 ^ 3 = 1 := by
    simpa using odd_square_mod_eight p.toNat hp_odd
  have hx1 : p.toNat * x1.toNat % 2 ^ 6 = 1 := by
    simpa [x1] using
      montPosInvStep_mod_refine (p := p) (x := p) (k := 3) (t := 6)
        hx0 (by omega) (by omega) (by omega)
  have hx2 : p.toNat * x2.toNat % 2 ^ 12 = 1 := by
    simpa [x2] using
      montPosInvStep_mod_refine (p := p) (x := x1) (k := 6) (t := 12)
        hx1 (by omega) (by omega) (by omega)
  have hx3 : p.toNat * x3.toNat % 2 ^ 24 = 1 := by
    simpa [x3] using
      montPosInvStep_mod_refine (p := p) (x := x2) (k := 12) (t := 24)
        hx2 (by omega) (by omega) (by omega)
  have hx4 : p.toNat * x4.toNat % 2 ^ 48 = 1 := by
    simpa [x4] using
      montPosInvStep_mod_refine (p := p) (x := x3) (k := 24) (t := 48)
        hx3 (by omega) (by omega) (by omega)
  have hx5 :
      p.toNat * (montPosInvStep p x4).toNat % 2 ^ 64 = 1 := by
    simpa using
      montPosInvStep_mod_refine (p := p) (x := x4) (k := 48) (t := 64)
        hx4 (by omega) (by omega) (by omega)
  simpa [montPosInv, x1, x2, x3, x4, UInt64.word] using hx5

/-- The negated Montgomery inverse satisfies `p * p' ≡ -1 (mod 2^64)`. -/
theorem montInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montInv p).toNat % UInt64.word = UInt64.word - 1 := by
  let x := (montPosInv p).toNat
  let W := UInt64.word
  have hpos : p.toNat * x % W = 1 := by
    simpa [x] using montPosInv_spec p hp_odd
  have hxlt : x < W := by
    simpa [x, W, UInt64.word, UInt64.size] using UInt64.toNat_lt_size (montPosInv p)
  have hsub :
      (montInv p).toNat % W = (W - x) % W := by
    simp [montInv, x, W, UInt64.word]
  have hmul :
      p.toNat * (montInv p).toNat % W = p.toNat * (W - x) % W := by
    calc
      p.toNat * (montInv p).toNat % W
          = p.toNat * ((montInv p).toNat % W) % W := by
            rw [Nat.mul_mod_mod]
      _ = p.toNat * ((W - x) % W) % W := by rw [hsub]
      _ = p.toNat * (W - x) % W := by rw [Nat.mul_mod_mod]
  rw [hmul]
  apply nat_mod_eq_pred_of_int_dvd_add_one
  · simp [W, UInt64.word]
  · have hpx : (W : Int) ∣ ((p.toNat * x : Nat) : Int) - 1 :=
      int_dvd_sub_one_of_nat_mod_eq_one hpos
    have hpW : (W : Int) ∣ ((p.toNat * W : Nat) : Int) := by
      refine ⟨(p.toNat : Int), ?_⟩
      simp [Nat.mul_comm]
    have hdiff := Int.dvd_sub hpW hpx
    rcases hdiff with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [← hq]
    have hmul_sub : p.toNat * (W - x) = p.toNat * W - p.toNat * x := by
      exact Nat.mul_sub_left_distrib p.toNat W x
    have hxle : x ≤ W := Nat.le_of_lt hxlt
    have hmul_sub_cast :
        ((p.toNat * (W - x) : Nat) : Int) =
          ((p.toNat * W : Nat) : Int) - ((p.toNat * x : Nat) : Int) := by
      rw [hmul_sub]
      exact Int.natCast_sub (Nat.mul_le_mul_left p.toNat hxle)
    omega
