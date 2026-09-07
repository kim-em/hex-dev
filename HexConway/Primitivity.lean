module

public import HexConway.PrimitivityCore

public section

namespace Hex
namespace Conway

set_option maxRecDepth 1000000
set_option maxHeartbeats 80000000

-- BEGIN GENERATED
/-- C(2, 1) has a generator of order 1. -/
theorem primitive_2_1 :
    Primitive 2 1 supportedEntry_2_1 [] []
      [1] [] where
  primes := by
    intro q hq
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(2, 2) has a generator of order 3. -/
theorem primitive_2_2 :
    Primitive 2 2 supportedEntry_2_2 [3] [1]
      [1, 1] [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(2, 3) has a generator of order 7. -/
theorem primitive_2_3 :
    Primitive 2 3 supportedEntry_2_3 [7] [1]
      [1, 1, 1] [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(2, 4) has a generator of order 15. -/
theorem primitive_2_4 :
    Primitive 2 4 supportedEntry_2_4 [3, 5] [1, 1]
      [1, 1, 1, 1] [[1, 0, 1], [1, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(2, 5) has a generator of order 31. -/
theorem primitive_2_5 :
    Primitive 2 5 supportedEntry_2_5 [31] [1]
      [1, 1, 1, 1, 1] [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 31) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(2, 6) has a generator of order 63. -/
theorem primitive_2_6 :
    Primitive 2 6 supportedEntry_2_6 [3, 7] [2, 1]
      [1, 1, 1, 1, 1, 1] [[1, 0, 1, 0, 1], [1, 0, 0, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(2, 7) has a generator of order 127. -/
theorem primitive_2_7 :
    Primitive 2 7 supportedEntry_2_7 [127] [1]
      [1, 1, 1, 1, 1, 1, 1] [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 127 [(3, 0, .small 2), (3, 1, .small 3), (2, 0, .small 7)]) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(2, 8) has a generator of order 255. -/
theorem primitive_2_8 :
    Primitive 2 8 supportedEntry_2_8 [3, 5, 17] [1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1] [[1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 1], [1, 1, 1, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 17) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(3, 1) has a generator of order 2. -/
theorem primitive_3_1 :
    Primitive 3 1 supportedEntry_3_1 [2] [1]
      [1, 0] [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(3, 2) has a generator of order 8. -/
theorem primitive_3_2 :
    Primitive 3 2 supportedEntry_3_2 [2] [3]
      [1, 0, 0, 0] [[1, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(3, 3) has a generator of order 26. -/
theorem primitive_3_3 :
    Primitive 3 3 supportedEntry_3_3 [2, 13] [1, 1]
      [1, 1, 0, 1, 0] [[1, 1, 0, 1], [1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 13) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(3, 4) has a generator of order 80. -/
theorem primitive_3_4 :
    Primitive 3 4 supportedEntry_3_4 [2, 5] [4, 1]
      [1, 0, 1, 0, 0, 0, 0] [[1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(3, 5) has a generator of order 242. -/
theorem primitive_3_5 :
    Primitive 3 5 supportedEntry_3_5 [2, 11] [1, 2]
      [1, 1, 1, 1, 0, 0, 1, 0] [[1, 1, 1, 1, 0, 0, 1], [1, 0, 1, 1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 11) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(3, 6) has a generator of order 728. -/
theorem primitive_3_6 :
    Primitive 3 6 supportedEntry_3_6 [2, 7, 13] [3, 1, 1]
      [1, 0, 1, 1, 0, 1, 1, 0, 0, 0] [[1, 0, 1, 1, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 13) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(5, 1) has a generator of order 4. -/
theorem primitive_5_1 :
    Primitive 5 1 supportedEntry_5_1 [2] [2]
      [1, 0, 0] [[1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(5, 2) has a generator of order 24. -/
theorem primitive_5_2 :
    Primitive 5 2 supportedEntry_5_2 [2, 3] [3, 1]
      [1, 1, 0, 0, 0] [[1, 1, 0, 0], [1, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(5, 3) has a generator of order 124. -/
theorem primitive_5_3 :
    Primitive 5 3 supportedEntry_5_3 [2, 31] [2, 1]
      [1, 1, 1, 1, 1, 0, 0] [[1, 1, 1, 1, 1, 0], [1, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 31) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(5, 4) has a generator of order 624. -/
theorem primitive_5_4 :
    Primitive 5 4 supportedEntry_5_4 [2, 3, 13] [4, 1, 1]
      [1, 0, 0, 1, 1, 1, 0, 0, 0, 0] [[1, 0, 0, 1, 1, 1, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 13) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(5, 5) has a generator of order 3124. -/
theorem primitive_5_5 :
    Primitive 5 5 supportedEntry_5_5 [2, 11, 71] [2, 1, 1]
      [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0] [[1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0], [1, 0, 0, 0, 1, 1, 1, 0, 0], [1, 0, 1, 1, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 11) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 71) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(5, 6) has a generator of order 15624. -/
theorem primitive_5_6 :
    Primitive 5 6 supportedEntry_5_6 [2, 3, 7, 31] [3, 2, 1, 1]
      [1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0] [[1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 31) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(7, 1) has a generator of order 6. -/
theorem primitive_7_1 :
    Primitive 7 1 supportedEntry_7_1 [2, 3] [1, 1]
      [1, 1, 0] [[1, 1], [1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(7, 2) has a generator of order 48. -/
theorem primitive_7_2 :
    Primitive 7 2 supportedEntry_7_2 [2, 3] [4, 1]
      [1, 1, 0, 0, 0, 0] [[1, 1, 0, 0, 0], [1, 0, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(7, 3) has a generator of order 342. -/
theorem primitive_7_3 :
    Primitive 7 3 supportedEntry_7_3 [2, 3, 19] [1, 2, 1]
      [1, 0, 1, 0, 1, 0, 1, 1, 0] [[1, 0, 1, 0, 1, 0, 1, 1], [1, 1, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 19) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(7, 4) has a generator of order 2400. -/
theorem primitive_7_4 :
    Primitive 7 4 supportedEntry_7_4 [2, 3, 5] [5, 1, 2]
      [1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0] [[1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(7, 5) has a generator of order 16806. -/
theorem primitive_7_5 :
    Primitive 7 5 supportedEntry_7_5 [2, 3, 2801] [1, 1, 1]
      [1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0] [[1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0], [1, 1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 2801 [(3, 3, .small 2), (2, 1, .small 5), (2, 0, .small 7)]) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(7, 6) has a generator of order 117648. -/
theorem primitive_7_6 :
    Primitive 7 6 supportedEntry_7_6 [2, 3, 19, 43] [4, 2, 1, 1]
      [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0] [[1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 19) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 43) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(11, 1) has a generator of order 10. -/
theorem primitive_11_1 :
    Primitive 11 1 supportedEntry_11_1 [2, 5] [1, 1]
      [1, 0, 1, 0] [[1, 0, 1], [1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(11, 2) has a generator of order 120. -/
theorem primitive_11_2 :
    Primitive 11 2 supportedEntry_11_2 [2, 3, 5] [3, 1, 1]
      [1, 1, 1, 1, 0, 0, 0] [[1, 1, 1, 1, 0, 0], [1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(11, 3) has a generator of order 1330. -/
theorem primitive_11_3 :
    Primitive 11 3 supportedEntry_11_3 [2, 5, 7, 19] [1, 1, 1, 1]
      [1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0] [[1, 0, 1, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 1, 1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 19) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(11, 4) has a generator of order 14640. -/
theorem primitive_11_4 :
    Primitive 11 4 supportedEntry_11_4 [2, 3, 5, 61] [4, 1, 1, 1]
      [1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0] [[1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 61) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(11, 5) has a generator of order 161050. -/
theorem primitive_11_5 :
    Primitive 11 5 supportedEntry_11_5 [2, 5, 3221] [1, 2, 1]
      [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0] [[1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1], [1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 3221 [(2, 1, .small 2), (5, 0, .small 5), (2, 0, .small 7), (2, 0, .small 23)]) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(11, 6) has a generator of order 1771560. -/
theorem primitive_11_6 :
    Primitive 11 6 supportedEntry_11_6 [2, 3, 5, 7, 19, 37] [3, 2, 1, 1, 1, 1]
      [1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] [[1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 19) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 37) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(13, 1) has a generator of order 12. -/
theorem primitive_13_1 :
    Primitive 13 1 supportedEntry_13_1 [2, 3] [2, 1]
      [1, 1, 0, 0] [[1, 1, 0], [1, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(13, 2) has a generator of order 168. -/
theorem primitive_13_2 :
    Primitive 13 2 supportedEntry_13_2 [2, 3, 7] [3, 1, 1]
      [1, 0, 1, 0, 1, 0, 0, 0] [[1, 0, 1, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(13, 3) has a generator of order 2196. -/
theorem primitive_13_3 :
    Primitive 13 3 supportedEntry_13_3 [2, 3, 61] [2, 2, 1]
      [1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0] [[1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 61) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(13, 4) has a generator of order 28560. -/
theorem primitive_13_4 :
    Primitive 13 4 supportedEntry_13_4 [2, 3, 5, 7, 17] [4, 1, 1, 1, 1]
      [1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0] [[1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 5) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 17) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(13, 5) has a generator of order 371292. -/
theorem primitive_13_5 :
    Primitive 13 5 supportedEntry_13_5 [2, 3, 30941] [2, 1, 1]
      [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0] [[1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0], [1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 30941 [(2, 1, .small 2), (2, 0, .small 5), (2, 0, .small 7), (2, 0, .small 13), (2, 0, .small 17)]) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

/-- C(13, 6) has a generator of order 4826808. -/
theorem primitive_13_6 :
    Primitive 13 6 supportedEntry_13_6 [2, 3, 7, 61, 157] [3, 2, 1, 1, 1]
      [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0] [[1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0], [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 2) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 3) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 7) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .small 61) (by decide +kernel)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 157 [(2, 1, .small 2), (3, 0, .small 3), (2, 0, .small 13)]) (by decide +kernel)
    exact absurd hq (by simp)
  check := by decide +kernel

-- END GENERATED

end Conway
end Hex
