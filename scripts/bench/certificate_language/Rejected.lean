/- Intentionally rejected by the kernel; build separately and require failure. -/
module
public import PrimeCert
public section
example : Nat.Prime 15 := prime_cert% [small 2, pock (15, 2, 2)]
