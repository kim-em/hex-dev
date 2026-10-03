module

public import HexIntFactor.Replay

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[expose] def Hex.IntFactorFrozen.case3 : Hex.Nat.Factorization :=
  ⟨53739425505922110098241478198196257576470600960682015825098539243996639, [⟨1, (Hex.Nat.PrimeCert.pock3 926510094425921 253301 1806 253300 [(3, 5, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 41)), (2, 0, (Hex.Nat.PrimeCert.small 193))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3 1363620137403810529 3662353 119440 3662352 [(7, 4, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 197)), (2, 0, (Hex.Nat.PrimeCert.small 379))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3Sieve 2305843009213693951 523073 1689203 523060 2 [(3, 0, (Hex.Nat.PrimeCert.small 2)), (3, 1, (Hex.Nat.PrimeCert.small 5)), (3, 0, (Hex.Nat.PrimeCert.small 13)), (3, 0, (Hex.Nat.PrimeCert.small 31)), (3, 0, (Hex.Nat.PrimeCert.small 41))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock 18446744069414584321 [(7, 31, (Hex.Nat.PrimeCert.small 2))])⟩]⟩

@[expose] def Hex.IntFactorFrozen.case3_checked : Hex.Nat.CheckedFactorization 53739425505922110098241478198196257576470600960682015825098539243996639 :=
  ⟨Hex.IntFactorFrozen.case3, rfl, by decide +kernel⟩
