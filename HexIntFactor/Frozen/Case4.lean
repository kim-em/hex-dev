module

public import HexIntFactor.Replay

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[expose] def Hex.IntFactorFrozen.case4 : Hex.Nat.Factorization :=
  ⟨5865086737153646739775266298177935466733017070941921214531039, [⟨1, (Hex.Nat.PrimeCert.pock 2013265921 [(11, 26, (Hex.Nat.PrimeCert.small 2))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3 926510094425921 253301 1806 253300 [(3, 5, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 41)), (2, 0, (Hex.Nat.PrimeCert.small 193))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3 1363620137403810529 3662353 119440 3662352 [(7, 4, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 197)), (2, 0, (Hex.Nat.PrimeCert.small 379))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3Sieve 2305843009213693951 523073 1689203 523060 2 [(3, 0, (Hex.Nat.PrimeCert.small 2)), (3, 1, (Hex.Nat.PrimeCert.small 5)), (3, 0, (Hex.Nat.PrimeCert.small 13)), (3, 0, (Hex.Nat.PrimeCert.small 31)), (3, 0, (Hex.Nat.PrimeCert.small 41))])⟩]⟩

@[expose] def Hex.IntFactorFrozen.case4_checked : Hex.Nat.CheckedFactorization 5865086737153646739775266298177935466733017070941921214531039 :=
  ⟨Hex.IntFactorFrozen.case4, rfl, by decide +kernel⟩
