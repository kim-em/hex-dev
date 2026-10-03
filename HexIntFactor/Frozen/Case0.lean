module

public import HexIntFactor.Replay

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[expose] def Hex.IntFactorFrozen.case0 : Hex.Nat.Factorization :=
  ⟨1263407822267091861725148110322209, [⟨1, (Hex.Nat.PrimeCert.pock3 926510094425921 253301 1806 253300 [(3, 5, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 41)), (2, 0, (Hex.Nat.PrimeCert.small 193))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3 1363620137403810529 3662353 119440 3662352 [(7, 4, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 197)), (2, 0, (Hex.Nat.PrimeCert.small 379))])⟩]⟩

@[expose] def Hex.IntFactorFrozen.case0_checked : Hex.Nat.CheckedFactorization 1263407822267091861725148110322209 :=
  ⟨Hex.IntFactorFrozen.case0, rfl, by decide +kernel⟩
