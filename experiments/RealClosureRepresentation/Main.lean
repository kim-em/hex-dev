import Prototype
import Search
open Prototype

def main : IO Unit := do
  IO.println s!"finite-witness total sign: {Search.result}"
  IO.println s!"structurally equal roots: {decide (root = (1 : Rep))}"
  IO.println s!"zero difference: {decide (root - 1 = (0 : Rep))}"
  IO.println s!"normalized size: {p.size}"
  IO.println s!"division remainder zero: {decide (remainder = 0)}"
  IO.println s!"gcd degree: {(Hex.DensePoly.gcd product a).natDegree}"
  IO.println s!"xgcd degree: {(Hex.DensePoly.xgcd product a).gcd.natDegree}"
