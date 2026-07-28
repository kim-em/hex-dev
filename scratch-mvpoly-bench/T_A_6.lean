import MV
set_option maxRecDepth 100000 in
example : ((powA (genA 3) 6).toListX == (PA.mul (powA (genA 3) 3) (powA (genA 3) 3)).toListX) = true := by
  decide +kernel
