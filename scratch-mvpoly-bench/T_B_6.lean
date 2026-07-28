import MV
set_option maxRecDepth 100000 in
example : ((powB (genB 3) 6).toListX == (PB.mul (powB (genB 3) 3) (powB (genB 3) 3)).toListX) = true := by
  decide +kernel
