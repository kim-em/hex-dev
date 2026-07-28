rep=$1; k=$2
cat > T_${rep}_${k}.lean <<EOF
import MV
set_option maxRecDepth 100000 in
example : ((pow${rep} (gen${rep} 3) ${k}).toListX == (P${rep}.mul (pow${rep} (gen${rep} 3) $((k/2))) (pow${rep} (gen${rep} 3) $((k-k/2)))).toListX) = true := by
  decide +kernel
EOF
