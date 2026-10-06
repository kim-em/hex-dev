# Short-chain degree family: independent derivation

Let P=2X^n−1, F=1 and the endpoints be −1 and 1, with even registered
n=16384,32768,65536,131072. The open interval contains both real roots.
Degree grows while chain length remains three. Input construction and
validation use the existing producers; no replacement Sturm computation is
implemented. Preparation checks both query backends' value and the stored
squarefree chain length, including the small smoke parameters clamped to two.

`Sturm.normalize` divides by the absolute leading coefficient. Its squarefree
chain is P, X^(n−1), 1. The derivative's normalization factor is 2n.
The subsequent pseudo-divisions have d=2 with m=n−1, then d=n with m=0.
`DensePoly.pseudoDivMod` therefore has O(d*m)=O(n) correction summands,
O(n) powers/active/quotient/remainder entries and fixed-size scalars. The
terminal divisor is one: its n powers do not grow. The integer backend's
positive-content normalization gives the same short chain and bounded scalars.
All stored scalars are within fixed word sizes on this declared ladder; this
is a family-specific word-arithmetic model, not a general bit-cost bound.

At endpoints ±1 Horner never grows its accumulators with n. Each pass traverses
P and X^(n−1), hence Θ(n) work. Both infinity signs would be cheaper, but this
family keeps finite endpoint work in every count and certificate. Literal
replay multiplies a linear quotient by a degree-(n−1) monomial, or a
length-n quotient by a constant; the dense convolution work is Θ(n).
The remaining scalar products, binding comparisons and coefficient checks
are at most linear. Cached replay still verifies the query certificate.
Denominator clearing and embedding traverse the literal length-n arrays;
all denominators are one and scalar hashes have fixed word cost. Full
certificate hashes likewise traverse all coefficient arrays.

Every declared mode-1 family has a necessary Θ(n) traversal and no
higher-order phase. Result-only queries and count return a small scalar,
but still execute the actual producer or finite endpoint evaluation inside
the timed body. The derivation applies to domain preparation, full and
prepared queries/counts, full and prepared/count certificates, literal and
cached replay, clearing and embedding. It does not characterize long chains,
growing coefficient/endpoint bit height, extension signs or nested evidence.
The previously failed/inconclusive families remain unchanged and retained.

Declarations precede measurement: four fixed trial-major outer trials,
100 ms tuning target, the four compiled rungs and a 600-second operational
cap. The rational and integer whole-query comparators use identical inputs
and complete Option Int outputs, joined by actual hashes in four adjacent
alternating AB/BA blocks. Host activity is recorded and does not reject a
completed sample. No scientific observation or Phase-4 admission is claimed
by this derivation alone.
