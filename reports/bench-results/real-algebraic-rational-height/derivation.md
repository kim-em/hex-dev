# Degree-one rational height family

Let `A = 2^b - 1`, `D = 2^b + 1` and `q = A/D`, at the registered rungs
`b = 256,512,1024,2048,4096,8192`. Both integers are odd and coprime: Euclidean
division gives `D mod A = 2`, `A mod 2 = 1`, then zero. The canonical minimal
polynomial of `q` is the primitive linear polynomial `D*X-A`. This changes the
actual coefficient height of one leaf while fixing its degree at one.

Preparation constructs the canonical real value using the existing `ofRat`
and checks its degree and recognition against the independently supplied `q`.
Preparation and input hashing are excluded from the operation measurement.
No root representation or arithmetic algorithm is replaced.

`runRationalRecognition` calls the implemented `toRat?`. It reads the linear
coefficients and normalizes their rational quotient. The large gcd's bounded
Euclidean quotient sequence reduces to subtraction and one-word modular
reduction on `b`-bit operands. In this classical word-volume regime those
operations read a linear number of limbs, giving the mode-1 candidate `Θ(b)`.
This is a family-specific model, not a general gcd bit-complexity claim.

`runRationalFloor` and `runRationalCeil` call the actual rational-first rounding
APIs on the same leaf. Recognition supplies the linear work; rounding a
positive numerator smaller than its denominator adds at most linear work.
Their mode-1 candidates are also `Θ(b)`; the independent expected results are
floor zero and ceiling one. These families cover the rational branch only.
They do not establish nonrational rounding, rational construction, arbitrary
coefficient gcd costs, or growth of a root exactification problem.

The declared schedule has four trials in the harness's fixed trial-major
order. Every completed sample and any failed or inconclusive verdict is retained;
an automatic fit or a convenient replacement exponent does not admit the model.
