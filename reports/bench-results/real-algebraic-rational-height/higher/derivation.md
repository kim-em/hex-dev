# Larger coefficient-height range

This range uses the same degree-one family and the same independently derived
linear model. The original 256–8192-bit ladder remains retained with its three
inconclusive verdicts. The native 131072-bit profile passes its diagnostics and
attributes most kernel work to single-limb division, copying and multiplication:
these traverse the coefficient limbs linearly. Canonical fixture preparation
is outside the kernel and is costly at that largest point.

The scheduled range is 8192,16384,32768,65536 bits, with four trial-major samples
at each point for recognition, floor and ceiling. This tests the linear limb
work at larger sizes without changing the expected exponent, arithmetic body
or input formula. The 600-second per-call override is an operational safeguard
for canonical preparation, not a performance budget. Every completed row and
any failure or inconclusive verdict is retained; host activity does not select
or reject samples.
