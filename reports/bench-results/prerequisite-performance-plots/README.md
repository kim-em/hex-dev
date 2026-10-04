# Prerequisite elapsed-time plots

These figures replot retained measurements, with actual elapsed time and
problem size on the axes. They contain no fitted complexity curve or invented
performance budget. Every completed trial is plotted, including leading
points excluded from earlier model verdicts. Shading and error bars show
observed min–max ranges, not statistical confidence intervals. Measurements
come from the shared `chungus2` host and retain their original source scope;
they are not new timings of the latest binary.

- [Sturm time and memory against degree](sturm-growth.png): sparse heads
  `2X^n−1` with constant query, and growing queries `X^m+1` against `X²−2`.
  The first family reaches about 566 ms over rationals versus 48 ms through
  the integer backend at degree 131072. The second reaches about 99 seconds
  and 32 GiB whole-child peak RSS at query degree 1048576, exposing expensive
  quotient materialization even for the value-only query.
- [Real-algebraic list and arithmetic costs](real-algebraic-costs.png): stored
  root-list construction and membership, sorting distinct rational root
  records, and the retained canonical arithmetic fixture. Adding/subtracting
  the positive root of `X⁶−2` and `√3` takes about 6.5 seconds and produces
  degree 12. The bare number-field parent has essentially the same cost.
  These fixed-size arithmetic bars are not a growth curve; the cheap stored
  list operations do not establish fast root production.
- [Fixed-degree Z3 RCF and FLINT comparisons](external-fixed-comparison.png):
  complete signed-root queries for `T_8` on `(-2,2)`. Adjacent alternating
  AB/BA comparisons check the full result hashes. Z3's count is approximately
  tied with Hex after measured transport adjustment. Black ticks show
  protocol-adjusted ratios alongside raw ratios; they do not isolate pure
  algorithm bodies. FLINT uses generic real-qqbar Horner evaluation, which is
  especially expensive for the common-factor query. Its result is not a
  claim about an optimized polynomial-evaluation implementation.

For each figure, SVG and PDF versions are provided alongside the PNG.
[plot.py](plot.py) regenerates them from the retained JSON using matplotlib
3.11.1 and numpy 2.5.3. [plot-inputs.json](plot-inputs.json) records every input
checksum. No existing timing observation or phase counter is changed.

A useful next comparison varies head degree across the same exact query
semantics, then varies coefficient height and root separation independently.
Canonical real-algebraic arithmetic should be compared with FLINT `qqbar`;
Z3 RCF supplies a different exact strategy, whose representation/materialization
boundary must be stated. Internal integer Sturm and bare number-field calls
remain useful for identifying wrapper and representation costs. A single
successful small example does not resolve the large-query memory issue or
the canonical-addition bottleneck.
