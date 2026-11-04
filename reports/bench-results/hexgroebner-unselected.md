# Unselected F4 optimizations and compiler profiles

These independent experiments do not establish overall performance leadership. Their implementations and compiler profiles remain unselected. Every completed sample, outlier, failure, source snapshot and command is retained. Each full-system experiment has a first pass and its sole unchanged repeat; no further unchanged repeat is collected.

The baseline is the four-row packed provider `294f219094cd`, using native `clang version 21.1.8` and `clang version 23.1.0` (SDK) for generated C. All comparisons use degree scheduling, grevlex, complete reduced bases, one leased CPU per sweep and one algorithm thread. Adjacent comparisons alternate AB/BA. F₂ enables binary pivots in both arms; the prime controls disable them at p = 32003 and 2147483647. Each experiment retains 192 completed processes and 96 equal paired complete bases and logical statistics. Candidate timings exclude certificate generation, independent native verification and kernel checking.

## Exact hash overlay for virtual insertion buckets

A 128-slot exact-key overlay replaces linear searches among the at-most-64 virtual insertion buckets. Exact key comparisons resolve secondary collisions; a directed test exercises 39 such collisions. The existing atomic refusal and 4096-work contracts remain in force.

Runtime `e19677650562`. All twelve Clang/GCC sanitized variants and all nine project checks passed.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max |
|---|---:|---:|---:|---:|---|
| f2-false | 8 | 0.960168 | 0.964941 | 0.933857 | 0.431570 / 0.977399 / 1.260594 |
| f2-false-repeat | 5 | 0.963630 | 0.938123 | 0.931614 | 0.387943 / 0.975372 / 1.646915 |
| prime-control | 36 | 0.984485 | 0.984485 | 0.975675 | 0.257228 / 0.996789 / 4.265804 |
| prime-control-repeat | 60 | 1.084017 | 1.084017 | 1.085307 | 0.641296 / 1.019140 / 2.099732 |

The prime-control process ratio changes from 0.984485 to 1.084017; the repeated control regression and flagged insertion kernels do not support selecting this implementation for a broad performance gain.

## Lazy four-row XOR combinations

Four-row groups construct only combinations selected by targets, caching dependencies in the existing private table. Logical charges, sugar labels, bounded admission and workspace sizes remain unchanged. Directed tests check actual construction and group-use counters.

Runtime `1f2f6df212ed`. All twelve Clang/GCC sanitized variants and all nine project checks passed.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max |
|---|---:|---:|---:|---:|---|
| f2-false | 90 | 0.965205 | 0.956909 | 1.075093 | 0.439656 / 0.996289 / 1.248793 |
| f2-false-repeat | 53 | 1.021095 | 1.023856 | 1.003067 | 0.820827 / 1.009826 / 1.266342 |
| prime-control | 61 | 1.003924 | 1.003924 | 1.007700 | 0.870602 / 1.002767 / 1.180514 |
| prime-control-repeat | 76 | 1.002865 | 1.002865 | 1.001741 | 0.834195 / 1.001947 / 1.222607 |

The F₂ process ratio changes from 0.965205 to 1.021095. The overall gain does not reproduce.

## Clang 23 with generic x86-64

Only the native C compiler changes to Clang 23.1.3. The requested -march=native was stripped by the Nix wrapper: retained effective-target diagnostics identify x86-64. These results are therefore labelled generic, and do not measure native CPU tuning.

Runtime `294f219094cd`. All six Clang ASan/UBSan variants passed for this profile. The nine project checks were run for the unchanged source under the baseline configuration; no complete project audit under this alternative compiler profile is claimed.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max |
|---|---:|---:|---:|---:|---|
| f2-false | 48 | 0.974781 | 0.986166 | 0.966950 | 0.851881 / 0.959128 / 1.238550 |
| f2-false-repeat | 32 | 0.959886 | 0.969791 | 0.946931 | 0.798463 / 0.952203 / 1.160550 |
| prime-control | 61 | 0.969337 | 0.969337 | 0.954049 | 0.846464 / 0.956850 / 1.187012 |
| prime-control-repeat | 56 | 0.957947 | 0.957947 | 0.951490 | 0.813628 / 0.952824 / 1.169307 |

The compiler profile remains a candidate pending the complete nine-gate project audit under this compiler. Its observed gains remain documented separately from the runtime implementation; compiler selection is configurable.

## Clang 23 with znver5 tuning

The native C wrapper explicitly disables Nix’s native-target stripping and uses Clang 23.1.3 with -march=native. The effective-target diagnostic identifies znver5. Generated C retains the SDK compiler. This compares a combined compiler/ISA profile with the generic baseline.

Runtime `294f219094cd`. All six Clang ASan/UBSan variants passed for this profile. The nine project checks were run for the unchanged source under the baseline configuration; no complete project audit under this alternative compiler profile is claimed.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max |
|---|---:|---:|---:|---:|---|
| f2-false | 34 | 0.986683 | 1.000254 | 0.976296 | 0.850965 / 0.981348 / 1.267135 |
| f2-false-repeat | 50 | 0.984807 | 0.999191 | 0.959255 | 0.857423 / 0.977554 / 1.216126 |
| prime-control | 95 | 0.995393 | 0.995393 | 0.983004 | 0.851115 / 0.995364 / 1.239686 |
| prime-control-repeat | 6 | 0.988286 | 0.988286 | 0.975802 | 0.849684 / 0.984405 / 1.271315 |

No repeatable family-balanced F₂ gain is established. The complete project audit was also not run under this alternative compiler/ISA profile.

## Diagnostic limits

The insertion-overlay kernel’s first pass and sole longer-target repeat both remained clamped by the benchmark’s one-second per-call cap. All sixteen matched samples in each pass had signal flags. All records are retained; independently compiled checks validate the complete result hashes at every matched size. No kernel speed claim is made from those passes.

A separate non-timed ownership probe observed all ten F₂ cases. Complete outputs and logical statistics matched the frozen provider. Accepted inserting calls forced no shared table, arena or workspace copies. This rules out that particular copy hypothesis on these inputs; it does not rule out allocation or copying elsewhere. Four adjacent AB/BA user-cycle profiles of the packed providers are retained as diagnostics, without timing or acceptance claims.

The compiler experiments do not close the measured comparator gap or demonstrate that Lean language/runtime changes are necessary. The small suites do not meet the SPEC’s leadership acceptance requirements. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.

Raw capsule `f4-unselected-optimizations-294f219094cd.tar.xz`: SHA-256 `9202a44f406232084082fd1809d4be477b2db1372832bef7cfd87d94f6372d0f`.

```bash
python3 scripts/bench/groebner_unselected_report.py \
  --archive reports/bench-results/raw/f4-unselected-optimizations-294f219094cd.tar.xz \
  --report reports/bench-results/hexgroebner-unselected.md --check
```
