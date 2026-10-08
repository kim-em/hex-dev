# First-level generators as products of inputs

A `perm_group` certificate's first level used to keep every distinct
non-identity input as a generator, because the checker required each
first-level generator to be an input or an input's inverse. The checker's work
at a level is one sift per generator and orbit point, so a first level with many
inputs is expensive. The first level now records, for each generator, the input
indices whose product it is, and the producer chooses fewer such products than
there are inputs when it can: one input whose order is the group's, or two or
three products of three inputs, and then of eight.

Certificate sizes, counted as Schreier pairs (generators times orbit points,
summed over levels):

| group | inputs | first-level generators before | after | pairs before | after |
|---|---|---|---|---|---|
| Rubik's cube | 6 | 6 | 2 | 671 | 605 |
| cube reassembly | 9 | 9 | 3 | 932 | 788 |

Groups with two inputs, such as the sporadic groups of
`reports/data/perm-group-gap-comparison/groups.json`, are unchanged.

Kernel time of the order proof, `lake lean` on the files of
`reports/data/perm-group-gap-comparison/`, alternating before and after on
2026-10-08 on a heavily loaded shared machine (load average 85 to 130), so the
absolute times are inflated; "before" is
https://github.com/kim-em/hex-dev/pull/10848:

| group | before | after | before | after |
|---|---|---|---|---|
| Rubik's cube | 9.8 s | 6.7 s | 9.6 s | 7.7 s |
| cube reassembly | 13.3 s | 7.5 s | 10.0 s | 5.5 s |

These are exploratory observations, not measurements under the paired protocol
of `SPEC/benchmarking.md`.
