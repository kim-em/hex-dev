# Scalar controls with an independently prepared expected root

This superseded collection retains all 432 scheduled arms, including every
failed/capped native square-root arm. Four adjacent AB/BA blocks compare native,
FLINT qqbar and Z3 RCF operations, with persistent-protocol controls.
Its source is `6edf1b74d6`; source snapshots, executable hash, commands, CPU,
host context and the original `source_unchanged: false` remain in metadata.
The snapshot is preserved because benchmark/driver changes occurred while this
frozen executable was still running. The binary remains at its recorded
persistent path.

Expected sums and square roots were prepared outside timing. In Z3 this can
populate the same RCF context with the expected algebraic root. These ratios
are therefore warm expected-root controls, not the primary scalar comparison.
The [replacement comparison](../real-algebraic-scalar-annihilation/) instead
checks exact annihilation/sign without preconstructing the expected root.
No observations from this dataset are substituted into that comparison.

The [separate boundary diagnostic](../scalar-sqrt8-boundary/) records about
32.8 seconds of fixture preparation and 9.3 seconds for the square-root operation
on its named source. It explains why a 60-second whole-child cap is not an
operation-only lower bound. The unsuccessful scientific arms remain failed;
the diagnostic does not replace them or turn them into passes.
