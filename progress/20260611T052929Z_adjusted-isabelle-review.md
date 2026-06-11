# Progress: adjusted Isabelle-certified comparator review

## Accomplished

Reviewed the mid-PR change that subtracts a fixed `18.8 ms` Isabelle-certified
fork overhead from plotted comparator curves. Checked the surrounding report
text, plotting script, scaling script, regenerated-plot code path, and the
committed certified export values.

## Current frontier

The review found no direct plotting bug, but identified methodological and
provenance concerns around subtracting the whole trivial end-to-end overhead
and around applying an audit-host measurement to carica bench curves.

## Next step

Use the review findings to revise the PR text/code before merge, especially by
making the adjustment provenance explicit and guarding the adjusted series.

## Blockers

None.
