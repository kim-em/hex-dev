# General kernel replay comparison

`final/results.json.gz` and `final/observations.jsonl.gz` retain the quiet
six-pair comparison, including separate route/axiom audits and per-arm import
baselines. `before`, `components`, `recursors`, `sharing` and `list_recursors`
retain two-pair diagnostic stages. `review_fixes` retains the two-pair recheck
after shared-budget and metavariable-closure fixes; its first pairs overlap
the downstream validation build. `diagnosis` contains the extra first-use
component check. No completed sample is filtered out.

All times are shared-host observations. Proof-work diagnostics exclude imports,
statement elaboration, serialization and Lake overhead. Quiet build deltas use
fresh module builds and import-only controls. The two metrics are not pooled.
The aggregate measurement time is about 9.1 minutes; setup/rebuilds are separate.
Each measured build has a 60-second limit. All measurements are serial and
there is no memory cap. The final campaign aborts on a timeout or error.

The `*.lean.txt` files are exact source snapshots, not executable benchmark
registrations. `Frontend.before` and `Kernel.before` are the baseline source;
`Frontend.components` and `Kernel.exponents` capture intermediate changes.
Each stage records hashes of its computational and frontend sources.
Failed development builds are retained as compressed logs. The original
executed Python scripts retain their original paths for provenance.

To repeat the final quiet comparison after `lake build`, run from the repository
root, with a new output directory:

```
python reports/bench-results/hex-det-tree/kernel-improvements/reproduce.py /tmp/det-kernel-recheck
```

This entrypoint uses the same runner as the recorded campaign, with input paths
made relative to this archive and the output directory supplied by the caller.
It creates temporary proof modules, deletes their source files on completion,
and retains their exact content with the results. It fails if the output
already exists. No monitor or service is installed.
