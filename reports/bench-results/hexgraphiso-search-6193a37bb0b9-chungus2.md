# Search comparison, 6193a37bb0b9

Both arms use the same `search` driver and corpus. The baseline is the
state consolidation at `dcc5e8c221a0c252a91ae55091891b7197c08583`; the
candidate is `e462a54c5` (source fingerprint `6193a37bb0b9`). The candidate
calls the shared inline recovery operation from the direct and generic
recursions. Raw files and sibling metadata retain executable digests,
commands and host load. Trials ran adjacent AB then BA on chungus2 CPU 6.

| Trial | Search time ratio | Nauty time ratio | Changed node counts |
|---|---:|---:|---:|
| 1 | 0.9934 | 1.0037 | 0 / 98 |
| 2 | 0.9971 | 0.9980 | 0 / 98 |

Ratios are candidate/baseline geometric means over all 98 cases. Every
completed sample is retained. These shared-host observations show no
material slowdown in this corpus; they do not establish a small speed
improvement. The full frozen trace regression separately checks all
39,032 operational outputs, including generator order and return control.
