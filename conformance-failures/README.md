# conformance-failures/

Empty by design.  Oracle drivers under `scripts/oracle/` write
JSON failure records here when an external oracle disagrees with
the Lean-side answer.  CI uploads the directory as a workflow
artifact so the failure is replayable from the recorded input.

The directory itself stays in git (via this README); the failure
records are gitignored — see the top-level `.gitignore`.
