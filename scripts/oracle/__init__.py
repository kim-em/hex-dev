"""Oracle drivers for the Hex conformance suite.

Each driver reads JSONL fixture/result records produced by Lean (see
`scripts/oracle/common.py` for the schema), invokes an external oracle
(python-flint, cypari2, fpylll, ...), and compares its output against
the Lean-side result.  Mismatches are written as JSON failure records
under ``conformance-failures/`` for replay.
"""
