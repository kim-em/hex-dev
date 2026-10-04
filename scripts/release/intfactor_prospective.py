"""Prospective factor-library release inputs; no repository is registered for publication."""

ENTRY = dict(
    repo="prospective/hex-int-factor", lib="HexIntFactor", umbrella=True,
    spec="hex-int-factor", lakefile="lean",
    build_modules=["HexIntFactor.Pari", "HexIntFactor.Export", "HexIntFactor.Replay"] +
                  [f"HexIntFactor.Mixed.{m}" for m in ("Replay", "Import", "Pari", "Export")],
    test_modules=["HexIntFactor.ImportTests", "HexIntFactor.PariTests",
                  "HexIntFactor.ExportTests", "HexIntFactor.Mixed.ImportTests",
                  "HexIntFactor.Mixed.ExportTests"] +
                 [f"HexIntFactor.Mixed.Frozen.{m}" for m in ("Small", "CaseA", "CaseB", "Partial")] +
                 [f"HexIntFactor.Frozen.Case{i}" for i in range(7)] +
                 ["HexIntFactor.Frozen.Partial12"],
)
