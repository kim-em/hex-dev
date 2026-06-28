#!/usr/bin/env python3
"""Publish the released split repos from this monorepo.

For each repo in scripts/release/released.yml (topological order), this:
  1. clones the repo's `main`,
  2. overwrites its *managed* paths from this monorepo (leaving lakefiles, CI,
     toolchains, LICENSE, README, manifests untouched),
  3. rewrites the root lakefile's cross-repo Hex pins to the commits synced
     this run,
  4. commits `chore: sync from hex-dev@<sha>` and pushes to `main`
     (unless --dry-run, which prints the planned changes and pin rewrites).

Auth (non-dry-run): a token from --token or $RELEASED_SYNC_PAT is used as an
`x-access-token` basic-auth credential for clone and push. Dry-run clones over
public https and never pushes.

Usage:
  python3 scripts/release/sync_released.py --dry-run
  RELEASED_SYNC_PAT=... python3 scripts/release/sync_released.py
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "release" / "released.yml"
BASELINE = REPO_ROOT / "scripts" / "release" / "synced.json"


def run(cmd: list[str], cwd: Path | None = None, capture: bool = False) -> str:
    result = subprocess.run(
        cmd, cwd=cwd, check=True, text=True,
        stdout=subprocess.PIPE if capture else None,
    )
    return (result.stdout or "").strip()


def clone_url(repo: str, token: str | None) -> str:
    if token:
        return f"https://x-access-token:{token}@github.com/{repo}.git"
    return f"https://github.com/{repo}.git"


def rsync_dir(src: Path, dest: Path, excludes: list[str] | None = None) -> None:
    """Mirror src/ onto dest/ (creating dest), deleting stale files under dest."""
    dest.mkdir(parents=True, exist_ok=True)
    cmd = ["rsync", "-a", "--delete"]
    for e in excludes or []:
        cmd += ["--exclude", e]
    cmd += [f"{src}/", f"{dest}/"]
    run(cmd)


def copy_file(src: Path, dest: Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dest)


def managed_paths(entry: dict) -> list[tuple[Path, Path, bool]]:
    """Yield (src, dest_rel, is_dir) managed mappings for one repo entry.

    Sources are absolute monorepo paths; dest_rel is relative to the repo root.
    """
    lib = entry["lib"]
    out: list[tuple[Path, Path, bool]] = []
    # explicit path list (e.g. hex-test-kit ships only `Hex/`)
    for p in entry.get("paths") or []:
        src = REPO_ROOT / p["src"]
        out.append((src, Path(p["dest"]), src.is_dir()))
    # conventional library source dir (minus its co-located SPEC/)
    if not entry.get("paths"):
        out.append((REPO_ROOT / lib, Path(lib), True))
    if entry.get("umbrella"):
        out.append((REPO_ROOT / f"{lib}.lean", Path(f"{lib}.lean"), False))
    if entry.get("spec"):
        slug = entry["spec"]
        out.append((REPO_ROOT / lib / "SPEC" / f"{slug}.md", Path("SPEC") / f"{slug}.md", False))
    if entry.get("bench"):
        bdir = entry.get("bench_dir", lib)
        out.append((REPO_ROOT / "bench" / bdir, Path("bench") / bdir, True))
        umb = REPO_ROOT / "bench" / f"{bdir}.lean"
        if umb.exists():
            out.append((umb, Path("bench") / f"{bdir}.lean", False))
    if entry.get("conformance"):
        out.append((REPO_ROOT / "conformance" / lib, Path("conformance") / lib, True))
    for f in entry.get("fixtures") or []:
        out.append((REPO_ROOT / "conformance-fixtures" / f, Path("conformance-fixtures") / f, True))
    for o in entry.get("oracles") or []:
        src = REPO_ROOT / "scripts" / "oracle" / o
        out.append((src, Path("scripts") / "oracle" / o, src.is_dir()))
    return out


def apply_paths(entry: dict, clone: Path) -> list[str]:
    notes: list[str] = []
    lib = entry["lib"]
    for src, dest_rel, is_dir in managed_paths(entry):
        dest = clone / dest_rel
        if not src.exists():
            notes.append(f"  WARN missing source {src.relative_to(REPO_ROOT)} -> {dest_rel} (skipped)")
            continue
        if is_dir:
            # the library source dir excludes its co-located SPEC/ subtree
            excludes = ["SPEC/"] if dest_rel == Path(lib) else None
            rsync_dir(src, dest, excludes)
        else:
            copy_file(src, dest)
        notes.append(f"  {src.relative_to(REPO_ROOT)} -> {dest_rel}")
    return notes


def rewrite_pins(entry: dict, clone: Path, synced: dict[str, str]) -> list[str]:
    """Rewrite the root lakefile's cross-repo Hex pins to synced SHAs."""
    notes: list[str] = []
    pins = entry.get("pins") or []
    if not pins:
        return notes
    fmt = entry["lakefile"]
    lf = clone / ("lakefile.toml" if fmt == "toml" else "lakefile.lean")
    text = lf.read_text(encoding="utf-8")
    for dep in pins:
        sha = synced.get(dep)
        if sha is None:
            notes.append(f"  WARN no synced SHA for pin {dep} (left unchanged)")
            continue
        url = re.escape(f"github.com/kim-em/{dep}.git")
        if fmt == "toml":
            # `git = ".../<dep>.git"` then the next `rev = "..."`
            pat = re.compile(r'(git\s*=\s*"https://' + url + r'"\s*\n\s*rev\s*=\s*")[0-9a-f]{7,40}(")')
        else:
            # `".../<dep>.git" @ "<sha>"`
            pat = re.compile(r'("https://' + url + r'"\s*@\s*")[0-9a-f]{7,40}(")')
        text, n = pat.subn(lambda m: m.group(1) + sha + m.group(2), text)
        if n:
            notes.append(f"  pin {dep} -> {sha[:12]} ({n} site)")
        else:
            notes.append(f"  WARN pin {dep} not found in {lf.name}")
    lf.write_text(text, encoding="utf-8")
    return notes


def sync_repo(entry: dict, source_sha: str, token: str | None, dry_run: bool,
              synced: dict[str, str], baseline: dict[str, str], force: bool) -> bool:
    """Sync one repo. Returns True if the baseline SHA changed (a push happened)."""
    repo = entry["repo"]
    short = repo.split("/")[-1]
    print(f"\n=== {repo} ===")
    with tempfile.TemporaryDirectory() as td:
        clone = Path(td) / short
        run(["git", "clone", "--depth", "1", clone_url(repo, token), str(clone)], capture=True)
        head = run(["git", "rev-parse", "HEAD"], cwd=clone, capture=True)
        # Compare-and-swap guard: refuse to overwrite a repo whose main has moved
        # off the baseline this monorepo was synced from (an uncoordinated commit).
        expected = baseline.get(short)
        if expected and head != expected:
            msg = (f"  UNCOORDINATED: {repo} main is {head[:12]}, baseline expects "
                   f"{expected[:12]}. Reconcile (re-seed from main) before syncing.")
            if not force:
                print(msg + " Skipping (use --force to override).")
                synced[short] = expected
                return False
            print(msg + " Overriding (--force).")
        for line in apply_paths(entry, clone):
            print(line)
        for line in rewrite_pins(entry, clone, synced):
            print(line)
        status = run(["git", "status", "--porcelain"], cwd=clone, capture=True)
        if not status:
            print("  (no changes)")
            synced[short] = head
            return False
        print("  changed files:")
        for l in status.splitlines():
            print(f"    {l}")
        if dry_run:
            synced[short] = head  # stand-in so downstream pin previews resolve
            print("  DRY-RUN: not committing or pushing")
            return False
        run(["git", "add", "-A"], cwd=clone)
        run(["git", "-c", "user.name=hex-dev sync",
             "-c", "user.email=noreply@anthropic.com",
             "commit", "-q", "-m", f"chore: sync from hex-dev@{source_sha[:12]}"], cwd=clone)
        run(["git", "push", "origin", "HEAD:main"], cwd=clone)
        synced[short] = run(["git", "rev-parse", "HEAD"], cwd=clone, capture=True)
        print(f"  pushed {synced[short][:12]} to {repo}@main")
        return True


def main() -> int:
    ap = argparse.ArgumentParser(description="Publish released split repos from the monorepo.")
    ap.add_argument("--dry-run", action="store_true", help="print planned changes; do not push")
    ap.add_argument("--token", default=os.environ.get("RELEASED_SYNC_PAT"),
                    help="GitHub token with contents:write on the released repos")
    ap.add_argument("--only", help="sync only this repo short-name (e.g. hex-matrix)")
    ap.add_argument("--force", action="store_true",
                    help="override the uncoordinated-commit guard and overwrite anyway")
    ap.add_argument("--baseline", default=str(BASELINE), type=Path,
                    help="path to the per-repo baseline JSON to read and advance "
                         "(the workflow points this at the release-sync-baseline branch's copy)")
    args = ap.parse_args()

    if not args.dry_run and not args.token:
        ap.error("a token (--token or $RELEASED_SYNC_PAT) is required unless --dry-run")

    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    baseline_doc = json.loads(args.baseline.read_text(encoding="utf-8")) if args.baseline.exists() else {}
    baseline = {k: v for k, v in baseline_doc.items() if not k.startswith("_")}
    source_sha = run(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, capture=True)
    synced: dict[str, str] = {}
    for entry in manifest["repos"]:
        if args.only and entry["repo"].split("/")[-1] != args.only:
            continue
        sync_repo(entry, source_sha, args.token, args.dry_run,
                  synced, baseline, args.force)
    # Advance the baseline to every processed repo's current HEAD (pushed, skipped,
    # or unchanged) so the next run's guard is accurate. Written on a real run only;
    # the workflow commits it to the release-sync-baseline branch.
    if not args.dry_run and synced:
        baseline_doc.update(synced)
        args.baseline.write_text(json.dumps(baseline_doc, indent=2) + "\n", encoding="utf-8")
        print(f"\nadvanced baseline -> {args.baseline}")
    print(f"\nsynced {len(synced)} repo(s) from hex-dev@{source_sha[:12]}"
          + (" (dry-run)" if args.dry_run else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
