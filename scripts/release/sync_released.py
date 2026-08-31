#!/usr/bin/env python3
"""Publish the released split repos from this monorepo.

For each repo in scripts/release/released.yml (topological order), this:
  1. clones the repo's `main`,
  2. overwrites its *managed* paths and centrally owned CI workflow,
  3. for managed-source repos, enables native Verso docstrings,
  4. copies the stable Lean toolchain and exact external dependency pins,
  5. rewrites cross-repo Hex pins in the repo's Lake files,
  6. commits `chore: sync from hex-dev@<sha>` and pushes to `main`
     (unless --dry-run, which prints the planned changes and pin rewrites).

A `pins_only` entry (the `leanprover/hex` aggregate) receives the managed CI
workflow but no library source or Verso rewrite from the monorepo. The sync
re-pins it to the SHAs published this run. Listed last, after its upstreams, its
pins resolve to the freshly-pushed commits. Its other managed artifact is the
README, rendered by `aggregate_readme.py` from a template plus the manifest's
`component:` labels so the published library table cannot fall behind.

Auth (non-dry-run): tokens from --token (repeatable) or the environment
($RELEASED_SYNC_PAT, $RELEASED_SYNC_PAT_2, ... in numeric order) are used as
`x-access-token` basic-auth credentials for clone and push. A fine-grained
token caps its selected-repository list, so the published set is split across
more than one token; for each target repository the preflight probes the
tokens in order until one can push to it, and routes that repository's clone and
push through that token. Dry-run clones over public https and never pushes.

Usage:
  python3 scripts/release/sync_released.py --dry-run
  RELEASED_SYNC_PAT=... RELEASED_SYNC_PAT_2=... python3 scripts/release/sync_released.py
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
import urllib.error
import urllib.request
from pathlib import Path

import yaml

# Importable both as a script and as scripts.release.sync_released, so the
# sibling module is reached through the directory rather than the package.
sys.path.insert(0, str(Path(__file__).resolve().parent))

import aggregate_readme  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "release" / "released.yml"
RELEASED_CI = REPO_ROOT / "scripts" / "release" / "released-ci.yml"
BASELINE = REPO_ROOT / "scripts" / "release" / "synced.json"
TOOLCHAIN = REPO_ROOT / "lean-toolchain"
# The `RELEASED_SYNC_PAT` / `RELEASED_SYNC_PAT_2` secrets hold the
# `hex-publishing` / `hex-publishing-2` fine-grained tokens. Each is
# deliberately scoped to hex repositories rather than to every repository, and
# a fine-grained token caps how many repositories it can select, which is why
# there is more than one. Publishing a *new* library is therefore a two-part
# change: add it to released.yml here, and add it to the selected repositories
# of a token with room. The second part needs an organization owner's
# approval, so start it before the release rather than discovering it
# mid-publish. The sync does not care which token carries which repository; it
# routes per repository to the first token that can push to it.
TOKEN_HELP = (
    "Follow the per-token reasons above: a repository reported without a\n"
    "write grant must be added to the selected repositories of one of the\n"
    "tokens behind the\n"
    "RELEASED_SYNC_PAT / RELEASED_SYNC_PAT_2 secrets (Contents: Read and write);\n"
    "a missing repository must be created first; an indeterminate reason (rate\n"
    "limit, network, credentials) calls for a retry or a token repair, not a\n"
    "selection change. The tokens are currently `hex-publishing` and\n"
    "`hex-publishing-2`, listed under\n"
    "https://github.com/settings/personal-access-tokens . Any token with room\n"
    "works; the sync routes per repository. Each token is scoped to hex\n"
    "repositories on purpose, so each newly published library has to be added by\n"
    "hand. An organization owner then approves the request at\n"
    "https://github.com/organizations/leanprover/settings/personal-access-token-requests"
)
LAKE_MANIFEST = REPO_ROOT / "lake-manifest.json"


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


def released_ci_workflows(path: Path | None = None) -> dict[str, str]:
    """Load the complete managed CI workflow for every released repository."""
    source = path or RELEASED_CI
    document = yaml.safe_load(source.read_text(encoding="utf-8"))
    workflows = document.get("workflows") if isinstance(document, dict) else None
    if not isinstance(workflows, dict) or not workflows:
        raise ValueError(f"{source}: workflows must be a non-empty mapping")
    for repo, workflow in workflows.items():
        if not isinstance(repo, str) or not isinstance(workflow, str):
            raise ValueError(f"{source}: workflow entries must map names to text")
        if not workflow.endswith("\n"):
            raise ValueError(f"{source}: workflow for {repo} must end in a newline")
    return workflows


def apply_ci_workflow(entry: dict, clone: Path) -> str:
    """Publish the selected central workflow into a released clone."""
    short = entry["repo"].split("/")[-1]
    workflows = released_ci_workflows()
    if short not in workflows:
        raise RuntimeError(f"no managed CI workflow for {entry['repo']}")
    destination = clone / ".github" / "workflows" / "ci.yml"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(workflows[short], encoding="utf-8")
    return "  scripts/release/released-ci.yml -> .github/workflows/ci.yml"


def managed_paths(entry: dict) -> list[tuple[Path, Path, bool]]:
    """Yield (src, dest_rel, is_dir) managed mappings for one repo entry.

    Sources are absolute monorepo paths; dest_rel is relative to the repo root.
    """
    # Aggregate repos (e.g. leanprover/hex) manage no library source:
    # their umbrella lakefile, umbrella .lean and README live only in the released
    # repo. Their centrally owned CI workflow is applied separately by
    # apply_ci_workflow; this function only describes library-source mappings.
    if entry.get("pins_only"):
        return []
    lib = entry["lib"]
    out: list[tuple[Path, Path, bool]] = []
    # explicit path list (e.g. hex-test-kit ships only `Hex/`)
    for p in entry.get("paths") or []:
        src = REPO_ROOT / p["src"]
        out.append((src, Path(p["dest"]), src.is_dir()))
    # conventional library source dir (minus its co-located SPEC/ and README.md)
    if not entry.get("paths"):
        out.append((REPO_ROOT / lib, Path(lib), True))
    # root README, authored as <lib>/README.md, published to the repo root
    if entry.get("readme", True):
        out.append((REPO_ROOT / lib / "README.md", Path("README.md"), False))
    # root PERFORMANCE.md, authored as <lib>/PERFORMANCE.md, published to root
    # (mirrors README so its relative figure links resolve identically)
    if entry.get("performance"):
        out.append((REPO_ROOT / lib / "PERFORMANCE.md", Path("PERFORMANCE.md"), False))
    # committed comparator/scaling figures: an explicit, tight allow-list (never
    # a broad glob) so stale or volatile artifacts are never published silently
    for fig in entry.get("figures") or []:
        out.append((REPO_ROOT / "reports" / "figures" / fig,
                    Path("reports") / "figures" / fig, False))
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
    for f in entry.get("bench_files") or []:
        out.append((REPO_ROOT / "bench" / f, Path("bench") / f, False))
    if entry.get("conformance"):
        out.append((REPO_ROOT / "conformance" / lib, Path("conformance") / lib, True))
    for f in entry.get("conformance_files") or []:
        out.append((REPO_ROOT / "conformance" / f, Path("conformance") / f, False))
    for f in entry.get("fixtures") or []:
        out.append((REPO_ROOT / "conformance-fixtures" / f, Path("conformance-fixtures") / f, True))
    for o in entry.get("oracles") or []:
        src = REPO_ROOT / "scripts" / "oracle" / o
        out.append((src, Path("scripts") / "oracle" / o, src.is_dir()))
    return out


def removal_paths(entry: dict) -> list[Path]:
    """Return validated released-repo paths explicitly scheduled for deletion."""
    paths: list[Path] = []
    for raw in entry.get("remove_paths") or []:
        if not isinstance(raw, str):
            raise ValueError("remove_paths entries must be strings")
        path = Path(raw)
        if path.is_absolute() or not path.parts or any(
            part in {".", ".."} for part in path.parts
        ):
            raise ValueError(f"unsafe remove_paths entry: {raw!r}")
        paths.append(path)
    if len(paths) != len(set(paths)):
        raise ValueError("remove_paths contains duplicate entries")
    return paths


def apply_paths(entry: dict, clone: Path) -> list[str]:
    notes: list[str] = []
    template = entry.get("readme_template")
    if template:
        manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
        rendered = aggregate_readme.render(manifest, REPO_ROOT / template)
        (clone / "README.md").write_text(rendered, encoding="utf-8")
        notes.append(f"  {template} + released.yml -> README.md (generated)")
    notes.append(apply_ci_workflow(entry, clone))
    if entry.get("pins_only"):
        return notes
    lib = entry["lib"]
    clone_root = clone.resolve()
    for dest_rel in removal_paths(entry):
        dest = clone / dest_rel
        resolved_parent = dest.parent.resolve()
        if (
            resolved_parent != clone_root
            and clone_root not in resolved_parent.parents
        ):
            raise ValueError(
                f"unsafe remove_paths destination escapes clone: {dest_rel}"
            )
        if dest.is_symlink() or dest.is_file():
            dest.unlink()
        elif dest.is_dir():
            shutil.rmtree(dest)
        else:
            continue
        notes.append(f"  remove {dest_rel}")
    for src, dest_rel, is_dir in managed_paths(entry):
        dest = clone / dest_rel
        if not src.exists():
            notes.append(f"  WARN missing source {src.relative_to(REPO_ROOT)} -> {dest_rel} (skipped)")
            continue
        if is_dir:
            # the library source dir excludes its co-located SPEC/ subtree and
            # its README.md (published separately to the repo root)
            excludes = ["SPEC/", "README.md"] if dest_rel == Path(lib) else None
            rsync_dir(src, dest, excludes)
        else:
            copy_file(src, dest)
        notes.append(f"  {src.relative_to(REPO_ROOT)} -> {dest_rel}")
    return notes


def _api_repo(repo: str, token: str | None) -> dict | int:
    """The repos API payload, or the HTTP status if the request was refused."""
    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "hex-dev-release-sync",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    request = urllib.request.Request(f"https://api.github.com/repos/{repo}", headers=headers)
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.load(response)
    except urllib.error.HTTPError as exc:
        return exc.code


def _receive_pack_status(repo: str, token: str) -> int:
    """HTTP status of the smart-HTTP receive-pack advertisement.

    `GET <repo>.git/info/refs?service=git-receive-pack` is the handshake `git
    push` performs before sending anything, so it is authorized exactly like a
    push (`Contents: write`) and has no side effects: 200 means this token can
    push, 401/403 mean it cannot, 404 means the repository is not there.
    """
    auth = base64.b64encode(f"x-access-token:{token}".encode()).decode()
    request = urllib.request.Request(
        f"https://github.com/{repo}.git/info/refs?service=git-receive-pack",
        headers={"Authorization": f"Basic {auth}",
                 "User-Agent": "hex-dev-release-sync"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return response.status
    except urllib.error.HTTPError as exc:
        return exc.code


def selection_check(repo: str, token: str) -> str | None:
    """None if `token` can push to `repo`, else why not.

    Probes the receive-pack advertisement rather than `GET /repos`: a
    fine-grained token reads any *public* repository whether or not it is in
    the token's selection, so a metadata probe routes a repository to the
    first token even when only a later token holds the write grant, and the
    failure then surfaces at push time, after earlier repositories were
    already published (this has actually bitten a first publish). The
    receive-pack handshake is authorized exactly like the push itself.

    A repository that does not exist answers 404; an anonymous metadata probe
    separates "missing" from anything odder. Any other status is reported as
    indeterminate rather than guessed at, so a rate limit or an outage never
    reads as a missing grant.
    """
    try:
        status = _receive_pack_status(repo, token)
    except (urllib.error.URLError, OSError, ValueError) as exc:
        return f"could not be checked ({exc})"
    if status == 200:
        return None
    if status in (401, 403):
        return ("not granted Contents: write (repository unselected on this "
                "token, or selected read-only)")
    if status == 429:
        return f"could not be checked (HTTP {status}; rate limited)"
    if status != 404:
        return f"could not be checked (HTTP {status})"
    try:
        anonymous = _api_repo(repo, None)
    except (urllib.error.URLError, OSError, ValueError) as exc:
        return f"HTTP 404, and could not be checked anonymously ({exc})"
    if not isinstance(anonymous, int):
        return "HTTP 404 with the token yet publicly visible; undetermined"
    if anonymous == 404:
        return "no such repository (create it before publishing)"
    return (f"HTTP 404, and anonymously HTTP {anonymous}, so whether it is "
            "missing or unselected is undetermined")


def route_tokens(entries: list[dict], tokens: list[str]) -> tuple[dict[str, str], list[str]]:
    """Assign each target repo the first token that can see it.

    Returns (repo -> token, blocked-report lines). Checked up front, before the
    first push: each publishing token is scoped to an explicit list of
    repositories, and a fine-grained token caps that list, so the published set
    is split across more than one token. Nothing here assumes any particular
    split; each repository is probed against the tokens in order until one sees
    it, and every later clone and push uses the token routed here. A library
    released here
    but on no token's list would otherwise fail partway through, after earlier
    repos were already published. The probe authorizes like the push itself;
    see `selection_check`.
    """
    routed: dict[str, str] = {}
    blocked: list[str] = []
    for entry in entries:
        repo = entry["repo"]
        reasons: list[str] = []
        for index, token in enumerate(tokens):
            reason = selection_check(repo, token)
            if reason is None:
                routed[repo] = token
                break
            reasons.append(f"token {index + 1}: {reason}")
        else:
            blocked.append(f"{repo}: " + "; ".join(reasons))
    return routed, blocked


def _lake_files(clone: Path, name_globs: list[str]) -> list[Path]:
    """All matching files in the repo, excluding Lake build dirs. Covers the
    root and the bench/ and conformance/ sub-Lake-projects."""
    out: list[Path] = []
    for g in name_globs:
        out += [p for p in clone.glob(f"**/{g}") if ".lake" not in p.parts]
    return sorted(out)


def _git_url(url: str) -> str:
    """Normalize a Git URL for comparison without changing its published form."""
    normalized = url.rstrip("/")
    if normalized.endswith(".git"):
        normalized = normalized[:-4]
    return normalized.lower()


def external_pins() -> dict[str, dict[str, str]]:
    """Exact non-Hex Git dependencies selected by this monorepo's lockfile."""
    doc = json.loads(LAKE_MANIFEST.read_text(encoding="utf-8"))
    pins: dict[str, dict[str, str]] = {}
    for package in doc.get("packages", []):
        url = package.get("url")
        rev = package.get("rev")
        input_rev = package.get("inputRev")
        if not all(isinstance(value, str) for value in (url, rev, input_rev)):
            continue
        normalized = _git_url(url)
        if re.fullmatch(r"https://github\.com/(?:kim-em|leanprover)/hex(?:-[^/]+)?",
                        normalized):
            continue
        name = package.get("name")
        if not isinstance(name, str):
            continue
        pins[normalized] = {
            "name": name,
            "url": url,
            "rev": rev,
            "inputRev": input_rev,
        }
    return pins


def rewrite_toolchains(clone: Path) -> list[str]:
    """Use one stable Lean toolchain in the root and every side project."""
    notes: list[str] = []
    expected = TOOLCHAIN.read_text(encoding="utf-8")
    toolchains = _lake_files(clone, ["lean-toolchain"])
    if clone / "lean-toolchain" not in toolchains:
        raise RuntimeError(f"released repository has no root lean-toolchain: {clone}")
    for toolchain in toolchains:
        if toolchain.read_text(encoding="utf-8") != expected:
            toolchain.write_text(expected, encoding="utf-8")
            notes.append(f"  toolchain {expected.strip()} ({toolchain.relative_to(clone)})")
    return notes


def validate_skeleton(entry: dict, clone: Path) -> None:
    """Check the unmanaged Lake file carries every release build root.

    Source synchronization deliberately does not overwrite a released
    repository's Lake configuration.  This check keeps that boundary explicit:
    a renamed executable or newly separate development umbrella must be added
    to the mirror skeleton before publication can proceed.
    """
    lakefile = clone / f"lakefile.{entry['lakefile']}"
    if not lakefile.is_file():
        raise RuntimeError(
            f"released repository expects {lakefile.name}, but it is missing: "
            f"{clone}"
        )
    text = lakefile.read_text(encoding="utf-8")
    if entry.get("precompile_modules"):
        assignment = (
            r"(?m)^\s*precompileModules\s*=\s*true\s*$"
            if entry["lakefile"] == "toml"
            else r"(?m)^\s*precompileModules\s*:=\s*true\s*$"
        )
        if re.search(assignment, text) is None:
            raise RuntimeError(
                f"released Lake file {lakefile} must precompile modules"
            )
    for module in entry.get("test_modules", []):
        if module not in text:
            raise RuntimeError(
                f"released Lake file {lakefile} does not build test module "
                f"{module}"
            )
    for module in entry.get("build_modules", []):
        if module not in text:
            raise RuntimeError(
                f"released Lake file {lakefile} does not build development "
                f"module {module}"
            )
    for executable, module in entry.get("executables", {}).items():
        executable_pattern = (
            rf"(?ms)^\s*lean_exe\s+[«\"]?{re.escape(executable)}[»\"]?\s+where\s*$"
            rf"(?P<body>.*?)(?=^\S|\Z)"
        )
        executable_match = re.search(executable_pattern, text)
        root_pattern = rf"(?m)^\s*root\s*:=\s*`{re.escape(module)}\s*$"
        if (
            executable_match is None
            or not re.search(root_pattern, executable_match.group("body"))
        ):
            raise RuntimeError(
                f"released Lake file {lakefile} must define executable "
                f"{executable} at {module}"
            )


def rewrite_external_pins(clone: Path,
                          pins: dict[str, dict[str, str]]) -> list[str]:
    """Synchronize direct non-Hex requirements with the monorepo lock.

    Lake files retain a readable tag or branch in ``inputRev`` form. Their
    manifests carry the exact resolved commit, updated separately below.
    """
    notes: list[str] = []
    pins_by_name = {pin["name"].lower(): pin for pin in pins.values()}
    for lakefile in _lake_files(clone, ["lakefile.toml", "lakefile.lean"]):
        text = lakefile.read_text(encoding="utf-8")
        original = text
        if lakefile.name == "lakefile.toml":
            # A Reservoir requirement commonly has only `name`, `scope`, and
            # `rev`; it need not repeat the resolved Git URL.  Rewrite each
            # complete require table by parsed package identity, while
            # preserving the author's TOML formatting.
            def rewrite_require(match: re.Match[str]) -> str:
                block = match.group(0)
                try:
                    requirement = tomllib.loads(block)["require"][0]
                except (KeyError, IndexError, tomllib.TOMLDecodeError) as exc:
                    raise RuntimeError(
                        f"cannot parse require table in {lakefile}: {exc}"
                    ) from exc
                git = requirement.get("git")
                pin = (
                    pins.get(_git_url(git))
                    if isinstance(git, str)
                    else pins_by_name.get(str(requirement.get("name", "")).lower())
                )
                if pin is None:
                    return block
                if "rev" not in requirement:
                    raise RuntimeError(
                        f"direct external requirement {pin['name']} in "
                        f"{lakefile} has no rev"
                    )
                rewritten, count = re.subn(
                    r'(?m)^(\s*rev\s*=\s*")[^"]+(")',
                    lambda rev_match: (
                        rev_match.group(1)
                        + pin["inputRev"]
                        + rev_match.group(2)
                    ),
                    block,
                    count=1,
                )
                if count != 1:
                    raise RuntimeError(
                        f"cannot locate rev for {pin['name']} in {lakefile}"
                    )
                if rewritten != block:
                    notes.append(
                        f"  external pin {pin['url']} -> {pin['inputRev']} "
                        f"({lakefile.relative_to(clone)})"
                    )
                return rewritten

            text = re.sub(
                r"(?ms)^\[\[require\]\][^\n]*\n.*?(?=^\[|\Z)",
                rewrite_require,
                text,
            )
            if text != original:
                lakefile.write_text(text, encoding="utf-8")
            continue
        for normalized, pin in pins.items():
            before = text
            url_pattern = re.escape(normalized) + r"(?:\.git)?"
            pattern = (r'("' + url_pattern
                       + r'"\s*@\s*")[^"]+(")')
            text, count = re.subn(
                pattern,
                lambda match, rev=pin["inputRev"]:
                    match.group(1) + rev + match.group(2),
                text,
                flags=re.IGNORECASE,
            )
            if count and text != before:
                notes.append(
                    f"  external pin {pin['url']} -> {pin['inputRev']} "
                    f"({lakefile.relative_to(clone)})")
        if text != original:
            lakefile.write_text(text, encoding="utf-8")
    return notes


def _flatten_lean_options(options: dict, prefix: str = "") -> list[tuple[str, object]]:
    """Flatten Lake's dotted-table option encoding to ``(name, value)`` pairs."""
    flattened: list[tuple[str, object]] = []
    for key, value in options.items():
        name = f"{prefix}.{key}" if prefix else key
        if isinstance(value, dict):
            flattened.extend(_flatten_lean_options(value, name))
        else:
            flattened.append((name, value))
    return flattened


def _render_lean_options(options: list[tuple[str, object]]) -> str:
    """Render options using Lake's array form, which permits prefix option names."""
    lines = ["leanOptions = ["]
    for name, value in options:
        if isinstance(value, bool):
            rendered = "true" if value else "false"
        elif isinstance(value, int) and value >= 0:
            rendered = str(value)
        elif isinstance(value, str):
            rendered = json.dumps(value)
        else:
            raise RuntimeError(f"unsupported Lean option value for {name}: {value!r}")
        lines.append(f"  {{ name = {json.dumps(name)}, value = {rendered} }},")
    lines.append("]")
    return "\n".join(lines)


def _replace_toml_lean_options(text: str, source: Path) -> str:
    """Add the Verso options while preserving all existing package options."""
    try:
        parsed = tomllib.loads(text)
    except tomllib.TOMLDecodeError as err:
        raise RuntimeError(f"invalid TOML in {source}: {err}") from err

    raw_options = parsed.get("leanOptions")
    if raw_options is None:
        options: list[tuple[str, object]] = []
    elif isinstance(raw_options, dict):
        options = _flatten_lean_options(raw_options)
    elif isinstance(raw_options, list):
        options = []
        for option in raw_options:
            if (not isinstance(option, dict) or
                    not isinstance(option.get("name"), str) or
                    "value" not in option):
                raise RuntimeError(f"unsupported leanOptions entry in {source}: {option!r}")
            options.append((option["name"], option["value"]))
    else:
        raise RuntimeError(f"unsupported leanOptions value in {source}: {raw_options!r}")

    required = {"doc.verso": True, "doc.verso.suggestions": False}
    merged: list[tuple[str, object]] = []
    seen: set[str] = set()
    for name, value in options:
        if name in seen:
            raise RuntimeError(f"duplicate Lean option {name} in {source}")
        seen.add(name)
        merged.append((name, required.get(name, value)))
    for name, value in required.items():
        if name not in seen:
            merged.append((name, value))
    replacement = _render_lean_options(merged)

    section = re.search(r"(?m)^\[leanOptions\]\s*(?:#.*)?$", text)
    if section is not None:
        following = re.search(r"(?m)^\[", text[section.end():])
        end = section.end() + following.start() if following is not None else len(text)
        text = text[:section.start()] + replacement + "\n\n" + text[end:]
    else:
        assignment = re.search(r"(?m)^leanOptions\s*=", text)
        if assignment is not None:
            first_table = re.search(r"(?m)^\[", text)
            if first_table is not None and assignment.start() > first_table.start():
                raise RuntimeError(f"cannot locate package leanOptions assignment in {source}")
            value_start = assignment.end()
            while value_start < len(text) and text[value_start].isspace():
                value_start += 1
            if value_start >= len(text) or text[value_start] not in "[{":
                raise RuntimeError(f"unsupported leanOptions syntax in {source}")
            opening = text[value_start]
            closing = "]" if opening == "[" else "}"
            depth = 0
            in_string = False
            escaped = False
            end = value_start
            while end < len(text):
                char = text[end]
                if in_string:
                    if escaped:
                        escaped = False
                    elif char == "\\":
                        escaped = True
                    elif char == '"':
                        in_string = False
                elif char == '"':
                    in_string = True
                elif char == opening:
                    depth += 1
                elif char == closing:
                    depth -= 1
                    if depth == 0:
                        end += 1
                        break
                end += 1
            else:
                raise RuntimeError(f"unterminated leanOptions value in {source}")
            text = text[:assignment.start()] + replacement + text[end:]
        else:
            first_table = re.search(r"(?m)^\[", text)
            insert_at = first_table.start() if first_table is not None else len(text)
            text = text[:insert_at] + replacement + "\n\n" + text[insert_at:]

    try:
        tomllib.loads(text)
    except tomllib.TOMLDecodeError as err:
        raise RuntimeError(f"Verso rewrite produced invalid TOML in {source}: {err}") from err
    return text


def rewrite_doc_verso(clone: Path) -> list[str]:
    """Enable native Verso docstrings in every released Lake project.

    Managed Lean sources use native Verso markup, including declaration roles
    and module-doc headings. Released repos keep their Lake files locally, so
    the sync must carry the parser options across explicitly.
    """
    notes: list[str] = []
    for lf in _lake_files(clone, ["lakefile.toml", "lakefile.lean"]):
        text = lf.read_text(encoding="utf-8")
        orig = text
        if lf.name == "lakefile.toml":
            text = _replace_toml_lean_options(text, lf)
        else:
            package = re.search(r"(?m)^package\b[^\n]*\bwhere\s*$", text)
            if package is None:
                raise RuntimeError(f"cannot find package declaration in {lf}")
            following = re.search(r"(?m)^\S", text[package.end():])
            block_end = (package.end() + following.start()
                         if following is not None else len(text))
            package_block = text[package.end():block_end]
            has_verso = re.search(r"⟨`doc\.verso,\s*true⟩", package_block)
            has_suggestions = re.search(
                r"⟨`doc\.verso\.suggestions,\s*false⟩", package_block)
            if has_verso and has_suggestions:
                pass
            elif re.search(r"(?m)^\s+leanOptions\s*:=", package_block):
                raise RuntimeError(
                    f"cannot safely merge native Verso options into existing "
                    f"package leanOptions in {lf}")
            else:
                insert_at = package.end()
                options = ("\n  leanOptions := #[⟨`doc.verso, true⟩, "
                           "⟨`doc.verso.suggestions, false⟩]")
                text = text[:insert_at] + options + text[insert_at:]
        if text != orig:
            lf.write_text(text, encoding="utf-8")
            notes.append(f"  native Verso docstrings ({lf.relative_to(clone)})")
    return notes


def rewrite_pins(entry: dict, clone: Path, synced: dict[str, str],
                 dep_owner: dict[str, str]) -> list[str]:
    """Rewrite every synced-repo git pin across all lakefiles (root + the
    bench/ and conformance/ sub-projects pin upstream repos and hex-test-kit)."""
    notes: list[str] = []
    match_owner = r'(?:kim-em|leanprover)'
    for lf in _lake_files(clone, ["lakefile.toml", "lakefile.lean"]):
        text = lf.read_text(encoding="utf-8")
        orig = text
        for dep, sha in synced.items():
            # Match either owner so a pin still carrying the pre-transfer owner is
            # found, and rewrite it to the owner released.yml declares for this
            # dep (the single source of truth) — kim-em pre-cutover, leanprover
            # after. That makes this a no-op until released.yml flips.
            target = dep_owner.get(dep, "leanprover")
            tail = re.escape(f"{dep}.git")
            # toml: `git = "https://github.com/<owner>/<dep>.git"\n  rev = "..."`
            text, n1 = re.subn(
                r'(git\s*=\s*"https://github\.com/)' + match_owner
                + r'(/' + tail + r'"\s*\n\s*rev\s*=\s*")[0-9a-f]{7,40}(")',
                lambda m, t=target, s=sha: m.group(1) + t + m.group(2) + s + m.group(3), text)
            # lean: `"https://github.com/<owner>/<dep>.git" @ "<sha>"`
            text, n2 = re.subn(
                r'("https://github\.com/)' + match_owner
                + r'(/' + tail + r'"\s*@\s*")[0-9a-f]{7,40}(")',
                lambda m, t=target, s=sha: m.group(1) + t + m.group(2) + s + m.group(3), text)
            if n1 or n2:
                notes.append(f"  pin {dep} -> {sha[:12]} ({lf.relative_to(clone)})")
        if text != orig:
            lf.write_text(text, encoding="utf-8")
    return notes


def rewrite_manifest(entry: dict, clone: Path, synced: dict[str, str],
                     dep_owner: dict[str, str],
                     pins: dict[str, dict[str, str]]) -> list[str]:
    """Pin the synced SHAs in every lake-manifest.json (root + sub-projects), so
    Lake's lockfile points at the new revisions, not a stale checkout. Lake
    trusts the manifest, and the bench/ and conformance/ sub-projects keep their
    own manifests that otherwise pin the old hex-matrix."""
    notes: list[str] = []
    import json as _json
    # Match either owner so a manifest still carrying the pre-transfer URL is
    # found; the url's owner is then rewritten to what released.yml declares.
    by_url = {f"github.com/{o}/{dep}.git": dep
              for o in ("kim-em", "leanprover") for dep in synced}
    for mf in _lake_files(clone, ["lake-manifest.json"]):
        doc = _json.loads(mf.read_text(encoding="utf-8"))
        changed = 0
        for pkg in doc.get("packages", []):
            url = pkg.get("url", "")
            pin = pins.get(_git_url(url)) if isinstance(url, str) else None
            if pin is not None:
                if (pkg.get("rev") != pin["rev"] or
                        pkg.get("inputRev") != pin["inputRev"]):
                    pkg["rev"] = pin["rev"]
                    pkg["inputRev"] = pin["inputRev"]
                    changed += 1
                    notes.append(
                        f"  manifest {pin['url']} -> {pin['rev'][:12]} "
                        f"({mf.relative_to(clone)})")
            for frag, dep in by_url.items():
                if frag in url:
                    target = dep_owner.get(dep, "leanprover")
                    pkg["url"] = re.sub(r'(github\.com/)(?:kim-em|leanprover)(/)',
                                        rf'\g<1>{target}\g<2>', url)
                    pkg["rev"] = synced[dep]
                    if pkg.get("inputRev") and len(pkg["inputRev"]) >= 7:
                        pkg["inputRev"] = synced[dep]
                    changed += 1
                    notes.append(f"  manifest {dep} -> {synced[dep][:12]} ({mf.relative_to(clone)})")
        if changed:
            mf.write_text(_json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    return notes


def sync_repo(entry: dict, source_sha: str, token: str | None, dry_run: bool,
              synced: dict[str, str], baseline: dict[str, str], force: bool,
              dep_owner: dict[str, str],
              pins: dict[str, dict[str, str]]) -> bool:
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
        validate_skeleton(entry, clone)
        for line in apply_paths(entry, clone):
            print(line)
        if not entry.get("pins_only"):
            for line in rewrite_doc_verso(clone):
                print(line)
        for line in rewrite_toolchains(clone):
            print(line)
        for line in rewrite_external_pins(clone, pins):
            print(line)
        for line in rewrite_pins(entry, clone, synced, dep_owner):
            print(line)
        for line in rewrite_manifest(entry, clone, synced, dep_owner, pins):
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


def env_tokens() -> list[str]:
    """Tokens from $RELEASED_SYNC_PAT, $RELEASED_SYNC_PAT_2, ... in numeric order.

    Only the canonical slot names count: the base name, then suffixes that are
    integers >= 2 without leading zeroes, so no `_0`/`_1`/`_01` alias can sort
    ambiguously against the base slot. Empty slots are skipped (the workflow
    exports the secrets unconditionally, so an unset secret arrives as "").
    """
    def order(name: str) -> int:
        suffix = name.removeprefix("RELEASED_SYNC_PAT")
        return int(suffix[1:]) if suffix else 1
    names = [name for name in os.environ
             if re.fullmatch(r"RELEASED_SYNC_PAT(_(?:[2-9]|[1-9][0-9]+))?", name)
             and os.environ[name]]
    return [os.environ[name] for name in sorted(names, key=order)]


def main() -> int:
    ap = argparse.ArgumentParser(description="Publish released split repos from the monorepo.")
    ap.add_argument("--dry-run", action="store_true", help="print planned changes; do not push")
    ap.add_argument("--token", action="append", default=None,
                    help="GitHub token with contents:write on (a subset of) the "
                         "released repos; repeatable, tried in order per repo. "
                         "Defaults to $RELEASED_SYNC_PAT, $RELEASED_SYNC_PAT_2, ...")
    ap.add_argument("--only", help="sync only this repo short-name (e.g. hex-matrix)")
    ap.add_argument("--force", action="store_true",
                    help="override the uncoordinated-commit guard and overwrite anyway")
    ap.add_argument("--baseline", default=str(BASELINE), type=Path,
                    help="path to the per-repo baseline JSON to read and advance "
                         "(the workflow points this at the release-sync-baseline branch's copy)")
    args = ap.parse_args()

    # An empty token would probe anonymously, win the routing for every public
    # repository, and only fail at push time — after earlier repositories were
    # already published. Reject it loudly instead.
    if args.token is not None and any(not token.strip() for token in args.token):
        ap.error("--token values must be nonempty")
    tokens = args.token or env_tokens()
    if not args.dry_run and not tokens:
        ap.error("a token (--token or $RELEASED_SYNC_PAT / $RELEASED_SYNC_PAT_2 / ...) "
                 "is required unless --dry-run")

    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    baseline_doc = json.loads(args.baseline.read_text(encoding="utf-8")) if args.baseline.exists() else {}
    baseline = {k: v for k, v in baseline_doc.items() if not k.startswith("_")}
    source_sha = run(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, capture=True)
    # Owner each dep is published under, per released.yml — the single source of
    # truth the pin/manifest rewrites target (kim-em pre-cutover, leanprover after).
    dep_owner = {e["repo"].split("/")[-1]: e["repo"].split("/")[0]
                 for e in manifest["repos"]}
    pins = external_pins()
    # A staged `--only` publication still has to pin all of its already-published
    # upstreams. Seed the pin map from the live baseline; otherwise an isolated
    # downstream sync silently retains stale pins because skipped entries never
    # populate `synced`.
    synced: dict[str, str] = dict(baseline) if args.only else {}

    targets = [entry for entry in manifest["repos"]
               if not args.only or entry["repo"].split("/")[-1] == args.only]
    # A misspelled --only would otherwise select nothing, preflight vacuously,
    # publish nothing, and still exit 0 reporting the seeded baseline count.
    if args.only and len(targets) != 1:
        print(f"release sync: --only {args.only} matches {len(targets)} manifest "
              "entries; expected exactly one", file=sys.stderr)
        return 1
    repo_token: dict[str, str] = {}
    if not args.dry_run:
        repo_token, blocked = route_tokens(targets, tokens)
        if blocked:
            print(f"\nrelease sync: could not establish token coverage for "
                  f"{len(blocked)} of {len(targets)} target repositories:",
                  file=sys.stderr)
            for line in blocked:
                print(f"  {line}", file=sys.stderr)
            print(f"\n{TOKEN_HELP}", file=sys.stderr)
            return 1
        per_slot = ", ".join(
            f"token {index + 1}: {sum(1 for t in repo_token.values() if t == token)}"
            for index, token in enumerate(tokens))
        print(f"token preflight: all {len(targets)} target repositories are covered "
              f"({per_slot}; the probe authorizes like the push itself, see selection_check)")

    failed_repo: str | None = None
    current_repo = "<manifest>"
    try:
        for entry in manifest["repos"]:
            current_repo = entry["repo"]
            if args.only and entry["repo"].split("/")[-1] != args.only:
                continue
            # Dry runs skip routing and clone over public https; real runs index
            # the routed map so a repository routing ever missed fails closed.
            token = None if args.dry_run else repo_token[entry["repo"]]
            sync_repo(entry, source_sha, token, args.dry_run,
                      synced, baseline, args.force, dep_owner, pins)
    except Exception as exc:
        failed_repo = current_repo
        message = str(exc)
        for token in tokens:
            message = message.replace(token, "<redacted>")
        print(
            f"\nrelease sync failed in {failed_repo}: "
            f"{type(exc).__name__}: {message}",
            file=sys.stderr,
        )
    finally:
        # A real run may already have pushed upstream repositories when a later
        # skeleton or network operation fails. Persist those exact new heads so
        # the workflow can advance its guard branch even while reporting the
        # failed publication.
        if not args.dry_run and synced:
            baseline_doc.update(synced)
            args.baseline.write_text(
                json.dumps(baseline_doc, indent=2) + "\n",
                encoding="utf-8",
            )
            print(f"\nadvanced baseline -> {args.baseline}")
    print(f"\nsynced {len(synced)} repo(s) from hex-dev@{source_sha[:12]}"
          + (" (dry-run)" if args.dry_run else ""))
    return 1 if failed_repo else 0


if __name__ == "__main__":
    raise SystemExit(main())
