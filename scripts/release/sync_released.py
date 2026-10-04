#!/usr/bin/env python3
"""Publish the released split repos from this monorepo.

For each repo in scripts/release/released.yml (topological order), this:
  1. clones the repo's `main`,
  2. removes everything outside the entry's managed paths and the unmanaged
     skeleton, then overwrites its *managed* paths and centrally owned CI
     workflow,
  3. generates the repo's Lake file from released.yml and this monorepo's
     lakefile (see `render_lakefile`), requiring other Hex repos at one shared
     semantic version,
  4. copies the stable Lean toolchain,
  5. rewrites the lockfile to that version and the exact external pins,
  6. commits `chore: sync from hex-dev@<sha>`, pushes to `main`, and tags the
     resulting commit with that version
     (unless --dry-run, which prints the planned changes and pin rewrites).

A `pins_only` entry (the `leanprover/hex` aggregate) receives the managed CI
workflow but no library source or Verso rewrite from the monorepo. The sync
re-pins it to the version published this run. Listed last, after its upstreams,
its lockfile resolves those requirements to the freshly-pushed commits. Its
other managed artifact is the
README, rendered by `aggregate_readme.py` from a template plus the manifest's
`component:` labels so the published library table cannot fall behind.

Auth (non-dry-run): tokens from --token (repeatable) or the environment
($RELEASED_SYNC_PAT, $RELEASED_SYNC_PAT_2, ... in numeric order) are used as
`x-access-token` basic-auth credentials for clone and push. A fine-grained
token caps its selected-repository list, so the published set is split across
more than one token; for each target repository the preflight probes the
tokens in order until one can push to it, and routes that repository's clone and
push through that token. Because the sync updates `.github/workflows/ci.yml`,
each token also needs Workflows: read and write. The receive-pack preflight can
verify Contents permission but not this separate workflow-file permission.
Dry-run clones over public https and never pushes.

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
    "RELEASED_SYNC_PAT / RELEASED_SYNC_PAT_2 secrets (Contents: Read and write;\n"
    "Workflows: Read and write);\n"
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
LAKEFILE = REPO_ROOT / "lakefile.lean"

# The `lean_lib` settings that decide how a consumer builds a library; the
# generated Lake file copies them from this monorepo's lakefile.
BUILD_LIB_SETTINGS = ("precompileModules", "moreLinkObjs", "extraDepTargets",
                      "moreLinkArgs")
SEMVER = re.compile(r"^v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$")


def next_release_version(current: object = None) -> str:
    """Increment the shared minor version, starting with ``v0.2.0``."""
    if current is None:
        # A few libraries published independent v0.1.0 tags before releases
        # were coordinated. Treat that version as the historical floor.
        return "v0.2.0"
    if not isinstance(current, str) or (match := SEMVER.fullmatch(current)) is None:
        raise ValueError(f"invalid completed release version: {current!r}")
    major, minor, _patch = map(int, match.groups())
    return f"v{major}.{minor + 1}.0"


def release_transaction(document: dict, source_sha: str) -> tuple[str, set[str], bool]:
    """Return ``(version, completed repos, resumed)`` for the next publication.

    A pending transaction is deliberately tied to one hex-dev commit. This
    prevents a retry from placing the same version on different source states
    after main has advanced.
    """
    pending = document.get("_pending_release")
    if pending is None:
        return next_release_version(document.get("_version")), set(), False
    if not isinstance(pending, dict):
        raise ValueError("_pending_release must be an object")
    version = pending.get("version")
    source = pending.get("source")
    repos = pending.get("repos")
    if (not isinstance(version, str) or SEMVER.fullmatch(version) is None
            or not isinstance(source, str)
            or not isinstance(repos, list)
            or not all(isinstance(repo, str) for repo in repos)
            or len(repos) != len(set(repos))):
        raise ValueError("invalid _pending_release record")
    expected = next_release_version(document.get("_version"))
    if version != expected:
        raise ValueError(
            f"pending release is {version}, but {expected} must follow the "
            "completed release"
        )
    if source != source_sha:
        raise RuntimeError(
            f"release {version} is pending from hex-dev@{source[:12]}; rerun "
            "the sync at that commit before starting another release"
        )
    return version, set(repos), True


def write_baseline(path: Path, document: dict) -> None:
    """Atomically replace the live release baseline."""
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


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


def released_extra_workflows(path: Path | None = None) -> dict[str, dict[str, str]]:
    """Load the workflows a repository gets beyond its build-only `ci.yml`.

    Keyed by repository short name, then by workflow file stem, so `hex`'s
    `docs` entry is published as `.github/workflows/docs.yml`. Absent from the
    document means no repository has one, which is a legitimate state.
    """
    source = path or RELEASED_CI
    document = yaml.safe_load(source.read_text(encoding="utf-8"))
    extras = document.get("extra_workflows") if isinstance(document, dict) else None
    if extras is None:
        return {}
    if not isinstance(extras, dict):
        raise ValueError(f"{source}: extra_workflows must be a mapping")
    for repo, workflows in extras.items():
        if not isinstance(repo, str) or not isinstance(workflows, dict) or not workflows:
            raise ValueError(
                f"{source}: extra_workflows entries must map a name to a non-empty mapping")
        for stem, workflow in workflows.items():
            if not isinstance(stem, str) or not isinstance(workflow, str):
                raise ValueError(
                    f"{source}: extra workflow entries must map names to text")
            if stem == "ci":
                raise ValueError(
                    f"{source}: {repo} declares ci as an extra workflow; ci.yml is"
                    " published from the workflows mapping")
            if not workflow.endswith("\n"):
                raise ValueError(
                    f"{source}: extra workflow {stem} for {repo} must end in a newline")
    return extras


def managed_workflow_paths(entry: dict) -> set[Path]:
    """The `.github/workflows/` files one mirror is allowed to carry.

    Every mirror has `ci.yml`; the manifest may declare further workflows for a
    repository. This is the allowance, so it describes the destinations without
    requiring the content to exist: a repository with no managed CI workflow is
    an error when publishing, not when computing what may survive a sweep.
    """
    short = entry["repo"].split("/")[-1]
    stems = ["ci", *released_extra_workflows().get(short, {})]
    return {Path(".github") / "workflows" / f"{stem}.yml" for stem in stems}


def managed_workflows(entry: dict) -> dict[Path, str]:
    """The complete `.github/workflows/` content one mirror is published with."""
    short = entry["repo"].split("/")[-1]
    workflows = released_ci_workflows()
    if short not in workflows:
        raise RuntimeError(f"no managed CI workflow for {entry['repo']}")
    out = {Path(".github") / "workflows" / "ci.yml": workflows[short]}
    for stem, workflow in released_extra_workflows().get(short, {}).items():
        out[Path(".github") / "workflows" / f"{stem}.yml"] = workflow
    return out


def apply_ci_workflow(entry: dict, clone: Path) -> list[str]:
    """Publish the central workflows into a released clone."""
    notes: list[str] = []
    for dest_rel, workflow in managed_workflows(entry).items():
        destination = clone / dest_rel
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(workflow, encoding="utf-8")
        notes.append(f"  scripts/release/released-ci.yml -> {dest_rel.as_posix()}")
    return notes


def managed_paths(entry: dict) -> list[tuple[Path, Path, bool]]:
    """Yield (src, dest_rel, is_dir) managed mappings for one repo entry.

    Sources are absolute monorepo paths; dest_rel is relative to the repo root.
    A released repo receives the library and its documentation, never the
    benchmarks, conformance drivers, fixtures or oracles that exercise it here:
    those are development instruments for the whole graph and stay in hex-dev.
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
    # Tight, explicitly mapped supporting files outside the conventional
    # library tree.
    for p in entry.get("extra_paths") or []:
        src = REPO_ROOT / p["src"]
        out.append((src, Path(p["dest"]), src.is_dir()))
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
    return out


# The Lake and repository skeleton a mirror owns and the sync deliberately does
# not author: the root Lake project files, the repository's licence, ignore
# rules and agent notes. `.git` and `.lake` are named so no walk can reach into
# them. `.github/` is deliberately absent: only the managed
# `.github/workflows/ci.yml` survives, so a mirror cannot accumulate a second
# workflow beside the build-only one published from `released-ci.yml`.
SKELETON = (
    ".git",
    ".gitignore",
    ".lake",
    "AGENTS.md",
    "LICENSE",
    "README.md",
    "lake-manifest.json",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
)


# Removed from every released repository, the `pins_only` aggregate included.
# The aggregate is otherwise exempt from the sweep, because its umbrella module,
# lakefile, `docs/` site and the workflow that publishes it live only there and
# nothing here can tell them from an accident. Agent notes are the one thing no
# released repository has any use for, so they are named rather than swept.
NEVER_PUBLISHED = (".claude",)


def keep_paths(entry: dict) -> list[Path]:
    """Return validated mirror-local paths the sweep must leave alone.

    The escape hatch for a file a mirror owns that is neither managed nor part
    of the common skeleton, such as `hex-test-kit`'s fixed `HexTestKit.lean`
    umbrella. It can only preserve, never delete, so a forgotten entry shows up
    as a deletion in the dry run and a broken mirror build rather than as a
    silently over-published repository.
    """
    paths: list[Path] = []
    for raw in entry.get("keep_paths") or []:
        if not isinstance(raw, str):
            raise ValueError("keep_paths entries must be strings")
        path = Path(raw)
        if path.is_absolute() or not path.parts or any(
            part in {".", ".."} for part in path.parts
        ):
            raise ValueError(f"unsafe keep_paths entry: {raw!r}")
        paths.append(path)
    if len(paths) != len(set(paths)):
        raise ValueError("keep_paths contains duplicate entries")
    return paths


def allowed_paths(entry: dict) -> tuple[set[Path], set[Path]]:
    """Everything one mirror may contain, as (subtrees, files).

    A path is allowed when it is one of these, or lies under one of the
    subtrees. Computing the allowance from the entry, rather than enumerating
    the leftovers to delete, is what makes "a mirror ships the library and
    nothing else" a property of the tooling: a new entry inherits the whole
    policy, and an entry can only widen its mirror by declaring the widening
    here. `reports/` is not allowed wholesale: a mirror publishes exactly the
    figures its manifest entry names, which arrive as managed files under it.
    """
    subtrees = {Path(name) for name in SKELETON}
    subtrees.update(keep_paths(entry))
    files = managed_workflow_paths(entry)
    for _src, dest_rel, is_dir in managed_paths(entry):
        (subtrees if is_dir else files).add(dest_rel)
    return subtrees, files


def prune_unmanaged(entry: dict, clone: Path) -> list[str]:
    """Delete everything in a released clone outside `allowed_paths`.

    Benchmarks, conformance drivers, fixtures, oracles and the sidecar Lake
    projects that carried them are development instruments for the whole graph;
    they live in this monorepo and never reach a mirror. So do the bench-result
    ledgers and performance write-ups under `reports/`, the agent notes under
    `.claude/`, and any workflow beside the managed build-only one. The sweep
    enforces that by construction instead of by a per-entry list of things to
    forget.

    A `pins_only` aggregate is exempt from the sweep, since its umbrella module,
    lakefile and documentation site live only in the released repository, but it
    still loses everything in `NEVER_PUBLISHED`.
    """
    notes: list[str] = []
    for name in NEVER_PUBLISHED:
        target = clone / name
        if target.is_symlink() or target.is_file():
            target.unlink()
        elif target.is_dir():
            shutil.rmtree(target)
        else:
            continue
        notes.append(f"  remove {name}")
    if entry.get("pins_only"):
        return notes
    subtrees, files = allowed_paths(entry)
    ancestors = {
        parent
        for path in subtrees | files
        for parent in path.parents
        if parent != Path(".")
    }

    def sweep(directory: Path) -> None:
        for child in sorted(directory.iterdir()):
            relative = child.relative_to(clone)
            if relative in subtrees or relative in files:
                continue
            if (
                relative in ancestors
                and child.is_dir()
                and not child.is_symlink()
            ):
                sweep(child)
                continue
            if child.is_symlink() or child.is_file():
                child.unlink()
            elif child.is_dir():
                shutil.rmtree(child)
            else:
                continue
            notes.append(f"  remove {relative}")

    sweep(clone)
    return notes


def apply_paths(entry: dict, clone: Path) -> list[str]:
    notes: list[str] = []
    template = entry.get("readme_template")
    if template:
        manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
        rendered = aggregate_readme.render(manifest, REPO_ROOT / template)
        (clone / "README.md").write_text(rendered, encoding="utf-8")
        notes.append(f"  {template} + released.yml -> README.md (generated)")
    notes.extend(apply_ci_workflow(entry, clone))
    notes.extend(prune_unmanaged(entry, clone))
    if entry.get("pins_only"):
        return notes
    lib = entry["lib"]
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
    content push (`Contents: write`) and has no side effects: 200 means this
    token can push ordinary content, 401/403 mean it cannot, 404 means the
    repository is not there. GitHub's separate Workflows permission is checked
    only when a push changes `.github/workflows`.
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
    receive-pack handshake is authorized like an ordinary content push. It
    cannot preflight the separate Workflows permission needed when this sync
    updates `.github/workflows/ci.yml`.

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
    repos were already published. The probe authorizes ordinary content pushes;
    the separate Workflows grant required by the managed CI update cannot be
    preflighted this way. See `selection_check`.
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
    """All matching files in the repo, excluding Lake build dirs. A mirror keeps
    only its root Lake project; the walk stays recursive so anything a skeleton
    still carries is rewritten rather than silently left behind."""
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


def _lean_lib_header(text: str, lib: str) -> re.Match[str] | None:
    """The `lean_lib <lib>` declaration in a Lean Lake file, if it has one.

    Group `where` is unset for a bare `lean_lib Foo`, which Lake accepts and
    some mirror skeletons use; the settings block then has to be opened before a
    setting can be added.
    """
    return re.search(
        r"(?m)^lean_lib[ \t]+«?" + re.escape(lib)
        + r"»?[ \t]*(?P<where>where)?[ \t]*$",
        text,
    )


def _block_end(text: str, start: int) -> int:
    """Where an indented Lean settings block starting at `start` ends."""
    following = re.search(r"(?m)^\S", text[start:])
    return start + following.start() if following is not None else len(text)


def _lean_settings(body: str) -> dict[str, str]:
    """Settings assigned in an indented Lean `lean_lib` body, values joined."""
    settings: dict[str, str] = {}
    current: str | None = None
    for line in body.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        assignment = re.match(r"[ \t]+([A-Za-z][A-Za-z0-9_']*)[ \t]*:=(.*)$", line)
        if assignment is not None:
            current = assignment.group(1)
            settings[current] = assignment.group(2).strip()
        elif current is not None:
            settings[current] = f"{settings[current]} {stripped}".strip()
    return settings


def lean_lib_settings(text: str) -> dict[str, dict[str, str]]:
    """Every `lean_lib` in a Lean Lake file, mapped to its assigned settings."""
    libs: dict[str, dict[str, str]] = {}
    for header in re.finditer(
            r"(?m)^lean_lib[ \t]+«?([A-Za-z_][A-Za-z0-9_']*)»?[ \t]*(?:where)?[ \t]*$",
            text):
        body = text[header.end():_block_end(text, header.end())]
        libs[header.group(1)] = _lean_settings(body)
    return libs


def source_build_settings(lib: str, path: Path | None = None) -> dict[str, str]:
    """The build settings this monorepo's lakefile assigns to `lib`.

    The single source of truth for how a released library is built. A released
    library with no `lean_lib` here cannot have its settings carried into the
    mirror at all, so that is an error rather than an empty answer.
    """
    source = path or LAKEFILE
    libs = lean_lib_settings(source.read_text(encoding="utf-8"))
    if lib not in libs:
        raise RuntimeError(f"{source} declares no lean_lib {lib}")
    return {name: value for name, value in libs[lib].items()
            if name in BUILD_LIB_SETTINGS}


def lake_declaration(text: str, name: str) -> tuple[int, int]:
    """Locate an unindented named Lake declaration and its indented body.

    Managed declarations use `def`, `target`, `extern_lib` or `lean_lib`
    without attributes. Supporting both target forms lets the sync migrate an
    old package-wide `extern_lib` into a library-scoped custom `target`, and
    `lean_lib` carries a native carrier or sidecar library (see
    `HexArithNative`). Refuse
    missing or ambiguous declarations rather than modifying the wrong recipe.
    """
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name):
        raise RuntimeError(f"invalid Lake declaration name: {name!r}")
    matches = list(re.finditer(
        r"(?m)^(?:private |public )?(?:def|target|extern_lib|lean_lib) "
        + re.escape(name) + r"(?=\s|\()[^\n]*\n",
        text,
    ))
    if len(matches) != 1:
        raise RuntimeError(f"expected one Lake declaration {name}, found {len(matches)}")
    start = matches[0].start()
    end = _block_end(text, matches[0].end())
    return start, end


def validate_ci_helpers(entry: dict, clone: Path) -> None:
    """Require every centrally managed CI helper to exist in the mirror.

    Release workflows are managed here, while existing ``scripts/ci`` helpers
    remain part of each mirror's skeleton. Validate that boundary before any
    publication writes so a central workflow cannot point at a missing script.
    """
    short = entry["repo"].split("/", 1)[1]
    workflow = released_ci_workflows()[short]
    parsed = yaml.load(workflow, Loader=yaml.BaseLoader)
    jobs = parsed.get("jobs", {}) if isinstance(parsed, dict) else {}
    helpers: set[str] = set()
    for job in jobs.values():
        if not isinstance(job, dict):
            continue
        for step in job.get("steps", []):
            command = step.get("run") if isinstance(step, dict) else None
            if isinstance(command, str):
                helpers.update(
                    re.findall(r"scripts/ci/[A-Za-z0-9_.\-/]+", command)
                )
    missing = sorted(path for path in helpers if not (clone / path).is_file())
    if missing:
        raise RuntimeError(
            f"released repository {entry['repo']} lacks CI helpers {missing}"
        )


def rewrite_manifest(entry: dict, clone: Path, synced: dict[str, str],
                     dep_owner: dict[str, str],
                     pins: dict[str, dict[str, str]],
                     version: str,
                     catalog: dict[str, dict[str, str]] | None = None) -> list[str]:
    """Resolve Hex release tags to exact SHAs in every Lake manifest."""
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
                    pkg["inputRev"] = version
                    changed += 1
                    notes.append(f"  manifest {dep} -> {synced[dep][:12]} ({mf.relative_to(clone)})")
        if mf == clone / "lake-manifest.json":
            changed += _synthesize_manifest_packages(
                entry, clone, doc, synced, dep_owner, version, catalog, notes)
            changed += _reconcile_hex_packages(entry, doc, catalog, notes)
            # The Lake file is generated, so which packages it requires
            # directly can change; the lockfile's `inherited` flags follow it.
            direct = _direct_requires(clone)
            for pkg in doc.get("packages", []):
                inherited = pkg.get("name") not in direct
                if pkg.get("inherited") != inherited:
                    pkg["inherited"] = inherited
                    changed += 1
        if changed:
            mf.write_text(_json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    return notes


HEX_PACKAGE_URL = re.compile(r"github\.com/(?:kim-em|leanprover)/hex(?:-[A-Za-z0-9-]+)?(?:\.git)?$")


def _reconcile_hex_packages(entry: dict, doc: dict,
                            catalog: dict[str, dict[str, str]] | None,
                            notes: list[str]) -> int:
    """Make the lockfile's Hex packages exactly the entry's published closure.

    The generated Lake file can stop requiring a library, and a dependency can
    change Lake file format; the lockfile follows, so Lake is never handed a
    package set or `configFile` that disagrees with the Lake files it reads.
    """
    if catalog is None:
        catalog = _manifest_catalog()
    wanted = {catalog[dep]["lib"]: dep for dep in entry.get("pins") or []
              if dep in catalog and catalog[dep]["lib"]}
    changed = 0
    kept = []
    for pkg in doc.get("packages", []):
        if HEX_PACKAGE_URL.search(pkg.get("url") or ""):
            name = pkg.get("name")
            if name not in wanted:
                notes.append(f"  manifest - {name} (no longer a dependency)")
                changed += 1
                continue
            config = f"lakefile.{catalog[wanted[name]]['lakefile']}"
            if pkg.get("configFile") != config:
                pkg["configFile"] = config
                changed += 1
        kept.append(pkg)
    doc["packages"] = kept
    return changed


def validate_manifest(entry: dict, clone: Path) -> None:
    """Refuse to publish a lockfile that disagrees with the generated Lake file.

    Every direct requirement must have a lockfile entry; a missing external one
    (a mirror that newly needs Mathlib, say) cannot be synthesized without
    Lake resolving its own dependencies, so it stops the sync instead.
    """
    path = clone / "lake-manifest.json"
    if not path.is_file():
        raise RuntimeError(f"{entry['repo']} has no lake-manifest.json")
    present = {pkg.get("name") for pkg in
               json.loads(path.read_text(encoding="utf-8")).get("packages", [])}
    missing = sorted(_direct_requires(clone) - present)
    if missing:
        raise RuntimeError(
            f"{entry['repo']}'s generated Lake file requires {', '.join(missing)}, "
            "which its lake-manifest.json lacks; run `lake update` on the staged "
            "repository and commit the resulting lockfile to the mirror first")


def _direct_requires(clone: Path) -> set[str]:
    """Package names the mirror's root Lake file requires directly."""
    names: set[str] = set()
    toml = clone / "lakefile.toml"
    if toml.is_file():
        names.update(r["name"] for r in tomllib.loads(
            toml.read_text(encoding="utf-8")).get("require", []))
    lean = clone / "lakefile.lean"
    if lean.is_file():
        names.update(re.findall(r"(?m)^require\s+«?([A-Za-z0-9_]+)»?\s+from",
                                lean.read_text(encoding="utf-8")))
    return names


def _manifest_catalog() -> dict[str, dict[str, str]]:
    """Short name -> library name and Lake file format, from released.yml."""
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    return {e["repo"].split("/")[-1]: {"lib": e.get("lib", ""),
                                       "lakefile": e.get("lakefile", "toml")}
            for e in manifest["repos"]}


def _synthesize_manifest_packages(entry: dict, clone: Path, doc: dict,
                                  synced: dict[str, str],
                                  dep_owner: dict[str, str],
                                  version: str,
                                  catalog: dict[str, dict[str, str]] | None,
                                  notes: list[str]) -> int:
    """Add lockfile entries for pinned published dependencies the mirror's
    manifest has never seen.

    A mirror's `lake-manifest.json` is written by `lake update` in that mirror
    and only ever rewritten here, so a dependency that enters the published
    closure later (a library split out upstream, or a companion that gains a
    requirement) is absent from it, and Lake refuses to build: "dependency X
    of Y not in manifest". The sync knows every published dependency's exact
    revision, owner and Lake file format, which is all a lockfile entry holds,
    so it appends the missing entries itself. A pin the mirror's own Lake file
    requires directly is recorded as such; every other pin is inherited from
    a dependency. Entries already present are left to the rewrite above.
    """
    pins = entry.get("pins") or []
    if not pins:
        return 0
    if catalog is None:
        catalog = _manifest_catalog()
    packages = doc.setdefault("packages", [])
    present = {pkg.get("name") for pkg in packages}
    lake_text = ""
    for lf in _lake_files(clone, ["lakefile.toml", "lakefile.lean"]):
        if lf.parent == clone:
            lake_text = lf.read_text(encoding="utf-8")
    added = 0
    for dep in pins:
        spec = catalog.get(dep)
        if spec is None or not spec["lib"] or dep not in synced:
            continue
        if spec["lib"] in present:
            continue
        owner = dep_owner.get(dep, "leanprover")
        url = f"https://github.com/{owner}/{dep}.git"
        packages.append({
            "url": url,
            "type": "git",
            "subDir": None,
            "scope": "",
            "rev": synced[dep],
            "name": spec["lib"],
            "manifestFile": "lake-manifest.json",
            "inputRev": version,
            "inherited": f"{dep}.git" not in lake_text,
            "configFile": f"lakefile.{spec['lakefile']}",
        })
        present.add(spec["lib"])
        added += 1
        notes.append(f"  manifest + {dep} ({spec['lib']}) -> {synced[dep][:12]} "
                     "(lake-manifest.json)")
    return added


def validate_external_imports(entry: dict, clone: Path) -> None:
    """Require the mirror's Lake file to provide checked external import roots.

    The monorepo provides Batteries, Mathlib, Tau Ceti and AINTLIB; a mirror
    only has what its own Lake file requires. Scan synced sources for these
    roots and fail before pushing when a corresponding provider is absent.
    Mathlib also provides Batteries; Tau Ceti and HasseWeil require their
    own direct dependencies.
    """
    if entry.get("pins_only"):
        return
    lakefile = clone / f"lakefile.{entry['lakefile']}"
    text = lakefile.read_text(encoding="utf-8") if lakefile.is_file() else ""
    provided: set[str] = set()
    if re.search(r'(?i)mathlib4?\.git|name\s*=\s*"mathlib"|require\s+mathlib\b', text):
        provided.update({"Mathlib", "Batteries"})
    if re.search(r'(?i)batteries\.git|name\s*=\s*"batteries"|require\s+batteries\b', text):
        provided.add("Batteries")
    if re.search(r'(?i)tauceti\.git|name\s*=\s*"TauCeti"|require\s+TauCeti\b', text):
        provided.add("TauCeti")
    if re.search(r'(?i)AINTLIB\.git|name\s*=\s*"AINTLIB"|require\s+AINTLIB\b', text):
        provided.add("HasseWeil")
    roots: dict[str, str] = {}
    pattern = re.compile(
        r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(Batteries|Mathlib|TauCeti|HasseWeil)\b",
        re.M)
    for src, dest_rel, is_dir in managed_paths(entry):
        dest = clone / dest_rel
        files = list(dest.rglob("*.lean")) if is_dir else (
            [dest] if dest.suffix == ".lean" else [])
        for lean in files:
            if not lean.is_file():
                continue
            for root in pattern.findall(lean.read_text(encoding="utf-8")):
                roots.setdefault(root, str(lean.relative_to(clone)))
    missing = {root: where for root, where in roots.items() if root not in provided}
    if missing:
        raise RuntimeError(
            f"released repository {entry['repo']} imports "
            + ", ".join(f"{root} ({where})" for root, where in sorted(missing.items()))
            + f" but {lakefile.name} requires no package providing it")


# Generated Lake files. A mirror's Lake file is rendered here, from
# released.yml and this monorepo's lakefile.lean, on every sync: nothing in it is
# hand-maintained, so it cannot drift from how this repository builds the
# library, keep a target that no longer exists, or miss a newly published
# dependency. The format (TOML or Lean) follows the entry's `lakefile` field,
# because dependents' lockfiles record which file to read.
DOC_VERSO_OPTIONS = (("doc.verso", "true"), ("doc.verso.suggestions", "false"))
EXTERNAL_IMPORT_ROOTS = {"Mathlib": "mathlib", "Batteries": "batteries",
                         "TauCeti": "TauCeti", "HasseWeil": "AINTLIB"}


def _library_deps() -> dict[str, tuple[str, ...]]:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    from libgraph import load_libraries
    return {name: info.deps for name, info in load_libraries().items()}


def _source_import_roots(entry: dict) -> set[str]:
    """Top-level module roots imported by the library's published sources."""
    pattern = re.compile(
        r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Z][A-Za-z0-9]*)",
        re.M)
    roots: set[str] = set()
    for src, _dest, is_dir in managed_paths(entry):
        files = list(src.rglob("*.lean")) if is_dir else (
            [src] if src.suffix == ".lean" else [])
        for lean in files:
            if lean.is_file():
                roots.update(pattern.findall(lean.read_text(encoding="utf-8")))
    return roots


def release_requires(entry: dict, entries: list[dict], version: str,
                     dep_owner: dict[str, str],
                     pins: dict[str, dict[str, str]],
                     library_deps: dict[str, tuple[str, ...]] | None = None
                     ) -> list[tuple[str, str, str]]:
    """The mirror's direct requirements as (name, git URL, revision).

    A published Hex library is required when the library declares it as a
    dependency in libraries.yml or its sources import it directly, so a
    mirror never builds only because some other dependency happens to pull a
    library in. External packages are required for the roots the sources
    import (Mathlib also covers Batteries), at this monorepo's locked inputs.
    """
    if library_deps is None:
        library_deps = _library_deps()
    by_lib = {e["lib"]: e["repo"].split("/")[-1]
              for e in entries if e.get("lib") and not e.get("pins_only")}
    roots = _source_import_roots(entry)
    wanted = set(library_deps.get(entry["lib"], ())) | roots
    out: list[tuple[str, str, str]] = []
    for other in entries:
        lib = other.get("lib")
        if other.get("pins_only") or not lib or lib == entry["lib"] or lib not in wanted:
            continue
        short = by_lib[lib]
        owner = dep_owner.get(short, "leanprover")
        out.append((lib, f"https://github.com/{owner}/{short}.git", version))
    externals = {root for root in EXTERNAL_IMPORT_ROOTS if root in roots}
    if "Mathlib" in externals:
        externals.discard("Batteries")
    by_name = {pin["name"].lower(): pin for pin in pins.values()}
    for root in sorted(externals):
        pin = by_name.get(EXTERNAL_IMPORT_ROOTS[root].lower())
        if pin is None:
            raise RuntimeError(
                f"{entry['repo']} imports {root}, but this monorepo's lockfile has "
                f"no {EXTERNAL_IMPORT_ROOTS[root]} package to pin it to")
        out.append((pin["name"], pin["url"], pin["inputRev"]))
    return out


def _lean_declaration_text(source: str, name: str) -> str:
    start, end = lake_declaration(source, name)
    return source[start:end].rstrip() + "\n"


def _main_lib_text(source: str, lib: str) -> str:
    """This monorepo's `lean_lib` declaration for `lib`, verbatim."""
    header = _lean_lib_header(source, lib)
    if header is None:
        raise RuntimeError(f"lakefile.lean declares no lean_lib {lib}")
    end = _block_end(source, header.end())
    return source[header.start():end].rstrip() + "\n"


def render_lakefile(entry: dict, entries: list[dict], version: str,
                    dep_owner: dict[str, str],
                    pins: dict[str, dict[str, str]],
                    library_deps: dict[str, tuple[str, ...]] | None = None,
                    source: str | None = None) -> str:
    """Render a mirror's complete Lake file."""
    short = entry["repo"].split("/")[-1]
    if source is None:
        source = LAKEFILE.read_text(encoding="utf-8")
    if entry.get("pins_only"):
        return _render_aggregate_lakefile(entries, version, dep_owner)
    requires = release_requires(entry, entries, version, dep_owner, pins, library_deps)
    lib = entry.get("lean_lib_name", entry["lib"])
    tests = entry.get("test_modules") or []
    modules = entry.get("build_modules") or []
    executables = entry.get("executables") or {}
    defaults = [lib] + ([f"{lib}Modules"] if modules else [])
    # A source tree published through `extra_paths` that is a library here
    # (hex-graph-iso ships HexGraph) needs its own `lean_lib` in the mirror.
    declared = set(entry.get("lake_declarations") or [])
    source_libs = lean_lib_settings(source)
    extra_libs: list[str] = []
    for extra in entry.get("extra_paths") or []:
        name = Path(extra["dest"]).parts[0].removesuffix(".lean")
        if (name in source_libs and name != entry["lib"] and name not in declared
                and name not in extra_libs):
            extra_libs.append(name)
    if entry.get("lakefile") == "lean":
        out = ["import Lake", "open System Lake DSL", "",
               f"package «{short}» where",
               "  leanOptions := #["
               + ", ".join(f"⟨`{k}, {v}⟩" for k, v in DOC_VERSO_OPTIONS) + "]", ""]
        for name, url, rev in requires:
            out += [f"require {name} from git", f'  "{url}" @ "{rev}"']
        declarations = entry.get("lake_declarations") or []
        helpers = [d for d in declarations
                   if not re.search(rf"(?m)^lean_lib {re.escape(d)}\b", source)]
        carriers = [d for d in declarations if d not in helpers]
        for name in helpers:
            out += ["", _lean_declaration_text(source, name).rstrip()]
        out += ["", "@[default_target]", _main_lib_text(source, entry["lib"]).rstrip()]
        for name in carriers:
            out += ["", _lean_declaration_text(source, name).rstrip()]
        for name in extra_libs:
            out += ["", _main_lib_text(source, name).rstrip()]
        if modules:
            out += ["", "@[default_target]", f"lean_lib {lib}Modules where",
                    "  globs := #[" + ", ".join(f"`{m}" for m in modules) + "]"]
        if tests:
            out += ["", f"lean_lib {lib}Tests where",
                    "  globs := #[" + ", ".join(f"`{m}" for m in tests) + "]"]
        for exe, root in executables.items():
            out += ["", f"lean_exe {exe} where", f"  root := `{root}"]
        return "\n".join(out) + "\n"
    settings = {name: value for name, value in
                source_libs.get(entry["lib"], {}).items()
                if name in BUILD_LIB_SETTINGS}
    unsupported = sorted(set(settings) - {"precompileModules"})
    if unsupported or entry.get("lake_declarations"):
        raise RuntimeError(
            f"{entry['repo']} needs {', '.join(unsupported) or 'lake_declarations'}, "
            "which only a Lean Lake file can express; set `lakefile: lean`")
    quote = lambda items: "[" + ", ".join(f'"{item}"' for item in items) + "]"
    out = [f'name = "{short}"', f"defaultTargets = {quote(defaults)}", "",
           "leanOptions = ["]
    out += [f'  {{ name = "{k}", value = {v} }},' for k, v in DOC_VERSO_OPTIONS]
    out += ["]"]
    for name, url, rev in requires:
        out += ["", "[[require]]", f'name = "{name}"', f'git = "{url}"', f'rev = "{rev}"']
    out += ["", "[[lean_lib]]", f'name = "{lib}"']
    if entry.get("globs"):
        out += [f"globs = {quote(entry['globs'])}"]
    if settings.get("precompileModules") == "true":
        out += ["precompileModules = true"]
    for name in extra_libs:
        extra_settings = source_libs[name]
        if set(extra_settings) - {"precompileModules"}:
            raise RuntimeError(f"{entry['repo']}: {name} needs a Lean Lake file")
        out += ["", "[[lean_lib]]", f'name = "{name}"']
        if extra_settings.get("precompileModules") == "true":
            out += ["precompileModules = true"]
    if modules:
        out += ["", "[[lean_lib]]", f'name = "{lib}Modules"', f"globs = {quote(modules)}"]
    if tests:
        out += ["", "[[lean_lib]]", f'name = "{lib}Tests"', f"globs = {quote(tests)}"]
    for exe, root in executables.items():
        out += ["", "[[lean_exe]]", f'name = "{exe}"', f'root = "{root}"']
    return "\n".join(out) + "\n"


AGGREGATE_HEADER = (
    "# Aggregator: requires every released Hex library at one shared release\n"
    "# version. Require `hex` to depend on everything released; or require an\n"
    "# individual library (e.g. hex-mv-poly or hex-lll) for just that piece.\n"
    "# Generated by hex-dev's scripts/release/sync_released.py from released.yml."
)


def aggregate_libraries(entries: list[dict]) -> list[dict]:
    return [e for e in entries
            if not e.get("pins_only") and e.get("aggregate", True)]


def _render_aggregate_lakefile(entries: list[dict], version: str,
                               dep_owner: dict[str, str]) -> str:
    out = ['name = "hex"', 'defaultTargets = ["Hex"]', "",
           AGGREGATE_HEADER]
    for e in aggregate_libraries(entries):
        short = e["repo"].split("/")[-1]
        owner = dep_owner.get(short, "leanprover")
        out += ["", "[[require]]", f'name = "{e["lib"]}"',
                f'git = "https://github.com/{owner}/{short}.git"', f'rev = "{version}"']
    out += ["", "[[lean_lib]]", 'name = "Hex"']
    return "\n".join(out) + "\n"


def render_aggregate_umbrella(entries: list[dict]) -> str:
    return "module\n\n" + "".join(
        f"public import {e['lib']}\n" for e in aggregate_libraries(entries))


def write_lakefile(entry: dict, clone: Path, entries: list[dict], version: str,
                   dep_owner: dict[str, str],
                   pins: dict[str, dict[str, str]]) -> list[str]:
    """Replace the mirror's Lake file (and the aggregate's umbrella) with the rendering."""
    notes: list[str] = []
    fmt = "toml" if entry.get("pins_only") else entry.get("lakefile", "toml")
    path = clone / f"lakefile.{fmt}"
    text = render_lakefile(entry, entries, version, dep_owner, pins)
    if fmt == "toml":
        tomllib.loads(text)
    other = clone / f"lakefile.{'lean' if fmt == 'toml' else 'toml'}"
    if other.exists():
        other.unlink()
        notes.append(f"  removed {other.name}")
    if not path.is_file() or path.read_text(encoding="utf-8") != text:
        path.write_text(text, encoding="utf-8")
        notes.append(f"  generated {path.name}")
    if entry.get("pins_only"):
        umbrella = clone / "Hex.lean"
        body = render_aggregate_umbrella(entries)
        if not umbrella.is_file() or umbrella.read_text(encoding="utf-8") != body:
            umbrella.write_text(body, encoding="utf-8")
            notes.append("  generated Hex.lean")
    return notes


def remote_tag_target(clone: Path, version: str) -> str | None:
    """Return the commit named by a remote lightweight tag, if it exists."""
    output = run(
        ["git", "ls-remote", "--refs", "origin", f"refs/tags/{version}"],
        cwd=clone,
        capture=True,
    )
    if not output:
        return None
    lines = output.splitlines()
    if len(lines) != 1 or len(lines[0].split()) != 2:
        raise RuntimeError(f"unexpected remote tag response for {version!r}")
    return lines[0].split()[0]


def version_tag_collisions(entries: list[dict], version: str) -> dict[str, str]:
    """Existing tags that prevent allocating a new shared version."""
    collisions: dict[str, str] = {}
    for entry in entries:
        repo = entry["repo"]
        output = run(
            ["git", "ls-remote", "--refs", clone_url(repo, None),
             f"refs/tags/{version}"],
            capture=True,
        )
        if output:
            fields = output.split()
            if len(fields) != 2:
                raise RuntimeError(
                    f"unexpected remote tag response for {repo}@{version}"
                )
            collisions[repo] = fields[0]
    return collisions


def sync_repo(entry: dict, source_sha: str, token: str | None, dry_run: bool,
              synced: dict[str, str], baseline: dict[str, str], force: bool,
              dep_owner: dict[str, str],
              pins: dict[str, dict[str, str]], version: str,
              resuming: bool, stage: Path | None = None,
              entries: list[dict] | None = None) -> bool:
    """Sync and tag one repo; return whether it belongs to this release.

    With `stage`, the rewritten tree (without `.git`) is also copied to
    `stage/<short name>`, so `consumer_check.py` can build exactly what this
    run would publish.
    """
    if entries is None:
        entries = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))["repos"]
    repo = entry["repo"]
    short = repo.split("/")[-1]
    print(f"\n=== {repo} ===")
    with tempfile.TemporaryDirectory() as td:
        clone = Path(td) / short
        run(["git", "clone", "--depth", "1", clone_url(repo, token), str(clone)], capture=True)
        head = run(["git", "rev-parse", "HEAD"], cwd=clone, capture=True)
        tagged = remote_tag_target(clone, version)
        # Compare-and-swap guard: refuse to overwrite a repo whose main has moved
        # off the baseline this monorepo was synced from (an uncoordinated commit).
        expected = baseline.get(short)
        if expected and head != expected:
            # The process may have been interrupted after its atomic main+tag
            # push and before the baseline write. A recorded pending transaction
            # makes that exact tag a sufficient, immutable recovery marker.
            if resuming and tagged == head:
                print(f"  resumed {repo}@{version} ({head[:12]})")
                synced[short] = head
                return True
            msg = (f"  UNCOORDINATED: {repo} main is {head[:12]}, baseline expects "
                   f"{expected[:12]}. Reconcile (re-seed from main) before syncing.")
            if not force:
                print(msg + " Skipping (use --force to override).")
                synced[short] = expected
                return False
            print(msg + " Overriding (--force).")
        validate_ci_helpers(entry, clone)
        for line in apply_paths(entry, clone):
            print(line)
        for line in write_lakefile(entry, clone, entries, version, dep_owner, pins):
            print(line)
        validate_external_imports(entry, clone)
        for line in rewrite_toolchains(clone):
            print(line)
        for line in rewrite_manifest(entry, clone, synced, dep_owner, pins, version):
            print(line)
        validate_manifest(entry, clone)
        if stage is not None:
            shutil.copytree(clone, stage / short,
                            ignore=shutil.ignore_patterns(".git"))
        status = run(["git", "status", "--porcelain"], cwd=clone, capture=True)
        if not status:
            print("  (no changes)")
            synced[short] = head
            if dry_run:
                print(f"  DRY-RUN: would tag current main as {version}")
                return False
            if tagged is not None:
                if tagged != head:
                    raise RuntimeError(
                        f"{repo} already has {version} at {tagged[:12]}, not "
                        f"current main {head[:12]}"
                    )
                print(f"  {version} already tags {repo}@{head[:12]}")
                return True
            run(["git", "tag", version, head], cwd=clone)
            run(["git", "push", "origin", f"refs/tags/{version}"], cwd=clone)
            print(f"  tagged {repo}@{version} ({head[:12]})")
            return True
        print("  changed files:")
        for l in status.splitlines():
            print(f"    {l}")
        if dry_run:
            workflow_diff = run(
                ["git", "diff", "--", ".github/workflows/ci.yml"],
                cwd=clone,
                capture=True,
            )
            if workflow_diff:
                print("  managed workflow diff:")
                for line in workflow_diff.splitlines():
                    print(f"    {line}")
            synced[short] = head  # stand-in so downstream pin previews resolve
            print(f"  DRY-RUN: would commit, push, and tag {version}")
            return False
        if tagged is not None:
            raise RuntimeError(
                f"{repo} already has {version} at {tagged[:12]}, but this sync "
                "would change its contents"
            )
        run(["git", "add", "-A"], cwd=clone)
        run(["git", "-c", "user.name=hex-dev sync",
             "-c", "user.email=noreply@anthropic.com",
             "commit", "-q", "-m", f"chore: sync from hex-dev@{source_sha[:12]}"], cwd=clone)
        synced[short] = run(["git", "rev-parse", "HEAD"], cwd=clone, capture=True)
        run(["git", "tag", version, synced[short]], cwd=clone)
        run(["git", "push", "--atomic", "origin", "HEAD:main",
             f"refs/tags/{version}"], cwd=clone)
        print(f"  pushed {synced[short][:12]} to {repo}@main and tagged {version}")
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
                    help="GitHub token with contents:write and workflows:write "
                         "on (a subset of) the released repos; repeatable, "
                         "tried in order per repo. "
                         "Defaults to $RELEASED_SYNC_PAT, $RELEASED_SYNC_PAT_2, ...")
    ap.add_argument("--only", help="sync only this repo short-name (e.g. hex-matrix)")
    ap.add_argument("--force", action="store_true",
                    help="override the uncoordinated-commit guard and overwrite anyway")
    ap.add_argument("--baseline", default=str(BASELINE), type=Path,
                    help="path to the per-repo baseline JSON to read and advance "
                         "(the workflow points this at the release-sync-baseline branch's copy)")
    ap.add_argument("--stage", type=Path,
                    help="with --dry-run, copy every rewritten repository to "
                         "STAGE/<name> for scripts/release/consumer_check.py")
    args = ap.parse_args()
    if args.stage is not None and not args.dry_run:
        ap.error("--stage requires --dry-run")
    if args.stage is not None:
        args.stage.mkdir(parents=True, exist_ok=True)
        if any(args.stage.iterdir()):
            ap.error(f"--stage directory {args.stage} is not empty")

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
    try:
        version, completed, resuming = release_transaction(baseline_doc, source_sha)
    except (RuntimeError, ValueError) as exc:
        print(f"release sync: {exc}", file=sys.stderr)
        return 1
    all_repos = {entry["repo"].split("/")[-1] for entry in manifest["repos"]}
    unknown_completed = completed - all_repos
    if unknown_completed:
        print(
            "release sync: pending release names repositories absent from "
            f"released.yml: {', '.join(sorted(unknown_completed))}",
            file=sys.stderr,
        )
        return 1
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
    if not resuming:
        try:
            collisions = version_tag_collisions(manifest["repos"], version)
        except (RuntimeError, subprocess.CalledProcessError) as exc:
            print(f"release sync: version-tag preflight failed: {exc}", file=sys.stderr)
            return 1
        if collisions:
            print(
                f"release sync: cannot allocate shared version {version}; "
                "the tag already exists:",
                file=sys.stderr,
            )
            for repo, revision in collisions.items():
                print(f"  {repo}@{version} -> {revision[:12]}", file=sys.stderr)
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
              f"({per_slot}; Contents grants verified; Workflows grants are "
              "checked by GitHub when workflow changes are pushed)")

        # Allocate the version before the first push. The workflow publishes
        # this file even if a later repository fails, so retries resume rather
        # than minting a new version halfway through the repository graph.
        baseline_doc["_pending_release"] = {
            "version": version,
            "source": source_sha,
            "repos": sorted(completed),
        }
        write_baseline(args.baseline, baseline_doc)
        print(f"release {version}: " + ("resuming" if resuming else "started"))
    else:
        print(f"release {version}: preview")

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
            released = sync_repo(entry, source_sha, token, args.dry_run,
                                 synced, baseline, args.force, dep_owner, pins,
                                 version, resuming, args.stage, manifest["repos"])
            if not args.dry_run:
                if released:
                    completed.add(entry["repo"].split("/")[-1])
                baseline_doc.update(synced)
                baseline_doc["_pending_release"]["repos"] = sorted(completed)
                write_baseline(args.baseline, baseline_doc)
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
        if not args.dry_run:
            baseline_doc.update(synced)
            baseline_doc["_pending_release"]["repos"] = sorted(completed)
            if failed_repo is None and completed == all_repos:
                baseline_doc["_version"] = version
                del baseline_doc["_pending_release"]
                print(f"\ncompleted release {version} across {len(all_repos)} repositories")
            write_baseline(args.baseline, baseline_doc)
            print(f"\nadvanced baseline -> {args.baseline}")
    if not args.dry_run and failed_repo is None and completed != all_repos and not args.only:
        missing = ", ".join(sorted(all_repos - completed))
        failed_repo = "<release>"
        print(f"\nrelease {version} remains incomplete: {missing}", file=sys.stderr)
    print(f"\nsynced {len(synced)} repo(s) from hex-dev@{source_sha[:12]}"
          + (f" for {version} (dry-run)" if args.dry_run else f" for {version}"))
    return 1 if failed_repo else 0


if __name__ == "__main__":
    raise SystemExit(main())
