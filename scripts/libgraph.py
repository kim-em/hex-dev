from __future__ import annotations

from collections import OrderedDict, deque
from dataclasses import dataclass
from pathlib import Path
import re
import tomllib


KNOWN_EXCEPTIONS = {"Hex", "HexManual"}
EXTERNAL_IMPORT_ROOTS = {"Mathlib", "Verso"}
RELEASE_LIBRARIES = {
    1: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGfqRing",
        "HexGfqField",
        "HexGF2",
    ],
    2: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGfqRing",
        "HexGfqField",
        "HexGF2",
        "HexBerlekamp",
        "HexBerlekampMathlib",
        "HexConway",
        "HexGfq",
    ],
    3: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGfqRing",
        "HexGfqField",
        "HexGF2",
        "HexBerlekamp",
        "HexBerlekampMathlib",
        "HexConway",
        "HexGfq",
        "HexPolyZ",
        "HexHensel",
        "HexBerlekampZassenhaus",
    ],
    4: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGfqRing",
        "HexGfqField",
        "HexGF2",
        "HexBerlekamp",
        "HexBerlekampMathlib",
        "HexConway",
        "HexGfq",
        "HexPolyZ",
        "HexHensel",
        "HexBerlekampZassenhaus",
        "HexLLL",
    ],
}


VALID_STATUSES = {"active", "planned", "draft"}


@dataclass(frozen=True)
class LibraryInfo:
    name: str
    deps: tuple[str, ...]
    mathlib: bool
    done_through: int
    status: str

    @property
    def is_active(self) -> bool:
        return self.status == "active"


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def load_libraries(path: Path | None = None) -> "OrderedDict[str, LibraryInfo]":
    path = path or repo_root() / "libraries.yml"
    lines = path.read_text(encoding="utf-8").splitlines()
    libs: "OrderedDict[str, LibraryInfo]" = OrderedDict()
    in_libraries = False
    current_name: str | None = None
    current_fields: dict[str, object] = {}

    def flush_current() -> None:
        nonlocal current_name, current_fields
        if current_name is None:
            return
        missing = {"deps", "mathlib", "done_through", "status"} - current_fields.keys()
        if missing:
            raise ValueError(f"{current_name} missing fields: {sorted(missing)}")
        deps = current_fields["deps"]
        if not isinstance(deps, list) or not all(isinstance(dep, str) for dep in deps):
            raise ValueError(f"{current_name} has malformed deps")
        mathlib = current_fields["mathlib"]
        if not isinstance(mathlib, bool):
            raise ValueError(f"{current_name} has malformed mathlib flag")
        done_through = current_fields["done_through"]
        if not isinstance(done_through, int):
            raise ValueError(f"{current_name} has malformed done_through")
        status = current_fields["status"]
        if not isinstance(status, str) or status not in VALID_STATUSES:
            raise ValueError(
                f"{current_name} has malformed status {status!r}; "
                f"must be one of {sorted(VALID_STATUSES)}"
            )
        if status != "active" and done_through != 0:
            raise ValueError(
                f"{current_name} has status: {status} but done_through: {done_through}; "
                f"non-active libraries must have done_through == 0 "
                f"(see PLAN/Conventions.md §'Library status')"
            )
        libs[current_name] = LibraryInfo(
            name=current_name,
            deps=tuple(deps),
            mathlib=mathlib,
            done_through=done_through,
            status=status,
        )
        current_name = None
        current_fields = {}

    for raw_line in lines:
        content = raw_line.split("#", 1)[0].rstrip()
        if not content:
            continue
        if not in_libraries:
            if content == "libraries:":
                in_libraries = True
            continue
        indent = len(content) - len(content.lstrip(" "))
        stripped = content.strip()
        if indent == 2 and stripped.endswith(":"):
            flush_current()
            current_name = stripped[:-1]
            if not current_name:
                raise ValueError("empty library name")
            continue
        if indent == 4 and ":" in stripped and current_name is not None:
            key, value = [part.strip() for part in stripped.split(":", 1)]
            current_fields[key] = _parse_scalar(value)
            continue
        raise ValueError(f"cannot parse line: {raw_line}")
    flush_current()

    if not libs:
        raise ValueError("no libraries found in libraries.yml")

    for name, info in libs.items():
        for dep in info.deps:
            if dep not in libs:
                raise ValueError(f"{name} depends on unknown library {dep}")

    # Invariant: active libraries depend only on active libraries.
    # Non-active libraries may depend on anything (the dep graph is
    # informational and may reference libraries in any state).
    # See PLAN/Conventions.md §"Library status".
    for name, info in libs.items():
        if not info.is_active:
            continue
        for dep in info.deps:
            if not libs[dep].is_active:
                raise ValueError(
                    f"{name} (status: active) depends on {dep} "
                    f"(status: {libs[dep].status}); active libraries "
                    f"depend only on active libraries"
                )
    return libs


_BARE_STRING_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*$")


def _parse_scalar(raw: str) -> object:
    if raw == "[]":
        return []
    if raw.startswith("[") and raw.endswith("]"):
        inner = raw[1:-1].strip()
        if not inner:
            return []
        return [part.strip() for part in inner.split(",")]
    if raw == "true":
        return True
    if raw == "false":
        return False
    if raw.isdigit():
        return int(raw)
    if _BARE_STRING_RE.match(raw):
        return raw
    raise ValueError(f"unsupported scalar: {raw}")


LEAN_LIB_RE = re.compile(r"^\s*lean_lib\s+([A-Za-z0-9_«»]+)\s+where\s*$")
TOML_NAME_RE = re.compile(r'^\s*name\s*=\s*"([^"]+)"\s*$')


def load_lakefile_libs(path: Path | None = None) -> list[str]:
    root = repo_root()
    if path is None:
        lean_path = root / "lakefile.lean"
        toml_path = root / "lakefile.toml"
    elif path.is_dir():
        lean_path = path / "lakefile.lean"
        toml_path = path / "lakefile.toml"
    elif path.name == "lakefile.lean":
        lean_path = path
        toml_path = path.with_name("lakefile.toml")
    else:
        toml_path = path
        lean_path = path.with_name("lakefile.lean")

    if lean_path.exists():
        libs: list[str] = []
        for line in lean_path.read_text(encoding="utf-8").splitlines():
            match = LEAN_LIB_RE.match(line)
            if match:
                libs.append(match.group(1))
        if not libs:
            raise ValueError("no lean_lib entries found in lakefile.lean")
        return libs

    if not toml_path.exists():
        raise FileNotFoundError(f"missing Lake config: neither {lean_path} nor {toml_path} exists")

    data = tomllib.loads(toml_path.read_text(encoding="utf-8"))
    entries = data.get("lean_lib", [])
    libs: list[str] = []
    for entry in entries:
        if not isinstance(entry, dict) or "name" not in entry:
            raise ValueError("malformed [[lean_lib]] entry in lakefile.toml")
        libs.append(entry["name"])
    return libs


def check_lakefile_alignment(libraries: OrderedDict[str, LibraryInfo], lakefile_libs: list[str]) -> list[str]:
    errors: list[str] = []
    # Only active libraries must align with Lake; planned/draft entries are
    # exempt by design (no Lean code is expected to exist yet).
    # See PLAN/Conventions.md §"Library status".
    active_library_names = {name for name, info in libraries.items() if info.is_active}
    lake_names = set(lakefile_libs)
    for name in sorted(active_library_names - lake_names):
        errors.append(f"libraries.yml entry {name} missing from Lake config")
    for name in sorted(lake_names - active_library_names - KNOWN_EXCEPTIONS):
        errors.append(f"Lake config library {name} missing from libraries.yml (or library is non-active)")
    for name in sorted(KNOWN_EXCEPTIONS):
        if name not in lake_names:
            errors.append(f"known exception {name} missing from Lake config")
    return errors


def topological_order(libraries: OrderedDict[str, LibraryInfo]) -> list[str]:
    indegree = {name: 0 for name in libraries}
    reverse: dict[str, list[str]] = {name: [] for name in libraries}
    for name, info in libraries.items():
        indegree[name] = len(info.deps)
        for dep in info.deps:
            reverse[dep].append(name)
    queue = deque(name for name, degree in indegree.items() if degree == 0)
    order: list[str] = []
    while queue:
        name = queue.popleft()
        order.append(name)
        for child in reverse[name]:
            indegree[child] -= 1
            if indegree[child] == 0:
                queue.append(child)
    if len(order) != len(libraries):
        raise ValueError("libraries.yml dependency graph is cyclic")
    return order


def reachable_dependencies(libraries: OrderedDict[str, LibraryInfo]) -> dict[str, set[str]]:
    order = topological_order(libraries)
    closure: dict[str, set[str]] = {}
    for name in order:
        reachable = set()
        for dep in libraries[name].deps:
            reachable.add(dep)
            reachable.update(closure[dep])
        closure[name] = reachable
    return closure


def pascal_to_spec_path(name: str) -> str:
    if name == "HexManual":
        raise ValueError("HexManual does not have a SPEC/Libraries entry")
    if not name.startswith("Hex"):
        raise ValueError(f"unexpected library name {name}")
    tail = name[3:]
    tokens = []
    i = 0
    while i < len(tail):
        matched = None
        for token in ("GF2", "GFq", "LLL", "Fp", "CRT", "Mathlib"):
            if tail.startswith(token, i):
                matched = token
                break
        if matched is not None:
            tokens.append(matched)
            i += len(matched)
            continue
        j = i + 1
        while j < len(tail) and not tail[j].isupper():
            j += 1
        tokens.append(tail[i:j])
        i = j
    mapping = {
        "GF2": "gf2",
        "GFq": "gfq",
        "LLL": "lll",
        "Fp": "fp",
        "CRT": "crt",
        "Mathlib": "mathlib",
        "Z": "z",
    }
    parts = ["hex"]
    for token in tokens:
        parts.append(mapping.get(token, token.lower()))
    return f"SPEC/Libraries/{'-'.join(parts)}.md"


def library_owner_for_path(path: Path, libraries: OrderedDict[str, LibraryInfo]) -> str | None:
    parts = path.parts
    if not parts:
        return None
    first = parts[0]
    if first in libraries or first in KNOWN_EXCEPTIONS:
        return first
    if len(parts) == 1 and path.stem in libraries:
        return path.stem
    if len(parts) == 1 and path.stem in KNOWN_EXCEPTIONS:
        return path.stem
    return None
