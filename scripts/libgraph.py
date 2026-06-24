from __future__ import annotations

from collections import OrderedDict, deque
from dataclasses import dataclass
from pathlib import Path
import ast
import re
import tomllib


KNOWN_EXCEPTIONS = {"Hex", "HexManual"}
EXTERNAL_IMPORT_ROOTS = {"Mathlib", "Verso"}
RELEASE_LIBRARIES = {
    1: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGFqRing",
        "HexGFqField",
        "HexGF2",
    ],
    2: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGFqRing",
        "HexGFqField",
        "HexGF2",
        "HexBerlekamp",
        "HexBerlekampMathlib",
        "HexConway",
        "HexGFq",
    ],
    3: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGFqRing",
        "HexGFqField",
        "HexGF2",
        "HexBerlekamp",
        "HexBerlekampMathlib",
        "HexConway",
        "HexGFq",
        "HexPolyZ",
        "HexHensel",
        "HexBerlekampZassenhaus",
    ],
    4: [
        "HexModArith",
        "HexPoly",
        "HexPolyFp",
        "HexGFqRing",
        "HexGFqField",
        "HexGF2",
        "HexBerlekamp",
        "HexBerlekampMathlib",
        "HexConway",
        "HexGFq",
        "HexPolyZ",
        "HexHensel",
        "HexBerlekampZassenhaus",
        "HexLLL",
    ],
}


VALID_STATUSES = {"active", "planned", "draft"}
PHASE4_COMPARATOR_CLASSES = {"gating", "informational"}


@dataclass(frozen=True)
class Phase4Comparator:
    tool: str
    classification: str
    goal: str | None = None
    rationale: str | None = None


@dataclass(frozen=True)
class Phase4InputFamily:
    name: str
    description: str


@dataclass(frozen=True)
class Phase4Info:
    comparators: tuple[Phase4Comparator, ...] = ()
    input_families: tuple[Phase4InputFamily, ...] = ()


@dataclass(frozen=True)
class LibraryInfo:
    name: str
    deps: tuple[str, ...]
    mathlib: bool
    done_through: int
    status: str
    phase4: Phase4Info | None = None
    external: str | None = None

    @property
    def is_active(self) -> bool:
        return self.status == "active"

    @property
    def is_external(self) -> bool:
        """True iff the library lives in its own released git repo.

        External libraries are consumed via a git ``require`` in the
        Lake config rather than a local ``lean_lib`` plus root file, so
        the Lake-alignment and root-file checks are waived for them
        (they still participate in the dependency-closure graph)."""
        return self.external is not None


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
        phase4 = current_fields.get("phase4")
        if phase4 is not None and not isinstance(phase4, Phase4Info):
            raise ValueError(f"{current_name} has malformed phase4 block")
        external = current_fields.get("external")
        if external is not None and not isinstance(external, str):
            raise ValueError(f"{current_name} has malformed external field")
        libs[current_name] = LibraryInfo(
            name=current_name,
            deps=tuple(deps),
            mathlib=mathlib,
            done_through=done_through,
            status=status,
            phase4=phase4,
            external=external,
        )
        current_name = None
        current_fields = {}

    line_index = 0
    while line_index < len(lines):
        raw_line = lines[line_index]
        content = _strip_comment(raw_line).rstrip()
        line_index += 1
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
            if key == "phase4" and value == "":
                phase4, line_index = _parse_phase4_block(lines, line_index, current_name)
                current_fields[key] = phase4
                continue
            if key == "external":
                current_fields[key] = _parse_string(value)
                continue
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


def _strip_comment(raw: str) -> str:
    in_single = False
    in_double = False
    escaped = False
    for index, char in enumerate(raw):
        if escaped:
            escaped = False
            continue
        if char == "\\" and in_double:
            escaped = True
            continue
        if char == "'" and not in_double:
            in_single = not in_single
            continue
        if char == '"' and not in_single:
            in_double = not in_double
            continue
        if char == "#" and not in_single and not in_double:
            return raw[:index]
    return raw


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


def _parse_string(raw: str) -> str:
    raw = raw.strip()
    if (raw.startswith('"') and raw.endswith('"')) or (
        raw.startswith("'") and raw.endswith("'")
    ):
        value = ast.literal_eval(raw)
        if not isinstance(value, str):
            raise ValueError(f"expected string, got {raw}")
        return value
    if raw == "":
        raise ValueError("expected non-empty string")
    return raw


def _parse_phase4_block(
    lines: list[str], start_index: int, library_name: str
) -> tuple[Phase4Info, int]:
    fields: dict[str, list[dict[str, str]]] = {}
    index = start_index
    current_list_name: str | None = None
    current_item: dict[str, str] | None = None

    def fail(message: str) -> ValueError:
        return ValueError(f"{library_name}.phase4 {message}")

    while index < len(lines):
        raw_line = lines[index]
        content = _strip_comment(raw_line).rstrip()
        if not content:
            index += 1
            continue
        indent = len(content) - len(content.lstrip(" "))
        stripped = content.strip()
        if indent <= 4:
            break
        if indent == 6 and stripped.endswith(":"):
            current_list_name = stripped[:-1]
            if current_list_name not in {"comparators", "input_families"}:
                raise fail(f"has unknown key {current_list_name!r}")
            if current_list_name in fields:
                raise fail(f"duplicates {current_list_name}")
            fields[current_list_name] = []
            current_item = None
            index += 1
            continue
        if indent == 8 and stripped.startswith("- "):
            if current_list_name is None:
                raise fail("has list item outside comparators/input_families")
            item_text = stripped[2:].strip()
            current_item = {}
            fields[current_list_name].append(current_item)
            if item_text:
                key, value = _parse_phase4_key_value(item_text, library_name)
                current_item[key] = value
            index += 1
            continue
        if indent == 10 and current_item is not None:
            key, value = _parse_phase4_key_value(stripped, library_name)
            current_item[key] = value
            index += 1
            continue
        raise fail(f"cannot parse line: {raw_line}")

    comparators = tuple(
        _validate_phase4_comparator(library_name, entry)
        for entry in fields.get("comparators", [])
    )
    input_families = tuple(
        _validate_phase4_input_family(library_name, entry)
        for entry in fields.get("input_families", [])
    )
    return Phase4Info(comparators=comparators, input_families=input_families), index


def _parse_phase4_key_value(text: str, library_name: str) -> tuple[str, str]:
    if ":" not in text:
        raise ValueError(f"{library_name}.phase4 expected key: value, got {text!r}")
    key, value = [part.strip() for part in text.split(":", 1)]
    if not key:
        raise ValueError(f"{library_name}.phase4 has empty key")
    return key, _parse_string(value)


def _validate_phase4_comparator(
    library_name: str, entry: dict[str, str]
) -> Phase4Comparator:
    allowed = {"tool", "class", "goal", "rationale"}
    unknown = sorted(set(entry) - allowed)
    if unknown:
        raise ValueError(
            f"{library_name}.phase4.comparators has unknown keys: {unknown}"
        )
    missing = {"tool", "class"} - set(entry)
    if missing:
        raise ValueError(
            f"{library_name}.phase4.comparators entry missing keys: {sorted(missing)}"
        )
    classification = entry["class"]
    if classification not in PHASE4_COMPARATOR_CLASSES:
        raise ValueError(
            f"{library_name}.phase4.comparators class {classification!r} "
            f"must be one of {sorted(PHASE4_COMPARATOR_CLASSES)}"
        )
    if classification == "gating" and "goal" not in entry:
        raise ValueError(f"{library_name}.phase4.comparators gating entry missing goal")
    if classification == "informational" and "rationale" not in entry:
        raise ValueError(
            f"{library_name}.phase4.comparators informational entry missing rationale"
        )
    return Phase4Comparator(
        tool=entry["tool"],
        classification=classification,
        goal=entry.get("goal"),
        rationale=entry.get("rationale"),
    )


def _validate_phase4_input_family(
    library_name: str, entry: dict[str, str]
) -> Phase4InputFamily:
    allowed = {"name", "description"}
    unknown = sorted(set(entry) - allowed)
    if unknown:
        raise ValueError(
            f"{library_name}.phase4.input_families has unknown keys: {unknown}"
        )
    missing = allowed - set(entry)
    if missing:
        raise ValueError(
            f"{library_name}.phase4.input_families entry missing keys: {sorted(missing)}"
        )
    return Phase4InputFamily(name=entry["name"], description=entry["description"])


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
    # Lake alignment per PLAN/Conventions.md §"Library status":
    #   active local entry  ⟺  lean_lib in lakefile
    #   planned/draft entry  ⟹  no lean_lib in lakefile
    # External libraries (released into their own git repo and consumed via
    # a git `require`) have no local `lean_lib`; they are exempt from this
    # check while still participating in the dependency graph.
    active_library_names = {
        name for name, info in libraries.items()
        if info.is_active and not info.is_external
    }
    nonactive_library_names = {
        name for name, info in libraries.items()
        if not info.is_active and not info.is_external
    }
    external_library_names = {name for name, info in libraries.items() if info.is_external}
    lake_names = set(lakefile_libs)
    for name in sorted(active_library_names - lake_names):
        errors.append(f"libraries.yml entry {name} (status: active) missing from Lake config")
    for name in sorted(nonactive_library_names & lake_names):
        info = libraries[name]
        errors.append(
            f"libraries.yml entry {name} (status: {info.status}) "
            f"appears in Lake config; non-active libraries must not have a lean_lib entry"
        )
    for name in sorted(
        lake_names
        - active_library_names
        - nonactive_library_names
        - external_library_names
        - KNOWN_EXCEPTIONS
    ):
        errors.append(f"Lake config library {name} missing from libraries.yml")
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


def may_import(
    l_a: str,
    l_b: str,
    libraries: OrderedDict[str, LibraryInfo],
    closure: dict[str, set[str]] | None = None,
) -> bool:
    """True iff a file in library ``l_a`` may import a module from ``l_b``.

    This holds when ``l_b == l_a`` or ``l_b`` is in ``l_a``'s transitive
    ``libraries.yml`` dependency closure. It mirrors Lake's actual
    symbol-visibility semantics and is the predicate the import-boundary
    check in ``check_dag.py`` and the issue-graph guard both consult
    (see PLAN/Conventions.md §"Inverted dependencies are rejected").

    Pass a precomputed ``closure`` (from ``reachable_dependencies``) when
    making many calls to avoid recomputing the topological closure each
    time; otherwise it is built on demand.
    """
    if l_a not in libraries:
        raise ValueError(f"unknown library {l_a!r}")
    if l_b not in libraries:
        raise ValueError(f"unknown library {l_b!r}")
    if l_b == l_a:
        return True
    if closure is None:
        closure = reachable_dependencies(libraries)
    return l_b in closure[l_a]


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
