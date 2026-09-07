"""Source identities for in-repository Lean modules and their import closure."""

import hashlib
from pathlib import Path
import re


def imports(path):
    names = []
    for match in re.finditer(
        r"^[ \t]*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\n]+)",
        path.read_text(),
        re.MULTILINE,
    ):
        names.extend(match[1].split("--", 1)[0].split())
    return names


def sources(prefixes):
    return sorted(
        p
        for prefix in prefixes
        for p in [*Path(prefix).rglob("*.lean"), Path(prefix + ".lean")]
        if p.is_file()
    )


def dependencies(paths):
    """Return every existing local module reachable by imports, excluding roots."""
    roots = set(paths)
    seen, pending = set(roots), list(roots)
    while pending:
        for name in imports(pending.pop()):
            path = Path(name.replace(".", "/") + ".lean")
            if path.is_file() and path not in seen:
                seen.add(path)
                pending.append(path)
    return sorted(seen - roots)


def hashes(paths):
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
