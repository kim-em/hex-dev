"""Read a Lake build trace's compiler recipe, and digest files it names."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shlex


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def recipe(trace: Path) -> list[str]:
    rows = json.loads(trace.read_text())['log']
    commands = [row['message'][3:] for row in rows if row['message'].startswith('.> ')]
    if len(commands) != 1:
        raise ValueError(f'expected one Lake compiler recipe: {trace}')
    return shlex.split(commands[0])
