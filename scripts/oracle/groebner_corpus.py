#!/usr/bin/env python3
"""Validate both complete scheduling profiles and return their unique problems."""
from __future__ import annotations


def validate_corpus(records):
    profiles = {"degree": {}, "sugar": {}}
    unique = []
    for record in records:
        if not isinstance(record, dict) or any(record.get(key) != value for key, value in
                [("kind", "result"), ("lib", "HexGroebner"), ("op", "f4")]):
            raise ValueError("invalid F4 record header")
        value = record.get("value")
        if not isinstance(value, dict) or "scheduling" not in value:
            raise ValueError("missing scheduling metadata")
        strategy = value["scheduling"]
        if not isinstance(strategy, str) or strategy not in profiles:
            raise ValueError(f"unknown scheduling profile: {strategy}")
        name = record.get("case")
        if not isinstance(name, str) or name.endswith("/sugar") != (strategy == "sugar"):
            raise ValueError("scheduling case mismatch")
        key = name.removesuffix("/sugar")
        if key in profiles[strategy]:
            raise ValueError(f"duplicate {strategy} case: {key}")
        profiles[strategy][key] = value
        if strategy == "degree":
            unique.append(record)
    if any(len(cases) != 567 for cases in profiles.values()):
        raise ValueError("incomplete scheduling corpus")
    if profiles["degree"].keys() != profiles["sugar"].keys():
        raise ValueError("different scheduling cases")
    for name, degree in profiles["degree"].items():
        sugar = profiles["sugar"][name]
        for key in ["p", "variables", "order", "generators", "basis"]:
            if key not in degree or key not in sugar or degree[key] != sugar[key]:
                raise ValueError(f"{name}: scheduling changes {key}")
    return unique
