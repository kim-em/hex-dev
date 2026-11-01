#!/usr/bin/env python3
"""Require both complete scheduling profiles and identical polynomial problems."""
from __future__ import annotations


def validate_corpus(records):
    profiles = {"degree": {}, "sugar": {}}
    for record in records:
        value = record["value"]
        strategy = value["scheduling"]
        assert strategy in profiles, f"unknown scheduling profile: {strategy}"
        name = record["case"]
        assert name.endswith("/sugar") == (strategy == "sugar"), "scheduling case mismatch"
        key = name.removesuffix("/sugar")
        assert key not in profiles[strategy], f"duplicate {strategy} case: {key}"
        profiles[strategy][key] = value
    assert all(len(cases) == 567 for cases in profiles.values()), "incomplete scheduling corpus"
    assert profiles["degree"].keys() == profiles["sugar"].keys(), "different scheduling cases"
    for name, degree in profiles["degree"].items():
        sugar = profiles["sugar"][name]
        for key in ["p", "variables", "order", "generators", "basis"]:
            assert degree[key] == sugar[key], f"{name}: scheduling changes {key}"
