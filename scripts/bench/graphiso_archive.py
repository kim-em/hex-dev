"""Interpret archived canonical-search timing columns without rewriting evidence."""
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison


def normalize(record: dict) -> dict:
    result = dict(record)
    if "search_ns" not in result:
        if "eng_ns" in result:
            result["search_ns"] = result["eng_ns"]
            result["nodes"] = result.get("eng_nodes", result.get("nodes"))
        elif "lit_ns" in result:
            result["search_ns"] = result["lit_ns"]
    return result
