"""Interpret archived canonical-search timing columns without rewriting evidence."""
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison


def normalize(record: dict) -> dict:
    result = dict(record)
    result["search_column"] = "search_ns"
    if "search_ns" not in result:
        if "eng_ns" in result:
            result["search_column"] = "eng_ns"
            result["search_ns"] = result["eng_ns"]
            if "eng_nodes" in result and "nodes" in result and result["eng_nodes"] != result["nodes"]:
                raise ValueError("archived engine and literal traversal counts differ")
            result["nodes"] = result.get("eng_nodes", result.get("nodes"))
        elif "lit_ns" in result:
            result["search_column"] = "lit_ns"
            result["search_ns"] = result["lit_ns"]
    return result
