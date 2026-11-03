"""Strict JSON parsing for F4 driver output and retained timing evidence."""
import json


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def loads(text):
    return json.loads(text, object_pairs_hook=unique_object)
