#!/usr/bin/env python3
"""Independent integer-only JSON conformance for the proved byte backend."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import random
import subprocess
import sys

# Certificate integer sizes are checked explicitly by the wire frontend.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "conformance-fixtures/HexSignDet/json-bytes.jsonl"


def reject_number(text):
    raise ValueError("noninteger JSON number: " + text)


class ObjectPairs(list):
    """Keep object fields distinct from arrays, with literal order/duplicates."""


def tagged(value):
    if value is None:
        return ("null",)
    if type(value) is bool:
        return ("bool", value)
    if type(value) is int:
        return ("int", value)
    if isinstance(value, str):
        value.encode("utf-8", errors="strict")
        return ("string", value)
    if isinstance(value, ObjectPairs):
        return ("object", tuple((tagged(key), tagged(item)) for key, item in value))
    if isinstance(value, list):
        return ("array", tuple(tagged(item) for item in value))
    raise ValueError("unexpected JSON value type")


def expected(raw):
    # UTF-8 BOM is outside the byte format; do not use utf-8-sig decoding.
    value = json.loads(raw.decode("utf-8", errors="strict"), object_pairs_hook=ObjectPairs,
                       parse_float=reject_number, parse_constant=reject_number)
    return tagged(value)


def corpus():
    good = [b"null", b"true", b"false", b"-0", b"0", b"[]", b"{}",
            b' { "x" : [1,-2,null,true,false], "y":{} } \r\n',
            b'{"x":1,"x":2}', b'"\\ud83d\\ude00"', b'"\\uD83D\\uDE00"',
            b'"\\b\\f\\n\\r\\t\\/\\\\\\\""', b'"\\u0000\\u001f\\uFFFF"',
            b"[" * 48 + b"0" + b"]" * 48]
    rng = random.Random(10377)
    strings = ["", "\\\"/", "\x00\x01\x08\x0c\n\r\t\x1f", "λ雪😀", "\uffff\U0010ffff"]

    def value(depth):
        atom = [None, True, False, rng.randrange(-(10 ** 90), 10 ** 90), rng.choice(strings)]
        choices = len(atom) if depth == 0 else len(atom) + 2
        choice = rng.randrange(choices)
        if choice < len(atom):
            return atom[choice]
        if choice == len(atom):
            return [value(depth - 1) for _ in range(rng.randrange(5))]
        return {f"{rng.choice(strings)}:{i}": value(depth - 1) for i in range(rng.randrange(5))}

    for i in range(256):
        good.append(json.dumps(value(5), ensure_ascii=i % 2 == 0,
                               separators=(",", ":")).encode("utf-8"))
    bad = [b"", b" ", b"[", b"{", b"[1,]", b'{"a":1,}', b"[1}", b'{"a":1]',
           b"[1 2]", b'{"a" 1}', b"{1:2}", b"[,1]", b"[[,]]", b"00", b"01", b"-01",
           b"+1", b"--1", b"-", b"1.0", b"1e2", b"1E+2", b"NaN", b"Infinity",
           b"[] null", b"nulltrue", b"[truefalse]", b"[1:2]", b"[1,,2]", b"/*x*/null",
           b"\vnull", b"null\f", b'"unterminated', b'"\\q"', b'"\\u123"',
           b'"\\u12xz"', b'"\\ud800"', b'"\\udc00"', b'"\\ud800\\u0041"',
           b'"\\ud800x"', b'"a\nb"', b'"\x00"', b'"\x1f"', b"\xff", b"\xef\xbb\xbfnull", b"[\xef\xbb\xbf0]", b'"\xc0\xaf"',
           b'"\xed\xa0\x80"', b'"\xf4\x90\x80\x80"', b'"\xe2\x82"']
    return [{"bytes": list(raw), "accept": True} for raw in good] + [
        {"bytes": list(raw), "accept": False} for raw in bad]


def check_answer(record, answer):
    raw = bytes(record["bytes"])
    try:
        wanted = expected(raw)
    except (ValueError, UnicodeError):
        if record["accept"]:
            raise ValueError("invalid positive oracle input")
        if answer != ["error"]:
            raise ValueError("malformed or unsupported input accepted")
        return
    if not record["accept"]:
        raise ValueError("valid negative oracle input")
    if not isinstance(answer, list) or len(answer) != 2 or answer[0] != "ok":
        raise ValueError("valid input rejected")
    if expected(answer[1].encode("utf-8")) != wanted:
        raise ValueError("printer changed the parsed value")


def check(fixture, executable):
    records = [json.loads(line) for line in fixture.read_text().splitlines()]
    transport = "".join(json.dumps(r["bytes"]) + "\n" for r in records)
    completed = subprocess.run([str(executable)], input=transport, text=True,
                               capture_output=True, encoding="utf-8", check=True)
    lines = completed.stdout.splitlines()
    if len(lines) != len(records):
        raise ValueError("wrong result count: " + str(len(lines)))
    for i, (record, line) in enumerate(zip(records, lines)):
        try:
            check_answer(record, json.loads(line))
        except (ValueError, UnicodeError) as error:
            raise ValueError(f"case {i}, bytes={record['bytes']}: {error}") from error
    print(f"HexSignDet JSON bytes: {len(records)} independent cases, 0 failures")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path, default=FIXTURE)
    parser.add_argument("--exe", type=Path, default=ROOT / ".lake/build/bin/hexsigndet_json_bytes")
    parser.add_argument("--emit-fixtures", action="store_true")
    args = parser.parse_args()
    if args.emit_fixtures:
        for record in corpus():
            print(json.dumps(record, separators=(",", ":")))
    else:
        check(args.check, args.exe)


if __name__ == "__main__":
    main()
