#!/usr/bin/env python3
"""Audit direct mimalloc calls in a compiled profiler for graphiso_dhat.c.

Print the targets of callers without mi_/_mi_ prefixes, after demangling
C++ names. This conservatively includes C++ startup routines. It checks
direct symbol calls, not possible compiler-inlined or
indirect allocation paths. A changed entry-point set requires checking the
wrapper before using its allocation counts with a new toolchain.
"""
import re
import subprocess
import sys


def main() -> int:
    if len(sys.argv) != 2:
        sys.exit(f"usage: {sys.argv[0]} PROFILER")
    proc = subprocess.Popen(
        ["objdump", "-d", "--demangle", "--no-show-raw-insn", sys.argv[1]],
        stdout=subprocess.PIPE, text=True)
    caller = ""
    found = set()
    for line in proc.stdout:
        label = re.match(r"^[0-9a-f]+ <(.+)>:", line)
        if label:
            caller = label[1]
        call = re.search(r"\b(?:call|jmp)\s+[0-9a-f]+ <(mi_[^>]+)>", line)
        if call and not caller.startswith(("mi_", "_mi_")):
            found.add(call[1])
    if proc.wait():
        sys.exit("objdump failed")
    print("direct mi_* targets called from outside mimalloc:")
    for name in sorted(found):
        print(name)
    expected = {"mi_malloc", "mi_malloc_small", "mi_new_n", "mi_free", "mi_free_size",
                "mi_option_init(mi_option_desc_s*)"}
    if found != expected:
        sys.exit("entry points changed; recheck graphiso_dhat.c coverage")
    return 0


if __name__ == "__main__":
    sys.exit(main())
