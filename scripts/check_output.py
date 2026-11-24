"""Compare the output of an evidence run with its recorded output (Python 3, standard library only).

usage: python3 scripts/check_output.py <recorded .out> <new output>

Before comparing, the run times printed by the key-check runs (`ms=<n>`, `msCheck=<n>`,
`msDiag=<n>`) are replaced by `<field>=*` in both files; nothing else is changed. Prints the
number of differing lines (0 when the outputs agree) and exits with status 1 if it is not 0.
"""
import difflib
import re
import sys

TIME = re.compile(r"\b(ms|msCheck|msDiag)=\d+\b")


def lines(path):
    with open(path, encoding="utf-8") as f:
        return [TIME.sub(r"\1=*", x.rstrip("\n")) for x in f]


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    a, b = lines(sys.argv[1]), lines(sys.argv[2])
    d = [x for x in difflib.unified_diff(a, b, lineterm="", n=0)
         if x[:1] in "+-" and not x.startswith(("+++ ", "--- "))]
    for x in d[:20]:
        print(x)
    print("%s: %d differing lines (%d recorded, %d new)" % (sys.argv[1], len(d), len(a), len(b)))
    sys.exit(1 if d else 0)


main()
