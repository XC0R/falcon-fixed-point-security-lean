"""Split the output of a reference-vector run (Python 3, standard library only).

usage: lake env lean <run file> | python3 scripts/split_vectors.py <vecdir>

Lines '@@VEC <name> <text>' are written (text only) to <vecdir>/<name>; every other line is
copied to stdout. At the end, one line '<sha256>  <name>' per vector file written is printed to
stderr, in the format of evidence/vectors/*/SHA256SUMS.
"""
import hashlib
import os
import sys


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    vecdir = sys.argv[1]
    os.makedirs(vecdir, exist_ok=True)
    files = {}
    for line in sys.stdin:
        if line.startswith("@@VEC "):
            _, name, text = line.split(" ", 2)
            if "/" in name or not name.endswith(".json"):
                sys.exit("bad vector name: " + name)
            if name not in files:
                files[name] = open(os.path.join(vecdir, name), "w", encoding="utf-8", newline="\n")
            files[name].write(text)
            continue
        sys.stdout.write(line)
    for f in files.values():
        f.close()
    for name in sorted(files):
        with open(os.path.join(vecdir, name), "rb") as f:
            sys.stderr.write("%s  %s\n" % (hashlib.sha256(f.read()).hexdigest(), name))


main()
