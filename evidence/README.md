# Evidence for the `#eval` facts of LIMITS.md

The `#eval` facts E4-E7, E9-E11, E13-E16, E18 and E19 of [LIMITS.md](../LIMITS.md#eval-evidence) and entry 0 of
E8 are checked by `#guard_msgs` in `test/Exec*.lean` (`lake build Axioms`), E12 by
`lake env lean test/ExecEquivEval.lean`.
This directory holds what the other facts need: E1, E2, E3, E8 (entries 0-99) and E17.

## The KAT file

The run files of E1, E2, E3, E8 and E17 are generated from the Falcon-512 known-answer-test file
`falcon512-KAT.rsp` of the Falcon round-3 submission package (specification v1.2). It is not in this repository. It
is contained in either archive:

| Archive | URL | sha256 (downloaded 2026-11-22) |
|---|---|---|
| `Falcon-Round3.zip` | https://csrc.nist.gov/CSRC/media/Projects/post-quantum-cryptography/documents/round-3/submissions/Falcon-Round3.zip | `fd58f0454f6bfb4713734e60b2d2d75d96fbae62d5180fceeef1039df5362f44` |
| `falcon-round3.zip` | https://falcon-sign.info/falcon-round3.zip | `d625407dbda9e5835f610aaeba1147e029988a6610e0107dfd292033138e1d47` |

`falcon512-KAT.rsp` (1250115 bytes, 100 entries) has sha256
`dd75c946fdedef4ec46a2bee7e10c65c9126f1a839b9ced6921fd45f7354b5cd` in both archives (`unzip -l <archive>` lists its
path inside the archive).

## Running

From the repository root, after `lake build` (Python 3, standard library only):

```sh
python3 scripts/gen_evidence_runs.py <path>/falcon512-KAT.rsp runs   # checks the sha256, writes runs/
lake env lean runs/key-check-d45/halfEven-0-a.lean > runs/new.txt
python3 scripts/check_output.py evidence/key-check-d45/halfEven-0-a.out runs/new.txt
```

`scripts/gen_evidence_runs.py` writes one Lean file per run: the KAT data (hexadecimal strings copied from the
`.rsp`) followed by the code of the run, which is the fragment in this directory (`RunHead.lean`, `RunTail.lean`) or,
for the KAT entries and the vectors, the text in the script. No KAT data is in this directory apart from what the
vector files contain; entries 0 and 70 are also in `FalconPrecision/Exec/WitnessData.lean`, `test/ExecCodec.lean` and
`test/ExecRound3.lean` ([NOTICE](../NOTICE) lists what each contains, the source and the terms).
`scripts/check_output.py` compares a new output with the recorded one after replacing the run times
(`ms=`, `msCheck=`, `msDiag=`) by `*`, and prints the number of differing lines.

| LIMITS | Run files (written to `runs/`) | Recorded output |
|---|---|---|
| E1 | `key-check-d45/{halfEven,halfUp}-0-{a,b}.lean` (keys 0-49: `a`, 50-99: `b`) | `key-check-d45/*.out` |
| E2 | `key-check-d127/{halfEven,halfUp}-{0,16,32}-{a,b}.lean`, `key-check-d127/decode.lean` | `key-check-d127/*.out` |
| E3 | `key-check-d127-xn32/survey.lean` | `key-check-d127-xn32/survey.out` |
| E8 | `kat-entries/KatS0.lean` … `KatS11.lean` | none: each prints nothing and exits with status 0 (its `#guard_msgs` fails otherwise) |
| E17 | `vectors/d45/{e0,e70,e27}.lean`, `vectors/d127/{e0,e70}.lean` | `vectors/d45/*.out`, `vectors/d127/*.out`; the JSON files and `SHA256SUMS` |

The vector runs print the JSON file as lines `@@VEC <name> <text>`; to rebuild it:

```sh
lake env lean runs/vectors/d45/e0.lean | python3 scripts/split_vectors.py runs/vec45 > runs/new.txt
python3 scripts/check_output.py evidence/vectors/d45/e0.out runs/new.txt
```

`split_vectors.py` prints the sha256 of each file it writes, to compare with `evidence/vectors/d45/SHA256SUMS`
(`evidence/vectors/d127/SHA256SUMS` for the `δ127q` set).

## How the recorded outputs relate to the recorded runs

Each `.out` file holds the output lines of one recorded run, copied from its log. The run files written by the
script differ from the recorded ones only in their header comment and docstring, except in two cases: the recorded
E3 run printed a constant label before each line, which `RunTail.lean` does not print and `survey.out` does not
contain; the recorded `δ45q` vector runs had a second `#eval` (`checkFast` at ties to even, `xn = 0`, which the first
line of the output also reports), which is not in the script and whose output line is not in `vectors/d45/*.out`.
The KAT data in each run file is byte for byte that of the recorded run.

The recorded runs were on x86_64. Every run was repeated on x86_64 and on aarch64; see the last paragraph of
[`#eval` evidence](../LIMITS.md#eval-evidence) in LIMITS.md.
