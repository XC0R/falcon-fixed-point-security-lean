# Evidence for the `#eval` facts of LIMITS.md

The `#eval` facts E4-E7, E9-E11, E13-E16, E18, E19, E22, E24, E27, E29-E32 and E34 of
[LIMITS.md](../LIMITS.md#eval-evidence) and entry 0 of E8 are checked by `#guard_msgs` in `test/Exec*.lean`
(`lake build Axioms`), E12 by `lake env lean test/ExecEquivEval.lean`, E28 by
`lake env lean test/ExecEquivEval1024.lean` and `lake env lean test/ExecEquivEval1024Sig.lean`. This directory holds
what the other facts need: E1, E2, E3, E8 (entries 0-99), E17, E20, E21, E23, E25, E26 and E33.

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

The run files of E20, E21, E23, E25 and E33 are generated from the Falcon-1024 known-answer-test file
`falcon1024-KAT.rsp` of the same archives (not in this repository either; it is next to `falcon512-KAT.rsp` in each
archive, `unzip -l` lists its path). `falcon1024-KAT.rsp` (1757286 bytes, 100 entries) has sha256
`036a0bf5260573cec44977284dfef756cd1143db9961b981bd1fb55828acb20d` in both archives.

## The SamplerZ trace

The run files of E26 are generated from `test-vector-sampler-falcon1024.txt` (`Supporting_Documentation/additional/`
in both archives; 2548902 bytes, 57761 lines, sha256
`c07bc528284590a10d3d84e85446214107426bb7943f4e4aac9996ea93fd92cd` in both): one Falcon-1024 signature of the
reference implementation with each SamplerZ call's inputs, random values and output. It is not in this repository.

## Running

From the repository root, after `lake build` (Python 3, standard library only):

```sh
python3 scripts/gen_evidence_runs.py <path>/falcon512-KAT.rsp runs   # checks the sha256, writes runs/
lake env lean runs/key-check-d45/halfEven-0-a.lean > runs/new.txt
python3 scripts/check_output.py evidence/key-check-d45/halfEven-0-a.out runs/new.txt
python3 scripts/gen_evidence_runs.py <path>/falcon1024-KAT.rsp runs  # checks the sha256, adds runs/kat1024-entries/,
                                                                     # runs/key-check-1024-*/, runs/range-1024/ and
                                                                     # runs/vectors-1024/
lake env lean runs/kat1024-entries/KatS0.lean                         # prints nothing
python3 scripts/gen_evidence_runs.py <path>/test-vector-sampler-falcon1024.txt runs  # checks the sha256,
                                                                                    # adds runs/sampler-1024/
```

`scripts/gen_evidence_runs.py` writes one Lean file per run (the sha256 of the KAT file decides which): the KAT data
(hexadecimal strings copied from the `.rsp`) followed by the code of the run, which is the fragment in this directory
(`RunHead.lean`, `RunTail.lean`) or, for the KAT entries and the vectors, the text in the script. No KAT data is in this
directory apart from what the vector files (`vectors/`, `vectors-1024/`) contain; entries 0 and 70 of
`falcon512-KAT.rsp` are also in `FalconPrecision/Exec/WitnessData.lean`, `test/ExecCodec.lean` and
`test/ExecRound3.lean`, and entries 0, 2 and 70 of `falcon1024-KAT.rsp` (keys of 0 and 2; salt and message of all three)
in `FalconPrecision/Exec/WitnessData1024.lean` ([NOTICE](../NOTICE) lists what each contains, the source and the terms).
No other file of this repository contains values copied from `falcon1024-KAT.rsp`; the recorded outputs (`.out`) contain
per-key results and diagnostic values computed from the entries. A trace run file is
`sampler-1024/RunHead.lean` followed by the trace's values, written after the script has checked the trace's lines
against each other (`check_trace`); no file of this repository contains values from the trace except the number of
random bytes of each SamplerZ call in `sampler-1024/*.out`. `scripts/check_output.py` compares a new output with the
recorded one after replacing the run times (`ms=`, `msCheck=`, `msDiag=`) by `*`, and prints the number of differing
lines.

| LIMITS | Run files (written to `runs/`) | Recorded output |
|---|---|---|
| E1 | `key-check-d45/{halfEven,halfUp}-0-{a,b}.lean` (keys 0-49: `a`, 50-99: `b`) | `key-check-d45/*.out` |
| E2 | `key-check-d127/{halfEven,halfUp}-{0,16,32}-{a,b}.lean`, `key-check-d127/decode.lean` | `key-check-d127/*.out` |
| E3 | `key-check-d127-xn32/survey.lean` | `key-check-d127-xn32/survey.out` |
| E8 | `kat-entries/KatS0.lean` … `KatS11.lean` | none: each prints nothing and exits with status 0 (its `#guard_msgs` fails otherwise) |
| E17 | `vectors/d45/{e0,e70,e27}.lean`, `vectors/d127/{e0,e70}.lean` | `vectors/d45/*.out`, `vectors/d127/*.out`; the JSON files and `SHA256SUMS` |
| E20 | `kat1024-entries/KatS0.lean` … `KatS15.lean` | none: each prints nothing and exits with status 0 (its `#guard_msgs` fails otherwise) |
| E21 | `kat1024-entries/HashToPoint.lean` (the hashed points of entries 0 and 70 as computed by Python `hashlib`) | none: prints nothing and exits with status 0 |
| E23 | `key-check-1024-d43/{halfEven,halfUp}-0-<j>.lean`, `key-check-1024-d127/{halfEven,halfUp}-32-<j>.lean` (`j = 0 … 9`: keys `10j … 10j + 9`), `key-check-1024-d127/decode.lean` | `key-check-1024-d43/*.out`, `key-check-1024-d127/*.out` |
| E25 | `range-1024/{scaleFirst,multiplyFirst}-<j>.lean` (`j = 0 … 9`: keys `10j … 10j + 9`) | `range-1024/*.out` |
| E26 | `sampler-1024/calls-<j>.lean` (`j = 0 … 15`: calls `128j … 128j + 127`) | `sampler-1024/*.out` |
| E33 | `vectors-1024/d43/{e0,e2,e11}.lean`, `vectors-1024/d127/{e0,e2,e11}.lean` | `vectors-1024/d43/*.out`, `vectors-1024/d127/*.out`; the JSON files and `SHA256SUMS` |

The vector runs print the JSON file as lines `@@VEC <name> <text>`; to rebuild it:

```sh
lake env lean runs/vectors/d45/e0.lean | python3 scripts/split_vectors.py runs/vec45 > runs/new.txt
python3 scripts/check_output.py evidence/vectors/d45/e0.out runs/new.txt
```

`split_vectors.py` prints the sha256 of each file it writes, to compare with `evidence/vectors/d45/SHA256SUMS`
(`evidence/vectors/d127/SHA256SUMS` for the `δ127q` set). At Falcon-1024:
`lake env lean runs/vectors-1024/d43/e0.lean | python3 scripts/split_vectors.py runs/vec1024-43 > runs/new.txt`, then
`python3 scripts/check_output.py evidence/vectors-1024/d43/e0.out runs/new.txt` and compare with
`evidence/vectors-1024/d43/SHA256SUMS` (`d127/` for the `δ127q_1024` set).

## How the recorded outputs relate to the recorded runs

Each `.out` file holds the output lines of one recorded run, copied from its log. The run files written by the
script differ from the recorded ones only in their header comment and docstring, except in two cases: the recorded
E3 run printed a constant label before each line, which `RunTail.lean` does not print and `survey.out` does not
contain; the recorded `δ45q` vector runs had a second `#eval` (`checkFast` at ties to even, `xn = 0`, which the first
line of the output also reports), which is not in the script and whose output line is not in `vectors/d45/*.out`.
The KAT data in each run file is byte for byte that of the recorded run.

The recorded runs were on x86_64. Every run of the facts in the table above (E1-E3, E8, E17, E20, E21, E23, E25, E26,
E33), and of E12 and E28, was repeated on x86_64 and on aarch64 from the Lean sources, scripts and recorded outputs of
release 0.6.0; see the last paragraph
of [`#eval` evidence](../LIMITS.md#eval-evidence) in LIMITS.md.
