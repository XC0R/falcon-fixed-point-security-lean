# Limits of the executable track (Falcon-512)

What the executable track ([README](README.md#executable-track-falcon-512), `FalconPrecision/Exec/*.lean`,
`test/Exec*.lean`) does not prove, and every fact in it that is established by `#eval`. The limits of releases
0.2.0-0.4.0 (S7, S8, hop B) are in the README under Assumptions and limits; every theorem of the track that builds on
S8 or hop B inherits them.

## Common to every part

- Falcon-512 only (`n = 512`). Falcon-1024 is not covered.
- The reference is Falcon round 3 (specification v1.2) and its KAT file `falcon512-KAT.rsp` (sha256
  `dd75c946fdedef4ec46a2bee7e10c65c9126f1a839b9ced6921fd45f7354b5cd`; not in this repository,
  [evidence/README.md](evidence/README.md) says where to download it; the files that contain values from it are
  listed in [NOTICE](NOTICE)). FIPS 206 is unpublished as of 2026-11-10; no
  conformance to it is claimed. The FN-DSA encoding instance (`fndsaProv`, `fndsaProvV`) is a provisional reading of
  NIST's FIPS 206 status talk (Perlner, 2025), with placeholders for unpinned fields, and is tested against no FN-DSA
  data.
- Binary64 (floating-point) implementations are not modelled: the round-3 reference signer and c-fn-dsa are outside
  `Choices`; the KAT keys come from binary64 key generation, which is not modelled. Operation orders other than
  those of `Choices` (the association and computation order of every operation is fixed; only the target has two
  orders), the split (`t_frac`) target path, half-spectrum storage and Newton–Raphson division or square root are not
  modelled.
- `#eval` evaluates compiled code with Lean's interpreter; the kernel does not check it. The theorems use `#eval`
  results only as premises (`check … = true`, `checkRange … = true`, `entryOkB e = true`, `wit*B = true`,
  `refVecB … = some V`); no theorem asserts a premise. Trust in an `#eval` fact is trust in the Lean compiler and
  runtime.
- Facts about keys and messages are about the 100 round-3 KAT entries (or the ones named): samples, not bounds over
  keys or inputs.
- No UF-CMA game is defined (as in S7, S8 and hop B); the PRNG (SHAKE-256 driving SamplerZ) is not modelled.
- The recorded output of every run not checked by `#guard_msgs` is in `evidence/`;
  [evidence/README.md](evidence/README.md) says how each relates to its run. Where a run was recorded on an earlier
  tree, the modules it evaluates changed since only in docstrings, proofs, removed or added lemmas, or definitions the
  evaluation does not use.

## Arithmetic

- `Fx f` has no word size; `InRange i` is a predicate. That a word implementation of an operation computes `wrap` of
  the unbounded result is not proved.
- Division and square root are the exact quotient and root rounded once; the Newton–Raphson variants of ePrint
  2026/1531 §3.4 (seeds and iteration counts not pinned there) are not defined.
- `floor` gives no `Arith64` (`Arith` needs round to nearest); only the counterexample `RMode.not_isRound_floor` is
  proved.
- The twiddle tables of `RMode.arith64` are `ζ`, `ζ̄/2` rounded in `ℂ`; the executable tables enter through
  `Exec.arithX` and the decided condition `twOk` (Signer below).

## Key expansion and the check

- That any key passes `check` is not proved: the key counts (E1-E3) are `#eval` results.
- Key expansion runs in unbounded `Int`; `InRange` of the stored values is not checked, also in the theorems on words.
- `check` bounds `FFT(f)` (255) and `FFT(F)` (3500) only, the halves of `γf,g`, `γF,G` that the theorems use; `FFT(g)`
  and `FFT(G)` are not tested. Of the 100 KAT keys, keys 31, 52, 54, 65 pass `check` although
  `‖FFT(g)‖∞ > 255` for them (260.3-287.4; float computation, not certified), so ePrint 2026/1531 Alg. 2 l. 7
  would reject them. The 8 keys that fail `check` (27, 28, 37, 46, 47, 51, 81, 87) fail only `‖FFT(f)‖∞ ≤ 255`;
  whether 255 should be raised is not addressed.
- `check` (as `checkFast`) was evaluated only at `dm = direct`, `root = plain`, `rm = rc ∈ {halfEven, halfUp}` and
  `xn ∈ {0, 16, 32}`; at `floor`, `halfAway`, `dm = invMul`, `root = ntru` and other `xn` it is unevaluated.
- `checkFast` at `xn = 16` failed `realB` (every stored `ℓ̂` conjugate-symmetric) for key 1 under ties up (cause not
  isolated; ties up is not odd, so storing `−x` need not give `−(stored x)` at a tie).
- `check` gives per key what hop B assumes of a key: `FTree.Real` and `Close δ` (including the true leaves in
  `[1.2778, 1.825]`), and `fG − gF = q`. The checked theorems keep the other hypotheses of
  `Errors.HopB.falcon512_fixed_vs_true`: SamplerZ perfect in every world, auxiliary queries answered identically,
  `K ≤ 2³⁹` signing-oracle calls along every execution, `K·s2B 30.5 δ ≤ 2⁻⁹` (proved at `δ45q` and `δ127q`).

## Signer

- No Lean term `Adm C` is given for a concrete `C`: its condition `twOk C.x.rc = true` holds by `#eval` (E7).
- `Adm` excludes `floor` operation rounding and the multiply-first target (S8 models scale-first only); no security
  theorem covers multiply-first.
- `ffsX_refines` is stated for depth `L ≤ 9` (not stated for deeper trees, where `arithX`'s tables are exact above
  level 8 and `splitW`, `mergeW` use the rounded ones).
- Hop B is composed only without range checks (`C.rchk = none`) and with `1/q` at 77 fraction bits.
- `signX_word`, `sign32_eq_sign64` and `leafX_im` are stated for `i ≤ 64` (`signX_word`: `1 ≤ i ≤ 64`) and sampler
  answers within `W` of `⌊t̄⌋`; that a key passes `checkRange` is established by `#eval` only (E4).
- Only the attempt `signX` is the signing oracle of the security theorems (with the query count
  `pathSum_signLoopX`); that the whole signer `signMsgX` (loop, salt, norm check) is the hop-B experiment is not
  proved. Compress and its restart (spec Alg. 10 l. 10-11) are not modelled: `signMsgX` outputs `s`.
- The fractional centre (`C.samp.centre = fractional`, ePrint 2026/2902 Alg. 17) is defined only in the attempt
  `signXc` and its array form `signXcA`; `signX` and `signMsgX` compute the plain centre and pass `C.samp` only to
  the sampler, and `samplerZ` does not read `centre`. Apart from `wit_centre` and the lemmas it is proved from
  (`ofArr_targetFracXA`, `signXcA_eq`, `attDcA_eq`, `attDc_ne`, `attDc_ne_of`), no theorem concerns the fractional
  centre.

## SamplerZ

- `ub` is an ideal source of uniform bits; the PRNG is not modelled.
- `x`, `ccs` and `r` are exact in `ℚ` from the `Fx 64` inputs; fixed-point or floating-point preprocessing of these
  values is not modelled. The loop stops after 128 rejections with output `⌊t̄⌋` (the spec's loop is unbounded).
- `tab79` and the placement of the 79-bit draw (`u72·2⁷` plus the 7 high bits of the sign byte) are ours; NIST's
  79-bit table is unpublished. `samp_base` is about this table and draw.
- The spec's statement `R_513(χ ‖ D_{ℤ+,σmax}) ≤ 1 + 2⁻⁷⁸` (spec p. 40) is not proved; `tab_ok` checks table entries.
- With saturated shifts (the spec's own SamplerZ) the additive `2⁻⁶¹` makes `falcon512_exec_sampler_vs_true` empty
  for success `≤ 2⁻⁶¹` and is most of the threshold for `T ≤ 2⁶⁴`.
- Agreement with the spec beyond its 16 SamplerZ test vectors (E10) is not tested.
- `falcon512_exec_sampler_vs_true` takes `SampKey`s: stored leaves in `[σmin, σmax]`, the same bounds as `check`'s
  leaf test; no lemma derives it from `check`.

## Design-space pairs

- The 21 premises `wit*B = true` of the 22 attempt and signer witnesses (`wit_word_mf_none` and `wit_word_mf_sig`
  share one) hold by `#eval` (E12), not by a kernel proof.
  `samp_base` and `samp_shift` are kernel-checked.
- Witnesses are SamplerZ draw sequences, not PRNG seeds. Attempt witnesses compare attempt outputs `z` before the
  norm check; a signer-level difference is stated only where a `_sig` witness exists (none for the centre pair).
- `wit_salt` hashes salt 1 to the stand-in `c70`, not to HashToPoint(salt 1 ‖ message 0).
- Words reduce only the attempt in `signMsgX_32_64`, `signMsgZ_32_64` and `falcon512_exec_word_sampler_vs_true`; key
  expansion `storeC` runs in unbounded `Int` in both signers.
- The `dm` and `root` equivalence is per key: the stored trees of KAT key 0 at `xn = 32` are equal by `#eval` (E14);
  at `xn = 0` the pairs differ (witnesses). The `rc` equivalence (ties to even, ties up, ties away) rests on table
  and `σ` equality at 64 bits, by `#eval` (E13); for the signer at `xn > 0` it also needs equality at `64 + xn` bits,
  which is not evaluated.
- The hashed points of the witnesses (`wC0`, `wC70`) were computed with Python `hashlib` and are data; they equal
  Lean's HashToPoint of the entries' salt and message by `#eval` (E9).

## Encodings, HashToPoint and verification

- The codec theorems are round trips and uniqueness of encodings, not agreement with any other implementation;
  `decodePk_round3` and `decodeSk_round3` relate the decoders to this repository's own `Round3` decoders.
- VCVio's `shake256` is trusted as tested in VCVio and here; it is not proved equal to FIPS 202.
  `hashToPoint_spec` describes Alg. 3 on its stream.
- `hashToPoint` returns `none` when `4n·2¹¹` bytes give fewer than `n` values (Alg. 3 would squeeze further); not
  observed on any KAT entry.
- HashToPoint is compared with Python on the 100 KAT entries through a linear checksum mod `2⁶¹ − 1` (not a hash);
  in full only for entries 0 and 70.
- HashToPoint's 64-bit no-rejection variant, key-recovery mode and Falcon-1024 verification are not modelled.
- The KAT signatures are checked by decoding, verification and three one-bit mutations each. The executable signer
  is not compared with them end to end (its SamplerZ draws are not the reference's); the reference vectors condition
  on the `z` of a KAT signature instead.

## Reference vectors

- That `refVecB … = some V` holds for a given input, and that a key passes `check`, are `#eval` results (E17, E1-E3).
- The JSON printer is not proved; it prints the integers of `V`.
- Points covered: unbounded words, or `(i + 64)`-bit words with `1 ≤ i` and `magOkB C.target i`, with
  `twOk C.x.rc` and `check C.x C.xn δq k`. Points where `check` was not evaluated are not known to satisfy it.
- Not covered: binary64 implementations, other operation orders (a value outside a disc may come from one), key
  expansion on words (the tree is the unbounded `storeC C.x C.xn k`, also in `refVec_word`), the sampler itself
  (conditioned away), HashToPoint beyond VCVio's `shake256`, Compress, the restart loop, key generation.
- `signX_log` takes `C.rchk = none`. `(z0, z1)` is computed from the KAT signature; that it equals the reference
  signer's SamplerZ outputs is not proved.
- Each vector is one key, one message and one tape: a value inside its disc shows nothing beyond that.
- The vector files are in `evidence/vectors/` (`d45/`, `d127/`, each with `SHA256SUMS`).

## `#eval` evidence

Commands are run from the repository root after `lake build`. `lake build Axioms` runs every `#guard_msgs` of the
`Axioms` roots (among them every `test/Exec*.lean` except `test/ExecEquivEval.lean`) and fails if one fails.
The run files of E1, E2, E3, E8 (except entry 0) and E17 contain KAT data and are not in this repository;
`python3 scripts/gen_evidence_runs.py <path>/falcon512-KAT.rsp runs` writes them to `runs/` from the KAT file (it
checks its sha256; [evidence/README.md](evidence/README.md) says where to download it);
`python3 scripts/check_output.py <recorded .out> <new output>` compares a new output with the recorded one (run
times masked). Every other fact re-runs from this repository alone with the command given.

| # | Fact | Where | Re-run | Recorded output |
|---|---|---|---|---|
| E1 | `checkFast ⟨r, r, direct, plain⟩ 0 δ45q` on the 100 KAT keys, `r` = ties to even and ties up: `true` for 92, `false` for 27, 28, 37, 46, 47, 51, 81, 87 (only `‖FFT(f)‖∞ ≤ 255` fails) | `runs/key-check-d45/<r>-0-<h>.lean` (`h = a`: keys 0-49, `b`: 50-99; code: `evidence/key-check-d45/RunHead.lean`) | `lake env lean runs/key-check-d45/<r>-0-<h>.lean` | `evidence/key-check-d45/<r>-0-<h>.out` |
| E2 | `checkFast ⟨r, r, direct, plain⟩ xn δ127q`, same keys and `r`: `true` for none at `xn = 0` and `xn = 16`, for 92 (the same 8 fail) at `xn = 32`; all 100 keys decode, `fG − gF = q`, `h·f ≡ g (mod q)` | `runs/key-check-d127/<r>-<xn>-<h>.lean`, `runs/key-check-d127/decode.lean` (code: `evidence/key-check-d127/RunHead.lean`) | `lake env lean runs/key-check-d127/<r>-<xn>-<h>.lean`; `lake env lean runs/key-check-d127/decode.lean` | `evidence/key-check-d127/<r>-<xn>-<h>.out`, `evidence/key-check-d127/decode.out` |
| E3 | `checkFast ⟨halfEven, halfEven, direct, plain⟩ 32 δ127q`: `true` for 92 keys, `false` for the same 8 | `runs/key-check-d127-xn32/survey.lean` (code: `evidence/key-check-d127-xn32/RunTail.lean`) | `lake env lean runs/key-check-d127-xn32/survey.lean` | `evidence/key-check-d127-xn32/survey.out` |
| E4 | KAT entry 0: `checkFast` at `δ45q` (`xn = 0`, ties to even) and `checkRangeA` at `i = 32`, `i = 64`, `W = 19` (`cKat`, scale-first) | test/ExecRound3.lean:106 | `lake build Axioms` | `#guard_msgs` in the file |
| E5 | KAT entry 0: decoding (first coefficients of `f, g, F, G`), `fG − gF = q`, `h·f ≡ g (mod q)`; a wrong header, a trailing byte and a public-key value `≥ q` are rejected | test/ExecRound3.lean:76, :84, :92 | `lake build Axioms` | `#guard_msgs` in the file |
| E6 | KAT entries 0 and 70: the keys decode and satisfy `fG − gF = q`; the hashed points `wC0`, `wC70` have 512 coefficients in `[0, q)` | test/ExecEquiv.lean:15 | `lake build Axioms` | `#guard_msgs` in the file |
| E7 | `twOk` (as `twOkFast`) is `true` for `halfEven`, `halfUp`, `halfAway` and `false` for `floor`; at levels `< 3` (`twOkN`), `true` for `halfEven`, `halfUp` and `false` for `floor` | test/ExecCheckFast.lean:16, test/ExecSign.lean:111 | `lake build Axioms` | `#guard_msgs` in the file |
| E8 | `entryOkB` on all 100 entries of `falcon512-KAT.rsp`: `pk`, `sk`, `sm` re-encode byte for byte, decoders agree with `Round3`, `msg` recovered, HashToPoint checksum equals Python's, detached signature verifies, `openSm` accepts; 300/300 one-bit mutations (salt, message, compressed `s₂`) rejected | `runs/kat-entries/KatS0.lean` … `KatS11.lean` (`#eval sliceB`); entry 0 also test/ExecCodec.lean:85 | `lake env lean runs/kat-entries/KatS<k>.lean`; `lake build Axioms` | `#guard_msgs` in each file (a slice prints nothing) |
| E9 | HashToPoint of entries 0 and 70 equals the Python values `wC0`, `wC70` | test/ExecCodec.lean:90, :154 | `lake build Axioms` | `#guard_msgs` in the file |
| E10 | SamplerZ on the 16 test vectors of spec Table 3.2: the spec output with every byte used, saturated shifts (`b72`) and with shift rejection | test/ExecSampler.lean:63, :68 | `lake build Axioms` | `#guard_msgs` in the file |
| E11 | SamplerZ parts: table shapes and `Σ pdt = 2⁷²`; `pdt` values; BaseSampler at `u = 0` and at `RCDT[0]`; ApproxExp and acceptance at `x = 0`; a shift `≥ 64` rejected or saturated; the law at `σ̄ = 1.5`, `t̄ = 2.25` sums to 1 over `⌊t̄⌋ − 20` … `⌊t̄⌋ + 20`; the range check | test/ExecSampler.lean:74, :80, :85, :90, :95, :100, :108 | `lake build Axioms` | `#guard_msgs` in the file |
| E12 | the 21 witness premises `wit*B = true` (12 `wit*B` of `wit_word_mf` … `wit_cap`, 9 `wit*SigB` of the `_sig` witnesses) | test/ExecEquivEval.lean:12-92 | `lake env lean test/ExecEquivEval.lean` | `#guard_msgs` in the file |
| E13 | stored-constant tables at 64 bits equal for ties to even, ties up, ties away, not for floor; the stored `σ` likewise | test/ExecEquiv.lean:23, :27 | `lake build Axioms` | `#guard_msgs` in the file |
| E14 | the stored trees of KAT key 0 at `xn = 32` are equal under `dm = invMul` and under `root = ntru` | test/ExecEquiv.lean:34 | `lake build Axioms` | `#guard_msgs` in the file |
| E15 | the sampler witness outputs `(−16, −17, −18, 0)` and their `σ̄` in `[σmin, σmax]` | test/ExecEquiv.lean:42, :54 | `lake build Axioms` | `#guard_msgs` in the file |
| E16 | `δ45q 8 = 2⁻⁴⁵ = δ45q 0` | test/ExecInstance45.lean:9 | `lake build Axioms` | `#guard_msgs` in the file |
| E17 | reference vectors: `refVecB … = some V` for KAT entries 0, 70, 27 at `δ45q` and 0, 70 at `δ127q`; `checkFast` (ties to even, `xn = 0` and `xn = 32`) at the file's `δq`: entries 0, 70 true / true at `δ45q`, false / true at `δ127q`, entry 27 false / false; `magOkB` at 32 and 64 bits per target order (entry 70 multiply-first fails 32); the JSON files | `runs/vectors/d45/e0.lean`, `e70.lean`, `e27.lean`, `runs/vectors/d127/e0.lean`, `e70.lean` | `lake env lean runs/vectors/d45/e0.lean \| python3 scripts/split_vectors.py <dir>` (likewise for the others) | `evidence/vectors/d45/e<n>.out`, `evidence/vectors/d127/e<n>.out`; the JSON files and their `SHA256SUMS` in the same folders |
| E18 | unit checks on small inputs: fixed-point operations under the four roundings, ranges, words, `1/q` (44 checks) | test/ExecFixedPoint.lean:18-175 | `lake build Axioms` | `#guard_msgs` in the file |
| E19 | unit checks on small inputs: negacyclic product, storage rounding; array tables and FFT; words, products, FFT, range checks, clamping, a leaf, the restart loop, the norm bound, deviation bounds, array versions; bit orders, fields, Compress/Decompress, a degree-4 instance; tape order, slot exponents, a ball FFT, hull and widening; `ω` of order 1024 and 6-bit field decoding | test/ExecKeyCheck.lean:13, :17, :22; test/ExecCheckFast.lean:10, :22; test/ExecSign.lean:19-97; test/ExecCodec.lean:17, :30, :44; test/ExecRefVec.lean:13, :18, :23, :31; test/ExecRound3.lean:15 | `lake build Axioms` | `#guard_msgs` in the file |

The runs of E1, E2, E3, E8 (the 12 slices) and E12 were recorded on earlier trees of this repository, those of
E4-E7, E8 (entry 0), E9-E11 and E13-E19 on a tree that differs from that of release 0.5.0 only in comments,
docstrings and files that are not Lean modules. Every run was repeated on x86_64 and on aarch64 (Linux), after
`lake build` and `lake build Axioms` with no previously built module of this repository, from the Lean sources of
release 0.5.0, with run files equal byte for byte to those written by its `scripts/gen_evidence_runs.py`: each output
equals the recorded one (run times excepted), and the vector files have the sha256 in `SHA256SUMS`.
