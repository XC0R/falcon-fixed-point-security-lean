# Limits of the executable track (Falcon-512 and Falcon-1024)

What the executable track ([README](README.md#executable-track-falcon-512-and-falcon-1024),
`FalconPrecision/Exec/*.lean`, `test/Exec*.lean`) does not prove, and every fact in it that is established by `#eval`.
The limits of releases 0.2.0-0.4.0 (S7, S8, hop B) are in the README under Assumptions and limits; every theorem of
the track that builds on S8 or hop B inherits them.

## Common to every part

- Falcon-512 only (`n = 512`), except the encodings and verification, which are also instantiated at Falcon-1024
  (`n = 1024`) and checked against its KAT file ([below](#encodings-hashtopoint-and-verification)), the per-key check
  (`check1024`, [below](#key-expansion-and-the-check)), the refinement of S8's model signer by the attempt `signX` with
  its hop-B theorems (`signX_refines1024`, `falcon1024_exec_vs_true(256)`, [below](#signer)), the integer ranges and
  words of the attempt (`signX_word1024`, `sign32_eq_sign64_1024`, `leafX_im1024`, [below](#signer)), and the steps of
  the executable SamplerZ at `falcon1024S` (`lawZ_close1024`, `samplerZ_mgf1024`, `samplerZ_tv1024`, `sampler_hop1024`,
  `thresh_sampler1024`, `thresh_sampler1024_256`, [below](#samplerz)) and their composition with the signer
  (`falcon1024_exec_sampler_vs_true(256)`, `falcon1024_exec_word_sampler_vs_true(256)`, and their `_checked` versions on
  checked keys, `sampKey1024Equiv`, [below](#samplerz)), and the design-space equivalences and witnesses
  (`Exec.SignEquiv1024`, `Exec.SignWitness1024`, [below](#design-space-pairs)), and the reference vectors
  (`refVec_sound1024`, `refVec_word1024`, `refVec_exact1024`, `signX_log1024`, [below](#reference-vectors)). Falcon-1024
  is not covered otherwise.
- The reference is Falcon round 3 (specification v1.2) and its KAT file `falcon512-KAT.rsp` (sha256
  `dd75c946fdedef4ec46a2bee7e10c65c9126f1a839b9ced6921fd45f7354b5cd`; not in this repository,
  [evidence/README.md](evidence/README.md) says where to download it; the files that contain values from it are listed
  in [NOTICE](NOTICE)); for the encodings, verification, key check, integer-range check, design-space witnesses and
  reference vectors at Falcon-1024 also `falcon1024-KAT.rsp` of the same package (sha256
  `036a0bf5260573cec44977284dfef756cd1143db9961b981bd1fb55828acb20d`; not in this repository; the files that contain
  values from it are listed in [NOTICE](NOTICE)); for SamplerZ at Falcon-1024 also the SamplerZ trace
  `test-vector-sampler-falcon1024.txt` of the same package (sha256
  `c07bc528284590a10d3d84e85446214107426bb7943f4e4aac9996ea93fd92cd`; not in this repository; what this repository
  contains from it is listed in [NOTICE](NOTICE)). FIPS 206 is unpublished as of 2026-11-27; no conformance to it is
  claimed. The FN-DSA encoding instance (`fndsaProv`, `fndsaProvV`) is a provisional reading of NIST's FIPS 206 status
  talk (Perlner, 2025), with placeholders for unpinned fields, and is tested against no FN-DSA data.
- Binary64 (floating-point) implementations are not modelled: the round-3 reference signer and c-fn-dsa are outside
  `Choices`; the KAT keys come from binary64 key generation, which is not modelled. Operation orders other than
  those of `Choices` (the association and computation order of every operation is fixed; only the target has two
  orders), the split (`t_frac`) target path, half-spectrum storage and Newton–Raphson division or square root are not
  modelled.
- `#eval` evaluates compiled code with Lean's interpreter; the kernel does not check it. The theorems use `#eval`
  results only as premises (`check … = true`, `checkRange … = true`, `entryOkB e = true`, `wit*B = true`,
  `wit*B1024 = true`, `refVecB … = some V`, `refVecB1024 … = some V`, and `twOk rc = true`, `twOkN rc 10 = true`
  (directly or as fields of `Adm C`, `AdmN 10 C`)); no theorem asserts a premise. Trust in an `#eval` fact is trust in
  the Lean compiler and runtime.
- Facts about keys and messages are about the 100 round-3 KAT entries (or the ones named): samples, not bounds over
  keys or inputs.
- No UF-CMA game is defined (as in S7, S8 and hop B); the PRNG (SHAKE-256 driving SamplerZ) is not modelled.
- Side channels (timing, power, electromagnetic emanation) are not modelled. ePrint 2026/2908 recovers Falcon-1024
  secret keys from one power trace of the secret-key decoding at the start of signing; the codec theorems here state
  what that decoding computes, not what it leaks.
- The recorded output of every run not checked by `#guard_msgs` is in `evidence/`;
  [evidence/README.md](evidence/README.md) says how each relates to its run. Where a run was recorded on an earlier
  tree, the modules it evaluates changed since only in docstrings, proofs, removed or added lemmas, definitions the
  evaluation does not use, or definitions generalised in the size whose 0.5.0 bodies are proved equal to them at their
  defaults (`test/Compat050Defs.lean`); the printer of E17 (`vecJson`, `scopeJson`) now delegates to `vecJsonN`,
  `scopeJsonN`. Every run was repeated on the Lean sources, scripts and recorded outputs of release 0.6.0 (last
  paragraph of [`#eval` evidence](#eval-evidence)).

## Arithmetic

- `Fx f` has no word size; `InRange i` is a predicate. That a word implementation of an operation computes `wrap` of
  the unbounded result is not proved.
- Division and square root are the exact quotient and root rounded once; the Newton–Raphson variants of ePrint
  2026/1531 §3.4 (seeds and iteration counts not pinned there) are not defined.
- `floor` gives no `Arith64` (`Arith` needs round to nearest); only the counterexample `RMode.not_isRound_floor` is
  proved.
- The twiddle tables of `RMode.arith64` are `ζ`, `ζ̄/2` rounded in `ℂ`; the executable tables enter through
  `Exec.arithX` and the decided condition `twOk` (at Falcon-1024 `Exec.arithXN 10` and `twOkN rc 10`) (Signer below).

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
- `check` gives per key what hop B assumes of a key: `FTreeP.Real` and `Close δ` (including the true leaves in
  `[1.2778, 1.825]`), and `fG − gF = q`. The checked theorems keep the other hypotheses of
  `Errors.HopB.falcon512_fixed_vs_true`: SamplerZ perfect in every world, auxiliary queries answered identically,
  `K ≤ 2³⁹` signing-oracle calls along every execution, `K·s2B 30.5 δ ≤ 2⁻⁹` (proved at `δ45q` and `δ127q`).
- Falcon-1024 (`check1024`, `check1024_sound`, the `falcon1024_fixed_vs_true*_checked` theorems): that any key passes
  `check1024` is not proved: the key counts (E23) are `#eval` results. `check1024` bounds `FFT(f)` (256) and `FFT(F)`
  (7365) only; `FFT(g)`, `FFT(G)` and the `γhybrid` threshold of 2026/2431's tuple B are not tested. It was evaluated
  only at `dm = direct`, `root = plain`, `rm = rc ∈ {halfEven, halfUp}`, at `δ43q_1024` with `xn = 0` and at
  `δ127q_1024` with `xn = 32` (all 100 keys, E23), and at ties to even, `δ43q_1024` with `xn = 32` and `δ127q_1024` with
  `xn = 0`, on keys 0, 2 and 11 (E33). The checked theorems keep the other hypotheses of
  `Errors.HopB.falcon1024_fixed_vs_true` and `falcon1024_fixed_vs_true256` (`K ≤ 2²⁹`, `K·s2B1024 41.5 δ ≤ 2⁻⁹` resp.
  `2⁻¹⁰`, proved at `δ43q_1024` and `δ127q_1024`).

## Signer

- No Lean term `Adm C` or `AdmN 10 C` is given for a concrete `C`: their conditions `twOk C.x.rc = true` and
  `twOkN C.x.rc 10 = true` hold by `#eval` (E7, E24). `twOkN rc N` for `N > 10` is not evaluated.
- `Adm` and `AdmN N` exclude `floor` operation rounding and the multiply-first target (S8 models scale-first only); no
  security theorem covers multiply-first.
- `ffsX_refines` is stated for depth `L ≤ 9` (not stated for deeper trees, where `arithX`'s tables are exact above
  level 8 and `splitW`, `mergeW` use the rounded ones); `ffsX_refinesN` is the same at depth `L ≤ N` with `arithXN N`
  (executable tables at levels `< N`), used at `N = 10` for Falcon-1024.
- Hop B is composed only without range checks (`C.rchk = none`) and with `1/q` at 77 fraction bits.
- Falcon-1024 (`signX_refines1024`, `world_eq1024`, `falcon1024_exec_vs_true(43, 127)`,
  `falcon1024_exec_vs_true256(_43, _127)`): the attempt `signX` is the signing oracle under `AdmN 10 C`, on keys passing
  `check1024`, with `C.rchk = none` and `1/q` at 77 fraction bits; the other hypotheses are those of the
  `falcon1024_fixed_vs_true*_checked` theorems. The word theorems of the attempt are stated at Falcon-512 (`signX_word`,
  `sign32_eq_sign64`, `leafX_im`) and at Falcon-1024 (`signX_word1024`, `sign32_eq_sign64_1024`, `leafX_im1024`, on keys
  passing `check1024` and `checkRange C i W k σ1024q`); the word theorems of the whole signer are stated at Falcon-512
  (`signMsgX_32_64`, `signMsgZ_32_64`) and at Falcon-1024 (`signMsgX_word1024`, `signMsgZ_word1024` for `27 ≤ i ≤ 64`,
  and `signMsgX_32_64_1024`, `signMsgZ_32_64_1024`; keys passing `check1024` and `checkRange C i W k σ1024q`); the query
  count of the restart loop (`pathSum_signLoopX`) is stated at Falcon-512 only. The composition with the executable
  SamplerZ is stated at Falcon-512 (`falcon512_exec_sampler_vs_true`, `falcon512_exec_word_sampler_vs_true`) and at
  Falcon-1024 (`falcon1024_exec_sampler_vs_true(256)`, `falcon1024_exec_word_sampler_vs_true(256)`,
  [SamplerZ](#samplerz)).
- `signX_word`, `sign32_eq_sign64` and `leafX_im` are stated for `i ≤ 64` (`signX_word`: `1 ≤ i ≤ 64`), their
  Falcon-1024 versions for `27 ≤ i ≤ 64` (the leaf-centre certificate `gB_ten` needs `2^(i−1) ≥ 2²⁶`), and sampler
  answers within `W` of `⌊t̄⌋`; that a key passes `checkRange` is established by `#eval` only (E4, E25).
- Only the attempt `signX` is the signing oracle of the security theorems (with the query count
  `pathSum_signLoopX`); that the whole signer `signMsgX` (loop, salt, norm check) is the hop-B experiment is not
  proved. Compress and its restart (spec Alg. 10 l. 10-11) are not modelled: `signMsgX` outputs `s`.
- The fractional centre (`C.samp.centre = fractional`, ePrint 2026/2902 Alg. 17) is defined only in the attempt `signXc`
  and its array forms `signXcA` and `signXcAP`; `signX` and `signMsgX` compute the plain centre and pass `C.samp` only
  to the sampler, and `samplerZ` does not read `centre`. Apart from `wit_centre`, `wit_centre1024` and the lemmas they
  are proved from (`ofArr_targetFracXA`, `signXcA_eq`, `attDcA_eq`, `attDc_ne`, `attDc_ne_of`; `ofArr_targetFracXAP`,
  `signXcAP_eq`, `attDcAP_eq`, `attDcP_ne`, `attDcP_ne_of`), no theorem concerns the fractional centre.

## SamplerZ

- `ub` is an ideal source of uniform bits; the PRNG is not modelled.
- `x`, `ccs` and `r` are exact in `ℚ` from the `Fx 64` inputs; fixed-point or floating-point preprocessing of these
  values is not modelled. The loop stops after 128 rejections with output `⌊t̄⌋` (the spec's loop is unbounded).
- `tab79` and the placement of the 79-bit draw (`u72·2⁷` plus the 7 high bits of the sign byte) are ours; NIST's
  79-bit table is unpublished. `samp_base` is about this table and draw.
- The spec's statement `R_513(χ ‖ D_{ℤ+,σmax}) ≤ 1 + 2⁻⁷⁸` (spec p. 40) is not proved; `tab_ok` checks table entries.
- With saturated shifts (the spec's own SamplerZ) the additive `2⁻⁶¹` makes `falcon512_exec_sampler_vs_true` empty
  for success `≤ 2⁻⁶¹` and is most of the threshold for `T ≤ 2⁶⁴`.
- At Falcon-1024 the saturated additive is `2⁻⁷⁰` (`2⁻¹¹⁰` per call over `2048·2²⁹` calls). It makes
  `falcon1024_exec_sampler_vs_true` and `falcon1024_exec_word_sampler_vs_true` empty for success `≤ 2⁻⁷⁰` and is most
  of their threshold for `T ≤ 2⁵⁵`. The λ = 256 statements (`falcon1024_exec_sampler_vs_true256`,
  `falcon1024_exec_word_sampler_vs_true256`, threshold `2^(1/64)·(T·2⁻²⁵⁴ + 2⁻²⁸⁰)`) are meaningful only with shift
  rejection (`C.samp.shiftRej = true`, additive `0`): with saturated shifts the additive is `2¹⁸⁴` times the
  threshold's term at `T = 1` and most of the threshold for `T ≤ 2¹⁸³`.
- Agreement with the reference beyond the 16 SamplerZ test vectors of spec Table 3.2 (E10) and the 2048 SamplerZ calls
  of one round-3 Falcon-1024 signature trace (E26: one key, one message, no shift `≥ 64`) is not tested; the
  Falcon-512 trace `test-vector-sampler-falcon512.txt` of the same package is not replayed. In E26, `σ̄` is the
  ties-to-even `Fx 64` value of the exact reciprocal of the trace's binary64 `1/σ`; the reference's own floating-point
  preprocessing is not compared.
- `falcon512_exec_sampler_vs_true` takes `SampKey`s and the Falcon-1024 composed theorems take `SampKey1024`s: stored
  leaves in `[σmin, σmax]` of `falcon512S` resp. `falcon1024S` (`[1.298280334, 1.8205]`), the bounds of the leaf test of
  `check` resp. `check1024`. Every key passing the check is such a key (`CTree.leavesB_of_okB`, `sampKeyEquiv`,
  `sampKey1024Equiv`), and the `_checked` versions state the composed theorems on experiments over checked keys
  (`specK`, `specK1024`): `falcon512_exec_sampler_vs_true_checked`, `falcon1024_exec_sampler_vs_true(256)_checked`,
  `falcon1024_exec_sampler_vs_true(43, 127)_checked`, `falcon1024_exec_sampler_vs_true256(_43, _127)_checked`, and on
  words `falcon512_exec_word_sampler_vs_true_checked`, `falcon1024_exec_word_sampler_vs_true(256)_checked` (keys passing
  the check and `checkRange`, `rKeyEquiv`, `rKey1024Equiv`), with the other hypotheses and constants unchanged. That any
  key passes `check`, `check1024` or `checkRange` is established by `#eval` only.
- `lawZ_close`, `samplerZ_mgf`, `samplerZ_tv` and `sampler_hop` are proved for `sampS c` (`falcon512S` with
  `σmin := c`) at every `c ∈ [1.277833697, 1.3]` (`SminOk c`; the upper end keeps `K0ZP·Θ ≤ 3/5`, `K0ZP_theta`) and
  stated at Falcon-512 and at Falcon-1024 (`falcon1024S`, `σmin = 1.298280334`, spec Table 3.3); other `σmax`, `ln 2`,
  tables or loop bounds are not covered.
- At Falcon-1024 the signer side is `SampKey1024`, `execZ1024`, `exec_factor1024`, `pathSum_execZ1024` (`2048`
  SamplerZ calls per attempt), the step `exec_sampler_step1024`, and the composed
  `falcon1024_exec_sampler_vs_true(43, 127)`, `falcon1024_exec_sampler_vs_true256(_43, _127)`, and the word versions
  `falcon1024_exec_word_sampler_vs_true(256)` (`27 ≤ i ≤ 64`), all at `K ≤ 2²⁹` signing queries (`2048K ≤ 2⁴⁰` calls;
  Falcon's bound `2⁶⁴` is not covered; ePrint 2026/2902 reports bounds over `2⁶⁴` signatures under its own
  hypotheses, see the README's Related work); the loss factor is `2^(1/64)` at both levels (`thresh_samplerE`: every
  `θ ≥ 2⁻ᵉ`, `e < 256`, `N ≤ 2⁴⁶·(256 − e)` calls). Their other hypotheses and what they do not prove are those of
  `falcon1024_exec_vs_true(256)` (`AdmN 10 C` by `#eval` only, E24) and of the Falcon-512 composed theorem (ideal PRNG
  `ub`, `fuel = 128`, SamplerZ arithmetic exact in `ℚ`, `tab79` ours).

## Design-space pairs

- The 21 premises `wit*B = true` of the 22 attempt and signer witnesses (`wit_word_mf_none` and `wit_word_mf_sig` share
  one) hold by `#eval` (E12), not by a kernel proof; so do the 21 premises `wit*B1024 = true` of the 22 Falcon-1024
  witnesses (`wit_*1024`, `wit_*_sig1024`, `wit_word_mf_none1024`; E28). `samp_base`, `samp_shift`, `samp_base1024` and
  `samp_shift1024` are kernel-checked.
- Witnesses are SamplerZ draw sequences, not PRNG seeds. Attempt witnesses compare attempt outputs `z` before the norm
  check; a signer-level difference is stated only where a `_sig` witness exists (none for the centre pair, at either
  size).
- `wit_salt` hashes salt 1 to the stand-in `c70`, `wit_salt1024` to the stand-in `c70_1024`, not to HashToPoint(salt 1 ‖
  message 0).
- Words reduce only the attempt in `signMsgX_32_64`, `signMsgZ_32_64`, `signMsgX_32_64_1024`, `signMsgZ_32_64_1024`,
  `falcon512_exec_word_sampler_vs_true` and `falcon1024_exec_word_sampler_vs_true(256)` (the latter `27 ≤ i ≤ 64`, keys
  passing `checkRange C i 19 · σ1024q`, E25 by `#eval` only); key expansion `storeC` runs in unbounded `Int` in both
  signers.
- The `dm` and `root` equivalence is per key: the stored trees of KAT key 0 at `xn = 32` are equal by `#eval` (E14; key
  0 of `falcon1024-KAT.rsp` at Falcon-1024, E30); at `xn = 0` the pairs differ (witnesses). The `rc` equivalence (ties
  to even, ties up, ties away) rests on table and `σ` equality at 64 bits, by `#eval` (E13; at Falcon-1024 the tables at
  levels `≤ 9` and `σ1024q`, E29, where `σ1024q` at 64 bits is also equal under floor); for the signer at `xn > 0` it
  also needs equality at `64 + xn` bits, which is not evaluated.
- The Falcon-1024 witnesses use keys 0 and 2 of `falcon1024-KAT.rsp`, both passing `check1024` by `#eval` only (E23).
  Multiply-first 32.64 / 64.64 is witnessed on key 2 under policy draws; the search found no witness for it on key 0
  under policy draws, which does not make the pair equal there.
- The hashed points of the witnesses (`wC0`, `wC70`; `wC0_1024`, `wC2_1024`, `wC70_1024`) were computed with Python
  `hashlib` and are data; they equal Lean's HashToPoint of the entries' salt and message by `#eval` (E9; E32).

## Encodings, HashToPoint and verification

- The codec theorems are round trips and uniqueness of encodings, not agreement with any other implementation;
  `decodePk_round3`, `decodeSk_round3` (and `decodePk_round3_1024`, `decodeSk_round3_1024` at Falcon-1024) relate
  the decoders to this repository's own `Round3` decoders.
- VCVio's `shake256` is trusted as tested in VCVio and here; it is not proved equal to FIPS 202.
  `hashToPoint_spec` describes Alg. 3 on its stream.
- `hashToPoint` returns `none` when `4n·2¹¹` bytes give fewer than `n` values (Alg. 3 would squeeze further); not
  observed on any KAT entry.
- HashToPoint is compared with Python on the 100 entries of each KAT file through a linear checksum mod `2⁶¹ − 1`
  (not a hash); in full only for entries 0 and 70 of each.
- HashToPoint's 64-bit no-rejection variant and key-recovery mode are not modelled.
- At Falcon-1024 the compressed `s₂` of KAT entry 82 takes 9914 bits (1240 bytes), more than the
  `8·1280 − 328 = 9912` bits that a 1280-byte signature (`sbytelen`, Table 3.3) holds after the header and salt.
  Compress at that length returns ⊥ (Alg. 17 l. 7-8), so no padded detached signature encodes it; Alg. 10
  l. 10-11 would restart the signer, and Alg. 16 l. 2 at that length rejects it. The KAT file stores it in the
  NIST-API format (§3.11.6: no padding, variable length), which `openSm` decodes unpadded; `openSm` accepts it.
  For this entry the detached signature is checked unpadded (`round3V1024.unpadded`; §3.11.3 allows verifiers to
  support unpadded signatures), together with `NoSigEnc round3V1024` (E20).
- The Falcon-1024 FN-DSA instance (`fndsaProv1024`, `fndsaProvV1024`) has the placeholders of the Falcon-512 one,
  with header bytes, field widths, `sbytelen` and `⌊β²⌋` at the round-3 Falcon-1024 values; it is tested against
  no data.
- The KAT signatures are checked by decoding, verification and three one-bit mutations each. The executable signer
  is not compared with them end to end (its SamplerZ draws are not the reference's); the reference vectors condition
  on the `z` of a KAT signature instead.

## Reference vectors

- That `refVecB … = some V` or `refVecB1024 … = some V` holds for a given input, and that a key passes `check` or
  `check1024`, are `#eval` results (E17, E1-E3; E33, E23).
- The JSON printer is not proved; it prints the integers of `V`.
- Points covered: unbounded words, or `(i + 64)`-bit words with `1 ≤ i` and `magOkB C.target i`, with `twOk C.x.rc` and
  `check C.x C.xn δq k`; at Falcon-1024 the same with `magOkBP C.target i`, `twOkN C.x.rc 10` (`true` for ties to even,
  up, away by `#eval` only, E24) and `check1024 C.x C.xn δq k`. Points where the check was not evaluated are not known
  to satisfy it.
- The leaf balls are widened by `1.825·2⁻⁴²` at both sizes: the radius bound that the leaf test `CB.leafOkB` of `check`
  and of `check1024` gives (`s + r ≤ 1.825`, `2⁴²·r ≤ s − r`).
- Not covered: binary64 implementations, other operation orders (a value outside a disc may come from one), key
  expansion on words (the tree is the unbounded `storeC C.x C.xn k`, at Falcon-1024 `storeC C.x C.xn k σ1024q`, also in
  `refVec_word` and `refVec_word1024`), the sampler itself (conditioned away), HashToPoint beyond VCVio's `shake256`,
  Compress, the restart loop, key generation.
- `signX_log` and `signX_log1024` take `C.rchk = none`. `(z0, z1)` is computed from the KAT signature; that it equals
  the reference signer's SamplerZ outputs is not proved.
- Each vector is one key, one message and one tape: a value inside its disc shows nothing beyond that.
- The vector files are in `evidence/vectors/` (`d45/`, `d127/`) and `evidence/vectors-1024/` (`d43/`, `d127/`), each
  with `SHA256SUMS` (the Falcon-1024 files write `σ1024q` as `sigma1024q`, to stay ASCII).

## `#eval` evidence

Commands are run from the repository root after `lake build`. `lake build Axioms` runs every `#guard_msgs` of the
`Axioms` roots (among them every `test/Exec*.lean` except `test/ExecEquivEval.lean`, `test/ExecEquivEval1024.lean` and
`test/ExecEquivEval1024Sig.lean`) and fails if one fails. The run files of E1, E2, E3, E8 (except entry 0), E17, E20,
E21, E23, E25 and E33 contain KAT data and those of E26 data of the SamplerZ trace; they are not in this repository;
`python3 scripts/gen_evidence_runs.py <path>/falcon512-KAT.rsp runs` writes those of E1-E17,
`python3 scripts/gen_evidence_runs.py <path>/falcon1024-KAT.rsp runs` those of E20, E21, E23, E25 and E33 and
`python3 scripts/gen_evidence_runs.py <path>/test-vector-sampler-falcon1024.txt runs` those of E26 to `runs/` from the
file (it checks its sha256; [evidence/README.md](evidence/README.md) says where to download them);
`python3 scripts/check_output.py <recorded .out> <new output>` compares a new output with the recorded one (run times
masked). Every other fact re-runs from this repository alone with the command given.

| # | Fact | Where | Re-run | Recorded output |
|---|---|---|---|---|
| E1 | `checkFast ⟨r, r, direct, plain⟩ 0 δ45q` on the 100 KAT keys, `r` = ties to even and ties up: `true` for 92, `false` for 27, 28, 37, 46, 47, 51, 81, 87 (only `‖FFT(f)‖∞ ≤ 255` fails) | `runs/key-check-d45/<r>-0-<h>.lean` (`h = a`: keys 0-49, `b`: 50-99; code: `evidence/key-check-d45/RunHead.lean`) | `lake env lean runs/key-check-d45/<r>-0-<h>.lean` | `evidence/key-check-d45/<r>-0-<h>.out` |
| E2 | `checkFast ⟨r, r, direct, plain⟩ xn δ127q`, same keys and `r`: `true` for none at `xn = 0` and `xn = 16`, for 92 (the same 8 fail) at `xn = 32`; all 100 keys decode, `fG − gF = q`, `h·f ≡ g (mod q)` | `runs/key-check-d127/<r>-<xn>-<h>.lean`, `runs/key-check-d127/decode.lean` (code: `evidence/key-check-d127/RunHead.lean`) | `lake env lean runs/key-check-d127/<r>-<xn>-<h>.lean`; `lake env lean runs/key-check-d127/decode.lean` | `evidence/key-check-d127/<r>-<xn>-<h>.out`, `evidence/key-check-d127/decode.out` |
| E3 | `checkFast ⟨halfEven, halfEven, direct, plain⟩ 32 δ127q`: `true` for 92 keys, `false` for the same 8 | `runs/key-check-d127-xn32/survey.lean` (code: `evidence/key-check-d127-xn32/RunTail.lean`) | `lake env lean runs/key-check-d127-xn32/survey.lean` | `evidence/key-check-d127-xn32/survey.out` |
| E4 | KAT entry 0: `checkFast` at `δ45q` (`xn = 0`, ties to even) and `checkRangeA` at `i = 32`, `i = 64`, `W = 19` (`cKat`, scale-first) | test/ExecRound3.lean:106 | `lake build Axioms` | `#guard_msgs` in the file |
| E5 | KAT entry 0: decoding (first coefficients of `f, g, F, G`), `fG − gF = q`, `h·f ≡ g (mod q)`; a wrong header, a trailing byte and a public-key value `≥ q` are rejected | test/ExecRound3.lean:76, :84, :92 | `lake build Axioms` | `#guard_msgs` in the file |
| E6 | KAT entries 0 and 70: the keys decode and satisfy `fG − gF = q`; the hashed points `wC0`, `wC70` have 512 coefficients in `[0, q)` | test/ExecEquiv.lean:15 | `lake build Axioms` | `#guard_msgs` in the file |
| E7 | `twOk` (as `twOkFast`) is `true` for `halfEven`, `halfUp`, `halfAway` and `false` for `floor`; at levels `< 3` (`twOkN`), `true` for `halfEven`, `halfUp` and `false` for `floor` | test/ExecCheckFast.lean:17, test/ExecSign.lean:114 | `lake build Axioms` | `#guard_msgs` in the file |
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
| E19 | unit checks on small inputs: negacyclic product (also at size `2¹⁰`), storage rounding; array tables and FFT; words, products, FFT, range checks, clamping, a leaf, the restart loop, the norm bound, deviation bounds, array versions; bit orders, fields, Compress/Decompress, a degree-4 instance; tape order, slot exponents, a ball FFT, hull and widening; `ω` of order 1024 and 6-bit field decoding | test/ExecKeyCheck.lean:15, :19, :27, :32; test/ExecCheckFast.lean:11, :30; test/ExecSign.lean:22-100; test/ExecCodec.lean:17, :30, :44; test/ExecRefVec.lean:13, :18, :23, :31; test/ExecRound3.lean:15 | `lake build Axioms` | `#guard_msgs` in the file |
| E20 | `entryOkBP round3V1024` on the 100 entries of `falcon1024-KAT.rsp` except entry 82, `entryOkBU round3V1024` on entry 82: for all 100, `pk`, `sk`, `sm` re-encode byte for byte, the decoders agree with `Round3` at `logn = 10`, `msg` recovered, HashToPoint checksum (`n = 1024`) equals Python's, `openSm` accepts; 300/300 one-bit mutations (salt, message, compressed `s₂`) rejected; the detached 1280-byte signature verifies for 99; entry 82 has no 1280-byte encoding and its unpadded detached signature verifies | `runs/kat1024-entries/KatS0.lean` … `KatS15.lean` (`#eval sliceB`) | `lake env lean runs/kat1024-entries/KatS<k>.lean` | `#guard_msgs` in each file (a slice prints nothing) |
| E21 | HashToPoint (`n = 1024`) of entries 0 and 70 of `falcon1024-KAT.rsp` equals the values computed by Python `hashlib` | `runs/kat1024-entries/HashToPoint.lean` | `lake env lean runs/kat1024-entries/HashToPoint.lean` | `#guard_msgs` in the file (prints nothing) |
| E22 | Falcon-1024 encodings on inputs built in the file: sizes and header bytes (public key 1793, private key 2305, signature 1280, `sm` header `0x2A`), round trips and agreement with `Round3` at `logn = 10`, `⌊β²⌋ = 70265242` over 1024 coefficients (one value `6144` accepted at `round3V1024`, rejected at `round3V`), the round-3 decoders `none` at `logn = 0` and `11` | test/ExecFalcon1024.lean:28, :39, :54, :68 | `lake build Axioms` | `#guard_msgs` in the file |
| E23 | `checkFast ⟨r, r, direct, plain⟩ xn δq` at the `check1024` thresholds (`256`, `7365`, `1298280334/10⁹`, `lam1024q`, `σ1024q`) on the 100 keys of `falcon1024-KAT.rsp`, `r` = ties to even and ties up, `δq = δ43q_1024` at `xn = 0` and `δ127q_1024` at `xn = 32`: `true` for 77 in each of the four; `false` for 11, 19, 24, 25, 31, 34, 37, 39, 40, 42, 43, 49, 58, 69, 70, 72, 75, 78, 83, 84, 87, 93 (only `‖FFT(f)‖∞ ≤ 256` fails) and 60 (only the stored-tree bounds `okB` fail); all 100 keys decode, `fG − gF = q`, `h·f ≡ g (mod q)` | `runs/key-check-1024-d43/<r>-0-<j>.lean`, `runs/key-check-1024-d127/<r>-32-<j>.lean` (`j = 0 … 9`: keys `10j … 10j + 9`), `runs/key-check-1024-d127/decode.lean` (code: `evidence/key-check-1024-d43/RunHead.lean`, `evidence/key-check-1024-d127/RunHead.lean`) | `lake env lean runs/key-check-1024-d43/<r>-0-<j>.lean`, likewise for `d127` and `decode.lean` | `evidence/key-check-1024-d43/<r>-0-<j>.out`, `evidence/key-check-1024-d127/<r>-32-<j>.out`, `evidence/key-check-1024-d127/decode.out` |
| E24 | `twOkN rc 10` (as `twOkFastN rc 10`, the ten table levels of Falcon-1024) is `true` for `halfEven`, `halfUp`, `halfAway` and `false` for `floor` | test/ExecCheckFast.lean:24 | `lake build Axioms` | `#guard_msgs` in the file |
| E25 | `checkRangeA C i 19 k σ1024q` (`= checkRange C i 19 k σ1024q`, `checkRangeA_eqP`) with `C.x = ⟨halfEven, halfEven, direct, plain⟩`, `xn = 0`, `1/q` at 77 bits, on the 100 keys of `falcon1024-KAT.rsp` at `i = 32` and `i = 64`: scale-first `true` for all 100 at both; multiply-first `false` for all 100 at `i = 32` (the bound `bc·max(nmax F̂ + 1, nmax f̂ + 1) + 1` is above `2^35.8` on every key; this is the check failing, not an overflow shown) and `true` for all 100 at `i = 64`; with E23, 77 keys pass both checks at scale-first `i = 32`, `64` and multiply-first `i = 64` | `runs/range-1024/<t>-<j>.lean` (`t = scaleFirst, multiplyFirst`; `j = 0 … 9`: keys `10j … 10j + 9`; code: `evidence/range-1024/RunHead.lean`) | `lake env lean runs/range-1024/<t>-<j>.lean` | `evidence/range-1024/<t>-<j>.out` |
| E26 | `samplerZ falcon1024S ⟨plain, r, b72⟩` at `σ̄ = Fx.ofRat halfEven (1/isig)`, `t̄ = Fx.ofRat halfEven mu` (`mu`, `isig` the trace's binary64 `mu` and `1/sigma`, exact) on each of the 2048 SamplerZ calls of the round-3 Falcon-1024 signature trace `test-vector-sampler-falcon1024.txt` (one key, one message), on the call's recorded random values (BaseSampler's 72-bit `u` as 9 bytes big-endian, the sign byte, the BerExp bytes, round after round), `r` = saturated shifts and shift rejection: for all 2048 calls and both, the trace's accepted `z` with every byte used (37918 bytes in 3446 rounds); no call reaches a shift `≥ 64` (the largest is 11), so the two variants are not distinguished; every `σ̄` in `falcon1024S`'s range | `runs/sampler-1024/calls-<j>.lean` (`j = 0 … 15`: calls `128j … 128j + 127`; code: `evidence/sampler-1024/RunHead.lean`) | `lake env lean runs/sampler-1024/calls-<j>.lean` | `evidence/sampler-1024/calls-<j>.out` |
| E27 | SamplerZ at Falcon-1024: `σ̄ = ⌊1.29·2⁶⁴⌋·2⁻⁶⁴` in range at Falcon-512 and not at Falcon-1024, `σ̄ = 1.5` in range at Falcon-1024; the Falcon-1024 law at `σ̄ = 1.5`, `t̄ = 2.25` sums to 1 over `⌊t̄⌋ − 20` … `⌊t̄⌋ + 20` | test/ExecSampler.lean:239, :245 | `lake build Axioms` | `#guard_msgs` in the file |
| E28 | the 21 Falcon-1024 witness premises `wit*B1024 = true` (12 `wit*B1024` of `wit_word_mf1024` … `wit_cap1024`, 9 `wit*SigB1024` of the `_sig1024` witnesses) | test/ExecEquivEval1024.lean:14-58, test/ExecEquivEval1024Sig.lean:13-45 | `lake env lean test/ExecEquivEval1024.lean`, `lake env lean test/ExecEquivEval1024Sig.lean` | `#guard_msgs` in the files |
| E29 | Falcon-1024 stored-constant tables at levels `≤ 9` and 64 bits equal for ties to even, ties up, ties away, not for floor; the stored `σ1024q` at 64 bits equal under all four | test/ExecEquiv1024.lean:32, :37 | `lake build Axioms` | `#guard_msgs` in the file |
| E30 | the stored trees of key 0 of `falcon1024-KAT.rsp` at `xn = 32` are equal under `dm = invMul` and under `root = ntru` | test/ExecEquiv1024.lean:44 | `lake build Axioms` | `#guard_msgs` in the file |
| E31 | the Falcon-1024 sampler witness outputs `(−16, −17, −18, 0)`; their `σ̄` in `falcon1024S`'s range, `σ̄ − 2⁻⁶⁴` of `samp_shift1024` not | test/ExecEquiv1024.lean:52, :65 | `lake build Axioms` | `#guard_msgs` in the file |
| E32 | entries 0 and 2 of `falcon1024-KAT.rsp` decode at `logn = 10` and satisfy `fG − gF = q`; `wC0_1024`, `wC2_1024`, `wC70_1024` have 1024 values in `[0, q)` and equal `hashToPoint 1024` of the stored `nonce ‖ msg` | test/ExecEquiv1024.lean:16, :24 | `lake build Axioms` | `#guard_msgs` in the file |
| E33 | Falcon-1024 reference vectors: `refVecB1024 … = some V` for entries 0, 2, 11 of `falcon1024-KAT.rsp` at `δ43q_1024` and at `δ127q_1024`; `checkFast` at the `check1024` thresholds (ties to even, `xn = 0` and `xn = 32`) at the file's `δq`: entries 0, 2 true / true at `δ43q_1024`, false / true at `δ127q_1024`, entry 11 false / false (control; at E23's points it fails only `‖FFT(f)‖∞ ≤ 256`); `magOkBP` at 32 and 64 bits per target order (entry 2 multiply-first fails 32); the JSON files | `runs/vectors-1024/d43/e0.lean`, `e2.lean`, `e11.lean`, `runs/vectors-1024/d127/e0.lean`, `e2.lean`, `e11.lean` | `lake env lean runs/vectors-1024/d43/e0.lean \| python3 scripts/split_vectors.py <dir>` (likewise for the others) | `evidence/vectors-1024/d43/e<n>.out`, `evidence/vectors-1024/d127/e<n>.out`; the JSON files and their `SHA256SUMS` in the same folders |
| E34 | unit checks: the tables of `opsBN 10` (levels 0-9, level `L` with `2^L` balls) and the tape at depth 10 (2048 distinct answers, those of `z1` first) | test/ExecRefVec.lean:40, :46 | `lake build Axioms` | `#guard_msgs` in the file |

The runs of E1, E2, E3, E8 (the 12 slices) and E12 were recorded on earlier trees of this repository, those of E4-E7, E8
(entry 0), E9-E11 and E13-E19 on a tree that differs from that of release 0.5.0 only in comments, docstrings and files
that are not Lean modules. Every run of E1-E19 was repeated on x86_64 and on aarch64 (Linux), after `lake build` and
`lake build Axioms` with no previously built module of this repository, from the Lean sources of release 0.5.0, with run
files equal byte for byte to those written by its `scripts/gen_evidence_runs.py`: each output equals the recorded one
(run times excepted), and the vector files have the sha256 in `SHA256SUMS`. The runs of E20-E34 were recorded on x86_64
(Linux) on earlier trees of this repository, with the run files that `scripts/gen_evidence_runs.py` writes (from
`falcon1024-KAT.rsp`, and for E26 from `test-vector-sampler-falcon1024.txt`); 4 of the 40 key-check files of E23, 3 of
the 20 files of E25 and 3 of the 16 files of E26 were run twice, with equal outputs (run times excepted); each of the
two files of E28 was run twice, printing nothing both times; each of the six files of E33 was run three times, the three
`δ43q_1024` files a fourth time (one run of each `δ43q_1024` file used an earlier version of its run file, with the
`#eval` command on one line), on trees that differ only in two strings the printer writes (`zOfSig`/`zOfSigP`,
`σ1024q`/`sigma1024q`): the output lines are equal and the JSON files are equal apart from those strings. Every run of
E1-E34 was repeated on x86_64 and on aarch64 (Linux), after `lake build` and `lake build Axioms` with no previously
built module of this repository, from the Lean sources, scripts and recorded outputs of release 0.6.0, with the run
files its `scripts/gen_evidence_runs.py` writes: every `#guard_msgs` fact holds (`lake build Axioms`), every other
output equals the recorded one (run times excepted; the runs of E8, E12, E20, E21 and E28 print nothing), and the vector
files have the sha256 in `SHA256SUMS`.
