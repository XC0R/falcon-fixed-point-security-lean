# FalconPrecision

Kernel-checked security of fixed-point Falcon signing, with explicit constants.

A Lean 4 formalisation of the security argument of

> Daniel De Almeida Braga, Pierre-Alain Fouque, Bachir Lachguel, Thomas Prest,
> *Toward a Secure Fixed-Point Implementation of the Falcon Signature Scheme*, IACR ePrint 2026/1531
> (extended version of the CRYPTO 2026 paper; lemma and theorem numbers below are the ePrint's).

The paper proves that fixed-point Falcon loses at most 2 bits of UF-CMA security, conditionally on error bounds for
the leaves `σ̄ᵢ` and the sampler centers `t̄` of the fixed-point signer, through Rényi-divergence lemmas whose error
terms are stated as `O(ϵ)`. This repository proves those lemmas and both main theorems in Lean for Falcon's leaf
range, with every `O(·)` replaced by an explicit constant, and instantiates them at the Falcon-512 and Falcon-1024
parameters of the Falcon round-3 specification (v1.2). Falcon is being standardised by NIST as FN-DSA (FIPS 206);
as of 2026-11-10 FIPS 206 has not been published (statements below about "the FIPS 206 draft" refer to the draft
as previewed by NIST in its FIPS 206 status talk, Perlner, 2025), so the parameters used are those of the round-3
specification.

Release 0.2.0 (stage S7) adds, for Falcon-512, the fixed-point errors of the FFT and of the ffSampling centers, proved
from per-operation rounding bounds, and an execution model of signing in which the execution-level hypotheses `hN`
(SamplerZ calls) and `hS₂` (center errors summed along each execution) of Theorem 2 are proved
(`Falcon.falcon512_model`). Its reference world is exact signing on the stored tree, not exact Falcon; see [S7](#s7)
under Assumptions and limits.

Scope: the theorems are proved for leaf standard deviations in `[1.277, 2]` (both Falcon parameter sets have
`σmin ≥ 1.2778`, `σmax = 1.8205`), with explicit conditions in place of the paper's smoothing-parameter hypotheses
(`σmin ≥ √(1+3αΔσ)·ηϵ(Z)`, `αΔσ ≤ 1/8`); leaf errors enter as `|1/σ̄ᵢ² − 1/σᵢ²|` (the instances convert from the
relative error `|σ̄ᵢ/σᵢ − 1|`). Lemma 4 holds for every `σ` with `T(σ) < 1`; the constant of Lemma 5 is made
explicit on the Falcon leaf range.

The development is a library on top of [VCVio](https://github.com/Verified-zkEVM/VCV-io) (oracle computations,
measure semantics, Rényi divergence, discrete Gaussians) and [Mathlib](https://github.com/leanprover-community/mathlib4).

## Main results

Names are relative to the root namespace `FalconPrecision`.

| Lean | Paper | Statement |
|---|---|---|
| `RenyiShift.renyiMGF_discreteGaussian_shift` | eq. (52), App. B.2 | exact Rényi MGF of two discrete Gaussians with shifted centers |
| `ThetaTail.discreteGaussianSum_eq_fourier`, `discreteGaussianSum_mem` | (replaces smoothing-parameter arguments) | Poisson summation; `ρσ(Z−u) ∈ σ√(2π)(1 ± T(σ))` with an explicit theta tail `T` |
| `Lemma4.renyiDiv_shift_le` | Lemma 4 | for `a > 1`, `T(σ) < 1`: `Rₐ(D_{σ,c+δ} ‖ D_{σ,c}) ≤ exp(aδ²/(2σ²) + a(a+1)δ²M(σ)/(2(a−1)))` |
| `NumTail.falcon_tail` | — | `σ ≥ 1.277 ⇒ T(σ) < 1, M(σ) ≤ 2⁻³⁰` |
| `RenyiScale.renyiMGF_discreteGaussian_scale` | eq. (55) | exact Rényi MGF of two discrete Gaussians of different widths |
| `Lemma5.renyiDiv_scale_le`, `NumK.renyiDiv_scale_le_falcon` | Lemma 5 | `Rₐ(D_{σ₂,c} ‖ D_{σ₁,c}) ≤ exp(a(a+1)(τ₂−τ₁)²K/(2(a−1)))`, `τ = 1/σ²`, `K` a bound on `ψ''`; `K = (1/2 + 2⁻¹⁹)/τlo²` on the Falcon leaf range |
| `RenyiHybrid.renyiMGF_simulateQ_le`, `RenyiPath.lemma14` | Lemma 14 ([HPRR20, Lemma 11]) | adaptive Rényi hybrid over the queries of an `OracleComp` (uniform per-query bound); per-query `R_{2λ−1} ≤ 1 + 1/(4n)` gives the 1-bit transfer |
| `RenyiPath.renyiMGF_simulateQ_le_path` | Lemma 16 | chain rule along executions (path-budget form) |
| `RenyiPath.lemma15` | Lemma 15 | probability preservation from a joint bound, with a parameter `T ≥ 1` |
| `FalconGame.theorem1` | Theorem 1 | worst-case errors: fixed-point Falcon loses at most 2 bits |
| `FalconGame.theorem2` | Theorem 2 | errors summed along each execution (the RMSE form) |
| `Falcon.falcon512`, `Falcon.falcon1024` | Theorem 1, sufficient budgets chosen here | every `3 ≤ λ ≤ 128` (resp. `256`): per call `\|σ̄/σ − 1\| ≤ 2⁻⁴⁷` and `\|t̄ − t\| ≤ 2⁻⁴³` (resp. `2⁻⁴⁴`), at most `2⁷⁵` (resp. `2⁷⁶`) SamplerZ calls along every execution (`2n·Qs·(1+c)`, `Qs = 2⁶⁴`) |
| `Falcon.falcon512_rmse` | Theorem 2 at the paper's §5 operating point | every `3 ≤ λ ≤ 128`: per call `\|σ̄/σ − 1\| ≤ 2⁻⁴⁷`, at most `2⁷¹` SamplerZ calls (`2n·Qs·(1+c)`, `Qs = 2⁶⁰`, `c < 1`), `Σ(t̄ − t)² ≤ 2⁻⁹` along every execution |
| `FalconWitness.worlds_exist`, `test/EndToEnd.lean` | — | the sampler hypotheses are satisfiable; `falcon512` applied to a concrete experiment with a SamplerZ call |

The budgets of `falcon512`/`falcon1024` are sufficient conditions, not properties of any implementation: the paper's
measured center RMSE (`2⁻³⁹·⁵`, §7.5) does not meet the worst-case `2⁻⁴³`. `2⁻⁹` in `falcon512_rmse` is the sum the
measured RMSE gives over `2n·Qs = 2⁷⁰` calls (no restarts).

### S7 results (Falcon-512)

`ρ : Arith` is a fixed-point arithmetic: one function per operation, each within its error bound at the output ulp
(`p = 63`, §7.1-7.2). F and E are the worlds of [Form of the S7 statement](#form-of-the-s7-statement).

| Lean | Paper | Statement |
|---|---|---|
| `Falcon.falcon512_model` | Theorem 2, λ = 128 | F ⇒ E for `K ≤ 2³⁸` `sign1` calls; `hN`, `hS₂` proved |
| `Falcon.falcon512_proved` | Theorem 2, λ = 128 | per call `\|σ̄/σ − 1\| ≤ 2⁻⁴²`; `hN` (`2⁵¹`), `hS₂` (`2⁻⁹`) assumed |
| `Falcon.centers_budget` | — | `2³⁸·(49·3.65·2⁻³² + 135700·2⁻⁴²)² ≤ 2⁻⁹` |
| `Errors.FFSamp.input_err` | §7.3, Table 4 | `(t̂0, t̂1) = (−FFT(c/q)⊙F̂, FFT(c/q)⊙f̂)`: ℓ2 error `≤ 3.65·2⁻³²` |
| `Errors.FFSamp.falcon512_centers` | Alg. 8, Table 4 | budgets (assumed) ⇒ `√Σ(t̄ − t)² ≤ 49·‖δt̂‖₂ + 135700·2⁻⁴²` |
| `Errors.FFSamp.ffs_pathS`, `ffs_pathN` | Alg. 8 | along every execution of the model `ffs` (budgets derived, not assumed): `Σ(t̄ − t)² ≤ (Ā_L·e + C̄_L)²` for input ℓ2 error `≤ e`; `≤ 2^(L+1)` SamplerZ calls |
| `Errors.FFSamp.Uses.pathS`, `Uses.pathN` | — | `K` calls of `sign1`: `K·(49·3.65·2⁻³² + 135700·2⁻⁴²)²`, `1024·K` |
| `Errors.LDL.falcon512_leaf` | Lemma 8, §7.3 item 3 | given `hroot`, `hstep`, `hs`: leaves `\|σ̄ᵢ/σᵢ − 1\| ≤ 2⁻⁴²` |
| `Errors.FFTRec.fft_rec_err` | §7.3 item 1 | recursive FFT error `E_{L+1} = (2 + δ)E_L + δ·2^L·A + r` |
| `RenyiPath.PathSum.bind`, `PathSumP.bind` | (Lemma 16 budgets) | path budgets add along `>>=` |
| `RenyiPath.BlockPath.pathSum` | (Lemma 16 budgets) | `K` blocks with path sum `≤ c` each give path sum `≤ K·c` |
| `Errors.Fixed.Rnd.arith` | §7.2 | rounding within `½` ulp at every operation is an `Arith` (`Arith` is inhabited) |

`test/Axioms.lean` and `test/S7Axioms.lean` check with `#guard_msgs` that each theorem above
(`discreteGaussianSum_eq_fourier` through `discreteGaussianSum_mem`, which rewrites with it) depends only on
`propext`, `Classical.choice` and `Quot.sound`; `lake build Axioms` fails otherwise.

### Form of the security statements

The UF-CMA experiment is one computation `oa : OracleComp (spec aux Q) α`. Auxiliary oracles `aux` carry all
randomness other than the sampler (key generation, adversary coins, salts, hashing) and are answered identically in
the three worlds; each SamplerZ call carries the exact and fixed-point leaf and center computed by `oa` from its
history. The worlds answer SamplerZ by `D_{σ,t}` (exact), `D_{σ̄,t}` (intermediate) and `D_{σ̄,t̄}` (fixed point).
The conclusion, for every parameter `T ≥ 1`, is `T·2^{−(λ−2)} < Pr_fixed[win] ⇒ T·2^{−λ} < Pr_exact[win]`; read with
`T` the adversary's running time it is the bit-security statement `log₂(T/ε)`, but no cost model ties `T` to `oa`.

### Form of the S7 statement

`Falcon.falcon512_model` instantiates the experiment above with a model of standard signing at Falcon-512.
`sign1 ρ k c` computes `t̂ = (−FFT(c/q)⊙F̂, FFT(c/q)⊙f̂)` (spec Alg. 10 l. 3, with `c/q` before the FFT; tag 9 by §7.3
item 1) and runs ffSampling (`ffs`, Alg. 8) on the
stored tree of the key `k`, in exact and in fixed-point arithmetic side by side; each leaf issues SamplerZ calls that
carry the stored leaf `σ̄` and the exact and computed centers `t`, `t̄`. `Uses ρ K oa`: along every execution, `oa`
calls `sign1` at most `K` times (restarts included) and otherwise makes only auxiliary queries.

- World F: fixed-point signing with any arithmetic `ρ : Arith` meeting the per-operation bounds (complex product
  `√2·u`, halving `√2·u/2`, retag `u/2`, `c/q` at tag 0 within `2⁻⁶⁴`, twiddle tables within `0.7072·2⁻⁶³`).
  SamplerZ is called at the computed centers `t̄`, and signing returns `⊥` when a computed split input `t̄1`, `t̄0'`
  or odd merge input `ẑ1` leaves `‖·‖ ≤ 2²¹ − 1`. A signer is F when its operations form an `Arith`, follow
  `sign1`'s order of operations (`c/q` at tag 0, the FFTs of `c/q`, `F`, `f` by the merge recursion at tags 9, 12,
  8, the products at tag 21, then `ffs`) with the same result for the same output ulp and operands at every call
  site, return `⊥` exactly on these checks, overflow no other register and obtain the integers `z` exactly.
- World E: exact signing on the same stored tree, with the same aborts (the aborts are functions of the history,
  identical in the three worlds of Theorem 2).
- Result: `λ = 128`, `K ≤ 2³⁸` ffSampling calls (`sign1`, restarts included), every `T ≥ 1`:
  `T·2⁻¹²⁶ < Pr_F[s] ⇒ T·2⁻¹²⁸ < Pr_E[s]`. `hN` (`≤ 1024·K ≤ 2⁵¹` SamplerZ calls, `Uses.pathN`) and `hS₂`
  (`Σ(t̄ − t)² ≤ K·(49·3.65·2⁻³² + 135700·2⁻⁴²)² ≤ 2⁻⁹`, `Uses.pathS`, `centers_budget`) are proved from the model.
  The reference leaf is the stored leaf (`CallP.stored`), so the leaf error of Theorem 2 is `0`.
- Key: `Key` holds `f, F` with `‖FFT(f)‖∞ ≤ γf,g = 255` and `‖FFT(F)‖∞ ≤ γF,G = 3500` (exact FFTs), checks of the
  paper's modified NTRUGen (Alg. 2 l. 7, 13; §8.3-8.4). Keygen runs them in fixed point, so they hold up to
  keygen's rounding (not formalised).
- Tree: `FTree` holds every stored leaf in `[1.277833697, 1.8205]` (leaf range check, as in the FIPS 206 draft) and
  `‖ℓ̂‖∞ ≤ 24.0001` at the root, `≤ 0.9923` below. The `ℓ̂` check is added by the model; it is in neither Falcon
  round 3 nor the FIPS 206 draft. The root bound corresponds to `γroot = 24` (Alg. 2 l. 14-15, Lemma 7 (12)), the
  inner one to `γhybrid = 4` (Alg. 2 l. 8) through Lemma 8 (16). Nothing ties the tree to the key `f, F`.

### Explicit constants compared with the paper

- Lemma 4: main term `aδ²/(2σ²)` (paper: `a(a+1)δ²/(2(a−1)σ²)`), error `a(a+1)δ²M(σ)/(2(a−1))` with
  `M(σ) ≤ 2⁻³⁰` at Falcon's leaves (paper: `(1 + O(ϵ))`).
- Lemma 5: `ln Rₐ ≤ a(a+1)(τ₂−τ₁)²K/(2(a−1))` with `K ≈ 1/(2τlo²)`, `τlo` the smallest `τ` on the segment
  (paper: `3aδ²/(4(1−aδ)²)·(1 + O(ϵσ₁⁴))`). With one global `τlo = 0.3`, as in the instances, the relative-error
  form reaches about `4.2·aΔσ²` near `σmin`, above the paper's `3aΔσ²`.
- The smoothing parameter `ηϵ(Z)` is not used; the theta tails are bounded explicitly.

## Assumptions and limits

- The sampler is perfect: SamplerZ returns exact discrete Gaussians, as assumed by the paper's theorems.
- Everything other than SamplerZ's parameters is assumed identical in the three worlds: signature assembly, norm
  test, compression, restart decision and key-generation rejection. For a fixed-point signer this is an
  implementation obligation (integer recomputation, or fixed-point error small enough to round to the exact result),
  in addition to the leaf and center bounds. The paper makes the same assumption implicitly.
- The error bounds on leaves and centers (or their sums along executions) are hypotheses of `theorem1`, `theorem2`,
  `falcon512`, `falcon1024`, `falcon512_rmse` and `falcon512_proved`, as in the paper; proving them for a fixed-point
  implementation is the paper's stated open problem. S7 proves the call count and the center sum for its signing model
  only, within the limits below.
- `oa` is a finite term: signing restarts are capped, and the hypotheses range over every history, so out-of-range
  samples must abort or clamp identically in the three worlds. Relating this experiment to uncapped Falcon is not
  formalised (the paper's `c` and "for any history" leave the same gap).
- The center sum in `falcon512_rmse` is a hypothesis on every execution; the paper's RMSE is a sample average.
- Outputs of the experiment range over a countable type.

### S7

- Abort gap: `Pr_E[abort]` is not bounded. For exact stored-tree signing X without aborts, `Pr_X[s] ≥ Pr_E[s] −
  Pr_E[abort]` (a coupling argument, not formalised); Lemma 12 at `λ = 128` gives only about `K·2⁻¹²⁸` for
  `Pr_E[abort]` over `K ≤ 2³⁸` calls, so against abort-free exact signing the 128-bit statement does not follow.
- Hop B (stored tree to true tree: center shift `(t1 − z1)(ℓ̂ − ℓ)`, leaves `σ̄ → σ`) is not proved, so S7 states
  nothing relative to exact Falcon.
- Keys are those of the paper's modified NTRUGen (Alg. 2), not Falcon round 3 or FIPS 206 draft keys; `Key`'s
  exact-FFT bounds hold only up to keygen's fixed-point rounding (not formalised).
- SamplerZ is perfect (`hE`, `hM`, `hF`).
- No UF-CMA game is defined: `oa` is any experiment, and the conclusion transfers a success probability.
- Overflow is covered only on the checked values; sums and differences inside split, merge and line 10, products,
  each child's merged `ẑ0`, the root's merged output and the FFTs of `c/q`, `f`, `F` are not covered.
- The computation of the stored tree (ffLDL⋆, reciprocal, rsqrt) is not modelled; `falcon512_leaf` is conditional
  on `hroot`, `hstep`, `hs`. Lemma 8 (16), behind the inner `ℓ̂` bound, is not formalised.
- Tweak signing (tag 18) is not covered.
- Recovering `z` from the computed FFT form (invFFT and rounding) is not modelled.
- The norm check and restarts are integer code on `z` in `oa` (§7.3 item 4); signers computing `s = (t − z)B̂` in
  floating point are not modelled.
- The size-2 merge must multiply by `±i` exactly (tag 0 cannot hold `i`).
- Assumed (the paper does not specify their computation): `c/q` is within `½` ulp at tag 0, and the twiddle tables
  are within `0.7072·2⁻⁶³` of the exact roots. Not `Arith` instances: Karatsuba products, halve-then-multiply
  splits, truncating retags.
- The model uses the paper's Type 2 64-bit format (§7, centers at tag 21, Table 4); no existing implementation,
  including the paper's Type 2 Python implementation, is shown to meet F's conditions. It is not the paper's 64.64
  Type 1 C implementation (§6) and not the FIPS 206 draft signer, which signs in binary64 floating point.
  NIST has announced plans to specify FN-DSA signing in 64.64 fixed point (pqc-forum, 28 September 2026, as cited
  in ePrint 2026/2431); this release does not model that chain.
- Falcon-1024 is not covered by S7.

Open: the 64.64 fixed-point chain; a bound on `Pr_E[abort]` (Lemma 12 at `λ` above 128 within the `2²¹ − 2`
range); hop B.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and the VCVio commit are pinned (`lean-toolchain`,
`lakefile.lean`, `lake-manifest.json`): VCVio `e7770ef7`, Lean `v4.35.0`.

```sh
lake exe cache get   # optional: download Mathlib's build cache
lake build           # every module, including S7 (FalconPrecision/Errors, by glob)
lake build Axioms    # guarded #print axioms (test/Axioms.lean, test/S7Axioms.lean) and the end-to-end example
```

Both commands have been run on x86_64 and aarch64; every guarded `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.

## Development

Developed with Claude Code (Anthropic) under the direction of XC0R. Every theorem named above is checked by the
Lean kernel; `lake build` and `lake build Axioms` re-check them without trusting how they were produced.

## License

Apache 2.0, as VCVio and Mathlib.
