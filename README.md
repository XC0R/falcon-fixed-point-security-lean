# FalconPrecision

Kernel-checked security of fixed-point Falcon signing, with explicit constants.

A Lean 4 formalisation of the security argument of

> Daniel De Almeida Braga, Pierre-Alain Fouque, Bachir Lachguel, Thomas Prest,
> *Toward a Secure Fixed-Point Implementation of the Falcon Signature Scheme*, IACR ePrint 2026/1531
> (extended version of the CRYPTO 2026 paper, Advances in Cryptology – CRYPTO 2026, Lecture Notes in Computer
> Science, Springer, pp. 166–197, doi:10.1007/978-3-032-35377-1_6; lemma and theorem numbers below are the ePrint's).

The paper proves that fixed-point Falcon loses at most 2 bits of UF-CMA security, conditionally on error bounds for
the leaves `σ̄ᵢ` and the sampler centers `t̄` of the fixed-point signer, through Rényi-divergence lemmas whose error
terms are stated as `O(ϵ)`. This repository proves those lemmas and both main theorems in Lean for Falcon's leaf
range, with every `O(·)` replaced by an explicit constant, and instantiates them at the Falcon-512 and Falcon-1024
parameters of the Falcon round-3 specification (v1.2). Falcon is being standardised by NIST as FN-DSA (FIPS 206);
as of 2026-11-27 FIPS 206 has not been published (statements below about "the FIPS 206 draft" refer to the draft
as previewed by NIST in its FIPS 206 status talk, Perlner, 2025), so the parameters used are those of the round-3
specification.

Release 0.2.0 (stage S7) adds, for Falcon-512, the fixed-point errors of the FFT and of the ffSampling centers, proved
from per-operation rounding bounds, and an execution model of signing in which the execution-level hypotheses `hN`
(SamplerZ calls) and `hS₂` (center errors summed along each execution) of Theorem 2 are proved
(`Falcon.falcon512_model`). Its reference world is exact signing on the stored tree, not exact Falcon; see [S7](#s7)
under Assumptions and limits.

Release 0.3.0 (stage S8) adds, for Falcon-512, the same model for the non-split scale-first Type 1 chain of ePrint
2026/2431 §3.1 at 64 fractional bits, and bounds the abort gap of that model: signing with the model's range checks
(F), and fixed-point signing without them (F′), are related to abort-free exact signing on the stored tree (X), with
an explicit `2⁻¹⁴⁰` per side. See [S8 results](#s8-results-falcon-512) and [S8](#s8) under Assumptions and limits.

Release 0.4.0 (hop B) adds, for Falcon-512, the step from the stored tree to the true tree: abort-free exact signing
on the stored tree (X) is related to exact Falcon signing (Y), ffSampling on the exact ffLDL⋆ tree of the basis
`B = [[g, −f], [G, −F]]`, and, composed with S8, check-free fixed-point signing (F′) is related to Y. The relation
between the two trees is a hypothesis on every key (`Close δ`); hop B formalises no model of key expansion (the
executable track below adds one, with a per-key check that implies `Close δ`). See
[Hop B results](#hop-b-results-falcon-512) and [Hop B](#hop-b) under Assumptions and limits.

Release 0.5.0 (executable track) adds, for Falcon-512, executable Lean definitions of fixed-point arithmetic at 64
fraction bits, key expansion with a per-key check, the signer, SamplerZ, encodings, HashToPoint and verification, each
parametric in the unpinned choices of the FN-DSA design space that it models, theorems relating them to the S8 model
and hop B, to the Falcon round-3 specification and to each other, and certified interval reference vectors for
signing attempts. Facts about concrete keys, KAT entries and inputs are computed by `#eval` and enter the theorems as
`Bool` premises; the code, scripts and recorded outputs to re-run them are in [evidence/](evidence/README.md) and
`scripts/`. See [Executable track](#executable-track-falcon-512-and-falcon-1024) and [LIMITS.md](LIMITS.md).

Release 0.6.0 adds Falcon-1024 (`n = 1024`): S8 and hop B at tree depth 10, and the executable track at Falcon-1024
(the per-key check, the signer with its integer ranges and words, SamplerZ at Falcon-1024's `σmin`, encodings and
verification against the round-3 Falcon-1024 KAT file, design-space equivalences and witnesses, and certified
interval reference vectors). The executable signer with the executable SamplerZ is composed with hop B at the 128-bit
type and at the λ = 256 level for at most `2²⁹` signing queries, also on keys passing the per-key check; the λ = 256
statement is meaningful only with SamplerZ shift rejection. See
[S8 at Falcon-1024](#s8-at-falcon-1024-tree-depth-10), [Hop B at Falcon-1024](#hop-b-at-falcon-1024-tree-depth-10)
and [LIMITS.md](LIMITS.md).

Scope: the theorems are proved for leaf standard deviations in `[1.277, 2]` (both Falcon parameter sets have
`σmin ≥ 1.2778`, `σmax = 1.8205`), with explicit conditions in place of the paper's smoothing-parameter hypotheses
(`σmin ≥ √(1+3αΔσ)·ηϵ(Z)`, `αΔσ ≤ 1/8`); leaf errors enter as `|1/σ̄ᵢ² − 1/σᵢ²|` (the instances convert from the
relative error `|σ̄ᵢ/σᵢ − 1|`). Lemma 4 holds for every `σ` with `T(σ) < 1`; the constant of Lemma 5 is made
explicit on the Falcon leaf range.

The development is a library on top of [VCVio](https://github.com/Verified-zkEVM/VCVio) (oracle computations,
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
| `Errors.FFSamp.input_err` | §7.3, Table 4 | `(t̂0, t̂1) = (−FFT(c/q)⊙F̂, FFT(c/q)⊙f̂)`, `|cᵢ| < q`: ℓ2 error `≤ 3.65·2⁻³²` |
| `Errors.FFSamp.falcon512_centers` | Alg. 8, Table 4 | budgets (assumed) ⇒ `√Σ(t̄ − t)² ≤ 49·‖δt̂‖₂ + 135700·2⁻⁴²` |
| `Errors.FFSamp.ffs_pathS`, `ffs_pathN` | Alg. 8 | along every execution of the model `ffs` (budgets derived, not assumed): `Σ(t̄ − t)² ≤ (Ā_L·e + C̄_L)²` for input ℓ2 error `≤ e` when `L ≤ 9` and `Ā_L·e + C̄_L ≤ 2⁻¹⁰`; `≤ 2^(L+1)` SamplerZ calls |
| `Errors.FFSamp.Uses.pathS`, `Uses.pathN` | — | `K` calls of `sign1`: `K·(49·3.65·2⁻³² + 135700·2⁻⁴²)²`, `1024·K` |
| `Errors.LDL.falcon512_leaf` | Lemma 8, §7.3 item 3 | given `hroot`, `hstep`, `hs`: leaves `\|σ̄ᵢ/σᵢ − 1\| ≤ 2⁻⁴²` |
| `Errors.FFTRec.fft_rec_err` | §7.3 item 1 | recursive FFT error `E_{L+1} = (2 + δ)E_L + δ·2^L·A + r` |
| `RenyiPath.PathSum.bind`, `PathSumP.bind` | (Lemma 16 budgets) | path budgets add along `>>=` |
| `RenyiPath.BlockPath.pathSum` | (Lemma 16 budgets) | `K` blocks with path sum `≤ c` each give path sum `≤ K·c` |
| `Errors.Fixed.Rnd.arith` | §7.2 | rounding within `½` ulp at every operation is an `Arith` (`Arith` is inhabited) |

### S8 results (Falcon-512)

`ρ : Arith64 εq` is a Type 1 arithmetic at 64 fractional bits (every operation at ulp `2⁻⁶⁴`, twiddle tables within
`0.7072·2⁻⁶⁴`, the stored `1/q` within `εq`). `sign164 ρ k c` is the scale-first target `((−ĉ/q)⊙F̂, (ĉ/q)⊙f̂)`
with `ĉ = FFT(c)` from the integers `c`, then ffSampling with range checks `‖·‖ ≤ R64 − 1`, `R64 = 2²⁴`, on the
computed split inputs and odd merge inputs. `sign164G ρ (fun _ _ _ => True)` is the same computation with no checks.

| Lean | Statement |
|---|---|
| `Errors.FFSamp.input_err64`, `inp64_base`, `inp64_norm` | ℓ2 input error of ffSampling `≤ 3.3·2⁻³²` (`1/q` within `2⁻⁶⁵`), `≤ 0.54·2⁻³²` (`1/q` within `2⁻⁷⁸`) |
| `Falcon.falcon512_model64`, `falcon512_model64n` | F ⇒ E (E: exact stored-tree signing with the same aborts) for `K ≤ 2³⁸` (`εq = 2⁻⁶⁵`), `K ≤ 2³⁹` (`εq = 2⁻⁷⁸`) calls of `sign164`; `hN`, `hS₂` proved |
| `Errors.FFSamp.sign164_eq_margin` | while the checks pass, every checked computed value is within `1` of its exact value |
| `Errors.GaussTail.measure_abs_ge_le`, `kappa_falcon` | `P[\|z − c\| ≥ r] ≤ 2κ(σ)exp(−r²/(2σ²))` for `D_{Z,σ,c}` at any centre; `κ(σ) ≤ 1 + 2⁻³⁶` for `σ ≥ 1.277` |
| `Errors.AbortTV.etvDist_simulateQ_le_path` | total variation along executions `≤ c·S` for per-query bounds `c·w` and a path sum `≤ S` |
| `RenyiPath.etvDist_simulateQ_rewrite` | the same against a run whose answers are post-processed, the path sum taken along the post-processed run |
| `Errors.AbortExact.ffsG_clamp` | with every SamplerZ answer within `30` of its exact centre and a real stored tree, every checked exact value is `≤ 2²⁴ − 2`, so no check that passes there fires |
| `Errors.AbortExact.etvDist_E_X`, `eps_le` | `\|Pr_E[oa ∈ s] − Pr_X[ox ∈ s]\| ≤ 2·p(30)·1024K ≤ 2⁻¹⁴⁰` for `K ≤ 2³⁹` |
| `Errors.AbortExact.etvDist_F_F'`, `eps_leF` | `\|Pr_F[oa ∈ s] − Pr_F′[ox ∈ s]\| ≤ 2·p_F(29.9)·1024K ≤ 2⁻¹⁴⁰` for `K ≤ 2³⁹` with centre budget `K·(49e + 43700·2⁻⁴⁰)² ≤ 2⁻⁸` (both `εq` above) |
| `Falcon.falcon512_exact64`, `falcon512_exact64n` | `T·2⁻¹²⁶ < Pr_F[oa ∈ s] ⇒ T·2⁻¹²⁸ < Pr_X[ox ∈ s] + 2⁻¹⁴⁰` (`K ≤ 2³⁸`, resp. `2³⁹`) |
| `Falcon.falcon512_exact64'`, `falcon512_exact64n'` | `T·2⁻¹²⁶ + 2⁻¹⁴⁰ < Pr_F′[ox ∈ s] ⇒ T·2⁻¹²⁸ < Pr_X[ox ∈ s] + 2⁻¹⁴⁰` (`K ≤ 2³⁸`, resp. `2³⁹`) |
| `Errors.AbortExact.Swap.signLoopG` | a signing loop (spec Alg. 10 l. 4-11) and its abort-free version satisfy `Swap` |

`p(y) = 2(1 + 2⁻³⁶)exp(−y²/(2·1.825²))` and `p_F(y)` the same with `1.826`. The proved constant is `2⁻¹⁴⁰` on both
sides; the values, not proved, are about `2⁻¹⁴³·⁹` (E side) and `2⁻¹⁴²·⁴` (F side) at `K = 2³⁹`.

### Form of the S8 statements

- X runs `ox`, the experiment `oa` with each of its at most `K` calls of `sign164` replaced by
  `sign164G ρ (fun _ _ _ => True)` (`Swap`); its SamplerZ calls are answered by `D_{σ,t}`, so the computed centres
  they carry play no role. X, like every world, returns `⊥` for `c` with some `|c i| ≥ q`; HashToPoint outputs
  satisfy `|c i| < q`.
- F′ runs the same `ox`, answered by `D_{σ̄,t̄}`: fixed-point signing with no range checks.
- E side: clamping every SamplerZ answer of E to within `30` of its centre costs `p(30)` per query
  (`AbortTV.etvDist_implT_le`). Clamped answers keep every checked exact value in range (route B′: merges are `√2`
  times unitary, line 10 adds `ℓ̂⊙δ1`, deterministic part `≤ 512·3500`), so `sign164` and `sign164G ρ (fun _ _ _ =>
  True)` are equal on clamped runs.
- F side: an answer of F is kept when it lies within `29.9` of the computed centre `t̄` and `(t̄ − t)² ≤ 2⁻⁸`, and is
  otherwise replaced by the rounded exact centre (`clampF`). Along every execution of `oa` the sum of `(t̄ − t)²` is
  `≤ 2⁻⁹` (`Uses64.pathS`), so no query with `(t̄ − t)² > 2⁻⁸` occurs, and the clamped answers lie within `30` of the
  exact centres.
- Hypotheses beyond those of `falcon512_model64(n)`: every stored tree is real (`FTreeP.Real`, carried by `Swap`);
  for `falcon512_exact64(n)'`, every auxiliary answer type is inhabited.

### S8 at Falcon-1024 (tree depth 10)

The ffSampling path budget, the check margins, the clamp lemma and the two total-variation bounds of S8 are stated for
any node bounds `Λ` and norm factors `N` satisfying `Errors.FFSamp.TreeBounds` and any depth (`Budget Λ Lr`);
the Falcon-512 theorems above are their instances, with the statements of 0.5.0. At Falcon-1024 (`n = 1024`, depth 10,
`σmin = 1.298280334`): stored trees `FTree1024` with `‖ℓ̂‖∞ ≤ 32.0001` at the root and `≤ 0.9990` below, keys
`Key1024` with `‖f̂‖∞ ≤ 256`, `‖F̂‖∞ ≤ 7365` (the thresholds `γroot = 32`, `γhybrid = 6.53`, `γf,g = 256`,
`γF,G = 7365` of ePrint 2026/2431 §3.3, tuple B, with `≤` where that paper uses `<`; the inner bound `0.9990` is
above `(γhybrid⁴ − 1)/(γhybrid⁴ + 1) = 0.99890…`, the bound from `γhybrid` of 2026/2431 Table 1 and Lemma 8 (16) of ePrint
2026/1531, which is not formalised), and range checks `‖·‖ ≤ R64_1024 − 1`, `R64_1024 = 2²⁷` (`sign164R R64_1024`).

| Lean | Statement |
|---|---|
| `Errors.FFSamp.ffs_pathSP`, `ffsU_eq_marginP`, `Errors.AbortExact.ffsG_clampP`, `etvDist_E_XP`, `etvDist_F_F'P` | the path budget, check margins, clamp lemma and the two total-variation bounds for any tree bounds, depth and clamp radius, and any pair of signing calls with the stated call counts and clamp equality |
| `Errors.FFSamp.ffs64_pathS1024`, `ffs64_pathN1024`, `coef64_1024` | one Type 1 ffSampling call at depth 10, input errors of ℓ2 norm `≤ e` with `76e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰`: `Σ(t̄ − t)² ≤ (76e + 1084900·2⁻⁴⁰)²` along every execution, at most `2048` SamplerZ calls (`Ā₁₀ ≤ 76`, `C̄₁₀ ≤ 1084900·2⁻⁴⁰`) |
| `Errors.FFSamp.input_err64_1024`, `inp64_1024_base`, `inp64_1024_norm` | ℓ2 input error of ffSampling at Falcon-1024 `≤ 15.6·2⁻³²` (`1/q` within `2⁻⁶⁵`), `≤ 4.4·2⁻³²` (`1/q` within `2⁻⁷⁸`) |
| `Errors.FFSamp.Uses1024.pathS`, `Uses1024.pathN`, `centers_budget1024`, `centers_budget1024n` | `K` calls of `sign164R R64_1024`: `Σ(t̄ − t)² ≤ K·(76e + 1084900·2⁻⁴⁰)²` and `≤ 2048K` SamplerZ calls along every execution; `≤ 2⁻¹⁰` for `K ≤ 2²⁹` at either input bound |
| `Errors.AbortExact.sign1024_clamp`, `tables1024` | with every SamplerZ answer within `41` of its exact centre and a real stored tree, every checked exact value is `≤ 2²⁷ − 2`, so `sign164R R64_1024` equals its check-free version for an input bound `inp64_1024 εq ≤ e` with `76e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰` |
| `Errors.AbortExact.etvDist_E_X1024`, `eps_le1024` | `\|Pr_E[oa ∈ s] − Pr_X[ox ∈ s]\| ≤ 2·p(y)·2048K` for every `K`, `1/2 ≤ y ≤ 41` and an input bound `inp64_1024 εq ≤ e` with `76e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰`; `2·p(41)·2048K ≤ 2⁻²⁸⁰` for `K ≤ 2⁶⁴` |
| `Errors.AbortExact.etvDist_F_F'1024`, `eps_leF1024` | `\|Pr_F[oa ∈ s] − Pr_F′[ox ∈ s]\| ≤ 2·p_F(y)·2048K` for an input bound `inp64_1024 εq ≤ e` with `76e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰`, `1/2 ≤ y ≤ 40.9` and `K·(76e + 1084900·2⁻⁴⁰)² ≤ 2⁻⁸` (`K ≤ 2³¹` at either input bound, a value); `2·p_F(40.9)·2048K ≤ 2⁻²⁸⁰` for `K ≤ 2⁶⁴` |

The clamp radii are `41` and `40.9` (Falcon-512: `30`, `29.9`): at `y = 30` the E term is about `2⁻¹⁵³` at
`K = 2²⁹` (a value, not proved), above `2⁻²⁵⁶`. At depth 10 the route B′ bounds on the checked exact values reach
about `9.04·10⁷` at `y = 41` (`6.80·10⁷` at `y = 30`; values, above `2²⁶`), so the range is `2²⁷`, not Falcon-512's
`2²⁴`; the twiddle term of the per-node budgets grows with the range, and the centre budget `2⁻¹⁰` holds for
`K ≤ 2²⁹` calls at either input bound (`2⁻⁹` would allow `2³⁰`, a value; Falcon-512: `2⁻⁹` for `K ≤ 2³⁸`, resp.
`2³⁹`). At Falcon-1024 Theorem 2 is instantiated at `λ = 128` (hop A, `falcon1024_exact64n'`) and `λ = 131` (hop
B, [Hop B at Falcon-1024](#hop-b-at-falcon-1024-tree-depth-10)), and at the `λ = 256` level at `λ = 256` (hop A,
`Errors.HopB.falcon1024_exact256'`) and `λ = 259` (hop B, `Errors.HopB.falcon1024_hopB259`), with `2⁶⁴` SamplerZ
calls and the centre budget `2⁻¹⁰`.

### Hop B results (Falcon-512)

The experiment `oe` makes auxiliary queries and signing-oracle queries on keys passing `KeyB.Good δ` (stored tree real,
`Close δ` to the true tree); `K` bounds its signing-oracle calls (one ffSampling call each, restarts included) along
every execution. X is abort-free exact signing on the stored tree (`runX` under `implE`, as in S8; `falcon512_hopB`
states X as `runB` under `implF`, the same distribution by `relabel_X`). Hop A is S8's step from F′ to X
(`falcon512_exact64n'`). Y is exact Falcon signing: ffSampling (Alg. 8) on `KeyB.trueTree`, the exact ffLDL⋆ (Alg. 5) of
`B·B⋆` with leaves `σ/√D` (`runT` under `implE`). F′ is check-free Type 1 signing on the stored tree (`runX` under
`implF`, as in S8). `Close δ`: `‖ℓ̂ − ℓ‖∞ ≤ δ L` at every node of depth `L + 1` (leaves at depth 0, the root at depth
9); at every leaf `|σ̄/σ − 1| ≤ 2⁻⁴²` and the true leaf in `[1.2778, 1.825]`. `s2B y δ` bounds the sum of squared centre
differences `(t̄ − t)²` of one signing call between the two trees when every SamplerZ answer lies within `y` of its true
centre. All four theorems take SamplerZ perfect in every world (`hE`, `hM`, `hF`) and every auxiliary answer type
countable; the last three take a Type 1 arithmetic `ρ : Arith64 (1/2⁷⁸)` and every auxiliary answer type inhabited (the
hypotheses of `falcon512_exact64n'`).

| Lean | Worlds | Statement | Tree error |
|---|---|---|---|
| `Errors.HopB.falcon512_hopB` | X ⇒ Y | `K ≤ 2³⁹`: `T·2⁻¹²⁹ + 2⁻¹⁴¹ < Pr_X[s] ⇒ T·2⁻¹³¹ < Pr_Y[s] + 2⁻¹⁴¹` | any `δ` with `K·s2B 30.5 δ ≤ 2⁻⁹` |
| `Errors.HopB.falcon512_fixed_vs_true` | F′ ⇒ Y (hop A, then hop B) | `K ≤ 2³⁹`: `T·2⁻¹²⁶ + 2⁻¹⁴⁰ < Pr_F′[s] ⇒ T·2⁻¹³¹ < Pr_Y[s] + 2⁻¹⁴¹` | any `δ` with `K·s2B 30.5 δ ≤ 2⁻⁹` |
| `Errors.HopB.falcon512_fixed_vs_true127` | F′ ⇒ Y | `K ≤ 2³⁹`: as `falcon512_fixed_vs_true` | assumed (`Close δ127`): `2⁻⁵⁸` at the root, `2⁻⁶³` below (`2³⁹·s2B 30.5 δ127 ≤ 2⁻⁹` proved) |
| `Errors.HopB.falcon512_fixed_vs_true63` | F′ ⇒ Y | `K ≤ 2³⁰`: as `falcon512_fixed_vs_true` | assumed (`Close δ63`): `0.8123·2⁻⁴⁰` at the root, `0.7072·2⁻⁴¹` below (`2³⁰·s2B 30.5 δ63 ≤ 2⁻⁹` proved) |

`Pr_W[s]` is the probability that `oe` run in world W lands in `s`; `T ≥ 1` is arbitrary. Hop B runs Theorem 2 at
`λ = 131` (at most `2⁴⁹` SamplerZ calls, `|1/σ̄² − 1/σ²| ≤ 2⁻⁴⁰` per call, squared centre differences `≤ 2⁻⁹`
along every execution) on a run whose SamplerZ answers are clamped to within `30.5` of the true centres; the clamp
costs `≤ 2⁻¹⁴¹` in X and in Y. Composed with hop A (`falcon512_exact64n'`), F′ against Y loses 5 bits (`2⁻¹²⁶` to
`2⁻¹³¹`). The values, not proved, are about `2⁻³⁶·⁵` (`2³⁹·s2B 30.5 δ127`) and `2⁻⁹·⁴⁹` (`2³⁰·s2B 30.5 δ63`).

`test/Axioms.lean` and `test/S7Axioms.lean` check with `#guard_msgs` that each theorem above
(`discreteGaussianSum_eq_fourier` through `discreteGaussianSum_mem`, which rewrites with it; the hop B theorems in
`test/S7Axioms.lean`) depends only on `propext`, `Classical.choice` and `Quot.sound`; `lake build Axioms` fails
otherwise.

### Hop B at Falcon-1024 (tree depth 10)

Hop B and the definitions it uses are stated at every size: keys `KeyBP` with the true tree `KeyBP.trueTree σ` at
the signing `σ`, the key condition `KeyBP.Good σ δ`, the worlds `runKP`, `runBP`, `runTP`, and the budgets
`gainAP Λ`, `devBP Λ`, `cBP Λ`, `s2BP Λ D` over node bounds `Λ` and depth `D`. The Falcon-512 theorems above keep
the statements of 0.5.0 and are proved from these; `gainA`, `devB`, `cB`, `s2B`, `GoodB`, `signB`, `signT`,
`signImpl` and `specS` are defined through them and equal those of 0.5.0 (`test/Compat050Defs.lean`), and
`KeyB.Good` is `KeyBP.Good σ512`, with the fields of 0.5.0. Theorem 2 on SamplerZ calls (`Errors.HopB.renyiP`) and
hop B (`Errors.HopB.hopBP`) are stated for every `3 ≤ λ ≤ 512` (the range of `Falcon.CallP.hleaf1023`, which is
stated for `2λ − 1 ≤ 1023`; `Falcon.CallP.hleaf`, for `2λ − 1 ≤ 511`, keeps its 0.5.0 statement), with the Rényi
certificates of `FalconGame.theorem2` as hypotheses. At Falcon-1024 (`σ = 168.388571447`, keys `KeyB1024`, the
stored trees and key bounds of [S8 at Falcon-1024](#s8-at-falcon-1024-tree-depth-10)) the theorems below use
Theorem 2 at `λ = 128` (hop A) and `λ = 131` (hop B) with the certificates of Falcon-512, and at the `λ = 256` level
`λ = 256` (hop A) and `λ = 259` (hop B) with `certs256`, `certs259` (`N = 2⁵¹`, `2⁶⁴` SamplerZ calls,
`S₂ = 2⁻¹⁰`); hop B clamps at `41.5` (Falcon-512: `30.5`).

| Lean | Worlds | Statement | Tree error |
|---|---|---|---|
| `Falcon.falcon1024_exact64n'` | F′ ⇒ X (hop A) | `K ≤ 2²⁹`: `T·2⁻¹²⁶ + 2⁻²⁸⁰ < Pr_F′[s] ⇒ T·2⁻¹²⁸ < Pr_X[s] + 2⁻²⁸⁰` | — |
| `Errors.HopB.falcon1024_hopB` | X ⇒ Y | `K ≤ 2³⁸`: `T·2⁻¹²⁹ + 2⁻²⁸¹ < Pr_X[s] ⇒ T·2⁻¹³¹ < Pr_Y[s] + 2⁻²⁸¹` | any `δ` with `K·s2B1024 41.5 δ ≤ 2⁻⁹` |
| `Errors.HopB.falcon1024_fixed_vs_true` | F′ ⇒ Y (hop A, then hop B) | `K ≤ 2²⁹`: `T·2⁻¹²⁶ + 2⁻²⁸⁰ < Pr_F′[s] ⇒ T·2⁻¹³¹ < Pr_Y[s] + 2⁻²⁸¹` | any `δ` with `K·s2B1024 41.5 δ ≤ 2⁻⁹` |
| `Errors.HopB.falcon1024_fixed_vs_true43` | F′ ⇒ Y | `K ≤ 2²⁹`: as `falcon1024_fixed_vs_true` | assumed (`Close δ43_1024`): `2⁻⁴³` at every node (`2²⁹·s2B1024 41.5 δ43_1024 ≤ 2⁻¹⁰` proved) |
| `Errors.HopB.falcon1024_fixed_vs_true127` | F′ ⇒ Y | `K ≤ 2²⁹`: as `falcon1024_fixed_vs_true` | assumed (`Close δ127_1024`): `2⁻⁵⁸` at the root, `2⁻⁶³` below (`2³⁸·s2B1024 41.5 δ127_1024 ≤ 2⁻¹⁰` proved) |
| `Errors.HopB.falcon1024_exact256'` | F′ ⇒ X (hop A, `λ = 256`) | `K ≤ 2²⁹`: `T·2⁻²⁵⁴ + 2⁻²⁸⁰ < Pr_F′[s] ⇒ T·2⁻²⁵⁶ < Pr_X[s] + 2⁻²⁸⁰` | — |
| `Errors.HopB.falcon1024_hopB259` | X ⇒ Y (`λ′ = 259`) | `K ≤ 2⁵³`: `T·2⁻²⁵⁷ + 2⁻²⁸¹ < Pr_X[s] ⇒ T·2⁻²⁵⁹ < Pr_Y[s] + 2⁻²⁸¹` | any `δ` with `K·s2B1024 41.5 δ ≤ 2⁻¹⁰` |
| `Errors.HopB.falcon1024_fixed_vs_true256` | F′ ⇒ Y (`λ = 256` level) | `K ≤ 2²⁹`: `T·2⁻²⁵⁴ + 2⁻²⁸⁰ < Pr_F′[s] ⇒ T·2⁻²⁵⁹ < Pr_Y[s] + 2⁻²⁸¹` | any `δ` with `K·s2B1024 41.5 δ ≤ 2⁻¹⁰` |
| `Errors.HopB.falcon1024_fixed_vs_true256_43` | F′ ⇒ Y | `K ≤ 2²⁹`: as `falcon1024_fixed_vs_true256` | as `falcon1024_fixed_vs_true43` |
| `Errors.HopB.falcon1024_fixed_vs_true256_127` | F′ ⇒ Y | `K ≤ 2²⁹`: as `falcon1024_fixed_vs_true256` | as `falcon1024_fixed_vs_true127` |

Hop A at Falcon-1024 composes `etvDist_F_F'1024` (`y = 40.9`), Theorem 2 at `λ = 128` (`Falcon.falcon512_proved_n64`,
a statement on SamplerZ calls only: `2048K ≤ 2⁶⁴` calls, the centre budget `2⁻¹⁰` of `centers_budget1024n`) and
`etvDist_E_X1024` (`y = 41`). `K ≤ 2²⁹` is hop A's cap (its centre budget); hop B alone allows `K ≤ 2³⁸`
(`2048K ≤ 2⁴⁹` SamplerZ calls of Theorem 2 at `λ = 131`). The clamp costs are `≤ 2⁻²⁸⁰` per side in hop A and
`≤ 2⁻²⁸¹` in hop B (`eps281`); F′ against Y loses 5 bits, as at Falcon-512. `s2B1024 41.5 δ` is bounded term by term
(`gainA1024_le`, `devB1024_le`, `s2B1024_le`) for a tree error `≤ 2⁻⁴⁰` below the root. For the uniform tree error
`2⁻⁴³` the budget is proved at `K = 2²⁹` (`s2B1024_43`); `2⁻⁴²` does not fit by the values, which are not proved:
about `2⁻⁸·⁴⁵` for `2²⁹·s2B1024 41.5` at a uniform `2⁻⁴²` (above `2⁻⁹`), `2⁻¹⁰·⁴⁵` for `2²⁹·s2B1024 41.5 δ43_1024` and
`2⁻³²·⁸²` for `2³⁸·s2B1024 41.5 δ127_1024`. The first five rows are statements of the type of Falcon-512's (`T·2⁻¹²⁶`
in F′, `T·2⁻¹³¹` in Y); the last five are at the `λ = 256` level (`T·2⁻²⁵⁴` in F′, `T·2⁻²⁵⁹` in Y, 5 bits as at
Falcon-512), with both hops at the centre budget `2⁻¹⁰` (at `2⁻⁹` the exponent of `h36` is `0.3048` at `λ = 256` and
`0.3084` at `λ = 259`, above `1/4`, so `h36` fails for every `N`; values). The composed theorems cover at most `2²⁹`
signing queries (Falcon's `2⁶⁴`; hop B alone `2³⁸` at `λ = 131`, `2⁵³` at `λ = 259`). `Close δ` is a hypothesis here;
the executable track's per-key check `Exec.check1024` is proved to give `KeyBP.Good σ1024 δ` for every key that passes
it (`Exec.check1024_sound`, [below](#arithmetic-and-key-expansion)), and no key is proved to pass it.

`test/ErrorsFalcon1024.lean` checks with `#guard_msgs` that each theorem of this section and the depth-generic
theorems it instantiates depend only on `propext`, `Classical.choice` and `Quot.sound`.

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

- World F: fixed-point signing with any arithmetic `ρ : Arith` meeting the per-operation bounds (complex product `√2·u`,
  halving `√2·u/2`, retag `u/2`, `c/q` at tag 0 within `2⁻⁶⁴`, twiddle tables within `0.7072·2⁻⁶³`). SamplerZ is called
  at the computed centers `t̄`, and signing returns `⊥` when a computed split input `t̄1`, `t̄0'` or odd merge input
  `ẑ1` leaves `‖·‖ ≤ 2²¹ − 1`. A signer is F when its operations form an `Arith`, follow `sign1`'s order of operations
  (`c/q` at tag 0, the FFTs of `c/q`, `F`, `f` by the merge recursion at tags 9, 12, 8, the products at tag 21, then
  `ffs`) with the same result for the same output ulp and operands at every call site, return `⊥` exactly on these
  checks, overflow no other register and obtain the integers `z` exactly. Like every world, F returns `⊥` for `c` with
  some `|cᵢ| ≥ q`; HashToPoint outputs satisfy `|cᵢ| < q`.
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

## Executable track (Falcon-512 and Falcon-1024)

Names are relative to `FalconPrecision`; the modules are `FalconPrecision/Exec/*.lean`, the tests `test/Exec*.lean`.
`Exec.Choices` lists the unpinned points that affect signing: key expansion (`x : XChoices`: the rounding `rm` of
every operation (`floor`, `halfEven`, `halfUp`, `halfAway`), the rounding `rc` of stored constants, `y/x` or `1/x·y`
(`dm`), the root by direct expansion or the NTRU identity (`root`); `xn` extra key-expansion fraction bits), the
target order (scale-first `((−ĉ/q)⊙F̂, (ĉ/q)⊙f̂)` or multiply-first, ePrint 2026/2431 §3.1), the stored `1/q` (77 or
64 fraction bits), the integer budget (`word`: unbounded `Int`, or every operation result reduced to an
`(i + 64)`-bit two's-complement word; 32.64 and 64.64 at `i = 32`, `64`), S8's range checks (`rchk`), salt per
attempt or reused, the restart cap, the norm bounds and the SamplerZ choices. `Exec.signX C samp T k c` is one
signing attempt (ffSampling on the stored tree `T` with SamplerZ `samp`, `⊥` unless `|c i| < q`); `Exec.signMsgX`
is the signer (restart loop, salt, norm check), which outputs `s` (Compress is not modelled).

The track does not model binary64 (floating-point) signers, operation orders other than those of `Choices`, the PRNG or
Falcon-1024 (apart from the encodings, verification, the per-key check `Exec.check1024`, the refinement of S8's model
signer by the attempt `signX` with its hop-B theorems, `Exec.signX_refines1024` and `Exec.falcon1024_exec_vs_true(256)`,
the integer ranges and words of the attempt, `Exec.signX_word1024`, `Exec.sign32_eq_sign64_1024` and
`Exec.leafX_im1024`, and the steps of the executable SamplerZ, `Exec.lawZ_close1024`, `Exec.samplerZ_mgf1024`,
`Exec.samplerZ_tv1024`, `Exec.sampler_hop1024`, `Exec.thresh_sampler1024` and `Exec.thresh_sampler1024_256`, and their
composition with the signer, `Exec.falcon1024_exec_sampler_vs_true(256)` and
`Exec.falcon1024_exec_word_sampler_vs_true(256)`, also on checked keys: the `_checked` versions,
`Exec.sampKey1024Equiv`; and the design-space equivalences and witnesses, `Exec.SignEquiv1024` and
`Exec.SignWitness1024`; and the reference vectors, `Exec.refVec_sound1024`, `Exec.refVec_word1024`,
`Exec.refVec_exact1024` and `Exec.signX_log1024`), and it is not a FIPS 206 implementation (FIPS 206 is unpublished as
of 2026-11-27; the FN-DSA encoding instance is provisional). Facts about concrete keys, KAT entries and inputs are
computed by `#eval` (compiled code run by Lean's interpreter) and are not checked by the kernel; the theorems take them
as `Bool` premises (`check … = true`, `checkRange … = true`, `entryOkB e = true`, `wit*B = true`, `wit*B1024 = true`,
`refVecB … = some V`, `refVecB1024 … = some V`, and `twOk rc = true`, `twOkN rc 10 = true` (directly or as fields of
`Adm C`, `AdmN 10 C`)). [LIMITS.md](LIMITS.md) lists what each part does not prove and every `#eval` fact, with the
command that re-runs it and its recorded output.

### Arithmetic and key expansion

`Exec.Fx f` is an integer `m` read as `m·2⁻ᶠ`, with no word size; fixed point at 64 fraction bits is `Fx 64`.
`e r = 1` for `floor`, `1/2` otherwise. `Exec.check P n δq k` runs key expansion in balls at `64 + n` fraction bits
on the raw key `k`, rounds every stored value once to 64 fraction bits (the centres are the stored tree `storeC`) and
decides: `‖FFT(f)‖∞ ≤ 255`, `‖FFT(F)‖∞ ≤ 3500`, the leaf and `ℓ̂` bounds of `FTree`, every stored `ℓ̂`
conjugate-symmetric, every stored factor ball of radius `≤ δq L`, every leaf ball inside `[1.2778, 1.825]` with
relative radius `≤ 2⁻⁴²`, and `fG − gF = q` in `ℤ[x]/(x⁵¹² + 1)`.

| Lean | Paper / spec | Statement |
|---|---|---|
| `Exec.RMode.rnd_err`, `Exec.Fx.mul_err`, `half_err`, `div_err`, `sqrt_err` | 2026/1531 §3.4 | `\|rnd r y − y\| ≤ e r`; the product, halving, quotient (divisor `≠ 0`) and square root, each rounded once, are within `e r/2ᶠ` of the exact value |
| `Exec.Fx.InRange.wrap` | 2026/1531 §3.4 | a value in `[−2^i, 2^i)` is unchanged by reduction to an `(i + 1 + f)`-bit two's-complement word |
| `Exec.RMode.arith64`, `arith64_mul`, `arith64_halve`, `arith64_divq` | — | for `r ≠ floor`, an `Arith64 (1/2⁷⁸)` (S8's Type 1 arithmetic, `1/q` at 77 fraction bits) whose product, halving and `·1/q` are the executable operations on values at 64 fraction bits |
| `Exec.check_sound` | — | `check P n δq k = true` ⇒ the key `toKeyB` built from `k`, with stored tree `storeC`, passes `KeyB.Good δ` (`δ L = δq L`): the stored tree is real and `Close δ` to the true tree `KeyB.trueTree` |
| `Exec.checkFast_eq` | — | `checkFast P n δq k = check P n δq k` (the array version used for the runs) |
| `Exec.falcon512_fixed_vs_true_checked` | — | `Errors.HopB.falcon512_fixed_vs_true` with `KeyB.Good δ` replaced by `check P n δq k = true` on every raw signing key (and its other hypotheses: `K ≤ 2³⁹` signing-oracle calls along every execution, `K·s2B 30.5 δ ≤ 2⁻⁹`, SamplerZ perfect in every world, auxiliary queries answered identically, `T ≥ 1`, `s` measurable): `T·2⁻¹²⁶ + 2⁻¹⁴⁰ < Pr_F′[s] ⇒ T·2⁻¹³¹ < Pr_Y[s] + 2⁻¹⁴¹` |
| `Exec.s2B_falcon45`, `Exec.falcon512_fixed_vs_true45_checked` | — | `2³⁹·s2B 30.5 δ45 ≤ 2⁻⁹` for `δ45 = 2⁻⁴⁵` at every level; the checked theorem at `δ45q` with that condition proved |
| `Exec.falcon512_fixed_vs_true127_checked` | — | the checked theorem at `δ127q` (`2⁻⁵⁸` at the root, `2⁻⁶³` below) |
| `Exec.check1024_sound` | — | `check1024 P n δq k = true` (`check` at `logn = 10` with the thresholds `256`, `7365`, stored leaves `≥ 1.298280334`, `lam1024`, leaf constant `σ1024`) ⇒ the key `toKeyB1024` built from `k`, with stored tree `storeC`, passes `KeyBP.Good σ1024 δ` (`δ L = δq L`); an instance of `Exec.check_soundP`, the same at every size `2^(L+1)` with the thresholds as parameters |
| `Exec.checkFast_eq1024` | — | `checkFast` at the `check1024` thresholds is `check1024` |
| `Exec.falcon1024_fixed_vs_true_checked`, `Exec.falcon1024_fixed_vs_true256_checked` | — | `Errors.HopB.falcon1024_fixed_vs_true` and `falcon1024_fixed_vs_true256` with `KeyBP.Good σ1024 δ` replaced by `check1024 P n δq k = true` on every raw signing key (their other hypotheses, among them `K ≤ 2²⁹` and `K·s2B1024 41.5 δ ≤ 2⁻⁹`, resp. `2⁻¹⁰`) |
| `Exec.falcon1024_fixed_vs_true43_checked`, `…127_checked`, `…256_43_checked`, `…256_127_checked` | — | the checked theorems at `δ43q_1024` and `δ127q_1024`, with the budget proved |

By `#eval`, with `rm = rc` ties to even or ties up, `dm = direct`, `root = plain`: `checkFast` at `δ45q` with
`xn = 0` (fixed point at 64 fraction bits) is `true` for 92 of the 100 round-3 Falcon-512 KAT keys, the other 8
failing only `‖FFT(f)‖∞ ≤ 255`; at `δ127q` it is `true` for none at `xn = 0` and `xn = 16`, and for the same 92 at
`xn = 32`.

At Falcon-1024, with the same choices, `checkFast` at the `check1024` thresholds is `true` for 77 of the 100 round-3
Falcon-1024 KAT keys at `δ43q_1024` with `xn = 0` and at `δ127q_1024` with `xn = 32`; of the other 23, 22 fail only
`‖FFT(f)‖∞ ≤ 256` and key 60 only the stored-tree bounds (`okB`).

### Signer

`Exec.Adm C`: `rm ≠ floor`, `twOk rc` (the computed twiddle tables within `0.7072·2⁻⁶⁴`, decided), the scale-first
target, unbounded words, and range checks, if any, at `R ≥ 1`; every other field is free. `Exec.AdmN N C` is the same
with the tables decided at levels `< N` (`twOkN rc N`); `Adm C` gives `AdmN 9 C` (`Exec.Adm.toN`).
`Exec.arithXN N C h` takes the executable tables at levels `< N` and the exact `ζ`, `ζ̄/2` at levels `≥ N`;
`arithX C h = arithXN 9 C h.toN`. Falcon-1024 (depth 10) uses `N = 10`. `Exec.checkRange C i W k` is a computable
bound on every operation result of the attempt on `k` at budget `i`, for sampler answers within `W` of `⌊t̄⌋`. At
Falcon-1024 it is `checkRange C i W k σ1024q` (tables `twOkN rc 10`, stored tree `storeC … σ1024q`).

| Lean | Paper / spec | Statement |
|---|---|---|
| `Exec.signX_refines` | — | `Adm C`, `check C.x C.xn δq k = true`, a lawful monad, a world `impl` whose SamplerZ answer on `(σ̄, t̄)` is `samp σ̄ t̄`, every `c`: `simulateQ impl (sign164G (arithX C h) (chkOf C.rchk) (toKeyB … k hk).toKey c) = signX C samp (storeC C.x C.xn k) k c` |
| `Exec.falcon512_exec_vs_true` | — | `falcon512_fixed_vs_true_checked` with F′ replaced by the executable signer's world (`execImpl`), for `Adm C`, `C.rchk = none`, `1/q` at 77 fraction bits, and a sampler `samp` agreeing on grid values with a world distributed as `D_{σ̄,t̄}`; same hypotheses and thresholds |
| `Exec.signX_refines1024` | — | `AdmN 10 C`, `check1024 C.x C.xn δq k = true`, a lawful monad, a world `impl` whose SamplerZ answer on `(σ̄, t̄)` is `samp σ̄ t̄`, every `c`: `simulateQ impl (sign164G (arithXN 10 C h) (chkOf C.rchk) (toKeyB1024 … k hk).toKey c) = signX C samp (storeC C.x C.xn k σ1024q) k c`; an instance of `Exec.signX_refinesP` (every size `2^(L+1)`, tables cut at `L + 1`) |
| `Exec.falcon1024_exec_vs_true`, `Exec.falcon1024_exec_vs_true256` | — | `falcon1024_fixed_vs_true_checked`, `falcon1024_fixed_vs_true256_checked` with F′ replaced by the executable signer's world (`execImpl1024`), for `AdmN 10 C`, `C.rchk = none`, `1/q` at 77 fraction bits, and a sampler `samp` agreeing on grid values with a world distributed as `D_{σ̄,t̄}`; same hypotheses and thresholds |
| `Exec.falcon1024_exec_vs_true43`, `…127`, `…256_43`, `…256_127` | — | the same at `δ43q_1024` and `δ127q_1024`, with the budget proved |
| `Exec.signX_word` | 2026/1531 §3.4 | `1 ≤ i ≤ 64`, `check`, `checkRange C i W k = true`, sampler answers clamped to `⌊t̄⌋ ± W`, a lawful monad: the attempt on `(i + 64)`-bit words equals the attempt on unbounded `Int` |
| `Exec.sign32_eq_sign64` | — | `check`, `checkRange C i W k` at `i = 32` and `i = 64`, a lawful monad, sampler answers clamped to `⌊t̄⌋ ± W`: the 32.64 and 64.64 attempts are bit-identical |
| `Exec.leafX_im` | — | `i ≤ 64`, `check`, `checkRange C i W k`, `\|c j\| < q`, sampler answers within `W` of `⌊t̄⌋`: every leaf centre of the unbounded attempt has `\|Im t̄\| ≤ imE i` (`2^(i−1)·2⁻³²` for `i ≥ 1`, `2⁻³²` at `i = 0`) |
| `Exec.signX_word1024` | 2026/1531 §3.4 | `27 ≤ i ≤ 64`, `check1024`, `checkRange C i W k σ1024q = true`, sampler answers clamped to `⌊t̄⌋ ± W`, a lawful monad: the attempt on `(i + 64)`-bit words equals the attempt on unbounded `Int` (`k : RawKey 10`, stored tree `storeC … σ1024q`) |
| `Exec.sign32_eq_sign64_1024` | — | `check1024`, `checkRange C i W k σ1024q` at `i = 32` and `i = 64`, a lawful monad, sampler answers clamped to `⌊t̄⌋ ± W`: the 32.64 and 64.64 attempts at Falcon-1024 are bit-identical |
| `Exec.leafX_im1024` | — | `27 ≤ i ≤ 64`, `check1024`, `checkRange C i W k σ1024q`, `\|c j\| < q`, sampler answers within `W` of `⌊t̄⌋`: every leaf centre of the unbounded attempt has `\|Im t̄\| ≤ imE i` |
| `Exec.pathSum_signLoopX` | spec Alg. 10 l. 4-11 | a restart loop with cap `N` on a checked key, whose salt and hash make no signing-oracle call, makes at most `N` signing-oracle calls along every execution |

By `#eval`: `twOk` and `twOkN rc 10` (as `twOkFastN`, the ten table levels of Falcon-1024) are each `true` for
`halfEven`, `halfUp` and `halfAway` and `false` for `floor`; KAT entry 0 passes `checkFast` at `δ45q` and `checkRange`
at `i = 32` and `i = 64` with `W = 19` (ties to even, `xn = 0`, scale-first). At Falcon-1024 (ties to even, `xn = 0`,
`W = 19`) `checkRangeA … σ1024q` is `true` for all 100 round-3 KAT keys at scale-first `i = 32` and `i = 64` and at
multiply-first `i = 64`, and `false` for all 100 at multiply-first `i = 32`, where its bound does not fit
([LIMITS.md](LIMITS.md), E25).

### SamplerZ

`Exec.samplerZ P S ub σ̄ t̄` is SamplerZ (spec Alg. 12-15) on uniform bits `ub`. `S.base` selects the 72-bit table of
spec Table 3.1 or a 79-bit table `tab79` built by the rule that reproduces Table 3.1 (NIST's 79-bit table is
unpublished); `S.shiftRej` rejects a candidate whose shift is `≥ 64` (ePrint 2026/2902 Alg. 9) or saturates the shift
at 63 (spec). `x`, `ccs` and `r` are exact in `ℚ`; the loop stops after 128 rejections with output `⌊t̄⌋`.
`falcon512S` has `σmin = 1.277833697`, `σmax = 1.8205`; `falcon1024S` has `σmin = 1.298280334` (spec Table 3.3) and is
otherwise `falcon512S` (`sampS c` is `falcon512S` with `σmin := c`).

| Lean | Paper / spec | Statement |
|---|---|---|
| `Exec.samplerZ_law` | spec Alg. 12-15 | for a table passing `okB` and uniform bits (`UnifBits ub`), the output law of `samplerZ P S ub σ̄ t̄` is the computable `lawZ P S σ̄ t̄` |
| `Exec.lawZ_close` | — | with shift rejection, either table, every `σ̄ ∈ [σmin, σmax]` and every `t̄`: `lawZ ≤ (1 + 2⁻⁴⁰)·D_{σ̄,t̄}` pointwise and `χ²(lawZ ‖ D_{σ̄,t̄}) ≤ 2⁻⁷⁶` |
| `Exec.samplerZ_mgf` | — | for `a ≥ 2`, uniform bits (`UnifBits ub`) and `σ̄ ∈ [σmin, σmax]`: the Rényi MGF of order `a` of SamplerZ with shift rejection against `D_{σ̄,t̄}` is `≤ exp((a − 1)·εZ a)`, `εZ a = a/2·(1 + 2⁻⁴⁰)^(a−2)·2⁻⁷⁶` |
| `Exec.samplerZ_tv` | 2026/2902 Alg. 9 | for uniform bits (`UnifBits ub`) and `σ̄ ∈ [σmin, σmax]`, saturating instead of rejecting moves at most `2⁻¹¹⁰` per call in total variation |
| `Exec.lawZ_closeP`, `samplerZ_mgfP`, `samplerZ_tvP` | — | the three statements above for `sampS c`, every `c ∈ [1.277833697, 1.3]` (`SminOk c`) and `σ̄ ∈ [c, σmax]`; the Falcon-512 theorems are their instances |
| `Exec.lawZ_close1024`, `samplerZ_mgf1024`, `samplerZ_tv1024` | spec Table 3.3 | the same at Falcon-1024 (`falcon1024S`, `σ̄ ∈ [1.298280334, 1.8205]`) |
| `Exec.sampler_hop1024` | — | along executions with at most `N` SamplerZ calls on the oracle `specZP falcon1024S` (`σ̄` in `falcon1024S`'s range), SamplerZ with shift rejection against an ideal sampler: `Pr[s]^(a/(a−1))/exp(N·εZ a) ≤ Pr_ideal[s]` (`sampler_hopP` for `sampS c`) |
| `Exec.thresh_sampler1024`, `thresh_sampler1024_256` | — | with `R_{2¹⁴} ≤ exp(2048K·εZ)` along executions, `K ≤ 2²⁹`: success `> 2^(1/64)·θ` before the hop gives success `> θ` after it, `θ = T·2⁻¹²⁶ + 2⁻²⁸⁰` resp. `T·2⁻²⁵⁴ + 2⁻²⁸⁰` (`thresh_samplerE`: every `θ ≥ 2⁻ᵉ`, `e < 256`, `N ≤ 2⁴⁶·(256 − e)` calls) |
| `Exec.falcon512_exec_sampler_vs_true` | — | `falcon512_exec_vs_true` with the executable signer running `samplerZ falcon512S C.samp ub`, on keys whose stored leaves lie in `[σmin, σmax]` (`SampKey`; every key passing `check` is one, `sampKeyEquiv`; `Exec.falcon512_exec_sampler_vs_true_checked` is the statement on checked keys), for every SamplerZ choice (`C.samp`; the signer uses the plain centre, `C.samp.centre` is not read), on uniform bits `ub` (`UnifBits`): `2^(1/64)·(T·2⁻¹²⁶ + 2⁻¹⁴⁰) + ε < Pr_exec[s] ⇒ T·2⁻¹³¹ < Pr_Y[s] + 2⁻¹⁴¹`, `ε = 0` with shift rejection and `2⁻⁶¹` with saturated shifts; the perfect-sampler hypotheses remain only on ideal worlds |
| `Exec.exec_sampler_worlds_exist` | — | those ideal-world hypotheses and `UnifBits` hold together in one monad |
| `Exec.falcon1024_exec_sampler_vs_true`, `falcon1024_exec_sampler_vs_true256` | — | `falcon1024_exec_vs_true`, `falcon1024_exec_vs_true256` with the executable signer running `samplerZ falcon1024S C.samp ub`, on keys passing `check1024` (`SampKey1024`, whose leaf range `[1.298280334, 1.8205]` is derived from `check1024`, `sampKey1024Equiv`; the `_checked` versions state it on checked keys), `AdmN 10 C`, `K ≤ 2²⁹`, `K·s2B1024 41.5 δ ≤ 2⁻⁹` resp. `2⁻¹⁰`, for every SamplerZ choice (`C.samp`; `C.samp.centre` is not read), on uniform bits `ub` (`UnifBits`): `2^(1/64)·(T·2⁻¹²⁶ + 2⁻²⁸⁰) + ε < Pr_exec[s] ⇒ T·2⁻¹³¹ < Pr_Y[s] + 2⁻²⁸¹` resp. `2^(1/64)·(T·2⁻²⁵⁴ + 2⁻²⁸⁰) + ε < Pr_exec[s] ⇒ T·2⁻²⁵⁹ < Pr_Y[s] + 2⁻²⁸¹`, `ε = 0` with shift rejection and `2⁻⁷⁰` with saturated shifts (the λ = 256 statement is meaningful only with shift rejection); the perfect-sampler hypotheses remain only on ideal worlds |
| `Exec.falcon1024_exec_sampler_vs_true43`, `…127`, `…256_43`, `…256_127` | — | the same at `δ43q_1024` and `δ127q_1024`, with the budget proved |
| `Exec.sampKeyEquiv`, `sampKey1024Equiv`, `falcon512_exec_sampler_vs_true_checked`, `falcon1024_exec_sampler_vs_true(256)_checked`, `…(43, 127)_checked`, `…256(_43, _127)_checked` | — | keys passing `check` resp. `check1024` are `SampKey`s resp. `SampKey1024`s (`CTree.leavesB_of_okB`: the leaf test of `okB` is SamplerZ's range test); the composed theorems on experiments over checked keys (`specK`, `specK1024`), other hypotheses and constants unchanged; the word theorems likewise (`falcon512_exec_word_sampler_vs_true_checked`, `falcon1024_exec_word_sampler_vs_true(256)_checked`, keys passing the check and `checkRange`) |
| `Exec.exec_sampler_worlds_exist1024` | — | those ideal-world hypotheses (`hI` on `falcon1024S`'s range) and `UnifBits` hold together in one monad |

The sampler step is a Rényi step of order `2¹⁴` over the `1024K ≤ 2⁴⁹` SamplerZ calls. With saturated shifts (the
spec's own SamplerZ) the additive `2⁻⁶¹` makes the statement empty for success `≤ 2⁻⁶¹` and is most of the threshold
for `T ≤ 2⁶⁴`. By `#eval`: the 16 SamplerZ test vectors of spec Table 3.2 (output and bytes used), with the 72-bit
table, saturated and with shift rejection. At Falcon-1024, by `#eval`: `samplerZ falcon1024S` gives the accepted `z`
of all 2048 SamplerZ calls of one round-3 Falcon-1024 signature trace with every byte used, saturated and with shift
rejection (no call reaches a shift `≥ 64`) ([LIMITS.md](LIMITS.md), E26). There the sampler step over `2048K ≤ 2⁴⁰`
calls keeps the factor `2^(1/64)` at both thresholds (`thresh_sampler1024`, `thresh_sampler1024_256`), and
`Exec.falcon1024_exec_sampler_vs_true(256)` compose it with the signer. With saturated shifts the additive `2⁻⁷⁰`
makes them empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2⁵⁵` (128-bit type) and `T ≤ 2¹⁸³` (λ =
256 level); the λ = 256 statement is meaningful only with shift rejection.

### Design-space pairs

For pairs of `Choices`: equality on every input under stated conditions, or an input on which the two differ. Witness
inputs are round-3 KAT entries 0 and 70 of `falcon512-KAT.rsp` and entries 0 and 2 of `falcon1024-KAT.rsp` (and the hash
of its entry 70 as the second hash of `wit_salt1024`, `wit_cap1024`) with scripted SamplerZ draws (call `j` reads a
script, then fixed draws); the theorems `wit_*` are proved implications `wit*B = true → the outputs differ`, and each
`wit*B` (`wit*B1024`) is `true` by `#eval`.

| Lean | Paper / spec | Statement |
|---|---|---|
| `Exec.signMsgX_32_64` | 2026/1531 §3.4 | `check`, `checkRange` at `i = 32` and `i = 64`, every sampler clamped to `⌊t̄⌋ ± W`: the signers whose attempts run on 96-bit and 128-bit words give the same output on every message, salt source and hash |
| `Exec.signMsgZ_32_64` | — | the same with the executable SamplerZ (`W = 19`), unclamped, on every random-bit source |
| `Exec.signMsgX_32_64_1024`, `Exec.signMsgZ_32_64_1024` | 2026/1531 §3.4 | `signMsgX_32_64` and `signMsgZ_32_64` at Falcon-1024 (SamplerZ at `falcon1024S`), on keys passing `check1024` and `checkRange · σ1024q` at `i = 32` and `i = 64` |
| `Exec.falcon512_exec_word_sampler_vs_true` | — | `falcon512_exec_sampler_vs_true` for the signer whose attempts run on `(i + 64)`-bit words, `1 ≤ i ≤ 64`, on keys passing `checkRange C i 19`; same hypotheses and constants; on keys passing `check` and `checkRange C i 19` (`CheckedRKey`, `rKeyEquiv`): `Exec.falcon512_exec_word_sampler_vs_true_checked` |
| `Exec.falcon1024_exec_word_sampler_vs_true`, `…_vs_true256` | — | `falcon1024_exec_sampler_vs_true(256)` for the signer whose attempts run on `(i + 64)`-bit words, `27 ≤ i ≤ 64`, on keys passing `checkRange C i 19 · σ1024q`; same hypotheses and constants; on keys passing `check1024` and `checkRange C i 19 · σ1024q` (`CheckedRKey1024`, `rKey1024Equiv`): `Exec.falcon1024_exec_word_sampler_vs_true(256)_checked` |
| `Exec.signX_rc`, `Exec.signMsgX_rc` | — | two roundings of stored constants whose tables (and, for the signer, stored `σ`) agree give the same attempt, resp. signer output, on every input |
| `Exec.signMsgX_store` | 2026/2902 (iii), (iv) | choices that differ only in key expansion (`dm`, `root`, `xn`) give the same signer output on a key whose stored trees are equal |
| `Exec.signLoopX_one`, `Exec.signMsgX_cap_add` | spec Alg. 10 | with cap 1, salt per attempt and reused salt are equal; with a fresh salt per attempt, cap `N + j` is cap `N` followed, on failure, by cap `j` |
| `Exec.signX_rc1024`, `Exec.signMsgX_rc1024`, `Exec.signMsgX_store1024`, `Exec.signMsgX_cap_add1024` | 2026/2902 (iii), (iv); spec Alg. 10 | the stored-constant, key-expansion and cap statements at Falcon-1024 (tables at levels `≤ 9`, `σ1024q`); `signLoopX_oneP` holds at every size |
| `Exec.Witness.wit_target`, `wit_dm`, `wit_root`, `wit_rm_up`, `wit_rm_away`, `wit_rm_floor`, `wit_rc_floor`, `wit_qinv`, `wit_word_mf`, and `wit_*_sig` | 2026/2431 §3.1, §3.4; 2026/2902 (iii), (iv); 2026/1531 p. 15 | the attempts (`_sig`: the signers) differ: scale-first / multiply-first; `y/x` / `1/x·y` and plain / NTRU root at `xn = 0`; ties to even / ties up, ties up / ties away, ties to even / floor; stored constants ties to even / floor; `1/q` at 77 / 64 bits; multiply-first 32.64 / 64.64 (entry 70: `wit_word_mf_none`, no signature at 32.64, a signature at 64.64) |
| `Exec.Witness.wit_centre`, `wit_salt`, `wit_cap` | 2026/2902; spec Alg. 10 | plain / fractional centre (attempts); reused salt / salt per attempt after one rejection (stand-in hashes); cap 1 / cap 27 |
| `Exec.Witness.samp_base`, `samp_shift` | spec Table 3.1; 2026/2902 Alg. 9 | one SamplerZ call differs between the 72-bit table and `tab79` (with our 79-bit draw), and between saturated and rejected shifts; kernel-checked |
| `Exec.Witness.wit_*1024`, `wit_*_sig1024`, `samp_base1024`, `samp_shift1024` | as for Falcon-512 | the same 12 pairs (attempt witnesses for all 12, signer witnesses for 9) and the two sampler pairs at Falcon-1024 (`falcon1024S`, `σ1024q`); multiply-first 32.64 / 64.64 on entry 2 (`wit_word_mf1024`, `wit_word_mf_none1024`), the others on entry 0 |

### Encodings, HashToPoint and verification

`Exec.Codec.EncChoices` and `VerChoices` carry the bit order, headers, the public key in coefficient or NTT form,
field widths, a public-key hash in the secret key, the salt length, compressed or 12-bit signatures, padding, a
coefficient bound, BUFF hashing, raw, pure or prehash messages, `⌊β²⌋` and an optional ∞-norm bound. `round3` and
`round3V` are the round-3 (v1.2) instance at Falcon-512, `round3_1024` and `round3V1024` at Falcon-1024 (headers
`0x0A`, `0x5A`, `0x3A`, `f`, `g` over 5 bits, `sbytelen = 1280`, `⌊β²⌋ = 70265242`; spec §3.11, Table 3.3);
`fndsaProv`, `fndsaProvV` and `fndsaProv1024`, `fndsaProvV1024` are a provisional reading of NIST's FIPS 206 status
talk (Perlner, 2025), with placeholders for unpinned fields. Verification and the NTT form are at degree
`n = 2^logn` of the encoding choices. The round-3 decoders `Exec.Round3.decodePk`, `decodeSk` take `logn` and
return `none` unless `1 ≤ logn ≤ 10` (the spec's range).

| Lean | Paper / spec | Statement |
|---|---|---|
| `Exec.Codec.decodePk_encodePk`, `decodeSk_encodeSk`, `decodeSig_encodeSig`, `decodeSm_encodeSm`, `encodePk_of_decodePk`, `encodeSk_of_decodeSk`, `encodeSig_of_decodeSig`, `encodeSm_of_decodeSm` | spec §3.11 | for every `EncChoices`: decoding an encoding returns the encoded value (under each theorem's well-formedness hypothesis), and a byte string that decodes is the encoding of its result |
| `Exec.Codec.decompress_compress`, `compress_of_decompress` | spec §3.11.2, Alg. 17-18 | Decompress inverts Compress, for every coefficient bound; a string that decompresses to `s` is `Compress(s, slen)` |
| `Exec.Codec.decodePk_round3`, `decodeSk_round3` | — | at `round3` the decoders agree with `Exec.Round3.decodePk`, `decodeSk` |
| `Exec.Codec.decodePk_round3_1024`, `decodeSk_round3_1024` | — | at `round3_1024` the decoders agree with `Exec.Round3.decodePk`, `decodeSk` at `logn = 10` |
| `Exec.Codec.hashToPoint_spec` | spec Alg. 3 | `hashToPoint n str = some c` ⇒ `c` is the output of Alg. 3 l. 4-9 on every long enough prefix of the SHAKE-256 stream of `str` (VCVio's `shake256`) |
| `Exec.Codec.verifyCore_iffP` | spec Alg. 16 l. 5-9 | at every `logn`: acceptance iff some `s₁ ≡ c − s₂h (mod q)` in `ℤ[x]/(x^(2^logn) + 1)` with `\|s₁ᵢ\| ≤ ⌊q/2⌋` has `‖(s₁, s₂)‖² ≤ ⌊β²⌋` and passes the ∞-norm check |
| `Exec.Codec.verifyCore_iff` | spec Alg. 16 l. 5-9 | at `logn = 9` (the default of `verifyCore`): acceptance iff some `s₁ ≡ c − s₂h (mod q)` in `ℤ[x]/(x⁵¹² + 1)` with `\|s₁ᵢ\| ≤ ⌊q/2⌋` has `‖(s₁, s₂)‖² ≤ ⌊β²⌋` and passes the ∞-norm check |
| `Exec.Codec.verifyCoreChecked_iff`, `verifyCoreChecked_eq`, `verifyCoreChecked_spec` | spec Alg. 16 l. 5-9 | at every `logn`: `verifyCoreChecked` accepts iff `h`, `c` and `s₂` have exactly `2^logn` coefficients and `verifyCore` accepts (so iff the lengths are exact and the condition of `verifyCore_iffP` holds); on such inputs it equals `verifyCore`, which reads missing coefficients as `0` and ignores extra ones |
| `Exec.Codec.entryOk_of`, `entriesOk_of` | — | `entryOkB e = true` ⇒ `EntryOk e`: at `round3`, `pk`, `sk` and `sm` decode and re-encode byte for byte, the decoders agree with `Round3`, `sm` carries `msg`, a linear checksum (mod `2⁶¹ − 1`) of the hashed point equals a value computed outside Lean, the detached signature verifies, `openSm` accepts `sm` and rejects it with one bit flipped in the salt, in the message, or in the first byte of the compressed `s₂` |
| `Exec.Codec.entryOkP_of`, `entriesOkP_of`, `entryOkB_eq` | — | the same checks at any `VerChoices` `V` (`EntryOkP V`, decided by `entryOkBP V`; the message is flipped at its first byte); `entryOkB` is `entryOkBP round3V` |
| `Exec.Codec.entryOkU_of` | spec §3.11.3, Alg. 17 l. 7-8 | `entryOkBU V e = true` ⇒ `EntryOkP V.unpadded e` (detached signatures unpadded) and `NoSigEnc V e`: the salt and `s₂` of `sm` have no detached encoding at `V` |

By `#eval`: `entryOkB` is `true` for all 100 entries of the round-3 `falcon512-KAT.rsp` (sha256
`dd75c946…7354b5cd`), so the 300 one-bit mutations are rejected; HashToPoint equals the Python value in full for
entries 0 and 70 (for the others a linear checksum of it is compared). For the 100 entries of the round-3
`falcon1024-KAT.rsp` (sha256 `036a0bf5…8acb20d`), `entryOkBP round3V1024` is `true` for the 99 entries other than
82, and `entryOkBU round3V1024` for entry 82, whose compressed `s₂` (9914 bits) does not fit a 1280-byte signature
(9912 bits after header and salt; its detached signature is checked unpadded); so for all 100 the keys and `sm`
re-encode byte for byte, `openSm` accepts, and the 300 one-bit mutations are rejected. HashToPoint (`n = 1024`)
equals the Python value in full for entries 0 and 70.

### Reference vectors

`Exec.refVecB δq k c z0 z1` is a ball trace of one signing attempt on the key `k` and hashed point `c`, conditioned
on the SamplerZ outputs `(z0, z1)`: a complex disc (centre at 64 fraction bits, radius on the grid `2⁻⁹⁶`) for the
FFTs of `c`, `f`, `F`, the target (hull of both target orders), and every node and leaf value of ffSampling.
For a KAT entry, `(z0, z1)` is the unique `z` with `s = (c, 0) − z·B` for the entry's signature.

| Lean | Paper / spec | Statement |
|---|---|---|
| `Exec.refVec_sound` | — | `C.word = none`, `twOk C.x.rc`, `check C.x C.xn δq k = true`, `refVecB δq k c z0 z1 = some V`: every intermediate of the attempt at `C` (`traceX`) lies in its ball |
| `Exec.refVec_word` | — | the same at `(i + 64)`-bit words, `1 ≤ i`, when `V.magOkB C.target i` |
| `Exec.refVec_exact` | — | `0 ≤ δq L` for every `L`: the exact attempt (exact FFT, true tree `k.trueTree`, exact operations) lies in the same balls |
| `Exec.refVec_adm` | — | `refVec_sound` at every `C` with `Adm C` |
| `Exec.signX_log` | — | `C.rchk = none`, `\|c i\| < q`, a sampler answering by the tape of `(z0, z1)`: `signX` returns `(z0, z1)` and the SamplerZ queries it makes are the trace's leaf values |
| `Exec.katIn_spec` | — | `katIn e = some (k, c, s1, s2, z0, z1)` ⇒ `k` is the decoded `sk`, `c` the Lean HashToPoint of `sm`'s salt and message, `s1 = s1Of c s2 h`, and `sOf k c z0 z1 = (s1, s2)` |
| `Exec.refVec_sound1024`, `Exec.refVec_word1024`, `Exec.refVec_exact1024`, `Exec.refVec_adm1024` | — | the same at Falcon-1024 (`refVecB1024`, `traceX1024` on `storeC … σ1024q`, `traceE1024` on the true tree at `σ1024`), with `twOkN C.x.rc 10`, `check1024 C.x C.xn δq k`, `magOkBP` (resp. `AdmN 10 C`) |
| `Exec.signX_log1024`, `Exec.katIn1024_spec` | — | `signX_log` and `katIn_spec` at Falcon-1024 (`round3_1024`, `hashToPoint 1024`, `decodeKey · 10`) |
| `Exec.refVecBT_sound`, `Exec.refVecBT_word`, `Exec.refVecBT_exact`, `Exec.signX_logP` | — | the statements at every size `2^N`, on a ball tree given as a parameter that holds the stored tree (resp. the true tree) at its centres; the Falcon-512 and Falcon-1024 theorems are their instances |

By `#eval` (`Exec.genVecAt`; the JSON printer is not proved): vectors for KAT entries 0 and 70 at `δ45q` and at `δ127q`,
and for entry 27 at `δ45q` as a control (it fails `check` at every evaluated point, so `refVec_sound` does not apply to
it there). At Falcon-1024 (`Exec.genVecAt1024`): vectors for entries 0 and 2 of `falcon1024-KAT.rsp` at `δ43q_1024` and
at `δ127q_1024`, and for entry 11 at both as a control (it fails `check1024` at every evaluated point, so
`refVec_sound1024` does not apply to it there).

Which test vectors fixed-point implementations of Falcon should be checked against has been raised in public:
the CRYPTO 2026 talk "Toward a fixed-point implementation of the Falcon signature scheme" by De Almeida Braga,
Fouque, Lachguel and Prest asks, on its slide "KAT conformance", "Alternative set of KATs for fixed-point Falcon ?",
and the NIST pqc-forum thread "Fixed-point FN-DSA and special vs general purpose" (August 2026) discusses test
vectors (CAVP) generated from a fixed-point implementation.

## Related work

- Tian, Dong, Zhang, Wang, "Formal Verification Techniques for Implementing Post-quantum Cryptography Falcon"
  (in Chinese), Journal of Software 36(11):4990-5007, 2025: a Jasmin implementation of Falcon-512 signing and
  verification; EasyCrypt proofs of Montgomery multiplication and the NTT and of the values of the FFT root table;
  a proof of integer Gaussian sampling outlined, not completed.
- Vincent Hwang, "Formal Verification of Emulated Floating-Point Arithmetic in Falcon", IACR ePrint 2024/321, 2024:
  a CryptoLine model of the emulated floating-point addition, subtraction and multiplication of the Falcon
  submission package; shows that a discrepancy in the multiplication does not affect the complex FFT in signature
  generation; the author's Armv7-M and Jasmin floating-point multiplications proved equivalent to the model.
- Hannes Hacker, Shekoufeh Neisarian, Sara Zain, Elif Bilge Kavun, "PQMZ: Formally Verified Falcon-PKR for
  Post-Quantum Cryptographic Migration in Zcash", IACR ePrint 2026/2260, 2026: a machine-checked EasyCrypt
  formalisation of Falcon-PKR in the random oracle model, and machine-checked correctness of honest signing under an
  abstract Falcon signing interface.
- Bas Spitters, "CatCrypt: From Rust to Cryptographic Security in Lean", IACR ePrint 2026/604, 2026: a Lean library
  of security proofs in the computational model; lists FN-DSA (FIPS 206) among its constructions.
- Vincent Hwang, "Bounds of Falcon's Fast Fourier Sampler with Fixed-Point Arithmetic (Draft v0.1)", IACR ePrint
  2026/2902, 2026: bounds the Rényi divergence between the fast Fourier sampler in real arithmetic and a fixed-point
  implementation on the tail-cut event; reports 126.28 bits at `n = 512` (λ = 128) and 248.78 bits at `n = 1024`
  (λ = 256) over `2⁶⁴` signatures at the plain centre, with the SamplerZ shift rejection and key-generation checks
  it proposes, for every key that key generation accepts, under three code-alignment hypotheses and the summability
  hypotheses of its Lean theorems.
- Merve Karabulut, Panasayya Yalla, Reza Azarderakhsh, Mehran Mozaffari Kermani, "From Decoding Leakage to Full Key
  Recovery: A Single-Trace Attack on FALCON", IACR ePrint 2026/2908, 2026: a profiled template attack on the
  secret-key decoding at the start of signing; on an ARM Cortex-M4 running Falcon-1024 it recovers the secret key
  from one power trace for all 1000 keys tested.

## Assumptions and limits

This section covers releases 0.2.0-0.4.0 and the S8 results at Falcon-1024; the limits of the executable track are
in [LIMITS.md](LIMITS.md).

- The sampler is perfect: SamplerZ returns exact discrete Gaussians, as assumed by the paper's theorems.
- Everything other than SamplerZ's parameters is assumed identical in the three worlds: signature assembly, norm
  test, compression, restart decision and key-generation rejection. For a fixed-point signer this is an
  implementation obligation (integer recomputation, or fixed-point error small enough to round to the exact result),
  in addition to the leaf and center bounds. The paper makes the same assumption implicitly.
- The error bounds on leaves and centers (or their sums along executions) are hypotheses of `theorem1`, `theorem2`,
  `falcon512`, `falcon1024`, `falcon512_rmse` and `falcon512_proved`, as in the paper; proving them for a fixed-point
  implementation is the paper's stated open problem. S7, S8 and hop B prove the call count and the center sum for
  their signing models only, within the limits below.
- `oa` is a finite term: signing restarts are capped, and the hypotheses range over every history, so out-of-range
  samples must abort or clamp identically in the three worlds. Relating this experiment to uncapped Falcon is not
  formalised (the paper's `c` and "for any history" leave the same gap).
- The center sum in `falcon512_rmse` is a hypothesis on every execution; the paper's RMSE is a sample average.
- Outputs of the experiment and the answers of every auxiliary oracle range over countable types.

### S7

- Abort gap at tag 21: `Pr_E[abort]` is not bounded at the `2²¹` range of S7. For exact stored-tree signing X without
  aborts, `Pr_X[s] ≥ Pr_E[s] − Pr_E[abort]` (a coupling argument, not formalised for S7); the tree-only bound of S8
  (route B′) is vacuous at `2²¹`, so against abort-free exact signing the 128-bit statement does not follow for the S7
  model. S8 bounds it for the Type 1 model at `R64 = 2²⁴`.
- Hop B (stored tree to true tree: center shift `(t1 − z1)(ℓ̂ − ℓ)`, leaves `σ̄ → σ`) starts from abort-free exact
  signing on the stored tree (X); the S7 model is not related to X (abort gap above), so S7 states nothing relative
  to exact Falcon.
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
  in ePrint 2026/2431); S7 does not model that chain (S8 models one Type 1 chain, below).
- Falcon-1024 is not covered by S7.

### S8

- The model is the non-split scale-first Type 1 chain of ePrint 2026/2431 §3.1, which §5 suggests pinning; it is not a
  chain specified by NIST. The multiply-first order `−(ĉ⊙F̂)/q` of the reference code, c-fn-dsa and the 64.64 C
  prototype fixed-point-c ([DAB26] in 2026/2431) and the split (`t_frac`) path are not modelled.
- No implementation (2026/2431's fxp32.64 signer, fixed-point-c [DAB26]) is shown to meet `sign164`'s operation
  sequence. The model computes every FFT slot; 2026/2431 works over the `n/2` slots with the conjugates implied, which
  agrees with the model only under conjugation-symmetric rounding, and its recommended ties-up rounding is not.
  c-fn-dsa signs in binary64 and is not a Type 1 arithmetic.
- The range checks of F are the model's; deployed signers run none. `falcon512_exact64(n)'` covers fixed-point
  signing without them (F′) under the same model.
- `FTreeP.Real` (every stored `ℓ̂` the FFT of a real polynomial) is a hypothesis: it holds by construction with
  half-spectrum storage or sign-symmetric rounding; full-spectrum storage rounded ties-up can violate it at ties.
  The `ℓ̂` bounds of `FTree` remain checks added by the model.
- Keys (modified NTRUGen, `Key`'s bounds up to keygen's rounding), the perfect sampler, the stored tree (its
  computation is not modelled; only the hypothesis `Close δ` of hop B ties it to the key), recovering `z` from the
  computed FFT form (not modelled), the norm check and restarts (integer code on `z` in `oa`), the absence of a
  UF-CMA game and of overflow modelling are as in S7. In 32.64 the checked values fit the integer bits on paper; the
  unchecked even merge inputs, merge sums and the line-10 operand are not covered.
- `falcon512_exact64(n)'` (through `etvDist_F_F'`) assume every auxiliary answer type is inhabited (`Nonempty`).
- Falcon-1024: the per-call and per-experiment centre budgets, the clamp lemma, the two total-variation bounds
  ([above](#s8-at-falcon-1024-tree-depth-10)) and hop A at `λ = 128` (`falcon1024_exact64n'`) and at `λ = 256`
  (`Errors.HopB.falcon1024_exact256'`), both for `K ≤ 2²⁹`. The other limits above (the modelled chain,
  implementations, range checks, `FTreeP.Real`, sampler, stored tree, overflow) apply at Falcon-1024 with
  `sign164R R64_1024` in place of `sign164`. Keys are any with `Key1024`'s bounds `256`, `7365` on the exact FFTs
  (2026/2431's tuple B with `≤`); no key generation is modelled. The `ℓ̂` bounds `32.0001`, `0.9990` are checks added
  by the model; that the 64-bit twiddle tables meet `0.7072·2⁻⁶⁴` at every level, level 9 included, is a hypothesis of
  `ρ` (as at Falcon-512); for the executable tables (`Exec.arithXN 10`) it holds by `#eval` only (`twOkN rc 10`,
  [LIMITS.md](LIMITS.md), E24). `R64_1024 = 2²⁷` is a bound of the proof: in 32.64 the checked values fit the integer
  bits on paper; the unchecked values are not covered.

### Hop B

- Assumed on every signing key (`KeyB.Good δ`): the stored tree is real (`FTreeP.Real`, as in S8) and `Close δ` holds:
  the stored tree within `δ` of the true tree (`‖ℓ̂ − ℓ‖∞ ≤ δ L` at depth `L + 1`, `|σ̄/σ − 1| ≤ 2⁻⁴²` at every
  leaf), and the true leaves in `[1.2778, 1.825]`.
- `δ127` (`2⁻⁵⁸` at the root, `2⁻⁶³` below) is a target value for a key expansion at `p = 127` stored in 64-bit
  words. Hop B formalises no key expansion; the executable track's key expansion (at `64 + xn` fraction bits) is
  tied to `δ127` only by its per-key check, which is `true` for a key by `#eval` only ([LIMITS.md](LIMITS.md)). The
  constants of `δ63` (`0.8123·2⁻⁴⁰` at the root, `0.7072·2⁻⁴¹` below) are numerical estimates, not proved. For
  `δ63`, the leaf condition has the form of `LDL.falcon512_leaf`, which is conditional on its own hypotheses and
  whose tree is not tied to `KeyB.trueTree` in Lean.
- SamplerZ is perfect in every world (`hE`, `hM`, `hF`). The composed theorems take all hypotheses of hop A
  (`falcon512_exact64n'`: `εq = 2⁻⁷⁸`, every auxiliary answer type inhabited) and start from F′; F (with the model's
  range checks) and `εq = 2⁻⁶⁵` are not composed with hop B.
- `K` counts signing-oracle calls (one ffSampling call each, restarts included) along every execution. `K ≤ 2³⁹` is
  hop A's cap; hop B uses it for its clamp costs and the `2⁴⁹` SamplerZ calls of Theorem 2 at `λ = 131`. In hop A it
  enters through the centre budget (`2³⁹·(49·0.54·2⁻³² + 43700·2⁻⁴⁰)² ≤ 2⁻⁹`), the SamplerZ call count of Theorem 2
  and the clamp costs (`2·p(30)·1024K`, `2·p_F(29.9)·1024K ≤ 2⁻¹⁴⁰`); hop B's centre budget at `δ127` is not the
  limit (about `2⁻³⁶·⁵` against `2⁻⁹`).
- The clamp at `y = 30.5` (every SamplerZ answer within `30.5` of its true centre) is a proof device; no signer
  clamps. It costs `≤ 2⁻¹⁴¹` in X and in Y; in the composed theorems the X side is absorbed into
  `T·2⁻¹²⁸ ≥ T·2⁻¹²⁹ + 2⁻¹⁴¹ + 2⁻¹⁴⁰`.
- Not proved: that key expansion gives `Close δ` (at `p = 127` or `p = 63`) for any key (the executable track's
  check implies it per key; no key is proved to pass the check); NTRUSolve (nothing ties `g, G` to `f, F`;
  `fG − gF = q` is not assumed); the range `[1.2778, 1.825]` of the true leaves (paper §4.1, from `αGPV ≤ 1.17`);
  any query bound above `2³⁹`; and what S8 does not prove.
- Falcon-1024 (`falcon1024_hopB`, `falcon1024_fixed_vs_true(43, 127)`, `falcon1024_hopB259`,
  `falcon1024_fixed_vs_true256(_43, _127)`): the same assumptions on every key (`KeyBP.Good σ1024 δ`). `δ43_1024` and
  `δ127_1024` are candidate tree errors. Hop B formalises no key expansion; the executable track's key expansion at
  Falcon-1024 is tied to them only by its per-key check `Exec.check1024` (`Exec.check1024_sound`), which is `true` for
  77 of the 100 round-3 Falcon-1024 KAT keys at `δ43q_1024` (`xn = 0`) and at `δ127q_1024` (`xn = 32`) by `#eval` only
  ([LIMITS.md](LIMITS.md), E23). The executable attempt `signX` is the model signer of F′ at Falcon-1024
  (`Exec.signX_refines1024`, tables cut at `N = 10`); `Exec.falcon1024_exec_vs_true(256)` state
  `Exec.falcon1024_fixed_vs_true(256)_checked` for the executable signer's world under `AdmN 10 C`, whose table
  condition holds by `#eval` only ([LIMITS.md](LIMITS.md), E24). Its integer ranges and words are `Exec.signX_word1024`
  and `Exec.sign32_eq_sign64_1024` (keys passing `checkRange … σ1024q`, which holds by `#eval` only, E25); the word
  signer (`27 ≤ i ≤ 64`) is composed with hop B and the executable SamplerZ in
  `Exec.falcon1024_exec_word_sampler_vs_true(256)`. The design-space equivalences of the signer are stated at
  Falcon-1024 (`Exec.SignEquiv1024`); their table, stored-tree and key conditions hold by `#eval` only
  ([LIMITS.md](LIMITS.md), E23, E25, E29, E30). The 12 pairs that differ have witnesses on KAT keys 0 and 2 whose 21
  premises hold by `#eval` only (`Exec.SignWitness1024`, E28); the two sampler witnesses are kernel-checked. The
  reference vectors are stated at Falcon-1024 (`Exec.refVec_sound1024`, `Exec.refVec_word1024`,
  `Exec.refVec_exact1024`); that a vector exists for an input (`refVecB1024 … = some V`), and their key and table
  conditions, hold by `#eval` only ([LIMITS.md](LIMITS.md), E23, E24, E33). The executable SamplerZ's closeness, hop and
  threshold step hold at Falcon-1024 (`Exec.lawZ_close1024`, `Exec.samplerZ_mgf1024`, `Exec.samplerZ_tv1024`,
  `Exec.sampler_hop1024`, `Exec.thresh_sampler1024`, `Exec.thresh_sampler1024_256`), and
  `Exec.falcon1024_exec_sampler_vs_true(256)` compose them with the signer (λ = 256: meaningful only with shift
  rejection; on keys passing `Exec.check1024`: `Exec.falcon1024_exec_sampler_vs_true(256)_checked`,
  `Exec.sampKey1024Equiv`). Theorem 2 enters at `λ = 128` (hop A) and `λ = 131` (hop B) with the Falcon-512
  certificates, and at `λ = 256` (hop A) and `λ = 259` (hop B) with `certs256`, `certs259`; query bounds above `2²⁹`
  (composed), `2³⁸` (hop B at `λ = 131`) or `2⁵³` (hop B at `λ = 259`, budget `K·s2B1024 41.5 δ ≤ 2⁻¹⁰` a hypothesis)
  are not covered.

Open: a proof, for some key, that key expansion gives `Close δ`; NTRUSolve; the range of the true leaves; query bounds
above `2³⁹`; the multiply-first order; the split path; at Falcon-1024, query bounds above `2²⁹`.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and the VCVio commit are pinned (`lean-toolchain`,
`lakefile.lean`, `lake-manifest.json`): VCVio `e7770ef7`, Lean `v4.35.0`.

```sh
lake exe cache get   # optional: download Mathlib's build cache
lake build           # every module, including S7, S8 and hop B (FalconPrecision/Errors, by glob)
lake build Axioms    # guarded #print axioms (test/Axioms.lean, test/S7Axioms.lean, test/ErrorsFalcon1024.lean and the executable-track tests), the 0.5.0 compatibility tests (test/Compat050*.lean), the executable-track tests (every test/Exec*.lean except test/ExecEquivEval.lean, test/ExecEquivEval1024.lean and test/ExecEquivEval1024Sig.lean) and the end-to-end example
```

For release 0.5.0, both commands were run on x86_64 and on aarch64 (Linux, Lean `v4.35.0`, every dependency at its
pinned commit, no previously built module of this repository); every guarded `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`. On both, every `#eval` fact of [LIMITS.md](LIMITS.md) that `lake build Axioms`
does not check (E1, E2, E3, E8, E12, E17) was then re-run as described in [evidence/README.md](evidence/README.md):
each output equals the recorded one (run times excepted; the E8 and E12 runs print nothing), and the vector files
have the sha256 in `SHA256SUMS`.

For release 0.6.0, both commands were run on x86_64 and on aarch64 under the same conditions; every guarded
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. On both, every `#eval` fact of
[LIMITS.md](LIMITS.md) that `lake build Axioms` does not check (E1, E2, E3, E8, E12, E17, E20, E21, E23, E25, E26, E28,
E33) was then re-run as described in [evidence/README.md](evidence/README.md): each output equals the recorded one (run
times excepted; the E8, E12, E20, E21 and E28 runs print nothing), and the vector files have the sha256 in
`SHA256SUMS`.

## Development

Developed with Claude Code (Anthropic) under the direction of XC0R. Every theorem named above is checked by the
Lean kernel; `lake build` and `lake build Axioms` re-check them without trusting how they were produced.

Changes since 0.2.0 (statements of 0.2.0 unchanged): in 0.3.0, `Errors.FFSamp.Uses` is a `def` over `UsesG`, so its
constructors are `UsesG.pure`, `UsesG.query`, `UsesG.sign`; `ffs`, `splitC`, `mergeC`, `updC` and `join` are defined as
`ffsU` (through `ffsG`), `splitCU`, `mergeCU`, `updCU` and `joinU` at tag 21, so their equation lemmas differ; `InB` and
`InC` are defined through `InBR` and `InCR`. 0.4.0 adds the modules `Errors.HopBCore` and `Errors.HopB` and changes no
earlier module; `test/S7Axioms.lean` guards the four hop B theorems. 0.5.0 adds the modules `Exec.*`
(`FalconPrecision/Exec/`), the tests `test/Exec*.lean` (all but `test/ExecEquivEval.lean` are `Axioms` roots),
`evidence/` and `scripts/`, and changes no earlier module. 0.6.0 adds the modules `Errors.Falcon1024Model`,
`Errors.Falcon1024Abort`, `Errors.Falcon1024HopB`, `Exec.Falcon1024Codec`, `Exec.KeyCheck1024`, `Exec.SignRangeN`,
`Exec.SignRange1024`, `Exec.SignRefine1024`, `Exec.SamplerCloseP`, `Exec.SamplerHop1024`, `Exec.SignWordHop1024`,
`Exec.SampKeyCheck`, `Exec.SignEquiv1024`, `Exec.SignWitness1024`, `Exec.WitnessData1024` and `Exec.RefVec1024`, and
the tests `test/ErrorsFalcon1024.lean`, `test/ExecFalcon1024.lean`, `test/ExecSampler1024.lean`,
`test/ExecSampKeyCheck.lean`, `test/ExecEquiv1024.lean`, `test/Compat050.lean`, `test/Compat050Exec.lean`,
`test/Compat050Defs.lean` (`Axioms` roots) and `test/ExecEquivEval1024.lean`, `test/ExecEquivEval1024Sig.lean`.
It adds the evidence folders `key-check-1024-d43/`, `key-check-1024-d127/`, `range-1024/`, `sampler-1024/` and
`vectors-1024/`, and `scripts/gen_evidence_runs.py` also writes the runs from `falcon1024-KAT.rsp` and the
Falcon-1024 SamplerZ trace. Earlier modules are generalised in the size: some 0.5.0 definitions and theorems gained
size or threshold parameters, and every 0.5.0 theorem statement still elaborates and is proved as stated (checked
before release by 1133 examples generated from the 0.5.0 sources). Declarations moved from `Exec.SamplerClose` to
`Exec.SamplerCloseP` and from `Exec.SignRange` to `Exec.SignRangeN`, which the old modules import publicly;
`FTree.Real` and `KeyB.gram00`, `KeyB.gram10`, `KeyB.gram11` are now `FTreeP.Real` and `KeyBP.gram00`,
`KeyBP.gram10`, `KeyBP.gram11` (dot notation such as `T.Real`, `k.gram00` is unchanged); `FTree`, `Key`, `KeyB`,
`KeyB.Good`, `UsesG` and `Swap` are abbreviations of the size-generic `FTreeP`, `KeyP`, `KeyBP`, `KeyBP.Good`,
`UsesGP`, `SwapP`, whose constructors keep their 0.5.0 names; their projections and recursors are named after the
generic type (`KeyP.f`, `KeyBP.toKey`, `FTreeP.rec`), and generalised declarations take new implicit arguments, which
matters only for `@` applications.

## Acknowledgements

Developed with the assistance of Claude models (Anthropic).

## License

Apache 2.0, as VCVio and Mathlib. Some files contain values from the Falcon round-3 submission package (its
known-answer-test file and specification test vectors); their source and terms are in [NOTICE](NOTICE).
