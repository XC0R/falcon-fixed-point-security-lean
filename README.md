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
as of 2026-11-09 FIPS 206 has not been published, so the parameters used are those of the round-3 specification.

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
| `Falcon.falcon512`, `Falcon.falcon1024` | Theorem 1, sufficient budgets chosen here | every `3 ≤ λ ≤ 128` (resp. `256`): per call `|σ̄/σ − 1| ≤ 2⁻⁴⁷` and `|t̄ − t| ≤ 2⁻⁴³` (resp. `2⁻⁴⁴`), at most `2⁷⁵` (resp. `2⁷⁶`) SamplerZ calls along every execution (`2n·Qs·(1+c)`, `Qs = 2⁶⁴`) |
| `Falcon.falcon512_rmse` | Theorem 2 at the paper's §5 operating point | every `3 ≤ λ ≤ 128`: per call `|σ̄/σ − 1| ≤ 2⁻⁴⁷`, at most `2⁷¹` SamplerZ calls (`2n·Qs·(1+c)`, `Qs = 2⁶⁰`, `c < 1`), `Σ(t̄ − t)² ≤ 2⁻⁹` along every execution |
| `FalconWitness.worlds_exist`, `test/EndToEnd.lean` | — | the sampler hypotheses are satisfiable; `falcon512` applied to a concrete experiment with a SamplerZ call |

The budgets of `falcon512`/`falcon1024` are sufficient conditions, not properties of any implementation: the paper's
measured center RMSE (`2⁻³⁹·⁵`, §7.5) does not meet the worst-case `2⁻⁴³`. `2⁻⁹` in `falcon512_rmse` is the sum the
measured RMSE gives over `2n·Qs = 2⁷⁰` calls (no restarts).

`test/Axioms.lean` checks with `#guard_msgs` that each theorem above depends only on `propext`, `Classical.choice`
and `Quot.sound`; `lake build Axioms` fails otherwise.

### Form of the security statements

The UF-CMA experiment is one computation `oa : OracleComp (spec aux Q) α`. Auxiliary oracles `aux` carry all
randomness other than the sampler (key generation, adversary coins, salts, hashing) and are answered identically in
the three worlds; each SamplerZ call carries the exact and fixed-point leaf and center computed by `oa` from its
history. The worlds answer SamplerZ by `D_{σ,t}` (exact), `D_{σ̄,t}` (intermediate) and `D_{σ̄,t̄}` (fixed point).
The conclusion, for every parameter `T ≥ 1`, is `T·2^{−(λ−2)} < Pr_fixed[win] ⇒ T·2^{−λ} < Pr_exact[win]`; read with
`T` the adversary's running time it is the bit-security statement `log₂(T/ε)`, but no cost model ties `T` to `oa`.

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
- The error bounds on leaves and centers (or their sums along executions) are hypotheses, as in the paper; proving
  them for a fixed-point implementation is the paper's stated open problem.
- `oa` is a finite term: signing restarts are capped, and the hypotheses range over every history, so out-of-range
  samples must abort or clamp identically in the three worlds. Relating this experiment to uncapped Falcon is not
  formalised (the paper's `c` and "for any history" leave the same gap).
- The center sum in `falcon512_rmse` is a hypothesis on every execution; the paper's RMSE is a sample average.
- Outputs of the experiment range over a countable type.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and the VCVio commit are pinned (`lean-toolchain`,
`lakefile.lean`, `lake-manifest.json`).

```sh
lake exe cache get   # optional: download Mathlib's build cache
lake build           # the library
lake build Axioms    # axiom checks and the end-to-end example
```

## Development

Developed with Claude Code (Anthropic) under the direction of XC0R. Every result above is checked by the Lean
kernel; `lake build` and `lake build Axioms` re-check them without trusting how they were produced.

## License

Apache 2.0, as VCVio and Mathlib.
