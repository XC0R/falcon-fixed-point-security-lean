/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.SignModel
public import FalconPrecision.Errors.FFSampModel64

/-! # Type 1 fixed-point signing (64.64 / 32.64); Theorem 2 without `hN`, `hS₂`

The non-split scale-first Type 1 chain of ePrint 2026/2431 §3.1 (which §5 suggests pinning for FIPS
206; NIST plans 64.64 fixed-point signing, §1): every value at 64 fractional bits (`Arith64`,
`FxModel64`), the target in the scale-first order `t̂ = ((-ĉ/q) ⊙ F̂, (ĉ/q) ⊙ f̂)` with `ĉ = FFT(c)`
computed from the integers `c` (the input of the FFT is exact), `ĉ/q` by `divq` (one rounding per
component, stored `1/q`), `F̂`, `f̂` by the same FFT (`Arith.fft`), products by `mul`. Exact: `t0E`,
`t1E` of `SignModel` (`FFT(c/q) = FFT(c)/q`, `fftE_cdq`). `input_err64`: the ℓ2 input error of
ffSampling is `≤ inp64 εq`, composing `fft_rec_err_l2` with exact leaves (`‖ĉ‖∞ ≤ 512·12288`, `E_ĉ ≤
2628341000·2⁻⁶³`), the `divq` bound, `parseval` (`‖ĉ/q‖₂ ≤ 512`), the certified FFT of `F`, `f`
(`fft_cert64`, `‖F̂‖∞ ≤ 3500`, `‖f̂‖∞ ≤ 255`) and `prod_l2`: `inp64 2⁻⁶⁵ ≤ 3.3·2⁻³²` (1/q stored at
64 fractional bits, the baseline) and `inp64 2⁻⁷⁸ ≤ 0.54·2⁻³²` (1/q stored normalized, §3.4, the
constant 2026/2431 recommends). `sign164` runs `ffsU` at ulp `2⁻⁶⁴` with range checks `‖·‖ ≤ R64 -
1`, `R64 = 2²⁴`, on that input (`b64`; in 32.64, `m ≤ 31`, the checked values fit on paper, the
unchecked even merge inputs are not covered, `FFSampModel64`); the range checks are the model's,
deployed signers (2026/2431's fxp32.64 signer, [DAB26] 64.64, c-fn-dsa) run none; `Uses64 ρ K oa`:
along every execution `oa` calls `sign164` at most `K` times and makes otherwise only auxiliary
queries (`UsesG`).

Per call, `Σ (t̄ - t)² ≤ (49 e + 43700·2⁻⁴⁰)²` with `e` the input bound; `2⁻⁹` fits `K = 2³⁸` calls
at `e = 3.3·2⁻³²` (`falcon512_model64`) and `K = 2³⁹` at `e = 0.54·2⁻³²` (`falcon512_model64n`).
`sign164_eq_margin`: while the checks pass, every checked computed value is within `1` of its exact
value (`ffs64_eq_margin`), so exact checked values in `‖·‖ ≤ R64 - 2` pass every check
(`InBR.chkM`). The recommended one-rounding division, `x·1/σ`, normalized `1/σ` and Symplecroot
(2026/2431 §3.4, §5) act on the computation of the Falcon tree, which is stored here (`FTree`, not
computed); they change no bound of this model. The single-rounding complex product (§3.5) is an
instance of `mul_err` with a tighter bound that is not used.

The worlds, keys, sampler and what is not proved are those of `SignModel` (`falcon512_model`), with
tag 21 replaced by Type 1 at 64 fractional bits and the range `2²¹` by `R64 = 2²⁴`. `|Pr_E - Pr_X|`
against abort-free exact signing X and `|Pr_F - Pr_F′|` against check-free Type 1 signing F′ are
bounded in `AbortExact` (`falcon512_exact64(n)`, `falcon512_exact64(n)'`). No implementation
(2026/2431's fxp32.64 signer, [DAB26] 64.64) is shown to meet `sign164`'s operation sequence. The
model computes every FFT slot; 2026/2431 works over the `n/2` slots with the conjugates implied,
which agrees with the model only under conjugation-symmetric rounding, and its recommended ties-up
rounding is not. c-fn-dsa signs in binary64 and is not a Type 1 arithmetic. The multiply-first order
of the reference code, c-fn-dsa and [DAB26] (`ĉ ⊙ F̂`, then `·1/q`) and the split path are not
modelled. Not proved here: hop B. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath

namespace FalconPrecision.Errors.FFSamp

variable {εq : ℝ}

/-- `ĉ = FFT(c)` in Type 1, from the exact integers `c` (2026/2431 §3.1). -/
noncomputable def chC64 (ρ : Arith64 εq) (c : Fin (2 ^ 9) → ℤ) : Out 9 → ℂ :=
  ρ.fft (1 / 2 ^ 64) 9 fun i => (c i : ℂ)

/-- `ĉ/q` in Type 1: the product by the stored `1/q`. -/
noncomputable def cqC64 (ρ : Arith64 εq) (c : Fin (2 ^ 9) → ℤ) (o : Out 9) : ℂ :=
    ρ.divq (chC64 ρ c o)

/-- `t̂0 = (-ĉ/q) ⊙ F̂` in Type 1 (scale-first). -/
noncomputable def t0C64 (ρ : Arith64 εq) (k : Key) (c : Fin (2 ^ 9) → ℤ) (o : Out 9) : ℂ :=
  ρ.mul (1 / 2 ^ 64) (-cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 9 (fun i => (k.F i : ℂ)) o)

/-- `t̂1 = (ĉ/q) ⊙ f̂` in Type 1 (scale-first). -/
noncomputable def t1C64 (ρ : Arith64 εq) (k : Key) (c : Fin (2 ^ 9) → ℤ) (o : Out 9) : ℂ :=
  ρ.mul (1 / 2 ^ 64) (cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 9 (fun i => (k.f i : ℂ)) o)

theorem fftE_cdq (c : Fin (2 ^ 9) → ℤ) (o : Out 9) :
    fftE (cdq c) o = fftE (fun i => (c i : ℂ)) o / 12289 := by
  simp only [fftE, evalAt, cdq, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

/-- ℓ2 norm of `f` from pointwise affine bounds `‖f i‖ ≤ ε‖g i‖ + κ`. -/
theorem l2_le_affine {ι : Type} [Fintype ι] (f g : ι → ℂ) (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (h : ∀ i, ‖f i‖ ≤ ε * ‖g i‖ + κ) : l2 f ≤ ε * l2 g + √(Fintype.card ι) * κ := by
  have h1 : l2 f ≤ l2 (fun i => ((ε * ‖g i‖ + κ : ℝ) : ℂ)) := by
    unfold l2
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    rw [Complex.norm_real, Real.norm_of_nonneg (add_nonneg (mul_nonneg hε (norm_nonneg _)) hκ)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  have h2 : l2 (fun i => ((ε * ‖g i‖ : ℝ) : ℂ)) ≤ ε * l2 g := by
    refine le_trans (le_of_eq ?_) (l2_mul_le (fun _ => (ε : ℂ)) g ε hε fun _ => by
      rw [Complex.norm_real, Real.norm_of_nonneg hε])
    unfold l2
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hε (norm_nonneg _)), norm_mul,
        Complex.norm_real,
      Real.norm_of_nonneg hε]
  have h3 := l2_le_const (fun _ : ι => ((κ : ℝ) : ℂ)) κ hκ fun _ => by
    rw [Complex.norm_real, Real.norm_of_nonneg hκ]
  have e : (fun i => ((ε * ‖g i‖ + κ : ℝ) : ℂ)) =
      (fun i => ((ε * ‖g i‖ : ℝ) : ℂ)) + fun _ => ((κ : ℝ) : ℂ) := by
    funext i; simp
  rw [e] at h1
  linarith [l2_add_le (fun i => ((ε * ‖g i‖ : ℝ) : ℂ)) fun _ => ((κ : ℝ) : ℂ)]

/-- `E_ĉ` (arithmetic): `ezU` at `c = δ·512·12288 + √2·2⁻⁶⁴`, `δ = 0.7072·2⁻⁶⁴`. -/
theorem ec64 : ezU (7072 / 10000 / 2 ^ 64 * (512 * 12288) + 141422 / 100000 / 2 ^ 64) 9 ≤
    2628341000 / 2 ^ 63 := by
  simp only [ezU, sq512]; norm_num

/-- The computed `ĉ = FFT(c)` is within `2628341000·2⁻⁶³` in ℓ2. -/
theorem chC64_err (ρ : Arith64 εq) (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) :
    l2 (chC64 ρ c - fun o => fftE (fun i => (c i : ℂ)) o) ≤ 2628341000 / 2 ^ 63 := by
  set E : ℕ → ℝ := fun L => Nat.rec (motive := fun _ => ℝ) 0
    (fun L e => 2 * (1 + 7072 / 10000 / 2 ^ 64) * e +
      √2 * (√(2 ^ L) * (7072 / 10000 / 2 ^ 64 * (512 * 12288) + 141422 / 100000 / 2 ^ 64))) L
  have hu : (0 : ℝ) < 1 / 2 ^ 64 := by positivity
  have ha : ∀ i, ‖((c i : ℤ) : ℂ)‖ ≤ 12288 := fun i => by
    obtain ⟨h1, h2⟩ := abs_lt.1 (hc i)
    rw [Complex.norm_intCast, abs_le]
    exact ⟨by exact_mod_cast (by omega : (-12288 : ℤ) ≤ c i),
        by exact_mod_cast (by omega : c i ≤ 12288)⟩
  have h :=
      fft_rec_err_l2 (7072 / 10000 / 2 ^ 64) (141422 / 100000 / 2 ^ 64) (512 * 12288) E zeta ρ.tw pt
    pt_succ zeta_sq norm_zeta ρ.tw_err64 (fun L a => ρ.fft (1 / 2 ^ 64) L a)
    (fun a => by
      rw [l2_out0]
      change ‖a ⟨0, by norm_num⟩ - a ⟨0, by norm_num⟩‖ ≤ (0 : ℝ)
      simp)
    (fun L a => ⟨_, fun o => (ρ.mul_err hu _ _).trans sqrt_two_ulp64, fun o => ⟨rfl, rfl⟩⟩)
        (fun L => rfl) 9
    (fun i => (c i : ℂ)) fun o => (norm_evalAt_le _ _ (norm_pt 9 o) 12288 ha).trans (by norm_num)
  have he :=
      (ez_le (7072 / 10000 / 2 ^ 64)
          (7072 / 10000 / 2 ^ 64 * (512 * 12288) + 141422 / 100000 / 2 ^ 64)
    (by positivity) (by norm_num) (by positivity) E rfl (fun L => rfl) 9).2
  exact h.trans (he.trans ec64)

/-- Error bound of the computed `ĉ/q`. -/
noncomputable def ecq64 (εq : ℝ) : ℝ :=
  2628341000 / 2 ^ 63 / 12289 + εq * (12289 * 512 + 2628341000 / 2 ^ 63) + 2 ^ 5 *
      (141422 / 100000 / 2 ^ 65)

/-- The computed `ĉ/q` is within `ecq64 εq` of `FFT(c/q)` in ℓ2. -/
theorem cqC64_err (ρ : Arith64 εq) (hεq : 0 ≤ εq) (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) :
    l2 (fun o => cqC64 ρ c o - fftE (cdq c) o) ≤ ecq64 εq := by
  set ch := chC64 ρ c
  set C : Out 9 → ℂ := fun o => fftE (fun i => (c i : ℂ)) o
  have hE := chC64_err ρ c hc
  have hC : l2 C ≤ 12289 * 512 := by
    have hC' : C = fun o => (fun _ => (12289 : ℂ)) o * fftE (cdq c) o := by
      funext o; simp only [C, fftE_cdq]; ring
    rw [hC']
    exact (l2_mul_le _ _ 12289 (by norm_num) fun _ => by norm_num).trans
      (mul_le_mul_of_nonneg_left (fftE_l2 c hc) (by norm_num))
  have hch : l2 ch ≤ 12289 * 512 + 2628341000 / 2 ^ 63 := by
    have := l2_add_le C (ch - C)
    rw [add_sub_cancel] at this
    linarith
  have e : (fun o => cqC64 ρ c o - fftE (cdq c) o) =
      (fun o => ρ.divq (ch o) - ch o / 12289) + fun o => (fun _ => (1 / 12289 : ℂ)) o *
          (ch - C) o := by
    funext o; simp only [cqC64, Pi.add_apply, Pi.sub_apply, fftE_cdq, C, ch]; ring
  rw [e]
  have ha := l2_le_affine _ ch εq _ hεq (by positivity) fun o => ρ.divq_err (ch o)
  have hb := (l2_mul_le (fun _ => (1 / 12289 : ℂ)) (ch - C) (1 / 12289) (by norm_num) fun _ => by
    rw [norm_div, norm_one, Complex.norm_ofNat]).trans
    (mul_le_mul_of_nonneg_left hE (by norm_num))
  have hcard : √(Fintype.card (Out 9) : ℝ) ≤ 2 ^ 5 := by
    rw [card_out, Real.sqrt_le_left (by norm_num)]; norm_num
  have hk : √(Fintype.card (Out 9) : ℝ) * (√2 * (1 / 2 ^ 65)) ≤ 2 ^ 5 *
      (141422 / 100000 / 2 ^ 65) :=
    mul_le_mul hcard ((mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num))
      (by positivity) (by norm_num)
  have := mul_le_mul_of_nonneg_left hch hεq
  unfold ecq64
  linarith
      [l2_add_le (fun o => ρ.divq (ch o) - ch o / 12289) fun o => (fun _ => (1 / 12289 : ℂ)) o *
          (ch - C) o]

/-- Certified FFT in Type 1 at Falcon-512 (`‖FFT(a)‖∞ ≤ B`): sup error `(δB + √2·2⁻⁶⁴)·Σ_{j<9}(2 +
δ)^j`, `δ = 0.7072·2⁻⁶⁴`. -/
theorem fft_cert64 (ρ : Arith64 εq) (B : ℝ) (a : Fin (2 ^ 9) → ℂ) (hB : ∀ o, ‖fftE a o‖ ≤ B)
    (o : Out 9) :
    ‖ρ.fft (1 / 2 ^ 64) 9 a o - fftE a o‖ ≤ (7072 / 10000 / 2 ^ 64 * B + 141422 / 100000 / 2 ^ 64) *
      ∑ j ∈ Finset.range 9, (2 + 7072 / 10000 / 2 ^ 64) ^ j := by
  set E : ℕ → ℝ := fun L => Nat.rec (motive := fun _ => ℝ) 0
    (fun _ e => e * (2 + 7072 / 10000 / 2 ^ 64) + 7072 / 10000 / 2 ^ 64 * B + 141422 / 100000 /
        2 ^ 64) L
  have hE : ∀ L, E (L + 1) = E L * (2 + 7072 / 10000 / 2 ^ 64) + 7072 / 10000 / 2 ^ 64 * B +
      141422 / 100000 / 2 ^ 64 := fun _ => rfl
  have h :=
      fft_rec_err_cert (7072 / 10000 / 2 ^ 64)
          (141422 / 100000 / 2 ^ 64) B E zeta ρ.tw pt pt_succ zeta_sq
    norm_zeta ρ.tw_err64 (fun L a => ρ.fft (1 / 2 ^ 64) L a)
        (fun a o => by change ‖a _ - a _‖ ≤ 0; simp)
    (fun L a o => ⟨_, (ρ.mul_err (by positivity) _ _).trans sqrt_two_ulp64, rfl, rfl⟩) hE 9 a hB o
  rw [cert_closed _ _ _ E hE 9] at h
  simpa [E, fftE] using h

/--
`F̂` by the certified FFT in Type 1 (`‖F̂‖∞ ≤ γF,G = 3500`): sup error `≤ 632776·2⁻⁶³` (arithmetic).
-/
theorem fftF64_err : (7072 / 10000 / 2 ^ 64 * 3500 + 141422 / 100000 / 2 ^ 64) *
    ∑ j ∈ Finset.range 9, (2 + 7072 / 10000 / 2 ^ 64 : ℝ) ^ j ≤ 632776 / 2 ^ 63 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

/--
`f̂` by the certified FFT in Type 1 (`‖f̂‖∞ ≤ γf,g = 255`): sup error `≤ 46438·2⁻⁶³` (arithmetic).
-/
theorem fftf64_err : (7072 / 10000 / 2 ^ 64 * 255 + 141422 / 100000 / 2 ^ 64) *
    ∑ j ∈ Finset.range 9, (2 + 7072 / 10000 / 2 ^ 64 : ℝ) ^ j ≤ 46438 / 2 ^ 63 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

/-- The input-error bound `Σ (B·E_c + E·512 + E·E_c + √512·√2·2⁻⁶⁴)` of the Type 1 chain. -/
noncomputable def inp64 (εq : ℝ) : ℝ :=
  (3500 * ecq64 εq + 632776 / 2 ^ 63 * 512 + 632776 / 2 ^ 63 * ecq64 εq + 2 ^ 5 *
      (141422 / 100000 / 2 ^ 64)) +
    (255 * ecq64 εq + 46438 / 2 ^ 63 * 512 + 46438 / 2 ^ 63 * ecq64 εq + 2 ^ 5 *
        (141422 / 100000 / 2 ^ 64))

/-- `1/q` stored at 64 fractional bits: input error `≤ 3.3·2⁻³²` (arithmetic). -/
theorem inp64_base : inp64 (1 / 2 ^ 65) ≤ 33 / 10 / 2 ^ 32 := by
  simp only [inp64, ecq64]; norm_num

/-- `1/q` stored normalized (`⌊2⁷⁷/q⌉·2⁻⁷⁷`): input error `≤ 0.54·2⁻³²` (arithmetic). -/
theorem inp64_norm : inp64 (1 / 2 ^ 78) ≤ 54 / 100 / 2 ^ 32 := by
  simp only [inp64, ecq64]; norm_num

/--
**Input error of ffSampling in Type 1 at Falcon-512** (scale-first target, 2026/2431 §3.1): `‖(t̂0,
t̂1) computed - exact‖₂ ≤ inp64 εq`. -/
theorem input_err64 (ρ : Arith64 εq) (hεq : 0 ≤ εq) (k : Key) (c : Fin (2 ^ 9) → ℤ)
    (hc : ∀ i, |c i| < 12289) :
    l2 (pairF (t0C64 ρ k c - t0E k c) (t1C64 ρ k c - t1E k c)) ≤ inp64 εq := by
  have hcard : √(Fintype.card (Out 9) : ℝ) ≤ 2 ^ 5 := by
    rw [card_out, Real.sqrt_le_left (by norm_num)]; norm_num
  have hq := cqC64_err ρ hεq c hc
  have hn := fftE_l2 c hc
  have hr : ∀ z w, ‖ρ.mul (1 / 2 ^ 64) z w - z * w‖ ≤ 141422 / 100000 / 2 ^ 64 := fun z w =>
    (ρ.mul_err (by positivity) z w).trans sqrt_two_ulp64
  have h0 := prod_l2 (fun o => -fftE (cdq c) o) (fun o => -cqC64 ρ c o) (fftE fun i => (k.F i : ℂ))
    (ρ.fft (1 / 2 ^ 64) 9 fun i => (k.F i : ℂ))
    (fun o => ρ.mul (1 / 2 ^ 64) (-cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 9 (fun i => (k.F i : ℂ)) o))
        3500
    (632776 / 2 ^ 63) (ecq64 εq) 512 (141422 / 100000 / 2 ^ 64) (by norm_num) (by positivity)
        (by positivity)
    k.hF (fun o => (fft_cert64 ρ 3500 _ k.hF o).trans fftF64_err)
    (by
      have e : (fun o => -cqC64 ρ c o) - (fun o => -fftE (cdq c) o) =
          fun o => -(cqC64 ρ c o - fftE (cdq c) o) := by
        funext o; simp only [Pi.sub_apply]; ring
      rw [e, l2_neg]; exact hq)
    (by rw [l2_neg]; exact hn) (fun o => hr _ _)
  have h1 := prod_l2 (fun o => fftE (cdq c) o) (fun o => cqC64 ρ c o) (fftE fun i => (k.f i : ℂ))
    (ρ.fft (1 / 2 ^ 64) 9 fun i => (k.f i : ℂ))
    (fun o => ρ.mul (1 / 2 ^ 64) (cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 9 (fun i => (k.f i : ℂ)) o)) 255
    (46438 / 2 ^ 63) (ecq64 εq) 512 (141422 / 100000 / 2 ^ 64) (by norm_num) (by positivity)
        (by positivity)
    k.hf (fun o => (fft_cert64 ρ 255 _ k.hf o).trans fftf64_err) hq hn (fun o => hr _ _)
  have e0 : t0C64 ρ k c - t0E k c = fun o =>
      ρ.mul (1 / 2 ^ 64) (-cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 9 (fun i => (k.F i : ℂ)) o) -
        (fun o => -fftE (cdq c) o) o * fftE (fun i => (k.F i : ℂ)) o := by
    funext o; simp only [Pi.sub_apply, t0C64, t0E]; ring
  have e1 : t1C64 ρ k c - t1E k c = fun o =>
      ρ.mul (1 / 2 ^ 64) (cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 9 (fun i => (k.f i : ℂ)) o) -
        (fun o => fftE (cdq c) o) o * fftE (fun i => (k.f i : ℂ)) o := by
    funext o; simp only [Pi.sub_apply, t1C64, t1E]
  refine (l2_pairF_le _ _).trans ?_
  rw [e0, e1]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ 141422 / 100000 / 2 ^ 64)
  unfold inp64
  linarith

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

open Classical in
/-- One ffSampling call of Type 1 signing on the hash `c`: `none` (`⊥`) unless `|c i| < q`, else the
integer `z = (z0, z1)` of `ffsU` at ulp `2⁻⁶⁴` with range checks `‖·‖ ≤ R64 - 1` (or `⊥`). -/
noncomputable def sign164 (ρ : Arith64 εq) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    OracleComp (FalconGame.spec aux Falcon.CallP)
        (Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))) :=
  if ∀ i, |c i| < 12289 then
    (fun r => r.map fun s => (s.z0, s.z1)) <$>
      ffsU ρ.toArith (1 / 2 ^ 64) R64 k.tree (t0E k c) (t1E k c) (t0C64 ρ k c) (t1C64 ρ k c)
  else pure none

open Classical in
/-- `sign164` with the check `chk` on (computed, exact) pairs in place of the range checks (`ffsG`).
-/
noncomputable def sign164G (ρ : Arith64 εq) (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop)
    (k : Key)
    (c : Fin (2 ^ 9) → ℤ) :
    OracleComp (FalconGame.spec aux Falcon.CallP)
        (Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))) :=
  if ∀ i, |c i| < 12289 then
    (fun r => r.map fun s => (s.z0, s.z1)) <$>
      ffsG ρ.toArith (1 / 2 ^ 64) chk k.tree (t0E k c) (t1E k c) (t0C64 ρ k c) (t1C64 ρ k c)
  else pure none

/--
**Check margins of Type 1 signing at `R64`** (for the abort bound): for an input bound `inp64 εq ≤
e` with `49 e + 43700·2⁻⁴⁰ ≤ 2⁻¹⁰`, while the earlier checks pass every checked computed value is
within `1` of its exact value slotwise, so the range checks `‖vh‖ ≤ R64 - 1` may be replaced by
`chkM R64`; exact checked values in `‖·‖ ≤ R64 - 2` pass `chkM R64` (`InBR.chkM`). -/
theorem sign164_eq_margin (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    sign164 (aux := aux) ρ k c = sign164G ρ (chkM R64) k c := by
  unfold sign164 sign164G
  split_ifs with hc
  · rw [ffs64_eq_margin ρ k.tree _ _ _ _ e ((input_err64 ρ hεq k c hc).trans he) he1]
  · rfl

/-- **Centre-error budget of one Type 1 ffSampling call**, for an input bound `inp64 εq ≤ e`. -/
theorem sign164_pathS (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    PathSum wS (sign164 (aux := aux) ρ k c) ((49 * e + 43700 / 2 ^ 40) ^ 2) := by
  unfold sign164
  split_ifs with hc
  · rw [map_eq_bind_pure_comp]
    exact (PathSum.bind (ffs64_pathS ρ k.tree _ _ _ _ e ((input_err64 ρ hεq k c hc).trans he) he1)
      (T := 0) fun _ => .pure _ le_rfl).weaken (le_of_eq (add_zero _))
  · exact .pure _ (sq_nonneg _)

/-- **SamplerZ calls of one Type 1 ffSampling call**: at most `1024`. -/
theorem sign164_pathN (ρ : Arith64 εq) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    PathSum w1 (sign164 (aux := aux) ρ k c) 1024 := by
  unfold sign164
  split_ifs
  · rw [map_eq_bind_pure_comp]
    exact (PathSum.bind (ffs64_pathN ρ k.tree _ _ _ _) (T := 0) fun _ => .pure _ le_rfl).weaken
      (le_of_eq (add_zero _))
  · exact .pure _ (by norm_num)

/-- `oa` calls `sign164` at most `K` times along every execution; every other query is auxiliary. -/
def Uses64 (ρ : Arith64 εq) : ℕ → {α : Type} → OracleComp (FalconGame.spec aux Falcon.CallP) α →
    Prop :=
  UsesG (sign164 ρ)

/-- Spec Alg. 10 l. 4-11 with at most `n` calls of `sg`: `acc` returns a signature or restarts. -/
noncomputable def signLoopG {β : Type} (sg : Key → (Fin (2 ^ 9) → ℤ) →
    OracleComp (FalconGame.spec aux Falcon.CallP) (Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))))
    (k : Key) (c : Fin (2 ^ 9) → ℤ)
        (acc : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) → Option β) :
    ℕ → OracleComp (FalconGame.spec aux Falcon.CallP) (Option β)
  | 0 => pure none
  | n + 1 => sg k c >>= fun y => (acc y).elim (signLoopG sg k c acc n) fun b => pure (some b)

theorem UsesG.signLoopG {β : Type} (sg : Key → (Fin (2 ^ 9) → ℤ) →
    OracleComp (FalconGame.spec aux Falcon.CallP) (Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))))
    (k : Key) (c : Fin (2 ^ 9) → ℤ)
        (acc : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) → Option β) :
    ∀ n, UsesG sg n (signLoopG sg k c acc n)
  | 0 => UsesG.pure 0 none
  | n + 1 => UsesG.sign n k c _ fun y => by
    rcases acc y with _ | b
    exacts [UsesG.signLoopG sg k c acc n, UsesG.pure n _]

theorem Uses64.pathS {ρ : Arith64 εq} (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α} (h : Uses64 ρ K oa) :
    PathSum wS oa (K * (49 * e + 43700 / 2 ^ 40) ^ 2) :=
  UsesG.path h wS (fun _ => rfl) _ (sq_nonneg _) (sign164_pathS ρ hεq e he he1)

theorem Uses64.pathN {ρ : Arith64 εq} {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Uses64 ρ K oa) : PathSum w1 oa (K * 1024) :=
  UsesG.path h w1 (fun _ => rfl) _ (by norm_num) (sign164_pathN ρ)

end FalconPrecision.Errors.FFSamp

namespace FalconPrecision.Falcon

open MeasureTheory InformationTheory LatticeCrypto FalconPrecision.Errors.FFSamp
open scoped ENNReal

/-- `2³⁸` Type 1 calls at input error `3.3·2⁻³²` sum to `≤ 2⁻⁹`. -/
theorem centers_budget64 : (2 : ℝ) ^ 38 * (49 * (33 / 10 / 2 ^ 32) + 43700 / 2 ^ 40) ^ 2 ≤ 1 /
    2 ^ 9 := by
  norm_num

/-- `2³⁹` Type 1 calls at input error `0.54·2⁻³²` sum to `≤ 2⁻⁹`. -/
theorem centers_budget64n : (2 : ℝ) ^ 39 * (49 * (54 / 100 / 2 ^ 32) + 43700 / 2 ^ 40) ^ 2 ≤ 1 /
    2 ^ 9 := by
  norm_num

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/--
**Theorem 2 at Falcon-512 for Type 1 fixed-point signing** (64 fractional bits, 32.64 or 64.64; `λ =
128`, hop A). For every Type 1 arithmetic `ρ` whose stored `1/q` is within `2⁻⁶⁵` (64 fractional
bits) and every experiment `oa` that calls Type 1 ffSampling (`sign164`: the non-split scale-first
target of 2026/2431 §3.1, range checks `‖·‖ ≤ R64 - 1`, `R64 = 2²⁴`, which deployed signers do not
run) at most `K ≤ 2³⁸` times along every execution and makes otherwise only auxiliary queries:
success `> T·2⁻¹²⁶` in F (Type 1 signing with `ρ`, `⊥` when a range check fails) gives success `>
T·2⁻¹²⁸` in E (exact signing on the stored tree with the same aborts). `hN` and `hS₂` of
`falcon512_proved_n64` are proved (`Uses64.pathN`, `Uses64.pathS`).

Against abort-free exact signing X and check-free Type 1 signing F′ see `falcon512_exact64`,
`falcon512_exact64'` (`AbortExact`); hop B (true tree) is not proved. No implementation (2026/2431's
fxp32.64 signer, [DAB26] 64.64, c-fn-dsa) is shown to meet `sign164`'s operation sequence; the
multiply-first order and the split path are not modelled. Keys: the paper's modified NTRUGen (ePrint
2026/1531 Alg. 2, `γ = (255, 4, 3500, 24)`), not Falcon round 3 or FIPS 206 draft keys; `Key`'s
exact bounds hold up to keygen's rounding; the stored tree passed the checks of `FTree` and is not
tied to the key. SamplerZ is assumed perfect (`hE`, `hM`, `hF`). No UF-CMA game is defined: `oa` is
any experiment. The norm check and restarts are integer code in `oa`. Register overflow is not
represented. The FIPS 206 draft signs in binary64; a fixed-point specification is planned by NIST
and not published. Other hypotheses: `ρ : Arith64` (each operation within its bound, `FxModel64`),
the bounds of `Key`, the checks of `FTree`. -/
theorem falcon512_model64 (ρ : Arith64 (1 / 2 ^ 65)) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
        (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux CallP) α) (hoa : Uses64 ρ K oa)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by exact_mod_cast hK
  refine falcon512_proved_n64 T hT implA implE implM implF hAE hAM hAF hE hM hF oa
    (hoa.pathN.weaken (by linarith))
        ((hoa.pathS (by norm_num) _ inp64_base (by norm_num)).weaken ?_) hs hwin
  have := mul_le_mul_of_nonneg_right hK' (sq_nonneg (49 * (33 / 10 / 2 ^ 32) + 43700 / 2 ^ 40 : ℝ))
  linarith [centers_budget64]

/-- **Theorem 2 at Falcon-512 for Type 1 fixed-point signing with normalized `1/q`** (the constant
2026/2431 recommends, §3.4 "Wide 1/q", §5: `1/q` stored as `⌊2⁷⁷/q⌉·2⁻⁷⁷`, within `2⁻⁷⁸`):
`falcon512_model64` with `K ≤ 2³⁹` calls. Same worlds, hypotheses and limits as `falcon512_model64`.
-/
theorem falcon512_model64n (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
        (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux CallP) α) (hoa : Uses64 ρ K oa)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  refine falcon512_proved_n64 T hT implA implE implM implF hAE hAM hAF hE hM hF oa
    (hoa.pathN.weaken (by linarith))
        ((hoa.pathS (by norm_num) _ inp64_norm (by norm_num)).weaken ?_) hs hwin
  have := mul_le_mul_of_nonneg_right hK' (sq_nonneg (49 * (54 / 100 / 2 ^ 32) + 43700 / 2 ^ 40 : ℝ))
  linarith [centers_budget64n]

end FalconPrecision.Falcon
