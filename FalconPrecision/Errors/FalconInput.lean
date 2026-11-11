/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FalconW
public import FalconPrecision.Errors.Parseval

/-! # Input error of ffSampling at Falcon-512

Standard signing (§7.3 item 4): `t̂0 = -FFT(c/q)·F̂`, `t̂1 = FFT(c/q)·f̂`, products rounded at tag
21. With `ĉ = FFT(c/q)` (assumed: `c/q` is the round-to-nearest of the exact quotient at tag 0, `½
ulp = 2⁻⁶⁴`; Table 4 gives only the tag, and §3.4 describes division as a reciprocal followed by a
product; then retagged to tag 9 by rounding to nearest, `½ ulp = 2⁻⁵⁵`, so each input coefficient is
within `E₀ = 2⁻⁵⁵ + 2⁻⁶⁴`; `‖ĉ‖₂ ≤ 512` by Parseval since `|c_i/q| < 1`; ℓ2 error `E_c` by
`fft_rec_err_l2`), `F̂` and `f̂` (certified, sup errors `E_F`, `E_f`): `‖δt̂‖₂ ≤ Σ (B·E_c + E·512 +
E·E_c + √512·ρ) ≤ 3.65·2⁻³²`.

`ec512`, `fftF512_err` and `input512` are inequalities between constants; `SignModel.input_err`
composes `prod_l2`, `ec_le`, `fft_rec_err_l2`, `parseval` and `cert_closed` into `‖δt̂‖₂ ≤
3.65·2⁻³²` for the fixed-point model. `‖F̂‖∞ ≤ γF,G = 3500` and `‖f̂‖∞ ≤ γf,g = 255` are
keygen-enforced (Alg. 2 l. 7, 13; §8.3-8.4), not true of every Falcon key. Assumed: the merge
twiddle table at tag 0 is the componentwise round-to-nearest of the exact roots (the paper gives
neither its tag nor its generation), hence within `√2/2·2⁻⁶³` (`twiddle_err`), with the size-2 merge
multiplying by `±i` exactly (tag 0 cannot represent `i`). -/

@[expose] public section

namespace FalconPrecision.Errors.FFSamp

open FalconPrecision.Errors.FFTRec

/-- **Product error in ℓ2.** -/
theorem prod_l2 {ι : Type} [Fintype ι] (c ch F Fh out : ι → ℂ) (BF EF Ec Cn ρ : ℝ) (hBF : 0 ≤ BF)
    (hEF : 0 ≤ EF)
    (hρ : 0 ≤ ρ) (hF : ∀ o, ‖F o‖ ≤ BF) (hdF : ∀ o, ‖Fh o - F o‖ ≤ EF) (hc : l2 (ch - c) ≤ Ec)
        (hCn : l2 c ≤ Cn)
    (hout : ∀ o, ‖out o - ch o * Fh o‖ ≤ ρ) :
    l2 (fun o => out o - c o * F o) ≤ BF * Ec + EF * Cn + EF * Ec + √(Fintype.card ι) * ρ := by
  have hdec : (fun o => out o - c o * F o) = (fun o => F o * (ch - c) o) +
      (fun o => (Fh o - F o) * c o) +
      (fun o => (Fh o - F o) * (ch - c) o) + (fun o => out o - ch o * Fh o) := by
    funext o; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hdec]
  have h1 := (l2_mul_le _ _ _ hBF hF).trans (mul_le_mul_of_nonneg_left hc hBF)
  have h2 := (l2_mul_le _ _ _ hEF hdF).trans (mul_le_mul_of_nonneg_left hCn hEF)
  have h3 := (l2_mul_le _ _ _ hEF hdF).trans (mul_le_mul_of_nonneg_left hc hEF)
  have h4 := l2_le_const _ ρ hρ hout
  exact ((l2_add_le _ _).trans (add_le_add ((l2_add_le _ _).trans (add_le_add ((l2_add_le _ _).trans
    (add_le_add h1 h2)) h3)) h4))

/-- Upper recursion for the ℓ2 error of `FFT(c/q)` (leaf error `2⁻⁵⁵ + 2⁻⁶⁴`: tag 0, then tag 9). -/
noncomputable def ecU (c : ℝ) : ℕ → ℝ
  | 0 => 1 / 2 ^ 55 + 1 / 2 ^ 64
  | L + 1 => 2 * (1 + 1 / 2 ^ 63) * ecU c L + 141422 / 100000 * sq512 L * c

theorem ec_le (δ c : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2 ^ 63) (hc : 0 ≤ c) (E : ℕ → ℝ)
    (h0 : E 0 ≤ 1 / 2 ^ 55 + 1 / 2 ^ 64)
    (hE0 : 0 ≤ E 0) (hE : ∀ L, E (L + 1) = 2 * (1 + δ) * E L + √2 * (√(2 ^ L) * c)) :
    ∀ L, 0 ≤ E L ∧ E L ≤ ecU c L := by
  intro L; induction L with
  | zero => exact ⟨hE0, h0⟩
  | succ L ih =>
    rw [hE]; simp only [ecU]
    constructor
    · have := ih.1; positivity
    · have h1 : 2 * (1 + δ) * E L ≤ 2 * (1 + 1 / 2 ^ 63) * ecU c L :=
        mul_le_mul (by gcongr) ih.2 ih.1 (by positivity)
      have h2 : √2 * (√(2 ^ L) * c) ≤ 141422 / 100000 * (sq512 L * c) :=
        mul_le_mul sqrt_two_le (mul_le_mul_of_nonneg_right (sqrt_pow_le L) hc) (by positivity)
            (by norm_num)
      linarith

/-- `E_c ≤ 1414600·2⁻⁶³` (arithmetic). -/
theorem ec512 : ecU (7072 / 10000 / 2 ^ 63 * 512 + 141422 / 100000 / 2 ^ 54) 9 ≤ 1414600 /
    2 ^ 63 := by
  simp only [ecU, sq512]; norm_num

/-- `F̂` by the certified FFT at tag 12 (`‖F̂‖∞ ≤ γF,G = 3500`): sup error `≤ 4226000·2⁻⁶³`
(arithmetic). -/
theorem fftF512_err (δ r : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 7072 / 10000 / 2 ^ 63)
    (hr : r ≤ 141422 / 100000 / 2 ^ 51) :
    (δ * 3500 + r) * ∑ j ∈ Finset.range 9, (2 + δ) ^ j ≤ 4226000 / 2 ^ 63 := by
  have hδ' : δ ≤ 1 / 2 ^ 63 := hδ.trans (by norm_num)
  have hs : ∑ j ∈ Finset.range 9, (2 + δ) ^ j ≤ ∑ j ∈ Finset.range 9, (2 + 1 / 2 ^ 63 : ℝ) ^ j :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (by positivity) (by linarith) j
  have hs' : ∑ j ∈ Finset.range 9, (2 + 1 / 2 ^ 63 : ℝ) ^ j ≤ 5111 / 10 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hc : δ * 3500 + r ≤ 7072 / 10000 / 2 ^ 63 * 3500 + 141422 / 100000 / 2 ^ 51 := by nlinarith
  calc _ ≤ (7072 / 10000 / 2 ^ 63 * 3500 + 141422 / 100000 / 2 ^ 51) * (5111 / 10) :=
        mul_le_mul hc (hs.trans hs') (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ ≤ 4226000 / 2 ^ 63 := by norm_num

/--
**Input error at Falcon-512** (arithmetic): the bound `Σ (B·E_c + E·512 + E·E_c + √512·ρ)` at the
Falcon-512 constants is `≤ 3.65·2⁻³²`. -/
theorem input512 (Ec : ℝ) (hEc : Ec ≤ 1414600 / 2 ^ 63) :
    (3500 * Ec + 4226000 / 2 ^ 63 * 512 + 4226000 / 2 ^ 63 * Ec + 2 ^ 5 *
        (141422 / 100000 / 2 ^ 42)) +
      (255 * Ec + 277300 / 2 ^ 63 * 512 + 277300 / 2 ^ 63 * Ec + 2 ^ 5 *
          (141422 / 100000 / 2 ^ 42)) ≤
      365 / 100 / 2 ^ 32 := by
  linarith

end FalconPrecision.Errors.FFSamp
