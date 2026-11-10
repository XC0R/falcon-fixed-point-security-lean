/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

/-! # Error of an `L`-level fixed-point FFT (TASK-009 S7c)

Level `ℓ` merges with the layer bound of `FFTLayer.mergeH_err`: `E_{ℓ+1} ≤ (2 + δ)E_ℓ + δB_ℓ + r`,
where `B_ℓ` bounds the half-size transforms and grows at most `×2` per level
(`FFTLayer.norm_merge_le`). Closed form: `E_L ≤ (2 + δ)^L E₀ + L(2 + δ)^{L-1}(δB₀ + r)`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFTErr

theorem fft_err (δ r B₀ : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hB : 0 ≤ B₀) (E B : ℕ → ℝ)
    (hstep : ∀ ℓ, E (ℓ + 1) ≤ (2 + δ) * E ℓ + δ * B ℓ + r) (hBℓ : ∀ ℓ, B ℓ ≤ 2 ^ ℓ * B₀) :
    ∀ L, E L ≤ (2 + δ) ^ L * E 0 + L * (2 + δ) ^ (L - 1) * (δ * B₀ + r) := by
  have hq : (1 : ℝ) ≤ 2 + δ := by linarith
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    have h2 : (2 : ℝ) ^ L ≤ (2 + δ) ^ L := pow_le_pow_left₀ (by norm_num) (by linarith) L
    have hc : 0 ≤ δ * B₀ + r := by positivity
    have hstepL := hstep L
    have hBL : δ * B L ≤ δ * (2 ^ L * B₀) := mul_le_mul_of_nonneg_left (hBℓ L) hδ
    calc E (L + 1) ≤ (2 + δ) * E L + δ * B L + r := hstepL
      _ ≤ (2 + δ) * ((2 + δ) ^ L * E 0 + L * (2 + δ) ^ (L - 1) * (δ * B₀ + r)) + δ * (2 ^ L * B₀) +
          r := by
          gcongr
      _ ≤ (2 + δ) ^ (L + 1) * E 0 + ((L + 1 : ℕ) : ℝ) * (2 + δ) ^ (L + 1 - 1) * (δ * B₀ + r) := by
          rcases L with _ | L
          · simp; nlinarith
          · have h2' : δ * (2 ^ (L + 1) * B₀) + r ≤ (2 + δ) ^ (L + 1) * (δ * B₀ + r) := by
              have : (1 : ℝ) ≤ (2 + δ) ^ (L + 1) := one_le_pow₀ hq
              nlinarith [mul_le_mul_of_nonneg_right h2 (mul_nonneg hδ hB)]
            rw [show L + 1 - 1 = L by omega, show L + 1 + 1 - 1 = L + 1 by omega]
            push_cast
            have e : (2 + δ) * (((L : ℝ) + 1) * (2 + δ) ^ L * (δ * B₀ + r)) =
                ((L : ℝ) + 1) * (2 + δ) ^ (L + 1) * (δ * B₀ + r) := by ring
            have e2 : (2 + δ) * ((2 + δ) ^ (L + 1) * E 0) = (2 + δ) ^ (L + 1 + 1) * E 0 := by ring
            nlinarith [e, e2, h2']

end FalconPrecision.Errors.FFTErr
