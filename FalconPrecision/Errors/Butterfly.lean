/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Analysis.Complex.Basic

/-! # One FFT butterfly in fixed point

Falcon's FFT merges `f̂(ζ) = â + ζ·b̂`, `f̂(-ζ) = â - ζ·b̂` (ePrint 2026/1531 §7.3 item 1). With
inputs within `E` of `a, b`, a fixed-point twiddle `ζ̂` within `δ` of `ζ` (`|ζ| = 1`), and the
product `ζ̂·b̂` rounded within `r`: `|out - (a ± ζb)| ≤ E(2 + δ) + δ|b| + r`. -/

@[expose] public section

namespace FalconPrecision.Errors.Butterfly

/-- Error of a rounded product `ζ̂·b̂` against `ζ·b`. -/
theorem mul_err (ζ ζh b bh p : ℂ) (E δ r : ℝ) (hζ : ‖ζ‖ = 1) (hδ : ‖ζh - ζ‖ ≤ δ) (hb : ‖bh - b‖ ≤ E)
    (hp : ‖p - ζh * bh‖ ≤ r) : ‖p - ζ * b‖ ≤ E * (1 + δ) + δ * ‖b‖ + r := by
  have hid : p - ζ * b = (p - ζh * bh) + ζh * (bh - b) + (ζh - ζ) * b := by ring
  have hζh : ‖ζh‖ ≤ 1 + δ := by
    calc ‖ζh‖ = ‖ζ + (ζh - ζ)‖ := by ring_nf
      _ ≤ ‖ζ‖ + ‖ζh - ζ‖ := norm_add_le _ _
      _ ≤ 1 + δ := by rw [hζ]; linarith
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hb
  rw [hid]
  calc ‖(p - ζh * bh) + ζh * (bh - b) + (ζh - ζ) * b‖
      ≤ ‖p - ζh * bh‖ + ‖ζh * (bh - b)‖ + ‖(ζh - ζ) * b‖ := norm_add₃_le
    _ = ‖p - ζh * bh‖ + ‖ζh‖ * ‖bh - b‖ + ‖ζh - ζ‖ * ‖b‖ := by rw [norm_mul, norm_mul]
    _ ≤ r + (1 + δ) * E + δ * ‖b‖ := by
        have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
        gcongr
    _ = E * (1 + δ) + δ * ‖b‖ + r := by ring

/--
**Butterfly.** Addition is exact in fixed point (common tag), so the output error is the input error
plus the product error. -/
theorem butterfly_err (a ah ζ ζh b bh p : ℂ) (E δ r : ℝ) (hζ : ‖ζ‖ = 1) (hδ : ‖ζh - ζ‖ ≤ δ)
    (ha : ‖ah - a‖ ≤ E)
    (hb : ‖bh - b‖ ≤ E) (hp : ‖p - ζh * bh‖ ≤ r) :
    ‖(ah + p) - (a + ζ * b)‖ ≤ E * (2 + δ) + δ * ‖b‖ + r ∧
      ‖(ah - p) - (a - ζ * b)‖ ≤ E * (2 + δ) + δ * ‖b‖ + r := by
  have hm := mul_err ζ ζh b bh p E δ r hζ hδ hb hp
  constructor
  · calc ‖(ah + p) - (a + ζ * b)‖ = ‖(ah - a) + (p - ζ * b)‖ := by ring_nf
      _ ≤ ‖ah - a‖ + ‖p - ζ * b‖ := norm_add_le _ _
      _ ≤ E * (2 + δ) + δ * ‖b‖ + r := by linarith
  · calc ‖(ah - p) - (a - ζ * b)‖ = ‖(ah - a) - (p - ζ * b)‖ := by ring_nf
      _ ≤ ‖ah - a‖ + ‖p - ζ * b‖ := norm_sub_le _ _
      _ ≤ E * (2 + δ) + δ * ‖b‖ + r := by linarith

end FalconPrecision.Errors.Butterfly
