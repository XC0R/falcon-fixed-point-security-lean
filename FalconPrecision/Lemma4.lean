/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.RenyiShift
public import FalconPrecision.ThetaTail
public import FalconPrecision.Taylor2

/-! # Lemma 4 of ePrint 2026/1531 with an explicit constant

For `a > 1` and `T(σ) < 1`: `Rₐ(D_{Z,σ,c+δ} ‖ D_{Z,σ,c}) ≤ exp(aδ²/(2σ²) + a(a+1)δ² M(σ) /
(2(a-1)))`, with `M(σ) = (T₂(1+T) + T₁²)/(1-T)²` built from the explicit theta tails of
`ThetaTail.lean`. The paper states `exp(a(a+1)δ²/(2(a-1)σ²) (1 + O(ϵ)))` for `σ ≥ ηϵ(Z)`. -/

@[expose] public section

open Real MeasureTheory InformationTheory LatticeCrypto FalconPrecision.ThetaTail
open scoped ENNReal

namespace FalconPrecision.Lemma4

theorem sum_eq (σ u : ℝ) (hσ : 0 < σ) : discreteGaussianSum σ u = σ * √(2 * π) * f σ u := by
  rw [discreteGaussianSum_eq_fourier σ u hσ]; rfl

theorem f_pos (σ u : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) : 0 < f σ u := by
  linarith [(f_mem σ u hσ).1]

/-- The normalizer ratio of eq. (52) is `exp Δ`, `Δ` the second difference of `log f`. -/
theorem ratio_eq (σ c δ a : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) :
    discreteGaussianSum σ (c + a * δ) /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a)) =
      Real.exp
          (Real.log (f σ (c + a * δ)) - a * Real.log (f σ (c + δ)) - (1 - a) * Real.log (f σ c)) :=
              by
  have hK : 0 < σ * √(2 * π) := by positivity
  have h1 := f_pos σ (c + a * δ) hσ hT
  have h2 := f_pos σ (c + δ) hσ hT
  have h3 := f_pos σ c hσ hT
  rw [sum_eq _ _ hσ, sum_eq _ _ hσ, sum_eq _ _ hσ, Real.mul_rpow hK.le h2.le,
      Real.mul_rpow hK.le h3.le]
  have hKK : (σ * √(2 * π)) ^ a * (σ * √(2 * π)) ^ (1 - a) = σ * √(2 * π) := by
    rw [← Real.rpow_add hK]; simp
  rw [show (σ * √(2 * π)) ^ a * f σ (c + δ) ^ a * ((σ * √(2 * π)) ^ (1 - a) * f σ c ^ (1 - a)) =
      ((σ * √(2 * π)) ^ a * (σ * √(2 * π)) ^ (1 - a)) *
          (f σ (c + δ) ^ a * f σ c ^ (1 - a)) by ring, hKK,
    mul_div_mul_left _ _ hK.ne',
    show Real.log (f σ (c + a * δ)) - a * Real.log (f σ (c + δ)) - (1 - a) * Real.log (f σ c) =
      Real.log (f σ (c + a * δ)) -
          (Real.log (f σ (c + δ)) * a + Real.log (f σ c) * (1 - a)) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_log h1, ← Real.rpow_def_of_pos h2,
        ← Real.rpow_def_of_pos h3]

/-- The second difference is a Taylor remainder: `|Δ| ≤ M a(a+1)δ²/2`. -/
theorem abs_delta_le (σ c δ a : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (ha : 0 ≤ a) :
    |Real.log (f σ (c + a * δ)) - a * Real.log (f σ (c + δ)) - (1 - a) * Real.log (f σ c)| ≤
      M σ * (a * (a + 1)) * δ ^ 2 / 2 := by
  have hT' := fun x h => FalconPrecision.Taylor2.abs_sub_le_of_abs_deriv2_le
    (g := fun v => Real.log (f σ v)) (g' := fun v => f₁ σ v / f σ v)
    (g'' := fun v => (f₂ σ v * f σ v - f₁ σ v * f₁ σ v) / f σ v ^ 2)
    (hasDerivAt_log_f σ hσ hT) (hasDerivAt_f₁_div_f σ hσ hT) (abs_deriv2_log_f_le σ hσ hT) x h
  have hA := hT' c (a * δ)
  have hB := hT' c δ
  have hid : Real.log (f σ (c + a * δ)) - a * Real.log (f σ (c + δ)) - (1 - a) * Real.log (f σ c) =
      (Real.log (f σ (c + a * δ)) - Real.log (f σ c) - a * δ * (f₁ σ c / f σ c)) -
        a * (Real.log (f σ (c + δ)) - Real.log (f σ c) - δ * (f₁ σ c / f σ c)) := by ring
  rw [hid]
  calc _ ≤ |Real.log (f σ (c + a * δ)) - Real.log (f σ c) - a * δ * (f₁ σ c / f σ c)| +
        |a * (Real.log (f σ (c + δ)) - Real.log (f σ c) - δ * (f₁ σ c / f σ c))| := abs_sub _ _
    _ ≤ M σ * (a * δ) ^ 2 / 2 + a * (M σ * δ ^ 2 / 2) := by
        rw [abs_mul, abs_of_nonneg ha]; gcongr
    _ = _ := by ring

/-- **Lemma 4, explicit.** -/
theorem renyiDiv_shift_le (σ c δ a : ℝ) (hσ : 0 < σ) (ha : 1 < a) (hT : tail σ < 1) :
    renyiDiv a (discreteGaussianMeasure σ (c + δ)) (discreteGaussianMeasure σ c) ≤
      ENNReal.ofReal
          (Real.exp (a * δ ^ 2 / (2 * σ ^ 2) + a * (a + 1) * δ ^ 2 * M σ / (2 * (a - 1)))) := by
  have ha0 : 0 ≤ a := by linarith
  have ham : 0 < a - 1 := by linarith
  rw [renyiDiv_eq_rpow ha,
      FalconPrecision.RenyiShift.renyiMGF_discreteGaussian_shift σ c δ a hσ ha0, mul_div_assoc,
    ratio_eq σ c δ a hσ hT, ← Real.exp_add]
  have hΔ := (le_abs_self _).trans (abs_delta_le σ c δ a hσ hT ha0)
  calc ENNReal.ofReal (Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2) +
        (Real.log (f σ (c + a * δ)) - a * Real.log (f σ (c + δ)) - (1 - a) * Real.log (f σ c)))) ^
            (a - 1)⁻¹
      ≤ ENNReal.ofReal
          (Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2) + M σ * (a * (a + 1)) * δ ^ 2 / 2)) ^
          (a - 1)⁻¹ := by
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 ham.le), ← Real.exp_mul]
        congr 2
        field_simp

end FalconPrecision.Lemma4
