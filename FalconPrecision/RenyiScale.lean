/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.RenyiShift

/-! # Rényi divergence between discrete Gaussians of different widths

Eq. (55) of ePrint 2026/1531 (Appendix B.3): with `τᵢ = 1/σᵢ²` and `τ' = aτ₂ + (1-a)τ₁ > 0`, `∑_x
D_{σ₂,c}(x)^a D_{σ₁,c}(x)^(1-a) = ρ_{1/√τ'}(Z-c) / (ρσ₂(Z-c)^a ρσ₁(Z-c)^(1-a))`. -/

@[expose] public section

open Real MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.RenyiScale

/-- The Hellinger weight of two Gaussian weights with the same center is a Gaussian weight. -/
theorem weight_rpow_mul_weight_rpow (σ₁ σ₂ σ' c a : ℝ) (hσ₁ : σ₁ ≠ 0) (hσ₂ : σ₂ ≠ 0) (hσ' : σ' ≠ 0)
    (h : 1 / σ' ^ 2 = a / σ₂ ^ 2 + (1 - a) / σ₁ ^ 2) (x : ℤ) :
    discreteGaussianWeight σ₂ c x ^ a * discreteGaussianWeight σ₁ c x ^ (1 - a) =
      discreteGaussianWeight σ' c x := by
  simp only [discreteGaussianWeight, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  have : -(↑x - c) ^ 2 / (2 * σ' ^ 2) = -(↑x - c) ^ 2 / 2 * (1 / σ' ^ 2) := by field_simp
  rw [this, h]
  field_simp
  ring

/-- **Eq. (55).** The Hellinger sum of two discrete Gaussians of widths `σ₂`, `σ₁` (eq. (55)). -/
theorem tsum_pmf_rpow_mul_pmf_rpow (σ₁ σ₂ σ' c a : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hσ' : 0 < σ')
    (h : 1 / σ' ^ 2 = a / σ₂ ^ 2 + (1 - a) / σ₁ ^ 2) :
    ∑' x : ℤ, discreteGaussianPMF σ₂ c x ^ a * discreteGaussianPMF σ₁ c x ^ (1 - a) =
      discreteGaussianSum σ' c /
          (discreteGaussianSum σ₂ c ^ a * discreteGaussianSum σ₁ c ^ (1 - a)) := by
  have hS : ∀ σ, 0 < σ → 0 < discreteGaussianSum σ c := fun σ hσ => discreteGaussianSum_pos σ c hσ
  have hp : ∀ x : ℤ, discreteGaussianPMF σ₂ c x ^ a * discreteGaussianPMF σ₁ c x ^ (1 - a) =
      discreteGaussianWeight σ' c x /
          (discreteGaussianSum σ₂ c ^ a * discreteGaussianSum σ₁ c ^ (1 - a)) :=
    fun x => by
      simp only [discreteGaussianPMF]
      rw [Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (hS _ hσ₂).le,
        Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (hS _ hσ₁).le, div_mul_div_comm,
        weight_rpow_mul_weight_rpow σ₁ σ₂ σ' c a hσ₁.ne' hσ₂.ne' hσ'.ne' h]
  rw [tsum_congr hp, tsum_div_const]
  rfl

/-- **Eq. (55), closed form.** The Rényi MGF between discrete Gaussians of widths `σ₂`, `σ₁` and the
same center. -/
theorem renyiMGF_discreteGaussian_scale (σ₁ σ₂ σ' c a : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hσ' : 0 < σ')
    (ha : 0 ≤ a) (h : 1 / σ' ^ 2 = a / σ₂ ^ 2 + (1 - a) / σ₁ ^ 2) :
    renyiMGF a (discreteGaussianMeasure σ₂ c) (discreteGaussianMeasure σ₁ c) =
      ENNReal.ofReal (discreteGaussianSum σ' c /
        (discreteGaussianSum σ₂ c ^ a * discreteGaussianSum σ₁ c ^ (1 - a))) := by
  have := isProbabilityMeasure_discreteGaussianMeasure σ₁ c hσ₁
  have hpos : ∀ σ, 0 < σ → ∀ x : ℤ, 0 < discreteGaussianPMF σ c x := fun σ hσ x =>
    discreteGaussianPMF_pos σ c hσ x
  have hp : ∀ x : ℤ, discreteGaussianPMF σ₂ c x ^ a * discreteGaussianPMF σ₁ c x ^ (1 - a) =
      discreteGaussianWeight σ' c x /
          (discreteGaussianSum σ₂ c ^ a * discreteGaussianSum σ₁ c ^ (1 - a)) :=
    fun x => by
      simp only [discreteGaussianPMF]
      rw [Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (discreteGaussianSum_pos σ₂ c hσ₂).le,
        Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (discreteGaussianSum_pos σ₁ c hσ₁).le,
        div_mul_div_comm, weight_rpow_mul_weight_rpow σ₁ σ₂ σ' c a hσ₁.ne' hσ₂.ne' hσ'.ne' h]
  rw [FalconPrecision.RenyiShift.renyiMGF_eq_tsum_of_pos ha _ _
      (fun x => (discreteGaussianMeasure_singleton_pos σ₁ c hσ₁ x).ne')
    (fun x => measure_ne_top _ _), ← tsum_pmf_rpow_mul_pmf_rpow σ₁ σ₂ σ' c a hσ₁ hσ₂ hσ' h,
    ENNReal.ofReal_tsum_of_nonneg
      (fun x => mul_nonneg (Real.rpow_nonneg (hpos _ hσ₂ x).le _)
          (Real.rpow_nonneg (hpos _ hσ₁ x).le _))]
  · refine tsum_congr fun x => ?_
    rw [discreteGaussianMeasure_singleton, discreteGaussianMeasure_singleton,
      ENNReal.ofReal_rpow_of_pos (hpos _ hσ₂ x), ENNReal.ofReal_rpow_of_pos (hpos _ hσ₁ x),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hpos _ hσ₂ x).le _)]
  · exact ((discreteGaussianSum_summable σ' c hσ').div_const _).congr fun x => (hp x).symm

end FalconPrecision.RenyiScale
