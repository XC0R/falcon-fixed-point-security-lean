/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import LatticeCrypto.DiscreteGaussian
public import ToMathlib.Probability.Divergence.Renyi

/-! # Rényi divergence between shifted discrete Gaussians

The exact identity behind Lemma 4 of De Almeida Braga, Fouque, Lachguel, Prest, "Toward a Secure
Fixed-Point Implementation of the Falcon Signature Scheme" (ePrint 2026/1531, Appendix B.2, eq.
(52)): for `a > 1`,

`∑_x D_{σ,c+δ}(x)^a D_{σ,c}(x)^(1-a) = exp(a(a-1)δ²/(2σ²)) · ρσ(Z-c-aδ) / (ρσ(Z-c-δ)^a
ρσ(Z-c)^(1-a))`. -/

@[expose] public section

open Real MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.RenyiShift

/--
Completing the square: the Hellinger weight of two shifted Gaussian weights is a Gaussian weight at
the `a`-shifted center. -/
theorem weight_rpow_mul_weight_rpow (σ c δ a : ℝ) (x : ℤ) :
    discreteGaussianWeight σ (c + δ) x ^ a * discreteGaussianWeight σ c x ^ (1 - a) =
      Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianWeight σ (c + a * δ) x := by
  simp only [discreteGaussianWeight, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Pointwise form of eq. (52). -/
theorem pmf_rpow_mul_pmf_rpow (σ c δ a : ℝ) (hσ : 0 < σ) (x : ℤ) :
    discreteGaussianPMF σ (c + δ) x ^ a * discreteGaussianPMF σ c x ^ (1 - a) =
      Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianWeight σ (c + a * δ) x /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a)) := by
  have hS : ∀ μ, 0 < discreteGaussianSum σ μ := fun μ => discreteGaussianSum_pos σ μ hσ
  simp only [discreteGaussianPMF]
  rw [Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (hS _).le,
    Real.div_rpow (discreteGaussianWeight_nonneg _ _ _) (hS _).le, div_mul_div_comm,
    weight_rpow_mul_weight_rpow]

/-- The Hellinger sum of two shifted discrete Gaussian PMFs (eq. (52)). -/
theorem tsum_pmf_rpow_mul_pmf_rpow (σ c δ a : ℝ) (hσ : 0 < σ) :
    ∑' x : ℤ, discreteGaussianPMF σ (c + δ) x ^ a * discreteGaussianPMF σ c x ^ (1 - a) =
      Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianSum σ (c + a * δ) /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a)) := by
  rw [tsum_congr (pmf_rpow_mul_pmf_rpow σ c δ a hσ), tsum_div_const, tsum_mul_left]
  rfl

/--
On a countable space, the Rényi MGF of order `a ≥ 0` is the Hellinger sum of the point masses, when
the second measure charges every point finitely. -/
theorem renyiMGF_eq_tsum_of_pos {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α]
    {a : ℝ} (ha : 0 ≤ a) (μ ν : Measure α) [SigmaFinite ν] (hν0 : ∀ x, ν {x} ≠ 0)
    (hν : ∀ x, ν {x} ≠ ⊤) :
    renyiMGF a μ ν = ∑' x, μ {x} ^ a * ν {x} ^ (1 - a) := by
  have hac : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s _ h0 => ?_
    have : s = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
      hν0 x (measure_mono_null (Set.singleton_subset_iff.2 hx) h0)
    simp [this]
  have hwd : ν.withDensity (fun x => μ {x} / ν {x}) = μ := by
    refine Measure.ext_of_singleton fun x => ?_
    rw [withDensity_apply _ (measurableSet_singleton x), Measure.restrict_singleton,
        lintegral_smul_measure,
      lintegral_dirac, smul_eq_mul, mul_comm, ENNReal.div_mul_cancel (hν0 x) (hν x)]
  have hrn : μ.rnDeriv ν =ᵐ[ν] fun x => μ {x} / ν {x} := by
    conv_lhs => rw [← hwd]
    exact Measure.rnDeriv_withDensity ν (measurable_of_countable _)
  rw [renyiMGF_of_ac hac, lintegral_congr_ae (hrn.mono fun x hx => by rw [hx]),
      lintegral_countable']
  refine tsum_congr fun x => ?_
  rw [ENNReal.div_rpow_of_nonneg _ _ ha, ENNReal.rpow_sub _ _ (hν0 x) (hν x), ENNReal.rpow_one]
  simp only [div_eq_mul_inv]
  ring

/-- **Eq. (52).** The Rényi MGF between shifted discrete Gaussians, in closed form. -/
theorem renyiMGF_discreteGaussian_shift (σ c δ a : ℝ) (hσ : 0 < σ) (ha : 0 ≤ a) :
    renyiMGF a (discreteGaussianMeasure σ (c + δ)) (discreteGaussianMeasure σ c) =
      ENNReal.ofReal
          (Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianSum σ (c + a * δ) /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a))) := by
  have := isProbabilityMeasure_discreteGaussianMeasure σ c hσ
  have hpos : ∀ μ (x : ℤ), 0 < discreteGaussianPMF σ μ x :=
      fun μ x => discreteGaussianPMF_pos σ μ hσ x
  rw [renyiMGF_eq_tsum_of_pos ha _ _ (fun x => (discreteGaussianMeasure_singleton_pos σ c hσ x).ne')
    (fun x => measure_ne_top _ _), ← tsum_pmf_rpow_mul_pmf_rpow σ c δ a hσ,
    ENNReal.ofReal_tsum_of_nonneg
      (fun x => mul_nonneg (Real.rpow_nonneg (hpos _ x).le _) (Real.rpow_nonneg (hpos _ x).le _))]
  · refine tsum_congr fun x => ?_
    rw [discreteGaussianMeasure_singleton, discreteGaussianMeasure_singleton,
      ENNReal.ofReal_rpow_of_pos (hpos _ x), ENNReal.ofReal_rpow_of_pos (hpos _ x),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hpos _ x).le _)]
  · refine Summable.congr ?_ (fun x => (pmf_rpow_mul_pmf_rpow σ c δ a hσ x).symm)
    exact ((discreteGaussianSum_summable σ (c + a * δ) hσ).mul_left _).div_const _

end FalconPrecision.RenyiShift
