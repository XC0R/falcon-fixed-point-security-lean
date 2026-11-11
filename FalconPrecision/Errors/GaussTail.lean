/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.NumTail
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Sub-Gaussian tails of the discrete Gaussian

For `z ~ D_{Z,σ,c}` (`discreteGaussianMeasure σ c`) and real `s`, completing the square gives
`E[exp(s(z - c))] = exp(σ²s²/2)·S(σ, c + σ²s)/S(σ, c)` (`tsum_pmf_mul_exp`), and the Fourier bounds
of `ThetaTail` give `E[exp(s(z - c))] ≤ κ(σ)·exp(σ²s²/2)` with `κ(σ) = (1 + T(σ))/(1 - T(σ))`
(`lintegral_exp_le`). Chernoff then gives `P[z ≥ c + r] ≤ κ(σ)·exp(-r²/(2σ²))`, the same below `c -
r`, and `P[|z - c| ≥ r] ≤ 2κ(σ)·exp(-r²/(2σ²))` (`measure_abs_ge_le`). For `σ ≥ 1.277`, `κ(σ) ≤ 1 +
2⁻³⁶` (`kappa_falcon`). This is the one-coordinate form of Lemma 1 of ePrint 2026/1531 ([Lyu12,
Lemma 4.3]) for a discrete Gaussian at any centre, with the factor `κ(σ)`; it does not treat inner
products of several samples. -/

@[expose] public section

open Real MeasureTheory LatticeCrypto FalconPrecision.ThetaTail
open scoped ENNReal

namespace FalconPrecision.Errors.GaussTail

/-- `κ(σ) = (1 + T(σ))/(1 - T(σ))`. -/
noncomputable def kappa (σ : ℝ) : ℝ := (1 + tail σ) / (1 - tail σ)

theorem tail_nonneg (σ : ℝ) (hσ : 0 < σ) : 0 ≤ tail σ := by
  obtain ⟨h1, h2⟩ := discreteGaussianSum_mem σ 0 hσ
  have := le_of_mul_le_mul_left (h1.trans h2) (by positivity)
  linarith

theorem kappa_pos (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) : 0 < kappa σ :=
  div_pos (by linarith [tail_nonneg σ hσ]) (by linarith)

theorem weight_mul_exp (σ c s : ℝ) (hσ : 0 < σ) (z : ℤ) :
    discreteGaussianWeight σ c z * Real.exp (s * (z - c)) =
      Real.exp (σ ^ 2 * s ^ 2 / 2) * discreteGaussianWeight σ (c + σ ^ 2 * s) z := by
  have : σ ≠ 0 := hσ.ne'
  simp only [discreteGaussianWeight, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem pmf_mul_exp (σ c s : ℝ) (hσ : 0 < σ) (z : ℤ) :
    discreteGaussianPMF σ c z * Real.exp (s * (z - c)) =
      Real.exp (σ ^ 2 * s ^ 2 / 2) * discreteGaussianWeight σ (c + σ ^ 2 * s) z /
        discreteGaussianSum σ c := by
  rw [discreteGaussianPMF, div_mul_eq_mul_div, weight_mul_exp σ c s hσ]

theorem summable_pmf_mul_exp (σ c s : ℝ) (hσ : 0 < σ) :
    Summable fun z : ℤ => discreteGaussianPMF σ c z * Real.exp (s * (z - c)) :=
  (((discreteGaussianSum_summable σ (c + σ ^ 2 * s) hσ).mul_left
    (Real.exp (σ ^ 2 * s ^ 2 / 2))).div_const (discreteGaussianSum σ c)).congr
      fun z => (pmf_mul_exp σ c s hσ z).symm

/-- **Moment generating function** of `z - c`, `z ~ D_{Z,σ,c}`. -/
theorem tsum_pmf_mul_exp (σ c s : ℝ) (hσ : 0 < σ) :
    ∑' z : ℤ, discreteGaussianPMF σ c z * Real.exp (s * (z - c)) =
      Real.exp (σ ^ 2 * s ^ 2 / 2) * discreteGaussianSum σ (c + σ ^ 2 * s) /
        discreteGaussianSum σ c := by
  rw [tsum_congr (pmf_mul_exp σ c s hσ), tsum_div_const, tsum_mul_left]
  rfl

/-- Normalizers at two centres differ by at most the factor `κ(σ)`. -/
theorem sum_div_sum_le (σ c u : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) :
    discreteGaussianSum σ u / discreteGaussianSum σ c ≤ kappa σ := by
  have h1 := (discreteGaussianSum_mem σ u hσ).2
  have h2 := (discreteGaussianSum_mem σ c hσ).1
  have h0 : 0 < 1 - tail σ := by linarith
  rw [div_le_iff₀ (discreteGaussianSum_pos σ c hσ)]
  calc discreteGaussianSum σ u ≤ σ * √(2 * π) * (1 + tail σ) := h1
    _ = kappa σ * (σ * √(2 * π) * (1 - tail σ)) := by rw [kappa]; field_simp
    _ ≤ kappa σ * discreteGaussianSum σ c := mul_le_mul_of_nonneg_left h2 (kappa_pos σ hσ hT).le

theorem lintegral_exp_eq (σ c s : ℝ) (hσ : 0 < σ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (s * (z - c))) ∂discreteGaussianMeasure σ c =
      ENNReal.ofReal (∑' z : ℤ, discreteGaussianPMF σ c z * Real.exp (s * (z - c))) := by
  rw [discreteGaussianMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (measurable_of_countable _), lintegral_count, ENNReal.ofReal_tsum_of_nonneg
    (fun z => mul_nonneg (discreteGaussianPMF_nonneg σ c hσ z) (Real.exp_pos _).le)
    (summable_pmf_mul_exp σ c s hσ)]
  refine tsum_congr fun z => ?_
  rw [Pi.mul_apply, ENNReal.ofReal_mul (discreteGaussianPMF_nonneg σ c hσ z)]

/-- **Sub-Gaussian moment bound**: `E[exp(s(z - c))] ≤ κ(σ)·exp(σ²s²/2)`, `z ~ D_{Z,σ,c}`. -/
theorem lintegral_exp_le (σ c s : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (s * (z - c))) ∂discreteGaussianMeasure σ c ≤
      ENNReal.ofReal (kappa σ * Real.exp (σ ^ 2 * s ^ 2 / 2)) := by
  rw [lintegral_exp_eq σ c s hσ, tsum_pmf_mul_exp σ c s hσ]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_div_assoc, mul_comm (kappa σ)]
  exact mul_le_mul_of_nonneg_left (sum_div_sum_le σ c _ hσ hT) (Real.exp_pos _).le

/--
Chernoff from the moment bound: `P[A] ≤ κ(σ)·exp(σ²s²/2 - a)` when `exp(s(z - c)) ≥ exp a` on `A`.
-/
theorem measure_le_of_exp (σ c s a : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (A : Set ℤ)
    (hA : ∀ z ∈ A, a ≤ s * (z - c)) :
    discreteGaussianMeasure σ c A ≤ ENNReal.ofReal (kappa σ * Real.exp (σ ^ 2 * s ^ 2 / 2 - a)) :=
        by
  have hM := mul_meas_ge_le_lintegral₀ (μ := discreteGaussianMeasure σ c)
    (measurable_of_countable fun z : ℤ => ENNReal.ofReal (Real.exp (s * (z - c)))).aemeasurable
    (ENNReal.ofReal (Real.exp a))
  have hsub : A ⊆ {z : ℤ | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (s * (z - c)))} :=
    fun z hz => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hA z hz))
  have h1 : ENNReal.ofReal (Real.exp a) * discreteGaussianMeasure σ c A ≤
      ENNReal.ofReal (kappa σ * Real.exp (σ ^ 2 * s ^ 2 / 2)) :=
    (by gcongr : _ ≤ ENNReal.ofReal (Real.exp a) * _).trans
        (hM.trans (lintegral_exp_le σ c s hσ hT))
  have he : ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (Real.exp a) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc discreteGaussianMeasure σ c A
      = ENNReal.ofReal (Real.exp (-a)) *
          (ENNReal.ofReal (Real.exp a) * discreteGaussianMeasure σ c A) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-a)) *
          ENNReal.ofReal (kappa σ * Real.exp (σ ^ 2 * s ^ 2 / 2)) := by gcongr
    _ = ENNReal.ofReal (kappa σ * Real.exp (σ ^ 2 * s ^ 2 / 2 - a)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_left_comm, ← Real.exp_add, neg_add_eq_sub]

theorem exponent_eq (σ r : ℝ) (hσ : 0 < σ) :
    σ ^ 2 * (r / σ ^ 2) ^ 2 / 2 - r / σ ^ 2 * r = -(r ^ 2 / (2 * σ ^ 2)) := by
  have : σ ≠ 0 := hσ.ne'
  field_simp
  ring

/-- **Upper tail**: `P[z ≥ c + r] ≤ κ(σ)·exp(-r²/(2σ²))`. -/
theorem measure_ge_le (σ c r : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (hr : 0 ≤ r) :
    discreteGaussianMeasure σ c {z | c + r ≤ z} ≤
      ENNReal.ofReal (kappa σ * Real.exp (-(r ^ 2 / (2 * σ ^ 2)))) := by
  rw [← exponent_eq σ r hσ]
  refine measure_le_of_exp σ c (r / σ ^ 2) _ hσ hT _ fun z (hz : c + r ≤ z) => ?_
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **Lower tail**: `P[z ≤ c - r] ≤ κ(σ)·exp(-r²/(2σ²))`. -/
theorem measure_le_le (σ c r : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (hr : 0 ≤ r) :
    discreteGaussianMeasure σ c {z | (z : ℝ) ≤ c - r} ≤
      ENNReal.ofReal (kappa σ * Real.exp (-(r ^ 2 / (2 * σ ^ 2)))) := by
  have h := measure_le_of_exp σ c (-(r / σ ^ 2)) (r / σ ^ 2 * r) hσ hT {z | (z : ℝ) ≤ c - r}
    fun z (hz : (z : ℝ) ≤ c - r) => by
      rw [neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rwa [neg_sq, exponent_eq σ r hσ] at h

/-- **Two-sided tail**: `P[|z - c| ≥ r] ≤ 2κ(σ)·exp(-r²/(2σ²))`, `z ~ D_{Z,σ,c}`. -/
theorem measure_abs_ge_le (σ c r : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (hr : 0 ≤ r) :
    discreteGaussianMeasure σ c {z | r ≤ |(z : ℝ) - c|} ≤
      ENNReal.ofReal (2 * kappa σ * Real.exp (-(r ^ 2 / (2 * σ ^ 2)))) := by
  have hsub : {z : ℤ | r ≤ |(z : ℝ) - c|} ⊆ {z | c + r ≤ z} ∪ {z | (z : ℝ) ≤ c - r} :=
    fun z (hz : r ≤ |(z : ℝ) - c|) => by
      rcases le_abs'.1 hz with h | h
      · exact Or.inr (show (z : ℝ) ≤ c - r by linarith)
      · exact Or.inl (show c + r ≤ (z : ℝ) by linarith)
  have h0 : 0 ≤ kappa σ * Real.exp (-(r ^ 2 / (2 * σ ^ 2))) :=
    mul_nonneg (kappa_pos σ hσ hT).le (Real.exp_pos _).le
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_ge_le σ c r hσ hT hr) (measure_le_le σ c r hσ hT hr)).trans ?_
  rw [← ENNReal.ofReal_add h0 h0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Falcon instance**: for `σ ≥ 1.277`, `T(σ) < 1` and `κ(σ) ≤ 1 + 2⁻³⁶`. -/
theorem kappa_falcon (σ : ℝ) (hσ : 1277 / 1000 ≤ σ) : tail σ < 1 ∧ kappa σ ≤ 1 + 1 / 2 ^ 36 := by
  have hσ0 : 0 < σ := by linarith
  have hT :=
      (FalconPrecision.NumTail.tails_le σ (1 / 2 ^ 40) hσ0 (FalconPrecision.NumTail.exp_bound σ hσ)
    (by norm_num)).1
  have hT' : tail σ ≤ 1 / 2 ^ 38 := hT.trans (by norm_num)
  refine ⟨by linarith, ?_⟩
  rw [kappa, div_le_iff₀ (by linarith)]
  nlinarith [hT', tail_nonneg σ hσ0]

/-- **Falcon leaves**: `P[|z - c| ≥ r] ≤ 2(1 + 2⁻³⁶)·exp(-r²/(2σ²))` for `σ ≥ 1.277`. -/
theorem measure_abs_ge_falcon (σ c r : ℝ) (hσ : 1277 / 1000 ≤ σ) (hr : 0 ≤ r) :
    discreteGaussianMeasure σ c {z | r ≤ |(z : ℝ) - c|} ≤
      ENNReal.ofReal (2 * (1 + 1 / 2 ^ 36) * Real.exp (-(r ^ 2 / (2 * σ ^ 2)))) := by
  obtain ⟨hT, hk⟩ := kappa_falcon σ hσ
  refine (measure_abs_ge_le σ c r (by linarith) hT hr).trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

end FalconPrecision.Errors.GaussTail
