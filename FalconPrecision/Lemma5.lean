/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.ThetaT
public import FalconPrecision.RenyiScale
public import FalconPrecision.Taylor2

/-! # Lemma 5 of ePrint 2026/1531 with an explicit constant

`ψ(τ) = -½ log τ + log G(c, 1/τ)` is `log ρ_{1/√τ}(Z - c)` up to the constant `½ log(2π)`. Its
second derivative is `1/(2τ²)` plus an explicit theta-tail correction. -/

@[expose] public section

open Real FalconPrecision.ThetaTail FalconPrecision.ThetaT

namespace FalconPrecision.Lemma5

noncomputable def ψ (c τ : ℝ) : ℝ := -(1 / 2) * Real.log τ + Real.log (G c τ⁻¹)

/-- `L' = G₁/G` and `L'' = (G₂G - G₁²)/G²` at `t`. -/
noncomputable def L₁ (c t : ℝ) : ℝ := G₁ c t / G c t
noncomputable def L₂ (c t : ℝ) : ℝ := (G₂ c t * G c t - G₁ c t * G₁ c t) / G c t ^ 2

noncomputable def ψ₁ (c τ : ℝ) : ℝ := -(1 / 2) * τ⁻¹ + L₁ c τ⁻¹ * (-(τ ^ 2)⁻¹)
noncomputable def ψ₂ (c τ : ℝ) : ℝ :=
  (1 / 2) * (τ ^ 2)⁻¹ + L₂ c τ⁻¹ * (-(τ ^ 2)⁻¹) * (-(τ ^ 2)⁻¹) + L₁ c τ⁻¹ * (2 * τ / (τ ^ 2) ^ 2)

theorem G_pos (c t : ℝ) (ht : 0 < t) (hT : tail (√t) < 1) : 0 < G c t := by
  linarith [(G_mem c t ht).1]

theorem hasDerivAt_ψ (c τ : ℝ) (hτ : 0 < τ) (hT : tail (√τ⁻¹) < 1) : HasDerivAt (ψ c) (ψ₁ c τ) τ :=
    by
  have hinv := hasDerivAt_inv hτ.ne'
  have hG := (hasDerivAt_G c τ⁻¹ (inv_pos.2 hτ)).comp τ hinv
  have hlog := hG.log (G_pos c τ⁻¹ (inv_pos.2 hτ) hT).ne'
  have := ((Real.hasDerivAt_log hτ.ne').const_mul (-(1 / 2))).add hlog
  convert this using 1
  · funext y; simp only [ψ, Pi.add_apply, Function.comp_def]
  · simp only [ψ₁, L₁, Function.comp_def]; ring

theorem hasDerivAt_L₁ (c t : ℝ) (ht : 0 < t) (hT : tail (√t) < 1) : HasDerivAt (L₁ c) (L₂ c t) t :=
    by
  exact (hasDerivAt_G₁ c t ht).div (hasDerivAt_G c t ht) (G_pos c t ht hT).ne'

theorem hasDerivAt_ψ₁ (c τ : ℝ) (hτ : 0 < τ) (hT : tail (√τ⁻¹) < 1) : HasDerivAt (ψ₁ c)
    (ψ₂ c τ) τ := by
  have hinv := hasDerivAt_inv hτ.ne'
  have hL := (hasDerivAt_L₁ c τ⁻¹ (inv_pos.2 hτ) hT).comp τ hinv
  have hsq : HasDerivAt (fun y : ℝ => -(y ^ 2)⁻¹) (2 * τ / (τ ^ 2) ^ 2) τ := by
    have := ((hasDerivAt_pow 2 τ).inv (by positivity)).neg
    convert this using 1; push_cast; ring
  have := (hinv.const_mul (-(1 / 2))).add (hL.mul hsq)
  convert this using 1
  · funext y; simp only [ψ₁, Pi.add_apply, Pi.mul_apply, Function.comp_def]
  · simp only [ψ₂, Function.comp_def]; ring

/-- The correction to `ψ'' = 1/(2τ²)`. -/
theorem abs_ψ₂_sub_le (c τ : ℝ) (hτ : 0 < τ) :
    |ψ₂ c τ - (1 / 2) * (τ ^ 2)⁻¹| ≤ |L₂ c τ⁻¹| * ((τ ^ 2)⁻¹) ^ 2 + |L₁ c τ⁻¹| *
        (2 * τ / (τ ^ 2) ^ 2) := by
  have h : ψ₂ c τ - (1 / 2) * (τ ^ 2)⁻¹ =
      L₂ c τ⁻¹ * ((τ ^ 2)⁻¹) ^ 2 + L₁ c τ⁻¹ * (2 * τ / (τ ^ 2) ^ 2) := by simp only [ψ₂]; ring
  rw [h]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((τ ^ 2)⁻¹) ^ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * τ / (τ ^ 2) ^ 2)]

theorem abs_L₁_le (c t : ℝ) (ht : 0 < t)
    (hT : tail (√t) < 1) : |L₁ c t| ≤ V₁ t / (1 - tail (√t)) := by
  have hG := G_mem c t ht
  rw [L₁, abs_div, abs_of_pos (G_pos c t ht hT)]
  exact div_le_div₀ (le_trans (abs_nonneg _) (abs_G₁_le c t ht)) (abs_G₁_le c t ht)
      (by linarith) hG.1

theorem abs_L₂_le (c t : ℝ) (ht : 0 < t) (hT : tail (√t) < 1) :
    |L₂ c t| ≤ (V₂ t * (1 + tail (√t)) + V₁ t ^ 2) / (1 - tail (√t)) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := G_mem c t ht
  have hG := G_pos c t ht hT
  have h1 := abs_G₁_le c t ht
  have h2 := abs_G₂_le c t ht
  have hV1 : 0 ≤ V₁ t := le_trans (abs_nonneg _) h1
  have hV2 : 0 ≤ V₂ t := le_trans (abs_nonneg _) h2
  rw [L₂, abs_div, abs_of_pos (by positivity : 0 < G c t ^ 2)]
  have hnum : |G₂ c t * G c t - G₁ c t * G₁ c t| ≤ V₂ t * (1 + tail (√t)) + V₁ t ^ 2 := by
    calc |G₂ c t * G c t - G₁ c t * G₁ c t| ≤ |G₂ c t| * |G c t| + |G₁ c t| * |G₁ c t| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ V₂ t * (1 + tail (√t)) + V₁ t * V₁ t :=
          add_le_add (mul_le_mul h2 (by rw [abs_of_pos hG]; exact hhi) (abs_nonneg _) hV2)
            (mul_le_mul h1 h1 (abs_nonneg _) hV1)
      _ = _ := by ring
  have hden : (1 - tail (√t)) ^ 2 ≤ G c t ^ 2 := by
    have : 0 ≤ 1 - tail (√t) := by linarith
    gcongr
  exact div_le_div₀ (le_trans (abs_nonneg _) hnum) hnum (by nlinarith) hden

theorem log_sum_eq (c τ : ℝ) (hτ : 0 < τ) (hT : tail (√τ⁻¹) < 1) :
    Real.log (LatticeCrypto.discreteGaussianSum (1 / √τ) c) = ψ c τ + (1 / 2) * Real.log (2 * π) :=
        by
  have hσ : 0 < 1 / √τ := by positivity
  have hS : LatticeCrypto.discreteGaussianSum (1 / √τ) c = 1 / √τ * √(2 * π) * G c τ⁻¹ := by
    rw [discreteGaussianSum_eq_fourier _ _ hσ, show τ⁻¹ = (1 / √τ) ^ 2 by
      rw [div_pow, one_pow, Real.sq_sqrt hτ.le, one_div], G_eq_f]
    rfl
  have hG := G_pos c τ⁻¹ (inv_pos.2 hτ) hT
  rw [hS, Real.log_mul (by positivity) hG.ne', Real.log_mul (by positivity)
      (by positivity), one_div,
    Real.log_inv, Real.log_sqrt hτ.le, Real.log_sqrt (by positivity), ψ]
  ring

/-- **Lemma 5, explicit.** With `τᵢ = 1/σᵢ²` and `|ψ''| ≤ K` on the segment `[τ₁, τ₁ + a(τ₂ - τ₁)]`:
`Rₐ(D_{σ₂,c} ‖ D_{σ₁,c}) ≤ exp(a(a+1)(τ₂ - τ₁)² K / (2(a-1)))`. -/
theorem renyiDiv_scale_le (σ₁ σ₂ c a K : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (ha : 1 < a)
    (hseg : ∀ τ ∈ Set.uIcc (1 / σ₁ ^ 2) (1 / σ₁ ^ 2 + a * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2)),
      0 < τ ∧ tail (√τ⁻¹) < 1 ∧ |ψ₂ c τ| ≤ K) :
    InformationTheory.renyiDiv a (LatticeCrypto.discreteGaussianMeasure σ₂ c)
        (LatticeCrypto.discreteGaussianMeasure σ₁ c) ≤
      ENNReal.ofReal
          (Real.exp (a * (a + 1) * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ^ 2 * K / (2 * (a - 1)))) := by
  set τ₁ := 1 / σ₁ ^ 2 with hτ₁
  set s := 1 / σ₂ ^ 2 - 1 / σ₁ ^ 2 with hs
  have ha0 : 0 ≤ a := by linarith
  have ham : 0 < a - 1 := by linarith
  have hend : τ₁ + a * s ∈ Set.uIcc τ₁ (τ₁ + a * s) := Set.right_mem_uIcc
  have hstart : τ₁ ∈ Set.uIcc τ₁ (τ₁ + a * s) := Set.left_mem_uIcc
  have hsub : Set.uIcc τ₁ (τ₁ + s) ⊆ Set.uIcc τ₁ (τ₁ + a * s) := by
    apply Set.uIcc_subset_uIcc hstart
    rcases le_total 0 s with h | h
    · rw [Set.uIcc_of_le (by nlinarith)]; constructor <;> nlinarith
    · rw [Set.uIcc_of_ge (by nlinarith)]; constructor <;> nlinarith
  obtain ⟨hτ', hT', -⟩ := hseg _ hend
  obtain ⟨hτ₁0, hT₁, -⟩ := hseg _ hstart
  obtain ⟨hτ₂0, hT₂, -⟩ := hseg _ (hsub Set.right_mem_uIcc)
  set σ' := 1 / √(τ₁ + a * s) with hσ'
  have hσ'0 : 0 < σ' := by positivity
  have hh : 1 / σ' ^ 2 = a / σ₂ ^ 2 + (1 - a) / σ₁ ^ 2 := by
    rw [hσ', div_pow, Real.sq_sqrt hτ'.le, one_pow, one_div_one_div, hτ₁, hs]; ring
  have hσ₁' : σ₁ = 1 / √τ₁ := by
    rw [hτ₁, one_div (σ₁ ^ 2), Real.sqrt_inv, Real.sqrt_sq hσ₁.le, one_div, inv_inv]
  have hσ₂' : σ₂ = 1 / √(τ₁ + s) := by
    rw [hτ₁, hs, add_sub_cancel, one_div (σ₂ ^ 2), Real.sqrt_inv, Real.sqrt_sq hσ₂.le, one_div,
        inv_inv]
  have hpos : ∀ σ, 0 < σ → 0 < LatticeCrypto.discreteGaussianSum σ c := fun σ h =>
    LatticeCrypto.discreteGaussianSum_pos σ c h
  -- the ratio is exp Δ
  have hratio : LatticeCrypto.discreteGaussianSum σ' c /
      (LatticeCrypto.discreteGaussianSum σ₂ c ^ a *
          LatticeCrypto.discreteGaussianSum σ₁ c ^ (1 - a)) =
      Real.exp (ψ c (τ₁ + a * s) - a * ψ c (τ₁ + s) - (1 - a) * ψ c τ₁) := by
    have h1 := log_sum_eq c _ hτ' hT'
    have h2 := log_sum_eq c _ hτ₂0 hT₂
    have h3 := log_sum_eq c _ hτ₁0 hT₁
    rw [← hσ'] at h1; rw [← hσ₂'] at h2; rw [← hσ₁'] at h3
    rw [← Real.exp_log (div_pos (hpos _ hσ'0) (mul_pos (Real.rpow_pos_of_pos (hpos _ hσ₂) _)
      (Real.rpow_pos_of_pos (hpos _ hσ₁) _))), Real.log_div (hpos _ hσ'0).ne'
      (mul_pos (Real.rpow_pos_of_pos (hpos _ hσ₂) _) (Real.rpow_pos_of_pos (hpos _ hσ₁) _)).ne',
      Real.log_mul (Real.rpow_pos_of_pos (hpos _ hσ₂) _).ne'
          (Real.rpow_pos_of_pos (hpos _ hσ₁) _).ne',
      Real.log_rpow (hpos _ hσ₂), Real.log_rpow (hpos _ hσ₁), h1, h2, h3]
    congr 1; ring
  -- Taylor
  have hT := fun h (hh' : Set.uIcc τ₁ (τ₁ + h) ⊆ Set.uIcc τ₁ (τ₁ + a * s)) =>
    FalconPrecision.Taylor2.abs_sub_le_of_abs_deriv2_le_on (g := ψ c) (g' := ψ₁ c) (g'' := ψ₂ c)
        (M := K) (x := τ₁)
      (h := h) (fun y hy => hasDerivAt_ψ c y (hseg y (hh' hy)).1 (hseg y (hh' hy)).2.1)
      (fun y hy => hasDerivAt_ψ₁ c y (hseg y (hh' hy)).1 (hseg y (hh' hy)).2.1)
      (fun y hy => (hseg y (hh' hy)).2.2)
  have hA := hT (a * s) le_rfl
  have hB := hT s hsub
  have hΔ : ψ c (τ₁ + a * s) - a * ψ c (τ₁ + s) - (1 - a) * ψ c τ₁ ≤ K * (a * (a + 1)) * s ^ 2 /
      2 := by
    have hid : ψ c (τ₁ + a * s) - a * ψ c (τ₁ + s) - (1 - a) * ψ c τ₁ =
        (ψ c (τ₁ + a * s) - ψ c τ₁ - a * s * ψ₁ c τ₁) - a *
            (ψ c (τ₁ + s) - ψ c τ₁ - s * ψ₁ c τ₁) := by ring
    rw [hid]
    have := abs_le.1 hA; have := abs_le.1 hB
    nlinarith
  rw [InformationTheory.renyiDiv_eq_rpow ha,
      RenyiScale.renyiMGF_discreteGaussian_scale σ₁ σ₂ σ' c a hσ₁ hσ₂
    hσ'0 ha0 hh, hratio]
  calc ENNReal.ofReal (Real.exp (ψ c (τ₁ + a * s) - a * ψ c (τ₁ + s) - (1 - a) * ψ c τ₁)) ^
      (a - 1)⁻¹
      ≤ ENNReal.ofReal (Real.exp (K * (a * (a + 1)) * s ^ 2 / 2)) ^ (a - 1)⁻¹ := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 ham.le), ← Real.exp_mul]
        congr 2; field_simp

end FalconPrecision.Lemma5
