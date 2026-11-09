/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import LatticeCrypto.DiscreteGaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Fourier form of the discrete Gaussian normalizer

Poisson summation turns `ρσ(Z - u) = ∑ₙ exp(-(n-u)²/(2σ²))` into `σ√(2π) ∑ₙ exp(-2π²σ²n²)
cos(2πnu)`: the normalizer is `σ√(2π)` up to an explicit theta tail. -/

@[expose] public section

open Real Complex LatticeCrypto

namespace FalconPrecision.ThetaTail

theorem weight_eq_cexp (σ u : ℝ) (hσ : 0 < σ) (n : ℤ) :
    (discreteGaussianWeight σ u n : ℂ) =
      cexp (-(u ^ 2 / (2 * σ ^ 2) : ℝ)) *
        cexp (-π * ((2 * π * σ ^ 2)⁻¹ : ℝ) * n ^ 2 + 2 * π * ((u / (2 * π * σ ^ 2)) : ℝ) * n) := by
  rw [discreteGaussianWeight, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

theorem fourier_term_eq (σ u : ℝ) (hσ : 0 < σ) (n : ℤ) :
    cexp (-π / ((2 * π * σ ^ 2)⁻¹ : ℝ) * (n + I * ((u / (2 * π * σ ^ 2)) : ℝ)) ^ 2) =
      cexp ((u ^ 2 / (2 * σ ^ 2) : ℝ)) *
        (Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * cexp (-(2 * π * n * u : ℝ) * I)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem summable_theta (σ : ℝ) (hσ : 0 < σ) :
    Summable fun n : ℤ => Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) := by
  have h := discreteGaussianSum_summable (1 / (2 * π * σ)) 0 (by positivity)
  refine h.congr fun n => ?_
  rw [discreteGaussianWeight]
  congr 1
  have : σ ≠ 0 := hσ.ne'
  have hp : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Poisson summation.** Poisson summation for the discrete Gaussian normalizer. -/
theorem discreteGaussianSum_eq_fourier (σ u : ℝ) (hσ : 0 < σ) :
    discreteGaussianSum σ u =
      σ * √(2 * π) * ∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) *
          Real.cos (2 * π * n * u) := by
  have ha : 0 < (((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  have hP := Complex.tsum_exp_neg_quadratic ha (((u / (2 * π * σ ^ 2)) : ℝ) : ℂ)
  have hH : Summable fun n : ℤ =>
      (Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) : ℂ) * cexp (-(2 * π * n * u : ℝ) * I) := by
    refine Summable.of_norm ?_
    refine (summable_theta σ hσ).congr fun n => ?_
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hc : (discreteGaussianSum σ u : ℂ) =
      1 / (((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ∑' n : ℤ,
        (Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) : ℂ) * cexp (-(2 * π * n * u : ℝ) * I) := by
    rw [discreteGaussianSum, Complex.ofReal_tsum, tsum_congr (weight_eq_cexp σ u hσ),
        tsum_mul_left, hP,
      tsum_congr (fourier_term_eq σ u hσ), tsum_mul_left, ← mul_assoc, mul_comm (cexp _), mul_assoc,
      ← mul_assoc (cexp _), ← Complex.exp_add]
    simp
  have hroot : 1 / (((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((σ * √(2 * π) : ℝ) : ℂ) := by
    have hr : (0 : ℝ) ≤ (2 * π * σ ^ 2)⁻¹ := by positivity
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr,
      ← Real.sqrt_eq_rpow, ← Complex.ofReal_one, ← Complex.ofReal_div]
    congr 1
    rw [Real.sqrt_inv, one_div, inv_inv, Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le,
        mul_comm]
  have hre := congrArg Complex.re hc
  rw [Complex.ofReal_re, hroot, Complex.re_ofReal_mul, Complex.re_tsum hH] at hre
  rw [hre]
  congr 1
  refine tsum_congr fun n => ?_
  rw [Complex.re_ofReal_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The theta tail `T(σ) = ∑_{n ≠ 0} exp(-2π²σ²n²)`. -/
noncomputable def tail (σ : ℝ) : ℝ := (∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)) - 1

theorem fourier_sum_mem (σ u : ℝ) (hσ : 0 < σ) :
    1 - tail σ ≤ ∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * Real.cos (2 * π * n * u) ∧
      ∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * Real.cos (2 * π * n * u) ≤ 1 + tail σ :=
          by
  have hs := summable_theta σ hσ
  have hsc : Summable fun n : ℤ => Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) *
      Real.cos (2 * π * n * u) :=
    hs.of_norm_bounded fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  constructor
  · have hle : ∀ n : ℤ, -Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) + (if n = 0 then 2 else 0) ≤
        Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) * Real.cos (2 * π * n * u) := fun n => by
      split_ifs with h
      · subst h; simp; norm_num
      · have := Real.neg_one_le_cos (2 * π * n * u)
        nlinarith [Real.exp_pos (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)]
    have := Summable.tsum_le_tsum hle (hs.neg.add (summable_of_ne_finset_zero (s := {0})
      fun n hn => by simp at hn; simp [hn])) hsc
    rw [hs.neg.tsum_add
        (summable_of_ne_finset_zero (s := {0}) fun n hn => by simp at hn; simp [hn]),
      tsum_neg, tsum_ite_eq] at this
    unfold tail; linarith
  · have := Summable.tsum_le_tsum (fun n : ℤ => mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.cos_le_one (2 * π * n * u))) hsc hs
    unfold tail; linarith

/-- **Normalizer bound.** The normalizer is `σ√(2π)` up to the relative error `T(σ)`. -/
theorem discreteGaussianSum_mem (σ u : ℝ) (hσ : 0 < σ) :
    σ * √(2 * π) * (1 - tail σ) ≤ discreteGaussianSum σ u ∧
      discreteGaussianSum σ u ≤ σ * √(2 * π) * (1 + tail σ) := by
  rw [discreteGaussianSum_eq_fourier σ u hσ]
  obtain ⟨h1, h2⟩ := fourier_sum_mem σ u hσ
  have hc : 0 ≤ σ * √(2 * π) := by positivity
  exact ⟨mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left h2 hc⟩

/-! ## Derivatives of the Fourier series -/

/-- The Fourier weights `exp(-2π²σ²n²)`. -/
noncomputable def w (σ : ℝ) (n : ℤ) : ℝ := Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)

/-- `f σ u = ∑ₙ w n cos(2πnu)`, so that `ρσ(Z - u) = σ√(2π) f σ u`. -/
noncomputable def f (σ u : ℝ) : ℝ := ∑' n : ℤ, w σ n * Real.cos (2 * π * n * u)
noncomputable def f₁ (σ u : ℝ) : ℝ := ∑' n : ℤ, -(w σ n * (2 * π * n)) * Real.sin (2 * π * n * u)
noncomputable def f₂ (σ u : ℝ) : ℝ :=
    ∑' n : ℤ, -(w σ n * (2 * π * n) ^ 2) * Real.cos (2 * π * n * u)

/-- First and second moment tails. -/
noncomputable def T₁ (σ : ℝ) : ℝ := ∑' n : ℤ, w σ n * |2 * π * n|
noncomputable def T₂ (σ : ℝ) : ℝ := ∑' n : ℤ, w σ n * (2 * π * n) ^ 2

theorem w_pos (σ : ℝ) (n : ℤ) : 0 < w σ n := Real.exp_pos _

theorem sq_mul_w_le (σ : ℝ) (hσ : 0 < σ) (n : ℤ) :
    (n : ℝ) ^ 2 * w σ n ≤ 1 / (π ^ 2 * σ ^ 2) * w (σ / √2) n := by
  have hc : 0 < π ^ 2 * σ ^ 2 := by positivity
  set y := π ^ 2 * σ ^ 2 * (n : ℝ) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hw : w σ n = Real.exp (-y) * Real.exp (-y) := by
    rw [w, ← Real.exp_add]; congr 1; rw [hy]; ring
  have hw2 : w (σ / √2) n = Real.exp (-y) := by
    rw [w]; congr 1; rw [hy, div_pow, Real.sq_sqrt zero_le_two]; field_simp
  rw [hw, hw2]
  have hle : y * Real.exp (-y) ≤ 1 := by
    have := Real.add_one_le_exp y
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos y)]; linarith
  have : (n : ℝ) ^ 2 = y / (π ^ 2 * σ ^ 2) := by rw [hy]; field_simp
  rw [this]
  calc y / (π ^ 2 * σ ^ 2) * (Real.exp (-y) * Real.exp (-y))
      = (y * Real.exp (-y)) / (π ^ 2 * σ ^ 2) * Real.exp (-y) := by ring
    _ ≤ 1 / (π ^ 2 * σ ^ 2) * Real.exp (-y) := by gcongr

theorem summable_w (σ : ℝ) (hσ : 0 < σ) : Summable (w σ) := summable_theta σ hσ

theorem summable_T₂ (σ : ℝ) (hσ : 0 < σ) : Summable fun n : ℤ => w σ n * (2 * π * n) ^ 2 := by
  have hs := (summable_w (σ / √2) (by positivity)).mul_left (4 * π ^ 2 * (1 / (π ^ 2 * σ ^ 2)))
  refine Summable.of_nonneg_of_le (fun n => by have := w_pos σ n; positivity) (fun n => ?_) hs
  have := sq_mul_w_le σ hσ n
  calc w σ n * (2 * π * n) ^ 2 = 4 * π ^ 2 * ((n : ℝ) ^ 2 * w σ n) := by ring
    _ ≤ 4 * π ^ 2 * (1 / (π ^ 2 * σ ^ 2) * w (σ / √2) n) := by gcongr
    _ = _ := by ring

theorem summable_T₁ (σ : ℝ) (hσ : 0 < σ) : Summable fun n : ℤ => w σ n * |2 * π * n| := by
  refine Summable.of_nonneg_of_le (fun n => by have := w_pos σ n; positivity) (fun n => ?_)
    ((summable_w σ hσ).add (summable_T₂ σ hσ))
  have h := w_pos σ n
  have : |2 * π * (n : ℝ)| ≤ 1 + (2 * π * n) ^ 2 := by
    nlinarith [abs_nonneg (2 * π * (n : ℝ)), sq_abs (2 * π * (n : ℝ))]
  calc w σ n * |2 * π * n| ≤ w σ n * (1 + (2 * π * n) ^ 2) := by gcongr
    _ = _ := by ring

theorem hasDerivAt_f (σ : ℝ) (hσ : 0 < σ) (u : ℝ) : HasDerivAt (f σ) (f₁ σ u) u := by
  refine hasDerivAt_tsum (g := fun (n : ℤ) (y : ℝ) => w σ n * Real.cos (2 * π * n * y))
    (g' := fun (n : ℤ) (y : ℝ) => -(w σ n * (2 * π * n)) * Real.sin (2 * π * n * y))
    (summable_T₁ σ hσ) (fun n y => ?_) (fun n y => ?_) (y₀ := 0) ?_ u
  · have :=
      ((Real.hasDerivAt_cos (2 * π * n * y)).comp y
          ((hasDerivAt_id y).const_mul (2 * π * n))).const_mul
      (w σ n)
    convert this using 1 <;> simp; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (w_pos σ n)]
    exact mul_le_of_le_one_right (mul_nonneg (w_pos σ n).le (abs_nonneg _)) (Real.abs_sin_le_one _)
  · simpa using summable_w σ hσ

theorem hasDerivAt_f₁ (σ : ℝ) (hσ : 0 < σ) (u : ℝ) : HasDerivAt (f₁ σ) (f₂ σ u) u := by
  refine hasDerivAt_tsum
      (g := fun (n : ℤ) (y : ℝ) => -(w σ n * (2 * π * n)) * Real.sin (2 * π * n * y))
    (g' := fun (n : ℤ) (y : ℝ) => -(w σ n * (2 * π * n) ^ 2) * Real.cos (2 * π * n * y))
    (summable_T₂ σ hσ) (fun n y => ?_) (fun n y => ?_) (y₀ := 0) ?_ u
  · have :=
      ((Real.hasDerivAt_sin (2 * π * n * y)).comp y
          ((hasDerivAt_id y).const_mul (2 * π * n))).const_mul
      (-(w σ n * (2 * π * n)))
    convert this using 1 <;> simp; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (w_pos σ n),
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_right (by have := w_pos σ n; positivity) (Real.abs_cos_le_one _)
  · simp

theorem abs_f₁_le (σ : ℝ) (hσ : 0 < σ) (u : ℝ) : |f₁ σ u| ≤ T₁ σ := by
  have hb : ∀ n : ℤ, ‖-(w σ n * (2 * π * n)) * Real.sin (2 * π * n * u)‖ ≤ w σ n * |2 * π * n| :=
      fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (w_pos σ n)]
    exact mul_le_of_le_one_right (mul_nonneg (w_pos σ n).le (abs_nonneg _)) (Real.abs_sin_le_one _)
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (summable_T₁ σ hσ)
  exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hb hs (summable_T₁ σ hσ))

theorem abs_f₂_le (σ : ℝ) (hσ : 0 < σ) (u : ℝ) : |f₂ σ u| ≤ T₂ σ := by
  have hb : ∀ n : ℤ, ‖-(w σ n * (2 * π * n) ^ 2) * Real.cos (2 * π * n * u)‖ ≤ w σ n *
      (2 * π * n) ^ 2 :=
    fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_of_pos (w_pos σ n),
          abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (by have := w_pos σ n; positivity) (Real.abs_cos_le_one _)
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (summable_T₂ σ hσ)
  exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hb hs (summable_T₂ σ hσ))

theorem f_mem (σ u : ℝ) (hσ : 0 < σ) : 1 - tail σ ≤ f σ u ∧ f σ u ≤ 1 + tail σ :=
  fourier_sum_mem σ u hσ

/-- The second-derivative bound for `log f`. -/
noncomputable def M (σ : ℝ) : ℝ := (T₂ σ * (1 + tail σ) + T₁ σ ^ 2) / (1 - tail σ) ^ 2

/-- **Second derivative of `log f`.** `log f` has derivative `f₁ / f` and second derivative `(f₂ f -
f₁²) / f²`, bounded by `M σ`. -/
theorem hasDerivAt_log_f (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (u : ℝ) :
    HasDerivAt (fun v => Real.log (f σ v)) (f₁ σ u / f σ u) u :=
  (hasDerivAt_f σ hσ u).log (by linarith [(f_mem σ u hσ).1])

theorem hasDerivAt_f₁_div_f (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (u : ℝ) :
    HasDerivAt (fun v => f₁ σ v / f σ v) ((f₂ σ u * f σ u - f₁ σ u * f₁ σ u) / f σ u ^ 2) u :=
  (hasDerivAt_f₁ σ hσ u).div (hasDerivAt_f σ hσ u) (by linarith [(f_mem σ u hσ).1])

theorem abs_deriv2_log_f_le (σ : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (u : ℝ) :
    |(f₂ σ u * f σ u - f₁ σ u * f₁ σ u) / f σ u ^ 2| ≤ M σ := by
  obtain ⟨hlo, hhi⟩ := f_mem σ u hσ
  have hf0 : 0 < f σ u := by linarith
  have h1 := abs_f₁_le σ hσ u
  have h2 := abs_f₂_le σ hσ u
  have hT0 : 0 ≤ tail σ := by
    have h := (summable_w σ hσ).le_tsum 0 fun n _ => (w_pos σ n).le
    simp only [w, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.exp_zero] at h
    unfold tail; linarith
  have hT1 : 0 ≤ T₁ σ := le_trans (abs_nonneg _) h1
  have hT2 : 0 ≤ T₂ σ := le_trans (abs_nonneg _) h2
  rw [abs_div, abs_of_pos (by positivity : 0 < f σ u ^ 2), M]
  have hnum : |f₂ σ u * f σ u - f₁ σ u * f₁ σ u| ≤ T₂ σ * (1 + tail σ) + T₁ σ ^ 2 := by
    calc |f₂ σ u * f σ u - f₁ σ u * f₁ σ u| ≤ |f₂ σ u| * |f σ u| + |f₁ σ u| * |f₁ σ u| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ T₂ σ * (1 + tail σ) + T₁ σ * T₁ σ :=
          add_le_add (mul_le_mul h2 (by rw [abs_of_pos hf0]; exact hhi) (abs_nonneg _) hT2)
            (mul_le_mul h1 h1 (abs_nonneg _) hT1)
      _ = _ := by ring
  have hden : (1 - tail σ) ^ 2 ≤ f σ u ^ 2 := by
    have : 0 ≤ 1 - tail σ := by linarith
    gcongr
  exact div_le_div₀ (by nlinarith [sq_nonneg (T₁ σ)]) hnum (by nlinarith) hden

end FalconPrecision.ThetaTail
