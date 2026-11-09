/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.ThetaTail

/-! # The Fourier series in `t = σ²` and its derivatives

`G c t = ∑ₙ exp(-2π²n²t) cos(2πnc)`, so that `ρ_σ(Z - c) = σ√(2π) G c (σ²)`. Derivatives in `t` on
`t > t₀ > 0`. -/

@[expose] public section

open Real FalconPrecision.ThetaTail

namespace FalconPrecision.ThetaT

noncomputable def e (t : ℝ) (n : ℤ) : ℝ := Real.exp (-(2 * π ^ 2 * t) * n ^ 2)

noncomputable def G (c t : ℝ) : ℝ := ∑' n : ℤ, e t n * Real.cos (2 * π * n * c)
noncomputable def G₁ (c t : ℝ) : ℝ :=
    ∑' n : ℤ, -(2 * π ^ 2 * n ^ 2) * e t n * Real.cos (2 * π * n * c)
noncomputable def G₂ (c t : ℝ) : ℝ :=
    ∑' n : ℤ, (2 * π ^ 2 * n ^ 2) ^ 2 * e t n * Real.cos (2 * π * n * c)

theorem e_eq_w (σ : ℝ) (n : ℤ) : e (σ ^ 2) n = w σ n := by rw [e, w]

theorem e_pos (t : ℝ) (n : ℤ) : 0 < e t n := Real.exp_pos _

theorem e_anti {t t₀ : ℝ} (h : t₀ ≤ t) (n : ℤ) : e t n ≤ e t₀ n := by
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * π ^ 2))
    (sq_nonneg (n : ℝ))
  linarith

theorem summable_pow_e (t₀ : ℝ) (ht : 0 < t₀) (j : ℕ) (hj : j ≤ 2) :
    Summable fun n : ℤ => ((n : ℝ) ^ 2) ^ j * e t₀ n := by
  set σ := √t₀
  have hσ : 0 < σ := Real.sqrt_pos.2 ht
  have hσt : σ ^ 2 = t₀ := Real.sq_sqrt ht.le
  have h0 : Summable fun n : ℤ => e t₀ n := by
    simpa [← hσt, e_eq_w] using summable_w σ hσ
  have h1 : ∀ s : ℝ, 0 < s → Summable fun n : ℤ => (n : ℝ) ^ 2 * w s n := fun s hs =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (w_pos s n).le) (sq_mul_w_le s hs)
      ((summable_w (s / √2) (by positivity)).mul_left _)
  interval_cases j
  · simpa using h0
  · simpa [← hσt, e_eq_w] using h1 σ hσ
  · have h2 : Summable fun n : ℤ => (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * w σ n) :=
      Summable.of_nonneg_of_le (fun n => by have := w_pos σ n; positivity)
        (fun n => mul_le_mul_of_nonneg_left (sq_mul_w_le σ hσ n) (sq_nonneg _))
        ((h1 (σ / √2) (by positivity)).mul_left (1 / (π ^ 2 * σ ^ 2)) |>.congr fun n => by ring)
    refine h2.congr fun n => ?_
    rw [← hσt, e_eq_w]; ring

theorem hasDerivAt_e (n : ℤ) (y : ℝ) : HasDerivAt (fun t => e t n)
    (-(2 * π ^ 2 * n ^ 2) * e y n) y := by
  have := ((((hasDerivAt_id y).const_mul (2 * π ^ 2)).neg).mul_const ((n : ℝ) ^ 2)).exp
  convert this using 1
  · funext t; simp [e]
  · simp [e]; ring

theorem hasDerivAt_G (c t : ℝ) (ht : 0 < t) : HasDerivAt (G c) (G₁ c t) t := by
  have hs := (summable_pow_e (t / 2) (by positivity) 1 (by norm_num)).mul_left (2 * π ^ 2)
  refine hasDerivAt_tsum_of_isPreconnected
      (g := fun (n : ℤ) (y : ℝ) => e y n * Real.cos (2 * π * n * c))
    (g' := fun (n : ℤ) (y : ℝ) => -(2 * π ^ 2 * n ^ 2) * e y n * Real.cos (2 * π * n * c))
    hs (isOpen_Ioi (a := t / 2)) (isPreconnected_Ioi (a := t / 2)) (fun n y _ => ?_)
        (fun n y hy => ?_) (y₀ := t)
    (Set.mem_Ioi.2 (by linarith)) ?_ (Set.mem_Ioi.2 (by linarith))
  · exact (hasDerivAt_e n y).mul_const _
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity),
      abs_of_pos (e_pos y n)]
    calc 2 * π ^ 2 * (n : ℝ) ^ 2 * e y n * |Real.cos (2 * π * n * c)| ≤ 2 * π ^ 2 * (n : ℝ) ^ 2 *
        e y n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
              (mul_nonneg (by positivity) (e_pos _ n).le)
      _ ≤ 2 * π ^ 2 * (((n : ℝ) ^ 2) ^ 1 * e (t / 2) n) := by
          rw [mul_one, pow_one, mul_assoc]; gcongr; exact e_anti (le_of_lt hy) n
  · refine Summable.of_norm_bounded (summable_pow_e t ht 0 (by norm_num)) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (e_pos t n), pow_zero, one_mul]
    exact mul_le_of_le_one_right (e_pos t n).le (Real.abs_cos_le_one _)

theorem hasDerivAt_G₁ (c t : ℝ) (ht : 0 < t) : HasDerivAt (G₁ c) (G₂ c t) t := by
  have hs := (summable_pow_e (t / 2) (by positivity) 2 le_rfl).mul_left ((2 * π ^ 2) ^ 2)
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℤ) (y : ℝ) => -(2 * π ^ 2 * n ^ 2) * e y n * Real.cos (2 * π * n * c))
    (g' := fun (n : ℤ) (y : ℝ) => (2 * π ^ 2 * n ^ 2) ^ 2 * e y n * Real.cos (2 * π * n * c))
    hs (isOpen_Ioi (a := t / 2)) (isPreconnected_Ioi (a := t / 2)) (fun n y _ => ?_)
        (fun n y hy => ?_) (y₀ := t)
    (Set.mem_Ioi.2 (by linarith)) ?_ (Set.mem_Ioi.2 (by linarith))
  · have :=
      ((hasDerivAt_e n y).const_mul (-(2 * π ^ 2 * n ^ 2))).mul_const (Real.cos (2 * π * n * c))
    convert this using 1; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_pos (e_pos y n)]
    calc (2 * π ^ 2 * (n : ℝ) ^ 2) ^ 2 * e y n * |Real.cos (2 * π * n * c)| ≤
          (2 * π ^ 2 * (n : ℝ) ^ 2) ^ 2 * e y n * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
                  (mul_nonneg (by positivity) (e_pos _ n).le)
      _ ≤ (2 * π ^ 2) ^ 2 * (((n : ℝ) ^ 2) ^ 2 * e (t / 2) n) := by
          rw [mul_one, mul_pow, mul_assoc]; gcongr; exact e_anti (le_of_lt hy) n
  · refine Summable.of_norm_bounded
      ((summable_pow_e t ht 1 (by norm_num)).mul_left (2 * π ^ 2)) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity),
        abs_of_pos (e_pos t n)]
    calc 2 * π ^ 2 * (n : ℝ) ^ 2 * e t n * |Real.cos (2 * π * n * c)| ≤ 2 * π ^ 2 * (n : ℝ) ^ 2 *
        e t n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
              (mul_nonneg (by positivity) (e_pos _ n).le)
      _ = 2 * π ^ 2 * (((n : ℝ) ^ 2) ^ 1 * e t n) := by ring

/-- Moment tails in `t`. -/
noncomputable def V₁ (t : ℝ) : ℝ := ∑' n : ℤ, 2 * π ^ 2 * (((n : ℝ) ^ 2) ^ 1 * e t n)
noncomputable def V₂ (t : ℝ) : ℝ := ∑' n : ℤ, (2 * π ^ 2) ^ 2 * (((n : ℝ) ^ 2) ^ 2 * e t n)

theorem abs_G₁_le (c t : ℝ) (ht : 0 < t) : |G₁ c t| ≤ V₁ t := by
  have hs := (summable_pow_e t ht 1 (by norm_num)).mul_left (2 * π ^ 2)
  have hb : ∀ n : ℤ, ‖-(2 * π ^ 2 * n ^ 2) * e t n * Real.cos (2 * π * n * c)‖ ≤
      2 * π ^ 2 * (((n : ℝ) ^ 2) ^ 1 * e t n) := fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity),
        abs_of_pos (e_pos t n)]
    calc 2 * π ^ 2 * (n : ℝ) ^ 2 * e t n * |Real.cos (2 * π * n * c)| ≤ 2 * π ^ 2 * (n : ℝ) ^ 2 *
        e t n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
              (mul_nonneg (by positivity) (e_pos _ n).le)
      _ = _ := by ring
  have hs' := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hs
  exact (norm_tsum_le_tsum_norm hs').trans (Summable.tsum_le_tsum hb hs' hs)

theorem abs_G₂_le (c t : ℝ) (ht : 0 < t) : |G₂ c t| ≤ V₂ t := by
  have hs := (summable_pow_e t ht 2 le_rfl).mul_left ((2 * π ^ 2) ^ 2)
  have hb : ∀ n : ℤ, ‖(2 * π ^ 2 * n ^ 2) ^ 2 * e t n * Real.cos (2 * π * n * c)‖ ≤
      (2 * π ^ 2) ^ 2 * (((n : ℝ) ^ 2) ^ 2 * e t n) := fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_pos (e_pos t n)]
    calc (2 * π ^ 2 * (n : ℝ) ^ 2) ^ 2 * e t n * |Real.cos (2 * π * n * c)| ≤
          (2 * π ^ 2 * (n : ℝ) ^ 2) ^ 2 * e t n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
              (mul_nonneg (by positivity) (e_pos _ n).le)
      _ = _ := by ring
  have hs' := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hs
  exact (norm_tsum_le_tsum_norm hs').trans (Summable.tsum_le_tsum hb hs' hs)

theorem V_anti {t t₀ : ℝ} (ht₀ : 0 < t₀) (h : t₀ ≤ t) : V₁ t ≤ V₁ t₀ ∧ V₂ t ≤ V₂ t₀ := by
  have ht : 0 < t := lt_of_lt_of_le ht₀ h
  constructor
  · exact Summable.tsum_le_tsum (fun n => by gcongr; exact e_anti h n)
      ((summable_pow_e t ht 1 (by norm_num)).mul_left _)
          ((summable_pow_e t₀ ht₀ 1 (by norm_num)).mul_left _)
  · exact Summable.tsum_le_tsum (fun n => by gcongr; exact e_anti h n)
      ((summable_pow_e t ht 2 le_rfl).mul_left _) ((summable_pow_e t₀ ht₀ 2 le_rfl).mul_left _)

theorem G_eq_f (c σ : ℝ) : G c (σ ^ 2) = f σ c := by
  unfold G f; congr 1

theorem G_mem (c t : ℝ) (ht : 0 < t) : 1 - tail (√t) ≤ G c t ∧ G c t ≤ 1 + tail (√t) := by
  have := f_mem (√t) c (Real.sqrt_pos.2 ht)
  rwa [← G_eq_f, Real.sq_sqrt ht.le] at this

end FalconPrecision.ThetaT
