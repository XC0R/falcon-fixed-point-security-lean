/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.NumTail
public import FalconPrecision.Lemma5

/-! # The constant `K` of Lemma 5 at Falcon's leaves

With `q = exp(-2π²t)` and `16q ≤ r < 1`: `V₁ t ≤ 2π²·2r/(1-r)`, `V₂ t ≤ (2π²)²·2r/(1-r)` (`n⁴ ≤
16^|n|`). For `t ≥ 1.277²`, `|L₁| ≤ 2⁻²⁵`, `|L₂| ≤ 2⁻²⁴`, so on `1/4 ≤ τ ≤ 1/1.277²` (every `σ ∈
[1.277, 2]`): `|ψ''(τ)| ≤ (1/2 + 2⁻¹⁹)/τ²`. -/

@[expose] public section

open Real FalconPrecision.ThetaTail FalconPrecision.ThetaT FalconPrecision.NumTail
    FalconPrecision.Lemma5

namespace FalconPrecision.NumK

/-- `(n²)ʲ e t n ≤ r^|n|` for `j ≤ 2` once `16 exp(-2π²t) ≤ r`. -/
theorem term_le4 (t r : ℝ) (ht : 0 ≤ t) (hr : 16 * Real.exp (-(2 * π ^ 2 * t)) ≤ r) (n : ℤ) (j : ℕ)
    (hj : j ≤ 2) :
    ((n : ℝ) ^ 2) ^ j * e t n ≤ r ^ n.natAbs := by
  set k := n.natAbs
  have hkn : ((n : ℝ) ^ 2) = (k : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hq0 : 0 ≤ Real.exp (-(2 * π ^ 2 * t)) := (Real.exp_pos _).le
  have hc : 0 ≤ 2 * π ^ 2 * t := by positivity
  have he : e t n ≤ Real.exp (-(2 * π ^ 2 * t)) ^ k := by
    rw [e, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hk : (k : ℝ) ≤ (n : ℝ) ^ 2 := by
      rw [hkn]
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h
        nlinarith
    nlinarith
  have hkj : ((k : ℝ) ^ 2) ^ j ≤ 16 ^ k := by
    have h4 : (k : ℝ) ^ 4 ≤ 16 ^ k := by
      have : k ^ 4 ≤ 16 ^ k := by
        calc k ^ 4 ≤ (2 ^ k) ^ 4 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 4
          _ = 16 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos k with h | h
    · rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; rw [pow_zero]; exact one_le_pow₀ (by norm_num)
      · simp [h, zero_pow hj0.ne']
    · have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast h)
      calc ((k : ℝ) ^ 2) ^ j ≤ ((k : ℝ) ^ 2) ^ 2 := pow_le_pow_right₀ h1 hj
        _ = (k : ℝ) ^ 4 := by ring
        _ ≤ 16 ^ k := h4
  rw [hkn]
  calc ((k : ℝ) ^ 2) ^ j * e t n ≤ 16 ^ k * Real.exp (-(2 * π ^ 2 * t)) ^ k :=
        mul_le_mul hkj he (e_pos t n).le (by positivity)
    _ = (16 * Real.exp (-(2 * π ^ 2 * t))) ^ k := by rw [mul_pow]
    _ ≤ r ^ k := pow_le_pow_left₀ (by positivity) hr k

theorem term_le4_b (t r : ℝ) (ht : 0 ≤ t) (hr : 16 * Real.exp (-(2 * π ^ 2 * t)) ≤ r) (n : ℤ)
    (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j ≤ 2) : ((n : ℝ) ^ 2) ^ j * e t n ≤ r ^ n.natAbs - if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [zero_pow (by omega : j ≠ 0)]
  · simpa using term_le4 t r ht hr n j hj

/-- **Explicit moment tails.** -/
theorem V_le (t r : ℝ) (ht : 0 < t) (hr : 16 * Real.exp (-(2 * π ^ 2 * t)) ≤ r) (h1 : r < 1) :
    V₁ t ≤ 2 * π ^ 2 * (2 * r / (1 - r)) ∧ V₂ t ≤ (2 * π ^ 2) ^ 2 * (2 * r / (1 - r)) := by
  have h0 : 0 ≤ r := le_trans (by positivity) hr
  have hB := hasSum_b r h0 h1
  constructor
  · unfold V₁
    rw [tsum_mul_left]
    gcongr
    rw [← hB.tsum_eq]
    exact Summable.tsum_le_tsum (fun n => term_le4_b t r ht.le hr n 1 le_rfl (by norm_num))
      (summable_pow_e t ht 1 (by norm_num)) hB.summable
  · unfold V₂
    rw [tsum_mul_left]
    gcongr
    rw [← hB.tsum_eq]
    exact Summable.tsum_le_tsum (fun n => term_le4_b t r ht.le hr n 2 (by norm_num) le_rfl)
      (summable_pow_e t ht 2 le_rfl) hB.summable

theorem exp_bound16 (t : ℝ)
    (ht : (1277 / 1000) ^ 2 ≤ t) : 16 * Real.exp (-(2 * π ^ 2 * t)) ≤ 1 / 2 ^ 38 := by
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hσ : 1277 / 1000 ≤ √t := Real.le_sqrt_of_sq_le ht
  have := exp_bound (√t) hσ
  rw [Real.sq_sqrt ht0] at this
  linarith

/-- **Falcon logarithmic derivatives.** For `t ≥ 1.277²`: `T ≤ 2⁻³⁶`, `|L₁| ≤ 2⁻²⁵`, `|L₂| ≤ 2⁻²⁴`.
-/
theorem falcon_L (c t : ℝ) (ht : (1277 / 1000) ^ 2 ≤ t) :
    tail (√t) ≤ 1 / 2 ^ 36 ∧ |L₁ c t| ≤ 1 / 2 ^ 25 ∧ |L₂ c t| ≤ 1 / 2 ^ 24 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set r : ℝ := 1 / 2 ^ 38 with hr
  have hr1 : r < 1 := by norm_num [hr]
  have hr16 := exp_bound16 t ht
  have hr4 : 4 * Real.exp (-(2 * π ^ 2 * √t ^ 2)) ≤ r := by
    rw [Real.sq_sqrt ht0.le, hr]; linarith [Real.exp_pos (-(2 * π ^ 2 * t))]
  set ε : ℝ := 1 / 2 ^ 36 with hε
  have hrε : 2 * r / (1 - r) ≤ ε := by
    rw [div_le_iff₀ (by norm_num [hr])]; norm_num [hr, hε]
  have hε0 : 0 ≤ 2 * r / (1 - r) := by
    apply div_nonneg <;> norm_num [hr]
  obtain ⟨hT, -, -⟩ := tails_le (√t) r (Real.sqrt_pos.2 ht0) hr4 hr1
  obtain ⟨hV1, hV2⟩ := V_le t r ht0 hr16 hr1
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hp2 : π ^ 2 ≤ 10 := by nlinarith
  have hTε : tail (√t) ≤ ε := hT.trans hrε
  have hT1 : tail (√t) < 1 := by
    have : ε < 1 := by norm_num [hε]
    linarith
  have hV1ε : V₁ t ≤ 20 * ε :=
    hV1.trans (mul_le_mul (by linarith) hrε hε0 (by norm_num))
  have hV2ε : V₂ t ≤ 400 * ε :=
    hV2.trans (mul_le_mul (by nlinarith [sq_nonneg (π ^ 2)]) hrε hε0 (by norm_num))
  have hV10 : 0 ≤ V₁ t := le_trans (abs_nonneg _) (abs_G₁_le c t ht0)
  have hV20 : 0 ≤ V₂ t := le_trans (abs_nonneg _) (abs_G₂_le c t ht0)
  have hT0 : 0 ≤ tail (√t) := by
    have h := (summable_w (√t) (Real.sqrt_pos.2 ht0)).le_tsum 0 fun n _ => (w_pos (√t) n).le
    simp only [w, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.exp_zero] at h
    unfold tail; linarith
  have hden : 1 / 2 ≤ 1 - tail (√t) := by
    have : ε ≤ 1 / 2 := by norm_num [hε]
    linarith
  refine ⟨hTε, ?_, ?_⟩
  · refine (abs_L₁_le c t ht0 hT1).trans ?_
    rw [div_le_iff₀ (by linarith)]
    calc V₁ t ≤ 20 * ε := hV1ε
      _ ≤ 1 / 2 ^ 25 * (1 / 2) := by norm_num [hε]
      _ ≤ 1 / 2 ^ 25 * (1 - tail (√t)) := by gcongr
  · refine (abs_L₂_le c t ht0 hT1).trans ?_
    rw [div_le_iff₀ (by nlinarith)]
    have h1 : V₂ t * (1 + tail (√t)) ≤ 400 * ε * 2 :=
      mul_le_mul hV2ε (by have : ε ≤ 1 := by norm_num [hε]
                          linarith) (by linarith) (by norm_num [hε])
    have h2 : V₁ t ^ 2 ≤ (20 * ε) ^ 2 := pow_le_pow_left₀ hV10 hV1ε 2
    have hsq : 1 / 4 ≤ (1 - tail (√t)) ^ 2 := by nlinarith
    calc V₂ t * (1 + tail (√t)) + V₁ t ^ 2 ≤ 400 * ε * 2 + (20 * ε) ^ 2 := add_le_add h1 h2
      _ ≤ 1 / 2 ^ 24 * (1 / 4) := by norm_num [hε]
      _ ≤ 1 / 2 ^ 24 * (1 - tail (√t)) ^ 2 := by gcongr

/--
**`K` at Falcon.** For `1/4 ≤ τlo ≤ τ ≤ 1/1.277²` (leaf standard deviations in `[1.277, 2]`): `tail
< 1` and `|ψ''(τ)| ≤ (1/2 + 2⁻¹⁹)/τlo²`. -/
theorem falcon_ψ₂ (c τ τlo : ℝ) (hlo : 1 / 4 ≤ τlo) (hτ : τlo ≤ τ) (hhi : τ ≤ (1000 / 1277) ^ 2) :
    0 < τ ∧ tail (√τ⁻¹) < 1 ∧ |ψ₂ c τ| ≤ (1 / 2 + 1 / 2 ^ 19) / τlo ^ 2 := by
  have hτ0 : 0 < τ := by linarith
  have hlo0 : 0 < τlo := by linarith
  have ht : (1277 / 1000) ^ 2 ≤ τ⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hτ0]
    calc τ ≤ (1000 / 1277) ^ 2 := hhi
      _ = ((1277 / 1000) ^ 2)⁻¹ := by norm_num
  obtain ⟨hT, hL1, hL2⟩ := falcon_L c τ⁻¹ ht
  have hT1 : tail (√τ⁻¹) < 1 := lt_of_le_of_lt hT (by norm_num)
  refine ⟨hτ0, hT1, ?_⟩
  have hsub := abs_ψ₂_sub_le c τ hτ0
  set u : ℝ := (τ ^ 2)⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have hulo : u ≤ (τlo ^ 2)⁻¹ := by
    rw [hu]; gcongr
  have hu16 : u ≤ 16 := by
    calc u ≤ (τlo ^ 2)⁻¹ := hulo
      _ ≤ ((1 / 4 : ℝ) ^ 2)⁻¹ := by gcongr
      _ = 16 := by norm_num
  have h3 : 2 * τ / (τ ^ 2) ^ 2 = 2 * u * τ⁻¹ := by
    rw [hu]; field_simp
  have hτinv : τ⁻¹ ≤ 4 := by
    calc τ⁻¹ ≤ τlo⁻¹ := by gcongr
      _ ≤ (1 / 4 : ℝ)⁻¹ := by gcongr
      _ = 4 := by norm_num
  have hcorr : |L₂ c τ⁻¹| * u ^ 2 + |L₁ c τ⁻¹| * (2 * u * τ⁻¹) ≤ 1 / 2 ^ 19 * u := by
    have a1 : |L₂ c τ⁻¹| * u ^ 2 ≤ 1 / 2 ^ 24 * (16 * u) := by
      rw [sq]; nlinarith [abs_nonneg (L₂ c τ⁻¹)]
    have a2 : |L₁ c τ⁻¹| * (2 * u * τ⁻¹) ≤ 1 / 2 ^ 25 * (8 * u) := by
      have : 2 * u * τ⁻¹ ≤ 8 * u := by nlinarith [inv_pos.2 hτ0]
      nlinarith [abs_nonneg (L₁ c τ⁻¹)]
    nlinarith
  rw [h3] at hsub
  have hψ : |ψ₂ c τ| ≤ (1 / 2) * u + 1 / 2 ^ 19 * u := by
    have := abs_sub_abs_le_abs_sub (ψ₂ c τ) ((1 / 2) * u)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) * u)] at this
    linarith
  calc |ψ₂ c τ| ≤ (1 / 2 + 1 / 2 ^ 19) * u := by linarith
    _ ≤ (1 / 2 + 1 / 2 ^ 19) * (τlo ^ 2)⁻¹ := by gcongr
    _ = _ := by ring

/-- **Lemma 5 at Falcon.** For `τᵢ = 1/σᵢ²` and `τ' = τ₁ + a(τ₂ - τ₁)` with `τ₁, τ'` in `[τlo,
1/1.277²]`, `τlo ≥ 1/4`: `Rₐ(D_{σ₂,c} ‖ D_{σ₁,c}) ≤ exp(a(a+1)(τ₂ - τ₁)²(1/2 + 2⁻¹⁹)/(2(a-1)τlo²))`.
-/
theorem renyiDiv_scale_le_falcon (σ₁ σ₂ c a τlo : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (ha : 1 < a)
    (hlo : 1 / 4 ≤ τlo)
    (h₁ : τlo ≤ 1 / σ₁ ^ 2 ∧ 1 / σ₁ ^ 2 ≤ (1000 / 1277) ^ 2)
    (h' : τlo ≤ 1 / σ₁ ^ 2 + a * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ∧
      1 / σ₁ ^ 2 + a * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ≤ (1000 / 1277) ^ 2) :
    InformationTheory.renyiDiv a (LatticeCrypto.discreteGaussianMeasure σ₂ c)
        (LatticeCrypto.discreteGaussianMeasure σ₁ c) ≤
      ENNReal.ofReal (Real.exp (a * (a + 1) * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ^ 2 *
        ((1 / 2 + 1 / 2 ^ 19) / τlo ^ 2) / (2 * (a - 1)))) := by
  refine renyiDiv_scale_le σ₁ σ₂ c a _ hσ₁ hσ₂ ha fun τ hτ => ?_
  have hlo' : τlo ≤ τ := by
    rcases Set.mem_uIcc.1 hτ with h | h
    · exact h₁.1.trans h.1
    · exact h'.1.trans h.1
  have hhi' : τ ≤ (1000 / 1277) ^ 2 := by
    rcases Set.mem_uIcc.1 hτ with h | h
    · exact h.2.trans h'.2
    · exact h.2.trans h₁.2
  exact falcon_ψ₂ c τ τlo hlo hlo' hhi'

end FalconPrecision.NumK
