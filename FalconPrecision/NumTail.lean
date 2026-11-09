/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.ThetaTail
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit geometric bounds on the theta tails, and the Falcon instance

With `q = exp(-2π²σ²)` and any `r ≥ 4q`, `r < 1`: `T ≤ 2r/(1-r)`, `T₁ ≤ 2π·2r/(1-r)`, `T₂ ≤
4π²·2r/(1-r)`. For `σ ≥ 1.277` (both Falcon parameter sets: `σmin = 1.2778…`, `1.2983…`) take `r =
2⁻⁴⁰`. -/

@[expose] public section

open Real FalconPrecision.ThetaTail

namespace FalconPrecision.NumTail

theorem tsum_rpow_natAbs (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 + r) / (1 - r)) := by
  have ha : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_lt_one h0 h1
  have hb : HasSum (fun n : ℕ => r ^ (n + 1)) (r * (1 - r)⁻¹) := by
    simpa [pow_succ, mul_comm] using ha.mul_left r
  have e : ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 := fun n => by omega
  have hb' : HasSum (fun n : ℕ => r ^ (-((n : ℤ) + 1)).natAbs) (r * (1 - r)⁻¹) := by
    simp only [e]; exact hb
  have := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => r ^ n.natAbs) (by simpa using ha) hb'
  convert this using 1
  have : 1 - r ≠ 0 := sub_ne_zero.2 h1.ne'
  field_simp

/-- Each weighted term is at most `r^|n|` once `4 exp(-2π²σ²) ≤ r`. -/
theorem term_le (σ r : ℝ) (hr : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ r) (n : ℤ) (j : ℕ)
    (hj : j ≤ 2) :
    (n.natAbs : ℝ) ^ j * w σ n ≤ r ^ n.natAbs := by
  set k := n.natAbs
  have hq0 : 0 ≤ Real.exp (-(2 * π ^ 2 * σ ^ 2)) := (Real.exp_pos _).le
  have hw : w σ n ≤ Real.exp (-(2 * π ^ 2 * σ ^ 2)) ^ k := by
    rw [w, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hk : (k : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (k : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [this, ← sq_abs]
      rcases eq_or_ne n 0 with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ |(n : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
        nlinarith
    have hc : 0 ≤ 2 * π ^ 2 * σ ^ 2 := by positivity
    nlinarith
  have hkj : (k : ℝ) ^ j ≤ 4 ^ k := by
    have h1 : (k : ℝ) ^ j ≤ (k : ℝ) ^ 2 ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · right; exact h
      · left; exact pow_le_pow_right₀ (by exact_mod_cast h) hj
    have h2 : (k : ℝ) ^ 2 ≤ 4 ^ k := by
      have : k ^ 2 ≤ 4 ^ k := by
        calc k ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 2
          _ = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      exact_mod_cast this
    rcases h1 with h | h
    · exact h.trans h2
    · rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp [h]
      · simp [h, zero_pow hj0.ne']
  calc (k : ℝ) ^ j * w σ n ≤ 4 ^ k * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ^ k :=
        mul_le_mul hkj hw (Real.exp_pos _).le (by positivity)
    _ = (4 * Real.exp (-(2 * π ^ 2 * σ ^ 2))) ^ k := by rw [mul_pow]
    _ ≤ r ^ k := pow_le_pow_left₀ (by positivity) hr k

theorem hasSum_b (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs - if n = 0 then 1 else 0) (2 * r / (1 - r)) := by
  have := (tsum_rpow_natAbs r h0 h1).sub (hasSum_ite_eq (0 : ℤ) (1 : ℝ))
  convert this using 1
  have : 1 - r ≠ 0 := sub_ne_zero.2 h1.ne'
  field_simp; ring

/-- `|n|ʲ w σ n ≤ r^|n| - [n = 0]` for `j = 1, 2`. -/
theorem term_le_b (σ r : ℝ) (hr : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ r) (n : ℤ) (j : ℕ)
    (hj1 : 1 ≤ j)
    (hj : j ≤ 2) : (n.natAbs : ℝ) ^ j * w σ n ≤ r ^ n.natAbs - if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [zero_pow (by omega : j ≠ 0)]
  · simpa using term_le σ r hr n j hj

/-- **Explicit tails.** -/
theorem tails_le (σ r : ℝ) (hσ : 0 < σ) (hr : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ r)
    (h1 : r < 1) :
    tail σ ≤ 2 * r / (1 - r) ∧ T₁ σ ≤ 2 * π * (2 * r / (1 - r)) ∧
      T₂ σ ≤ 4 * π ^ 2 * (2 * r / (1 - r)) := by
  have h0 : 0 ≤ r := le_trans (by positivity) hr
  have hB := hasSum_b r h0 h1
  have hG := tsum_rpow_natAbs r h0 h1
  refine ⟨?_, ?_, ?_⟩
  · have := Summable.tsum_le_tsum (fun n => by simpa using term_le σ r hr n 0 (by norm_num))
      (summable_w σ hσ) hG.summable
    rw [hG.tsum_eq] at this
    unfold tail
    have : 1 - r ≠ 0 := sub_ne_zero.2 h1.ne'
    calc (∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2)) - 1 ≤ (1 + r) / (1 - r) - 1 := by
          unfold w at *; linarith
      _ = 2 * r / (1 - r) := by field_simp; ring
  · have hle : ∀ n : ℤ, w σ n * |2 * π * n| = 2 * π * ((n.natAbs : ℝ) ^ 1 * w σ n) := fun n => by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), pow_one, Nat.cast_natAbs,
          Int.cast_abs]; ring
    unfold T₁
    rw [tsum_congr hle, tsum_mul_left]
    gcongr
    rw [← hB.tsum_eq]
    have hp : (2 * π) ≠ 0 := by positivity
    exact Summable.tsum_le_tsum (fun n => term_le_b σ r hr n 1 le_rfl (by norm_num))
      (((summable_T₁ σ hσ).mul_left (2 * π)⁻¹).congr fun n => by rw [hle]; field_simp) hB.summable
  · have hle : ∀ n : ℤ, w σ n * (2 * π * n) ^ 2 = 4 * π ^ 2 * ((n.natAbs : ℝ) ^ 2 * w σ n) :=
      fun n => by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]; ring
    unfold T₂
    rw [tsum_congr hle, tsum_mul_left]
    gcongr
    rw [← hB.tsum_eq]
    have hp : (4 * π ^ 2) ≠ 0 := by positivity
    exact Summable.tsum_le_tsum (fun n => term_le_b σ r hr n 2 (by norm_num) le_rfl)
      (((summable_T₂ σ hσ).mul_left (4 * π ^ 2)⁻¹).congr fun n => by rw [hle]; field_simp)
          hB.summable

theorem exp_bound (σ : ℝ)
    (hσ : 1277 / 1000 ≤ σ) : 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ 1 / 2 ^ 40 := by
  have hpi := Real.pi_gt_d2
  have hp2 : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hpi.le 2
  have hs2 : (1277 / 1000 : ℝ) ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ (by norm_num) hσ 2
  have hps := mul_le_mul hp2 hs2 (by norm_num) (sq_nonneg π)
  have hc : (32 : ℝ) ≤ 2 * π ^ 2 * σ ^ 2 := by nlinarith
  have he : (2 : ℝ) ^ 42 ≤ Real.exp 32 := by
    have h1 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (Real.exp_one_gt_d9).le
    calc (2 : ℝ) ^ 42 ≤ 2.7 ^ 32 := by norm_num
      _ ≤ Real.exp 1 ^ 32 := pow_le_pow_left₀ (by norm_num) h1 32
      _ = Real.exp 32 := by rw [← Real.exp_nat_mul]; norm_num
  have : Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ Real.exp (-32) := Real.exp_le_exp.2 (by linarith)
  calc 4 * Real.exp (-(2 * π ^ 2 * σ ^ 2)) ≤ 4 * Real.exp (-32) := by gcongr
    _ = 4 * (Real.exp 32)⁻¹ := by rw [Real.exp_neg]
    _ ≤ 4 * ((2 : ℝ) ^ 42)⁻¹ := by gcongr
    _ = 1 / 2 ^ 40 := by norm_num

/--
**Falcon instance.** For every leaf standard deviation `σ ≥ 1.277` (both parameter sets), the theta
tail is below `1` and the second-derivative constant of `Lemma4.renyiDiv_shift_le` is at most
`2⁻³⁰`. -/
theorem falcon_tail (σ : ℝ) (hσ : 1277 / 1000 ≤ σ) : tail σ < 1 ∧ M σ ≤ 1 / 2 ^ 30 := by
  have hσ0 : 0 < σ := by linarith
  set r : ℝ := 1 / 2 ^ 40 with hr
  have hr1 : r < 1 := by norm_num [hr]
  obtain ⟨hT, hT1, hT2⟩ := tails_le σ r hσ0 (exp_bound σ hσ) hr1
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hε : 2 * r / (1 - r) ≤ 1 / 2 ^ 38 := by
    rw [div_le_iff₀ (by norm_num [hr])]; norm_num [hr]
  have hT0 : 0 ≤ tail σ := by
    have h := (summable_w σ hσ0).le_tsum 0 fun n _ => (w_pos σ n).le
    simp only [w, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.exp_zero] at h
    unfold tail; linarith
  have hT1' : 0 ≤ T₁ σ := le_trans (abs_nonneg _) (abs_f₁_le σ hσ0 0)
  have hT2' : 0 ≤ T₂ σ := le_trans (abs_nonneg _) (abs_f₂_le σ hσ0 0)
  set ε : ℝ := 1 / 2 ^ 38
  have hTε : tail σ ≤ ε := hT.trans hε
  have hT1ε : T₁ σ ≤ 7 * ε := hT1.trans (by nlinarith)
  have hT2ε : T₂ σ ≤ 40 * ε := hT2.trans (by nlinarith)
  have hεs : ε ≤ 1 / 2 ^ 38 := le_rfl
  refine ⟨by norm_num [ε] at hTε; linarith, ?_⟩
  rw [M, div_le_iff₀ (by nlinarith [show tail σ < 1 by norm_num [ε] at hTε; linarith])]
  have hden : 1 / 2 ≤ (1 - tail σ) ^ 2 := by nlinarith [show tail σ ≤ 1 / 2 ^ 38 from hTε]
  have hnum : T₂ σ * (1 + tail σ) + T₁ σ ^ 2 ≤ 81 * ε := by
    have h1 : T₂ σ * (1 + tail σ) ≤ 40 * ε * 2 := by
      apply mul_le_mul hT2ε (by norm_num [ε] at hTε; linarith) (by linarith) (by norm_num [ε])
    have h2 : T₁ σ ^ 2 ≤ (7 * ε) ^ 2 := pow_le_pow_left₀ hT1' hT1ε 2
    have : (7 * ε) ^ 2 ≤ ε := by norm_num [ε]
    linarith
  calc T₂ σ * (1 + tail σ) + T₁ σ ^ 2 ≤ 81 * ε := hnum
    _ ≤ 1 / 2 ^ 30 * (1 / 2) := by norm_num [ε]
    _ ≤ 1 / 2 ^ 30 * (1 - tail σ) ^ 2 := by gcongr

end FalconPrecision.NumTail
