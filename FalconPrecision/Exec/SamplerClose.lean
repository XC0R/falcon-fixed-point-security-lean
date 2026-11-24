/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerLaw
public import FalconPrecision.RenyiHybrid
public import FalconPrecision.RenyiShift
public import FalconPrecision.Taylor2
public import FalconPrecision.Errors.GaussTail

/-! # The Rényi distance of SamplerZ to `D_{σ̄,t̄}`

`samplerZ_mgf`: for a sampler that rejects saturated shifts, at every `σ̄ ∈ [σmin, σmax]` and
every `t̄`, the Rényi MGF of order `a ≥ 2` against `D_{σ̄,t̄}` is at most `exp((a - 1)·εZ a)`, from
a `χ²` bound `chi2B = 2⁻⁷⁶` and a ratio bound `uB = 1 + 2⁻⁴⁰` (`lawZ_close`) through
`renyiMGF_le_chi2` (`t^a ≤ 1 + a(t - 1) + a(a-1)/2·u^(a-2)(t - 1)²` for `t ∈ [0, u]`,
`rpow_le_chi2`).

`lawZ_close` compares each of the `38` candidates `(z0 ≤ 18, b)` with its ideal weight
`pdt[0]/2^(w+1)·ccs·exp(-(z - r)²/(2σ̄²))` (`cand_bounds`: the table against
`exp(-i²/(2σmax²))`, `tab_ok`; BerExp's acceptance against `ccs·exp(-x)`, `accW_mem`), so the
acceptance of a round is within `2⁻⁴²` of `A* = pdt[0]/2^(w+1)·ccs·Θ` (`accZ_bounds`); the
`χ²` sum is at most `21·2⁻⁸¹` on the candidates (`chi_fin`) plus `11·2⁻⁸¹`, the mass of
`D_{σ̄,t̄}` at distance `≥ 19` from `t̄` (`tail19_le`, the Chernoff bound of `GaussTail`).

`samplerZ_tv`: saturating instead of rejecting moves at most `2⁻¹¹⁰` in total variation per call
(ePrint 2026/2902 p. 4: a saturated shift multiplies the acceptance by `2^(s-63)`, so no useful
Rényi bound of high order holds for it); a shift `≥ 64` needs `z0 ≥ 15`, whose `pdt` mass is at
most `2⁻⁵⁰` (`wZ_sat`, `pdt_tail15`). -/

@[expose] public section

open MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- Second-order bound for `t ↦ t^a` on `[0, u]`, `a ≥ 2`, `u ≥ 1`. -/
theorem rpow_le_chi2 {a u t : ℝ} (ha : 2 ≤ a) (ht0 : 0 ≤ t) (htu : t ≤ u) (hu : 1 ≤ u) :
    t ^ a ≤ 1 + a * (t - 1) + a * (a - 1) / 2 * u ^ (a - 2) * (t - 1) ^ 2 := by
  have e : 1 + (t - 1) = t := by ring
  have hseg : ∀ y ∈ Set.uIcc 1 (1 + (t - 1)), 0 ≤ y ∧ y ≤ u := fun y hy => by
    rw [e] at hy
    rcases Set.mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := Taylor2.sub_le_of_deriv2_le_on (g := fun y => y ^ a) (g' := fun y => a * y ^ (a - 1))
    (g'' := fun y => a * ((a - 1) * y ^ (a - 1 - 1))) (M := a * (a - 1) * u ^ (a - 2))
    (x := 1) (h := t - 1) (fun y _ => Real.hasDerivAt_rpow_const (Or.inr (by linarith)))
    (fun y _ => (Real.hasDerivAt_rpow_const (Or.inr (by linarith))).const_mul a)
    (fun y hy => by
      obtain ⟨h0, h1⟩ := hseg y hy
      rw [show a - 1 - 1 = a - 2 by ring, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 h1 (by linarith))
        (mul_nonneg (by linarith) (by linarith)))
  simp only [Real.one_rpow, mul_one, e] at h
  linarith

/-- **Node** (χ² form of the Rényi MGF). A subprobability `μ` with density `p ≤ u·q` against a
discrete Gaussian `q`, `u ≥ 1`, `a ≥ 2`, `χ ≥ 0`: `M_a(μ‖ν) ≤ 1 + a(a-1)/2·u^(a-2)·χ²(p‖q)`. -/
theorem renyiMGF_le_chi2 {a u χ : ℝ} (ha : 2 ≤ a) (hu : 1 ≤ u) (hχ0 : 0 ≤ χ) (μ : Measure ℤ)
    (σ c : ℝ)
    (hσ : 0 < σ) (p : ℤ → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hμ : ∀ y, μ {y} = ENNReal.ofReal (p y))
    (hμ1 : μ Set.univ ≤ 1) (hpu : ∀ y, p y ≤ u * discreteGaussianPMF σ c y)
    (hχ : ∑' y, ENNReal.ofReal ((p y - discreteGaussianPMF σ c y) ^ 2 /
      discreteGaussianPMF σ c y) ≤ ENNReal.ofReal χ) :
    renyiMGF a μ (discreteGaussianMeasure σ c) ≤
      ENNReal.ofReal (1 + a * (a - 1) / 2 * u ^ (a - 2) * χ) := by
  set q := discreteGaussianPMF σ c
  have hq : ∀ y, 0 < q y := discreteGaussianPMF_pos σ c hσ
  have := isProbabilityMeasure_discreteGaussianMeasure σ c hσ
  set C := a * (a - 1) / 2 * u ^ (a - 2) with hCdef
  have hC : 0 ≤ C :=
    mul_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) two_pos.le)
      (Real.rpow_nonneg (by linarith) _)
  have ha0 : 0 ≤ a := by linarith
  have hterm : ∀ y, μ {y} ^ a * discreteGaussianMeasure σ c {y} ^ (1 - a) +
      ENNReal.ofReal a * ENNReal.ofReal (q y) ≤ ENNReal.ofReal (q y) +
        ENNReal.ofReal a * ENNReal.ofReal (p y) +
          ENNReal.ofReal C * ENNReal.ofReal ((p y - q y) ^ 2 / q y) := by
    intro y
    have hqy := hq y
    have hX : 0 ≤ (p y - q y) ^ 2 / q y := by positivity
    rw [hμ, discreteGaussianMeasure_singleton, ENNReal.ofReal_rpow_of_nonneg (hp0 y) ha0,
      ENNReal.ofReal_rpow_of_pos hqy, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hp0 y) _),
      ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg (hp0 y) _) (Real.rpow_nonneg hqy.le _))
        (mul_nonneg ha0 hqy.le),
      ← ENNReal.ofReal_add hqy.le (mul_nonneg ha0 (hp0 y)),
      ← ENNReal.ofReal_add (add_nonneg hqy.le (mul_nonneg ha0 (hp0 y))) (mul_nonneg hC hX)]
    refine ENNReal.ofReal_le_ofReal ?_
    have ht := rpow_le_chi2 ha (div_nonneg (hp0 y) hqy.le)
      ((div_le_iff₀ hqy).2 (by linarith [hpu y])) hu
    have e : p y ^ a * q y ^ (1 - a) = q y * (p y / q y) ^ a := by
      rw [Real.div_rpow (hp0 y) hqy.le, Real.rpow_sub hqy, Real.rpow_one]
      field_simp
    have e2 : (p y - q y) ^ 2 / q y = q y * (p y / q y - 1) ^ 2 := by field_simp
    have e3 : q y * (p y / q y) = p y := by field_simp
    have h1 := mul_le_mul_of_nonneg_left ht hqy.le
    rw [show q y * (1 + a * (p y / q y - 1) + C * (p y / q y - 1) ^ 2) =
      q y + a * (q y * (p y / q y)) - a * q y + C * (q y * (p y / q y - 1) ^ 2) by ring,
      e3] at h1
    rw [e, e2]
    linarith
  rw [RenyiShift.renyiMGF_eq_tsum_of_pos ha0 _ _
    (fun y => (discreteGaussianMeasure_singleton_pos σ c hσ y).ne') (fun y => measure_ne_top _ _)]
  have hsum := ENNReal.tsum_le_tsum hterm
  have hq1 : ∑' y, ENNReal.ofReal (q y) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => (hq y).le) (discreteGaussianPMF_summable σ c hσ),
      discreteGaussianPMF_sum_eq_one σ c hσ, ENNReal.ofReal_one]
  have hp1 : ∑' y, ENNReal.ofReal (p y) ≤ 1 := by
    simp_rw [← hμ]
    simpa using (Measure.tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).le.trans hμ1
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hq1, mul_one] at hsum
  have hsum' := hsum.trans (add_le_add (add_le_add le_rfl
    (mul_le_of_le_one_right (by positivity) hp1)) (by gcongr :
      ENNReal.ofReal C * ∑' y, ENNReal.ofReal ((p y - q y) ^ 2 / q y) ≤
        ENNReal.ofReal C * ENNReal.ofReal χ))
  rw [add_right_comm] at hsum'
  rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hC hχ0), ENNReal.ofReal_one,
    ENNReal.ofReal_mul hC]
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 hsum'

/-- The `χ²` bound per call. -/
def chi2B : ℚ := 1 / 2 ^ 76

/-- The ratio bound per call. -/
def uB : ℚ := 1 + 1 / 2 ^ 40

/-- The per-call exponent at order `a`. -/
noncomputable def εZ (a : ℝ) : ℝ := a / 2 * (uB : ℝ) ^ (a - 2) * chi2B

theorem tab_okB (b : BaseBits) : (falcon512S.tab b).okB = true := by
  cases b <;> decide

/-- Relative errors below `D_{ℤ⁺,σmax}` of the table entries `pdt[i]/pdt[0]` checked in `tab_ok`. -/
def epsT (i : ℕ) : ℚ :=
  if i = 0 then 0 else if i ≤ 10 then 1 / 2 ^ 45 else if i = 11 then 1 / 2 ^ 43
  else if i = 12 then 1 / 2 ^ 38 else if i = 13 then 1 / 2 ^ 34 else if i = 14 then 1 / 2 ^ 28
  else if i = 15 then 1 / 2 ^ 23 else if i = 16 then 1 / 2 ^ 14 else if i = 17 then 1 / 2 ^ 10
  else 1 / 2 ^ 7

theorem tab_check {P0 Pi j : ℕ} {ε : ℚ}
    (h1 : (Pi : ℚ) ≤ P0 * (eLo ^ j) ^ j * (1 + 1 / 2 ^ 45))
    (h2 : (P0 : ℚ) * (eHi ^ j) ^ j * (1 - ε) ≤ Pi) (hε : ε ≤ 1) :
    (Pi : ℝ) ≤ P0 * Real.exp (-((j ^ 2 : ℕ) * kS)) * (1 + 1 / 2 ^ 45) ∧
      (P0 : ℝ) * Real.exp (-((j ^ 2 : ℕ) * kS)) * (1 - ε) ≤ Pi := by
  obtain ⟨hl, hh⟩ := exp_mul_kS_mem (j ^ 2)
  have h1' := (Rat.cast_le (K := ℝ)).2 h1
  have h2' := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h1' h2'
  rw [← pow_mul, ← sq] at h1' h2' 
  have hε' : (0 : ℝ) ≤ 1 - ε := by
    have : (ε : ℝ) ≤ 1 := by exact_mod_cast hε
    linarith
  exact ⟨h1'.trans (by gcongr), le_trans (by gcongr) h2'⟩

/-- **The tables against `D_{ℤ⁺,σmax}`** (both): for `1 ≤ i ≤ 18`,
`pdt[i]/pdt[0] ≤ exp(-i²/(2σmax²))·(1 + 2⁻⁴⁵)` and `≥ exp(-i²/(2σmax²))·(1 - epsT i)`. -/
theorem tab_ok (b : BaseBits) {i : ℕ} (hi : i ≤ 18) :
    (pdtZ (falcon512S.tab b) i : ℝ) ≤
        pdtZ (falcon512S.tab b) 0 * Real.exp (-((i ^ 2 : ℕ) * kS)) * (1 + 1 / 2 ^ 45) ∧
      (pdtZ (falcon512S.tab b) 0 : ℝ) * Real.exp (-((i ^ 2 : ℕ) * kS)) * (1 - epsT i) ≤
        pdtZ (falcon512S.tab b) i := by
  cases b <;> interval_cases i <;>
    exact tab_check
      (by norm_num [pdtZ, falcon512S, tab72, rcdt72, tab79, rcdt79, eLo, List.getD_cons_succ,
        List.getD_cons_zero])
      (by norm_num [pdtZ, falcon512S, tab72, rcdt72, tab79, rcdt79, eLo, eHi, epsT,
        List.getD_cons_succ, List.getD_cons_zero])
      (by norm_num [epsT])

theorem falcon512S_σ_pos {σ : Fx 64} (hσ : inRangeB falcon512S σ = true) : 0 < σ.toReal := by
  simp only [inRangeB, Bool.and_eq_true, decide_eq_true_eq] at hσ
  rw [Fx.toReal_eq_toRat]
  exact_mod_cast lt_of_lt_of_le (by norm_num [falcon512S]) hσ.1

/-! ## Closeness of `lawZ` to `D_{σ̄,t̄}` -/

theorem toInt_floor_eq (t : Fx 64) : t.toInt .floor = ⌊t.toRat⌋ := by
  have h : t.toInt .floor = t.m / 2 ^ 64 := by
    simp only [Fx.toInt, RMode.rdiv]
    cases compareOfLessAndEq (2 * (t.m % (2 : ℤ) ^ 64)) ((2 : ℤ) ^ 64) <;> rfl
  rw [h, Fx.toRat, show ((2 : ℚ) ^ 64) = ((2 ^ 64 : ℕ) : ℚ) by norm_num,
    Rat.floor_intCast_div_natCast]
  norm_num

theorem epsT_nonneg (i : ℕ) : 0 ≤ epsT i := by unfold epsT; split_ifs <;> norm_num

theorem epsT_le (i : ℕ) : epsT i ≤ 1 / 2 ^ 7 := by unfold epsT; split_ifs <;> norm_num

theorem epsT_ge {i : ℕ} (hi : i ≠ 0) : 1 / 2 ^ 45 ≤ epsT i := by
  unfold epsT; simp only [hi, ↓reduceIte]; split_ifs <;> norm_num

theorem zOf_sub_sq {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) (i : ℕ) (b : Bool) :
    ((i : ℚ)) ^ 2 ≤ ((zOf i b : ℚ) - r) ^ 2 ∧ ((zOf i b : ℚ) - r) ^ 2 ≤ ((i : ℚ) + 1) ^ 2 := by
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  cases b
  · simp only [zOf, Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
    rw [show (-(i : ℚ) - r) ^ 2 = ((i : ℚ) + r) ^ 2 by ring]
    exact ⟨pow_le_pow_left₀ hi (by linarith) 2, pow_le_pow_left₀ (by linarith) (by linarith) 2⟩
  · simp only [zOf, ↓reduceIte]
    push_cast
    exact ⟨pow_le_pow_left₀ hi (by linarith) 2,
      pow_le_pow_left₀ (by linarith) (by linarith) 2⟩

theorem xOf_eq (σq r : ℚ) (i : ℕ) (b : Bool) :
    xOf falcon512S σq r i b = ((zOf i b : ℚ) - r) ^ 2 / (2 * σq ^ 2) - (i ^ 2 : ℕ) * kS := by
  unfold xOf
  rw [← kS_eq]
  push_cast
  ring

theorem xOf_nonneg {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (i : ℕ) (b : Bool) : 0 ≤ xOf falcon512S σq r i b := by
  have hσ0 : 0 < σq := lt_of_lt_of_le (by norm_num [falcon512S]) hσ1
  have h1 : (i : ℚ) ^ 2 * kS ≤ (i : ℚ) ^ 2 / (2 * σq ^ 2) := by
    rw [← kS_eq, mul_one_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)
  have h2 : (i : ℚ) ^ 2 / (2 * σq ^ 2) ≤ ((zOf i b : ℚ) - r) ^ 2 / (2 * σq ^ 2) :=
    div_le_div_of_nonneg_right (zOf_sub_sq hr0 hr1 i b).1 (by positivity)
  rw [xOf_eq]
  push_cast
  linarith

theorem xOf_sub_le {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (hr0 : 0 ≤ r) (hr1 : r < 1) {i : ℕ}
    (hi : i ≤ 18) (b : Bool) : xOf falcon512S σq r i b - (i ^ 2 : ℕ) * kS ≤ 13 := by
  have hσ0 : 0 < σq := lt_of_lt_of_le (by norm_num [falcon512S]) hσ1
  have h1 : ((zOf i b : ℚ) - r) ^ 2 / (2 * σq ^ 2) ≤
      ((i : ℚ) + 1) ^ 2 / (2 * falcon512S.σmin ^ 2) :=
    div_le_div₀ (by positivity) (zOf_sub_sq hr0 hr1 i b).2 (by norm_num [falcon512S])
      (by have : (0 : ℚ) ≤ falcon512S.σmin := by norm_num [falcon512S]
          gcongr)
  have h2 : ((i : ℚ) + 1) ^ 2 / (2 * falcon512S.σmin ^ 2) - 2 * ((i ^ 2 : ℕ) * kS) ≤ 13 := by
    interval_cases i <;> norm_num [falcon512S, kS]
  rw [xOf_eq]
  linarith

/-- The ideal weight of the candidate `z`: `pdt[0]/2^(w+1)·ccs·exp(-(z - r)²/(2σ̄²))`. -/
noncomputable def wsZ (S : SampChoices) (σq r : ℚ) (z : ℤ) : ℝ :=
  (pdtZ (falcon512S.tab S.base) 0 : ℝ) / 2 ^ ((falcon512S.tab S.base).w + 1) *
    ((falcon512S.σmin / σq : ℚ) : ℝ) * Real.exp (-(((z : ℝ) - r) ^ 2 / (2 * (σq : ℝ) ^ 2)))

theorem exp_split (σq r : ℚ) (i : ℕ) (b : Bool) :
    Real.exp (-((((zOf i b : ℤ) : ℝ) - r) ^ 2 / (2 * (σq : ℝ) ^ 2))) =
      Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) * Real.exp (-(xOf falcon512S σq r i b : ℝ)) := by
  rw [← Real.exp_add, xOf_eq]
  push_cast
  ring_nf

theorem pdtZ0_le (b : BaseBits) : (pdtZ (falcon512S.tab b) 0 : ℝ) ≤ 2 ^ (falcon512S.tab b).w := by
  have : pdtZ (falcon512S.tab b) 0 ≤ 2 ^ (falcon512S.tab b).w := by
    simp only [pdtZ, ↓reduceIte]; exact Nat.sub_le _ _
  exact_mod_cast this

theorem exp13_le : Real.exp 13 ≤ 2 ^ 19 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  calc Real.exp 13 = Real.exp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 2.7182818286 ^ 13 := pow_le_pow_left₀ (Real.exp_pos _).le h1 13
    _ ≤ 2 ^ 19 := by norm_num

/-- **One candidate against its ideal weight** (`i ≤ 18`): above within `1 + 2⁻⁴³`, below within
`1 - epsT i - 2⁻⁴⁴` and `2⁻⁶²`, and the square of the difference. -/
theorem cand_bounds (S : SampChoices) (hS : S.shiftRej = true) {σq r : ℚ}
    (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) {i : ℕ}
    (hi : i ≤ 18) (b : Bool) :
    (wZ falcon512S S σq r i b : ℝ) ≤ wsZ S σq r (zOf i b) * (1 + 1 / 2 ^ 43) ∧
      wsZ S σq r (zOf i b) * (1 - epsT i - 1 / 2 ^ 44) - 1 / 2 ^ 62 ≤
        wZ falcon512S S σq r i b ∧
      ((wZ falcon512S S σq r i b : ℝ) - wsZ S σq r (zOf i b)) ^ 2 ≤
        wsZ S σq r (zOf i b) *
          ((8 * epsT i ^ 2 + 1 / 2 ^ 86) * wsZ S σq r (zOf i b) + 1 / 2 ^ 103) := by
  have hσ0 : (0 : ℚ) < σq := lt_of_lt_of_le (by norm_num [falcon512S]) hσ1
  have hx0 := xOf_nonneg hσ1 hσ2 hr0 hr1 i b
  have hc0 : 1 / 2 ≤ falcon512S.σmin / σq := by
    rw [le_div_iff₀ hσ0]; norm_num [falcon512S] at hσ2 ⊢; linarith
  have hc1 : falcon512S.σmin / σq ≤ 1 := by rw [div_le_one hσ0]; exact hσ1
  obtain ⟨ha1, ha2⟩ := accW_mem hx0 hc0 hc1
  have hΓ0 := xOf_sub_le hσ1 hr0 hr1 hi b
  obtain ⟨ht1, ht2⟩ := tab_ok S.base hi
  have hP0 := pdtZ0_le S.base
  have hε0 := epsT_nonneg i
  have hε1 := epsT_le i
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (accW falcon512S true (xOf falcon512S σq r i b)
    (falcon512S.σmin / σq) : ℝ) / 2 ^ 64 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((falcon512S.σmin / σq : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = c * Real.exp (-(xOf falcon512S σq r i b : ℝ)) := ⟨_, rfl⟩
  obtain ⟨P0, hP0d⟩ : ∃ P0 : ℝ, P0 = pdtZ (falcon512S.tab S.base) 0 := ⟨_, rfl⟩
  obtain ⟨Pi, hPid⟩ : ∃ Pi : ℝ, Pi = pdtZ (falcon512S.tab S.base) i := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 ^ ((falcon512S.tab S.base).w + 1) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = (epsT i : ℝ) := ⟨_, rfl⟩
  rw [← ha, ← hc, ← hg] at ha1 ha2
  rw [← hE, ← hP0d, ← hPid] at ht1
  rw [← hE, ← hP0d, ← hPid, ← hεd] at ht2
  rw [← hP0d] at hP0
  set x := xOf falcon512S σq r i b with hx
  have hK0 : 0 < K := by rw [hK]; positivity
  have hc0' : (1 / 2 : ℝ) ≤ c := by
    rw [hc, show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]; exact_mod_cast hc0
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE]
    exact Real.exp_le_one_iff.2 (by
      rw [neg_nonpos]; exact mul_nonneg (Nat.cast_nonneg _) (by norm_num [kS]))
  have hg0 : 0 < g := by rw [hg]; exact mul_pos (by linarith) (Real.exp_pos _)
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hP00 : 0 ≤ P0 := by rw [hP0d]; exact Nat.cast_nonneg _
  have hPK : P0 ≤ K / 2 := by rw [hK, pow_succ]; linarith
  have hε0' : (0 : ℝ) ≤ ε := by rw [hεd]; exact_mod_cast hε0
  have hε1' : ε ≤ 1 / 2 ^ 7 := by
    rw [hεd]; have := (Rat.cast_le (K := ℝ)).2 hε1; push_cast at this; exact this
  have hwZ : (wZ falcon512S S σq r i b : ℝ) = Pi / K * a := by
    rw [hPid, hK, ha]; simp only [wZ, hS]; push_cast; ring
  have hws : wsZ S σq r (zOf i b) = P0 * E * g / K := by
    rw [wsZ, exp_split, hP0d, hK, hE, hg, hc]; ring
  rw [hwZ, hws, ← hεd]
  have hPE0 : 0 ≤ P0 * E := mul_nonneg hP00 hE0.le
  have hPEg0 : 0 ≤ P0 * E * g := mul_nonneg hPE0 hg0.le
  have hdiff : |Pi - P0 * E| ≤ ε * (P0 * E) := by
    rcases eq_or_ne i 0 with h0 | h0
    · subst h0
      have : E = 1 := by simp [hE]
      rw [this, mul_one, hPid, hP0d, sub_self, abs_zero, ← hP0d]
      exact mul_nonneg hε0' hP00
    · have hεg : (1 / 2 ^ 45 : ℝ) ≤ ε := by
        rw [hεd]; have := (Rat.cast_le (K := ℝ)).2 (epsT_ge h0); push_cast at this; exact this
      have h1 := mul_le_mul_of_nonneg_right hεg hPE0
      rw [abs_le]; constructor <;> linarith
  have hag : |a - g| ≤ g / 2 ^ 44 + 1 / 2 ^ 62 := by
    rw [abs_le]; constructor <;> linarith
  have hΓ : P0 * E ≤ K * 2 ^ 19 * g := by
    have h13 : E ≤ 2 ^ 19 * Real.exp (-(x : ℝ)) := by
      have : Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) = Real.exp ((x : ℝ) - (i ^ 2 : ℕ) * kS) *
          Real.exp (-(x : ℝ)) := by rw [← Real.exp_add]; ring_nf
      rw [hE, this]
      refine mul_le_mul_of_nonneg_right ((Real.exp_le_exp.2 ?_).trans exp13_le)
        (Real.exp_pos _).le
      exact_mod_cast hΓ0
    have h2 : 2 ^ 19 * Real.exp (-(x : ℝ)) ≤ 2 * 2 ^ 19 * g := by
      rw [hg]; nlinarith [Real.exp_pos (-(x : ℝ))]
    calc P0 * E ≤ K / 2 * (2 * 2 ^ 19 * g) := mul_le_mul hPK (h13.trans h2) hE0.le (by positivity)
      _ = K * 2 ^ 19 * g := by ring
  refine ⟨?_, ?_, ?_⟩
  · have key : Pi * a ≤ P0 * E * g * (1 + 1 / 2 ^ 43) :=
      calc Pi * a ≤ (P0 * E * (1 + 1 / 2 ^ 45)) * (g * (1 + 1 / 2 ^ 44)) :=
            mul_le_mul ht1 ha1 ha0 (by positivity)
        _ = P0 * E * g * ((1 + 1 / 2 ^ 45) * (1 + 1 / 2 ^ 44)) := by ring
        _ ≤ P0 * E * g * (1 + 1 / 2 ^ 43) := mul_le_mul_of_nonneg_left (by norm_num) hPEg0
    calc Pi / K * a = Pi * a / K := by ring
      _ ≤ P0 * E * g * (1 + 1 / 2 ^ 43) / K := by gcongr
      _ = P0 * E * g / K * (1 + 1 / 2 ^ 43) := by ring
  · have h1 : P0 * E * (1 - ε) * (g * (1 - 1 / 2 ^ 44) - 1 / 2 ^ 62) ≤ Pi * a :=
      calc P0 * E * (1 - ε) * (g * (1 - 1 / 2 ^ 44) - 1 / 2 ^ 62) ≤ P0 * E * (1 - ε) * a :=
            mul_le_mul_of_nonneg_left ha2 (mul_nonneg hPE0 (by linarith))
        _ ≤ Pi * a := mul_le_mul_of_nonneg_right ht2 ha0
    have e2 : 0 ≤ P0 * E * g * ε * (1 / 2 ^ 44) :=
      mul_nonneg (mul_nonneg hPEg0 hε0') (by norm_num)
    have e3 : P0 * E * (1 - ε) * (1 / 2 ^ 62) ≤ K * (1 / 2 ^ 62) := by
      refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
      calc P0 * E * (1 - ε) ≤ P0 * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hE1 hP00) (by linarith)
              (by linarith) (by linarith)
        _ ≤ K := by linarith
    have key : P0 * E * g * (1 - ε - 1 / 2 ^ 44) - K * (1 / 2 ^ 62) ≤ Pi * a := by
      have e1 : P0 * E * (1 - ε) * (g * (1 - 1 / 2 ^ 44) - 1 / 2 ^ 62) =
          P0 * E * g * (1 - ε - 1 / 2 ^ 44) + P0 * E * g * ε * (1 / 2 ^ 44) -
            P0 * E * (1 - ε) * (1 / 2 ^ 62) := by ring
      linarith
    calc P0 * E * g / K * (1 - ε - 1 / 2 ^ 44) - 1 / 2 ^ 62 =
        (P0 * E * g * (1 - ε - 1 / 2 ^ 44) - K * (1 / 2 ^ 62)) / K := by field_simp
      _ ≤ Pi * a / K := by gcongr
      _ = Pi / K * a := by ring
  · set u := (Pi - P0 * E) * a with hu_def
    set v := P0 * E * (a - g) with hv_def
    have huv : Pi / K * a - P0 * E * g / K = (u + v) / K := by
      rw [hu_def, hv_def]; field_simp; ring
    rw [huv, div_pow]
    have hu : u ^ 2 ≤ 4 * ε ^ 2 * (P0 * E * g) ^ 2 := by
      have h1 : |u| ≤ 2 * ε * (P0 * E * g) := by
        rw [hu_def, abs_mul, abs_of_nonneg ha0]
        calc |Pi - P0 * E| * a ≤ ε * (P0 * E) * (g * (1 + 1 / 2 ^ 44)) :=
              mul_le_mul hdiff ha1 ha0 (mul_nonneg hε0' hPE0)
          _ = ε * (P0 * E * g) * (1 + 1 / 2 ^ 44) := by ring
          _ ≤ ε * (P0 * E * g) * 2 :=
            mul_le_mul_of_nonneg_left (by norm_num) (mul_nonneg hε0' hPEg0)
          _ = 2 * ε * (P0 * E * g) := by ring
      calc u ^ 2 ≤ (2 * ε * (P0 * E * g)) ^ 2 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
        _ = 4 * ε ^ 2 * (P0 * E * g) ^ 2 := by ring
    have hv : v ^ 2 ≤ 2 * (P0 * E * g) ^ 2 / 2 ^ 88 + 2 * (P0 * E) ^ 2 / 2 ^ 124 := by
      have h1 : |v| ≤ P0 * E * (g / 2 ^ 44 + 1 / 2 ^ 62) := by
        rw [hv_def, abs_mul, abs_of_nonneg hPE0]; exact mul_le_mul_of_nonneg_left hag hPE0
      have h3 : (g / 2 ^ 44 + 1 / 2 ^ 62) ^ 2 ≤ 2 * (g ^ 2 / 2 ^ 88 + 1 / 2 ^ 124) := by
        have e : 2 * (g ^ 2 / 2 ^ 88 + 1 / 2 ^ 124) - (g / 2 ^ 44 + 1 / 2 ^ 62) ^ 2 =
            (g / 2 ^ 44 - 1 / 2 ^ 62) ^ 2 := by ring
        linarith [sq_nonneg (g / 2 ^ 44 - 1 / 2 ^ 62)]
      calc v ^ 2 ≤ (P0 * E * (g / 2 ^ 44 + 1 / 2 ^ 62)) ^ 2 :=
            sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
        _ = (P0 * E) ^ 2 * (g / 2 ^ 44 + 1 / 2 ^ 62) ^ 2 := by ring
        _ ≤ (P0 * E) ^ 2 * (2 * (g ^ 2 / 2 ^ 88 + 1 / 2 ^ 124)) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = 2 * (P0 * E * g) ^ 2 / 2 ^ 88 + 2 * (P0 * E) ^ 2 / 2 ^ 124 := by ring
    have hsq : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
      have e : 2 * u ^ 2 + 2 * v ^ 2 - (u + v) ^ 2 = (u - v) ^ 2 := by ring
      linarith [sq_nonneg (u - v)]
    have hPEsq : (P0 * E) ^ 2 ≤ P0 * E * (K * 2 ^ 19 * g) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hΓ hPE0
    have key : (u + v) ^ 2 ≤ (8 * ε ^ 2 + 1 / 2 ^ 86) * (P0 * E * g) ^ 2 +
        P0 * E * g * K / 2 ^ 103 := by
      have e1 : (8 * ε ^ 2 + 1 / 2 ^ 86) * (P0 * E * g) ^ 2 =
          2 * (4 * ε ^ 2 * (P0 * E * g) ^ 2) + 2 * (2 * (P0 * E * g) ^ 2 / 2 ^ 88) := by ring
      have e2 : P0 * E * g * K / 2 ^ 103 = 4 * (P0 * E * (K * 2 ^ 19 * g)) / 2 ^ 124 := by ring
      linarith
    calc (u + v) ^ 2 / K ^ 2 ≤ ((8 * ε ^ 2 + 1 / 2 ^ 86) * (P0 * E * g) ^ 2 +
          P0 * E * g * K / 2 ^ 103) / K ^ 2 := by gcongr
      _ = P0 * E * g / K * ((8 * ε ^ 2 + 1 / 2 ^ 86) * (P0 * E * g / K) + 1 / 2 ^ 103) := by
          field_simp

theorem exp_kS_pow_le (i : ℕ) :
    Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) ≤ ((eHi : ℝ) ^ i) ^ i := by
  rw [← pow_mul, ← sq]; exact (exp_mul_kS_mem (i ^ 2)).2

theorem sum_E_eps :
    ∑ i ∈ Finset.range 19, Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) * epsT i ≤ 1 / 2 ^ 43 := by
  refine (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (exp_kS_pow_le i)
    (by exact_mod_cast epsT_nonneg i)).trans ?_
  norm_num [Finset.sum_range_succ, epsT, eHi, eLo]

theorem sum_E_eps2 :
    ∑ i ∈ Finset.range 19, Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) * epsT i ^ 2 ≤ 1 / 2 ^ 81 := by
  refine (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (exp_kS_pow_le i)
    (by positivity)).trans ?_
  norm_num [Finset.sum_range_succ, epsT, eHi, eLo]

/-- `D_{σ̄,t̄}` puts at most `11·2⁻⁸¹` at distance `≥ 19` from `t̄` for `σ̄ ∈ [σmin, σmax]`. -/
theorem tail19_le {σ c : ℝ} (hσ1 : 1277833697 / 1000000000 ≤ σ) (hσ2 : σ ≤ 18205 / 10000) :
    discreteGaussianMeasure σ c {z | 19 ≤ |(z : ℝ) - c|} ≤ ENNReal.ofReal (11 / 2 ^ 81) := by
  refine (Errors.GaussTail.measure_abs_ge_falcon σ c 19 (by linarith) (by norm_num)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hσ0 : 0 < σ := by linarith
  have h1 : Real.exp (-((19 : ℝ) ^ 2 / (2 * σ ^ 2))) ≤ ((eHi : ℝ) ^ 19) ^ 19 := by
    refine (Real.exp_le_exp.2 ?_).trans (exp_kS_pow_le 19)
    rw [neg_le_neg_iff, show ((19 ^ 2 : ℕ) : ℝ) * (kS : ℝ) = 19 ^ 2 / (2 * (18205 / 10000) ^ 2)
      by norm_num [kS]]
    gcongr
  calc 2 * (1 + 1 / 2 ^ 36) * Real.exp (-((19 : ℝ) ^ 2 / (2 * σ ^ 2))) ≤
        2 * (1 + 1 / 2 ^ 36) * ((eHi : ℝ) ^ 19) ^ 19 := by gcongr
    _ ≤ 11 / 2 ^ 81 := by norm_num [eHi, eLo]

/-- The normalizer `Σ_z exp(-(z - c)²/(2σ²))` for `σ ≥ σmin`. -/
theorem theta_mem {σ c : ℝ} (hσ1 : 1277833697 / 1000000000 ≤ σ) :
    σ * (25066 / 10000) * (1 - 1 / 2 ^ 38) ≤ discreteGaussianSum σ c ∧
      discreteGaussianSum σ c ≤ σ * (25067 / 10000) * (1 + 1 / 2 ^ 38) := by
  have hσ0 : 0 < σ := by linarith
  obtain ⟨h1, h2⟩ := ThetaTail.discreteGaussianSum_mem σ c hσ0
  have ht := (NumTail.tails_le σ (1 / 2 ^ 40) hσ0 (NumTail.exp_bound σ (by linarith))
    (by norm_num)).1
  have ht' : ThetaTail.tail σ ≤ 1 / 2 ^ 38 := ht.trans (by norm_num)
  have ht0 := Errors.GaussTail.tail_nonneg σ hσ0
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hs1 : (25066 / 10000 : ℝ) ≤ √(2 * Real.pi) :=
    (Real.le_sqrt (by norm_num) (by positivity)).2 (by linarith)
  have hs2 : √(2 * Real.pi) ≤ 25067 / 10000 := (Real.sqrt_le_left (by norm_num)).2 (by linarith)
  constructor
  · refine le_trans ?_ h1
    gcongr
  · refine h2.trans ?_
    gcongr

/-- `pdt[0]/2^(w+1)·ccs`. -/
noncomputable def K0Z (S : SampChoices) (σq : ℚ) : ℝ :=
  (pdtZ (falcon512S.tab S.base) 0 : ℝ) / 2 ^ ((falcon512S.tab S.base).w + 1) *
    ((falcon512S.σmin / σq : ℚ) : ℝ)

theorem wsZ_eq (S : SampChoices) (σq r : ℚ) (z : ℤ) :
    wsZ S σq r z = K0Z S σq * Real.exp (-(((z : ℝ) - r) ^ 2 / (2 * (σq : ℝ) ^ 2))) := rfl

theorem pdt0_mem (b : BaseBits) :
    (35949 / 100000 : ℝ) ≤ (pdtZ (falcon512S.tab b) 0 : ℝ) / 2 ^ (falcon512S.tab b).w ∧
      (pdtZ (falcon512S.tab b) 0 : ℝ) / 2 ^ (falcon512S.tab b).w ≤ 3595 / 10000 := by
  cases b <;> norm_num [pdtZ, falcon512S, tab72, rcdt72, tab79, rcdt79]

/-- `K0Z·Θ ∈ [1/2, 3/5]` and `Θ ∈ [16/5, 23/5]` on SamplerZ's range. -/
theorem K0Z_theta (S : SampChoices) {σq : ℚ} (c : ℝ) (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) :
    1 / 2 ≤ K0Z S σq * discreteGaussianSum σq c ∧ K0Z S σq * discreteGaussianSum σq c ≤ 3 / 5 ∧
      16 / 5 ≤ discreteGaussianSum σq c ∧ discreteGaussianSum σq c ≤ 23 / 5 := by
  have hσ1' : (1277833697 / 1000000000 : ℝ) ≤ σq := by
    have := (Rat.cast_le (K := ℝ)).2 hσ1; norm_num [falcon512S] at this; linarith
  have hσ2' : (σq : ℝ) ≤ 18205 / 10000 := by
    have := (Rat.cast_le (K := ℝ)).2 hσ2; norm_num [falcon512S] at this; linarith
  obtain ⟨h1, h2⟩ := theta_mem (c := c) hσ1'
  obtain ⟨p1, p2⟩ := pdt0_mem S.base
  have hσ0 : (0 : ℝ) < σq := by linarith
  have hK : K0Z S σq = (pdtZ (falcon512S.tab S.base) 0 : ℝ) / 2 ^ (falcon512S.tab S.base).w / 2 *
      ((1277833697 / 1000000000 : ℝ) / σq) := by
    rw [K0Z, pow_succ]; push_cast [falcon512S]; ring
  rw [hK]
  set p := (pdtZ (falcon512S.tab S.base) 0 : ℝ) / 2 ^ (falcon512S.tab S.base).w
  set Θ := discreteGaussianSum (σq : ℝ) c
  have e : p / 2 * ((1277833697 / 1000000000 : ℝ) / σq) * Θ =
      p / 2 * (1277833697 / 1000000000) * (Θ / σq) := by field_simp
  have hΘ1 : (25066 / 10000) * (1 - 1 / 2 ^ 38) ≤ Θ / σq := by
    rw [le_div_iff₀ hσ0]; linarith
  have hΘ2 : Θ / σq ≤ (25067 / 10000) * (1 + 1 / 2 ^ 38) := by
    rw [div_le_iff₀ hσ0]; linarith
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul p1 hΘ1 (by norm_num) (by linarith : (0 : ℝ) ≤ p)]
  · nlinarith [mul_le_mul p2 hΘ2 (by linarith) (by norm_num : (0 : ℝ) ≤ 3595 / 10000)]
  · linarith
  · linarith

theorem tab_len (b : BaseBits) : (falcon512S.tab b).rcdt.length = 18 := by cases b <;> rfl

theorem zOf_inj {i j : ℕ} {b b' : Bool} (h : zOf i b = zOf j b') : i = j ∧ b = b' := by
  cases b <;> cases b' <;> simp only [zOf, Bool.false_eq_true, ↓reduceIte] at h <;>
    refine ⟨by omega, ?_⟩ <;> first | rfl | (exfalso; omega)

theorem zOf_surj {z : ℤ} (h1 : -18 ≤ z) (h2 : z ≤ 19) :
    ∃ p ∈ Finset.range 19 ×ˢ (Finset.univ : Finset Bool), zOf p.1 p.2 = z := by
  rcases le_or_gt 1 z with hz | hz
  · exact ⟨((z - 1).toNat, true), by simp; omega, by simp [zOf]; omega⟩
  · exact ⟨((-z).toNat, false), by simp; omega, by simp [zOf]; omega⟩

theorem wZz_zOf (P : SampParams) (S : SampChoices) (σ r : ℚ) (i : ℕ) (b : Bool) :
    wZz P S σ r (zOf i b) = wZ P S σ r i b := by
  cases b
  · have h : ¬(1 ≤ -(i : ℤ)) := by omega
    simp only [wZz, zOf, Bool.false_eq_true, ↓reduceIte, h, neg_neg, Int.toNat_natCast]
  · simp [wZz, zOf]

theorem wZz_out (S : SampChoices) (σ r : ℚ) {z : ℤ} (hz : z < -18 ∨ 19 < z) :
    wZz falcon512S S σ r z = 0 := by
  have h0 : ∀ k b, 18 < k → wZ falcon512S S σ r k b = 0 := fun k b hk => by
    rw [wZ, pdtZ_eq_zero _ (by rw [tab_len]; exact hk)]; simp
  unfold wZz
  split_ifs with h
  · exact h0 _ _ (by omega)
  · exact h0 _ _ (by omega)

/-- `(a + b + e)² ≤ (5/4)·a² + 10·b² + 10·e²`, divided by `D = ws/A*`. -/
theorem chi_term {L D w ws As lam e : ℝ} (hws : 0 < ws) (hAs : 0 < As) (hD : D = ws / As)
    (hL : L = lam * w / As + e) :
    (L - D) ^ 2 / D ≤ 5 / 4 * lam ^ 2 * ((w - ws) ^ 2 / ws) / As +
      10 * (lam - 1) ^ 2 * (ws / As) + 10 * e ^ 2 / D := by
  have hD0 : 0 < D := hD ▸ div_pos hws hAs
  set a := lam * (w - ws) / As
  set b := (lam - 1) * ws / As
  have hLD : L - D = a + b + e := by rw [hL, hD]; simp only [a, b]; field_simp; ring
  have key : (L - D) ^ 2 ≤ 5 / 4 * a ^ 2 + 10 * b ^ 2 + 10 * e ^ 2 := by
    rw [hLD]
    have e1 : 5 / 4 * a ^ 2 + 10 * b ^ 2 + 10 * e ^ 2 - (a + b + e) ^ 2 =
        (a / 2 - 2 * (b + e)) ^ 2 + 5 * (b - e) ^ 2 := by ring
    nlinarith [sq_nonneg (a / 2 - 2 * (b + e)), sq_nonneg (b - e)]
  calc (L - D) ^ 2 / D ≤ (5 / 4 * a ^ 2 + 10 * b ^ 2 + 10 * e ^ 2) / D := by gcongr
    _ = 5 / 4 * lam ^ 2 * ((w - ws) ^ 2 / ws) / As + 10 * (lam - 1) ^ 2 * (ws / As) +
        10 * e ^ 2 / D := by
      rw [add_div, add_div, hD]; simp only [a, b]; field_simp

theorem sum_C_pair {f : ℕ → ℝ} :
    ∑ p ∈ Finset.range 19 ×ˢ (Finset.univ : Finset Bool), f p.1 =
      2 * ∑ i ∈ Finset.range 19, f i := by
  rw [Finset.sum_product, Finset.mul_sum]
  simp [two_mul]

/-- `D_{σ̄,t̄}` at `t̄ = s + r`. -/
noncomputable def DZ (σq : ℚ) (s : ℤ) (r : ℚ) (y : ℤ) : ℝ :=
  discreteGaussianPMF σq ((s : ℝ) + r) y

/-- The ideal acceptance `A* = K0·Θ`. -/
noncomputable def AsZ (S : SampChoices) (σq : ℚ) (s : ℤ) (r : ℚ) : ℝ :=
  K0Z S σq * discreteGaussianSum σq ((s : ℝ) + r)

/-- The `38` candidates `(z0, b)`, `z0 ≤ 18`. -/
def candC : Finset (ℕ × Bool) := Finset.range 19 ×ˢ Finset.univ

theorem candC_le {p : ℕ × Bool} (hp : p ∈ candC) : p.1 ≤ 18 := by
  simp only [candC, Finset.mem_product, Finset.mem_range] at hp; omega

theorem σq_real {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) :
    (1277833697 / 1000000000 : ℝ) ≤ σq ∧ (σq : ℝ) ≤ 18205 / 10000 := by
  have h1 := (Rat.cast_le (K := ℝ)).2 hσ1
  have h2 := (Rat.cast_le (K := ℝ)).2 hσ2
  norm_num [falcon512S] at h1 h2
  exact ⟨by linarith, by linarith⟩

theorem AsZ_mem (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) :
    1 / 2 ≤ AsZ S σq s r ∧ AsZ S σq s r ≤ 3 / 5 ∧ 0 < K0Z S σq ∧
      K0Z S σq ≤ AsZ S σq s r * (5 / 16) := by
  obtain ⟨h1, h2, h3, h4⟩ := K0Z_theta S ((s : ℝ) + r) hσ1 hσ2
  have hK : 0 < K0Z S σq :=
    pos_of_mul_pos_left (by linarith : 0 < K0Z S σq * discreteGaussianSum σq ((s : ℝ) + r))
      (by linarith)
  refine ⟨h1, h2, hK, ?_⟩
  rw [AsZ]; linarith [mul_le_mul_of_nonneg_left h3 hK.le]

theorem DZ_eq (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) (z : ℤ) :
    DZ σq s r (s + z) = wsZ S σq r z / AsZ S σq s r := by
  have hK := (AsZ_mem S hσ1 hσ2 s r).2.2.1
  rw [wsZ_eq, DZ, AsZ, discreteGaussianPMF, discreteGaussianWeight]
  have e : ((s + z : ℤ) : ℝ) - ((s : ℝ) + r) = (z : ℝ) - r := by push_cast; ring
  rw [e, neg_div]
  field_simp

theorem DZ_pos {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (s : ℤ) (r : ℚ) (y : ℤ) :
    0 < DZ σq s r y := by
  have h := (Rat.cast_le (K := ℝ)).2 hσ1
  norm_num [falcon512S] at h
  exact discreteGaussianPMF_pos _ _ (by linarith) y

theorem hws0' (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) (z : ℤ) : 0 < wsZ S σq r z := by
  rw [wsZ_eq]; exact mul_pos (AsZ_mem S hσ1 hσ2 s r).2.2.1 (Real.exp_pos _)

theorem candC_inj (s : ℤ) : Set.InjOn (fun p : ℕ × Bool => s + zOf p.1 p.2) candC :=
  fun p _ q _ h => by
    obtain ⟨h1, h2⟩ := zOf_inj (add_left_cancel h)
    exact Prod.ext h1 h2

theorem not_mem_candC {s y : ℤ} (hy : y ∉ candC.image fun p : ℕ × Bool => s + zOf p.1 p.2) :
    y - s < -18 ∨ 19 < y - s := by
  by_contra h
  push Not at h
  obtain ⟨p, hp, hpz⟩ := zOf_surj h.1 h.2
  exact hy (Finset.mem_image.2 ⟨p, hp, by show s + zOf p.1 p.2 = y; rw [hpz]; ring⟩)

/-- The mass of `D_{σ̄,t̄}` off the candidates. -/
theorem compl_candC {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax)
    (s : ℤ) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    discreteGaussianMeasure σq ((s : ℝ) + r)
      ((candC.image fun p : ℕ × Bool => s + zOf p.1 p.2 : Finset ℤ) : Set ℤ)ᶜ ≤
        ENNReal.ofReal (11 / 2 ^ 81) := by
  obtain ⟨h1, h2⟩ := σq_real hσ1 hσ2
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
  refine (measure_mono fun y hy => ?_).trans (tail19_le h1 h2)
  change 19 ≤ |(y : ℝ) - (s + r)|
  rcases not_mem_candC hy with h | h
  · have : (y : ℝ) - s ≤ -19 := by exact_mod_cast (show y - s ≤ -19 by omega)
    rw [abs_of_neg (by linarith)]; linarith
  · have : (20 : ℝ) ≤ y - s := by exact_mod_cast (show 20 ≤ y - s by omega)
    rw [abs_of_pos (by linarith)]; linarith

theorem mass_candC {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax)
    (s : ℤ) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 - 11 / 2 ^ 81 ≤ ∑ p ∈ candC, DZ σq s r (s + zOf p.1 p.2) ∧
      ∑ p ∈ candC, DZ σq s r (s + zOf p.1 p.2) ≤ 1 := by
  have hσ0 : (0 : ℝ) < σq := by linarith [(σq_real hσ1 hσ2).1]
  have := isProbabilityMeasure_discreteGaussianMeasure (σq : ℝ) ((s : ℝ) + r) hσ0
  have hc := compl_candC hσ1 hσ2 s hr0 hr1
  set F := candC.image fun p : ℕ × Bool => s + zOf p.1 p.2
  have hS0 : 0 ≤ ∑ y ∈ F, DZ σq s r y := Finset.sum_nonneg fun y _ => (DZ_pos hσ1 s r y).le
  have hμF : discreteGaussianMeasure σq ((s : ℝ) + r) (F : Set ℤ) =
      ENNReal.ofReal (∑ y ∈ F, DZ σq s r y) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun y _ => (DZ_pos hσ1 s r y).le]
    simp_rw [DZ, ← discreteGaussianMeasure_singleton]
    rw [sum_eq_tsum_indicator, Measure.tsum_indicator_apply_singleton _ _
      (Finset.measurableSet F)]
  have h1 := measure_add_measure_compl (μ := discreteGaussianMeasure σq ((s : ℝ) + r))
    (Finset.measurableSet F)
  rw [measure_univ, hμF] at h1
  rw [← Finset.sum_image (candC_inj s)]
  constructor
  · have h2 : ENNReal.ofReal (1 - 11 / 2 ^ 81) + ENNReal.ofReal (11 / 2 ^ 81) ≤
        ENNReal.ofReal (∑ y ∈ F, DZ σq s r y) + ENNReal.ofReal (11 / 2 ^ 81) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
        show (1 : ℝ) - 11 / 2 ^ 81 + 11 / 2 ^ 81 = 1 by ring, ENNReal.ofReal_one, ← h1]
      exact add_le_add le_rfl hc
    exact (ENNReal.ofReal_le_ofReal_iff hS0).1
      (ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h2)
  · refine (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 ?_
    rw [ENNReal.ofReal_one, ← h1]
    exact le_self_add

theorem sum_ws_candC (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) :
    ∑ p ∈ candC, wsZ S σq r (zOf p.1 p.2) =
      AsZ S σq s r * ∑ p ∈ candC, DZ σq s r (s + zOf p.1 p.2) := by
  have hA : 0 < AsZ S σq s r := by linarith [(AsZ_mem S hσ1 hσ2 s r).1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [DZ_eq S hσ1 hσ2]; field_simp

theorem ws_le_E (S : SampChoices) {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℤ) (i : ℕ) (b : Bool) :
    wsZ S σq r (zOf i b) ≤ K0Z S σq * Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) := by
  rw [wsZ_eq, exp_split]
  refine mul_le_mul_of_nonneg_left ?_ (AsZ_mem S hσ1 hσ2 s r).2.2.1.le
  refine mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.2 ?_)
  rw [neg_nonpos]; exact_mod_cast xOf_nonneg hσ1 hσ2 hr0 hr1 _ _

theorem eps_ws_candC (S : SampChoices) {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℤ) :
    ∑ p ∈ candC, (epsT p.1 : ℝ) * wsZ S σq r (zOf p.1 p.2) ≤ 2 * K0Z S σq * (1 / 2 ^ 43) ∧
      ∑ p ∈ candC, (epsT p.1 : ℝ) ^ 2 * wsZ S σq r (zOf p.1 p.2) ≤
        2 * K0Z S σq * (1 / 2 ^ 81) := by
  have hK := (AsZ_mem S hσ1 hσ2 s r).2.2.1
  have hE := ws_le_E S hσ1 hσ2 hr0 hr1 s
  have hε : ∀ i, (0 : ℝ) ≤ epsT i := fun i => by exact_mod_cast epsT_nonneg i
  constructor
  · calc ∑ p ∈ candC, (epsT p.1 : ℝ) * wsZ S σq r (zOf p.1 p.2) ≤
          ∑ p ∈ candC, K0Z S σq * (Real.exp (-((p.1 ^ 2 : ℕ) * (kS : ℝ))) * epsT p.1) :=
        Finset.sum_le_sum fun p _ => by
          rw [← mul_assoc, mul_comm _ (epsT p.1 : ℝ)]
          exact mul_le_mul_of_nonneg_left (hE _ _) (hε _)
      _ = 2 * K0Z S σq * ∑ i ∈ Finset.range 19,
          Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) * epsT i := by
        rw [candC, sum_C_pair (f := fun i => K0Z S σq *
          (Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) * epsT i)), ← Finset.mul_sum]
        ring
      _ ≤ 2 * K0Z S σq * (1 / 2 ^ 43) := by gcongr; exact sum_E_eps
  · calc ∑ p ∈ candC, (epsT p.1 : ℝ) ^ 2 * wsZ S σq r (zOf p.1 p.2) ≤
          ∑ p ∈ candC, K0Z S σq * (Real.exp (-((p.1 ^ 2 : ℕ) * (kS : ℝ))) * epsT p.1 ^ 2) :=
        Finset.sum_le_sum fun p _ => by
          rw [← mul_assoc, mul_comm _ ((epsT p.1 : ℝ) ^ 2)]
          exact mul_le_mul_of_nonneg_left (hE _ _) (sq_nonneg _)
      _ = 2 * K0Z S σq * ∑ i ∈ Finset.range 19,
          Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) * epsT i ^ 2 := by
        rw [candC, sum_C_pair (f := fun i => K0Z S σq *
          (Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) * epsT i ^ 2)), ← Finset.mul_sum]
        ring
      _ ≤ 2 * K0Z S σq * (1 / 2 ^ 81) := by gcongr; exact sum_E_eps2

theorem accZ_candC (S : SampChoices) (σq r : ℚ) :
    (accZ falcon512S S σq r : ℝ) = ∑ p ∈ candC, (wZ falcon512S S σq r p.1 p.2 : ℝ) := by
  rw [accZ, tab_len, list_range_map_sum, candC, Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, add_comm]

/-- **The acceptance of a round** against `A*`. -/
theorem accZ_bounds (S : SampChoices) (hS : S.shiftRej = true) {σq r : ℚ}
    (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ℤ) :
    AsZ S σq s r * (1 - 1 / 2 ^ 42) ≤ accZ falcon512S S σq r ∧
      (accZ falcon512S S σq r : ℝ) ≤ AsZ S σq s r * (1 + 1 / 2 ^ 43) := by
  obtain ⟨hA1, -, -, hK⟩ := AsZ_mem S hσ1 hσ2 s r
  obtain ⟨hm1, hm2⟩ := mass_candC hσ1 hσ2 s hr0 hr1
  obtain ⟨hs1, -⟩ := eps_ws_candC S hσ1 hσ2 hr0 hr1 s
  have hsws := sum_ws_candC S hσ1 hσ2 s r
  have hcb := fun p (hp : p ∈ candC) => cand_bounds S hS hσ1 hσ2 hr0 hr1 (candC_le hp) p.2
  have hcard : candC.card = 38 := by simp [candC]
  rw [accZ_candC]
  set W := ∑ p ∈ candC, wsZ S σq r (zOf p.1 p.2)
  set As := AsZ S σq s r
  constructor
  · calc As * (1 - 1 / 2 ^ 42) ≤ W - ∑ p ∈ candC, (epsT p.1 : ℝ) * wsZ S σq r (zOf p.1 p.2) -
          1 / 2 ^ 44 * W - 38 * (1 / 2 ^ 62) := by
          rw [hsws]; linarith [mul_le_mul_of_nonneg_left hm1 (by linarith : (0 : ℝ) ≤ As),
            mul_le_mul_of_nonneg_left hm2 (by linarith : (0 : ℝ) ≤ As)]
      _ = ∑ p ∈ candC, (wsZ S σq r (zOf p.1 p.2) * (1 - epsT p.1 - 1 / 2 ^ 44) - 1 / 2 ^ 62) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, Finset.mul_sum,
            ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          push_cast
          congr 1
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p ∈ candC, (wZ falcon512S S σq r p.1 p.2 : ℝ) :=
          Finset.sum_le_sum fun p hp => (hcb p hp).2.1
  · calc ∑ p ∈ candC, (wZ falcon512S S σq r p.1 p.2 : ℝ) ≤
          ∑ p ∈ candC, wsZ S σq r (zOf p.1 p.2) * (1 + 1 / 2 ^ 43) :=
        Finset.sum_le_sum fun p hp => (hcb p hp).1
      _ = W * (1 + 1 / 2 ^ 43) := by rw [Finset.sum_mul]
      _ ≤ As * (1 + 1 / 2 ^ 43) := by
        rw [hsws]; linarith [mul_le_mul_of_nonneg_left hm2 (by linarith : (0 : ℝ) ≤ As)]

theorem DZ_s_ge {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ)
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 1 / 8 ≤ DZ σq s r s := by
  obtain ⟨h1, h2⟩ := σq_real hσ1 hσ2
  obtain ⟨-, -, -, hΘ⟩ := K0Z_theta (S := ⟨.plain, true, .b72⟩) ((s : ℝ) + r) hσ1 hσ2
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
  have hx : ((s : ℝ) - (s + r)) ^ 2 / (2 * (σq : ℝ) ^ 2) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [pow_le_one₀ hr0' hr1'.le (n := 2), pow_le_pow_left₀ (by norm_num) h1 2]
  have he := Real.add_one_le_exp (-(((s : ℝ) - (s + r)) ^ 2 / (2 * (σq : ℝ) ^ 2)))
  have hΘ0 : 0 < discreteGaussianSum σq ((s : ℝ) + r) := by
    linarith [(K0Z_theta (S := ⟨.plain, true, .b72⟩) ((s : ℝ) + r) hσ1 hσ2).2.2.1]
  rw [DZ, discreteGaussianPMF, discreteGaussianWeight, le_div_iff₀ hΘ0, neg_div]
  linarith

theorem ratio_gen {lam w ws As e D : ℝ} (hws : 0 < ws) (hAs : 0 < As) (hD : D = ws / As)
    (hw0 : 0 ≤ w) (hw : w ≤ ws * (1 + 1 / 2 ^ 43)) (hlam : lam ≤ 1 + 1 / 2 ^ 41)
    (he : e ≤ D / 2 ^ 42) : lam * w / As + e ≤ (1 + 1 / 2 ^ 40) * D := by
  have h1 : lam * w ≤ ws * (1 + 1 / 2 ^ 40 - 1 / 2 ^ 42) := by
    rcases le_or_gt lam 0 with hl | hl
    · linarith [mul_le_mul_of_nonneg_right hl hw0,
        mul_pos hws (by norm_num : (0 : ℝ) < 1 + 1 / 2 ^ 40 - 1 / 2 ^ 42)]
    calc lam * w ≤ (1 + 1 / 2 ^ 41) * (ws * (1 + 1 / 2 ^ 43)) :=
          mul_le_mul hlam hw hw0 (by norm_num)
      _ ≤ ws * (1 + 1 / 2 ^ 40 - 1 / 2 ^ 42) := by linarith
  have h2 : lam * w / As ≤ D * (1 + 1 / 2 ^ 40 - 1 / 2 ^ 42) := by
    rw [hD, div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h1 hAs.le
  linarith

/-- **The `χ²` sum over the candidates**, with `λ` within `2⁻⁴¹` of `1` and the exhaustion
mass `ρF ≤ 2⁻⁶⁴` at `⌊t̄⌋`. -/
theorem chi_fin (S : SampChoices) (hS : S.shiftRej = true) {σq r : ℚ}
    (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ℤ) {lam ρF : ℝ} (hl1 : lam ≤ 1 + 1 / 2 ^ 41) (hl2 : 1 - 1 / 2 ^ 41 ≤ lam)
    (hρ0 : 0 ≤ ρF) (hρ1 : ρF ≤ 1 / 2 ^ 64) :
    ∑ p ∈ candC, ((lam * wZ falcon512S S σq r p.1 p.2 / AsZ S σq s r +
      (if s + zOf p.1 p.2 = s then ρF else 0)) - DZ σq s r (s + zOf p.1 p.2)) ^ 2 /
        DZ σq s r (s + zOf p.1 p.2) ≤ 21 / 2 ^ 81 := by
  obtain ⟨hA1, -, -, hK⟩ := AsZ_mem S hσ1 hσ2 s r
  obtain ⟨-, hm2⟩ := mass_candC hσ1 hσ2 s hr0 hr1
  obtain ⟨-, hs2⟩ := eps_ws_candC S hσ1 hσ2 hr0 hr1 s
  have hsws := sum_ws_candC S hσ1 hσ2 s r
  have hDs := DZ_s_ge hσ1 hσ2 s hr0 hr1
  have hcard : candC.card = 38 := by simp [candC]
  set As := AsZ S σq s r
  have hAs : 0 < As := by linarith
  have hl0 : 0 ≤ lam ^ 2 := sq_nonneg _
  set c := 5 / 4 * lam ^ 2 / 2 ^ 86 + 10 * (lam - 1) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hT : ∀ p ∈ candC, ((lam * wZ falcon512S S σq r p.1 p.2 / As +
      (if s + zOf p.1 p.2 = s then ρF else 0)) - DZ σq s r (s + zOf p.1 p.2)) ^ 2 /
        DZ σq s r (s + zOf p.1 p.2) ≤
      (10 * lam ^ 2 * ((epsT p.1 : ℝ) ^ 2 * wsZ S σq r (zOf p.1 p.2)) +
        c * wsZ S σq r (zOf p.1 p.2)) / As + (5 / 2 * lam ^ 2 / 2 ^ 103 + 80 / 2 ^ 128) := by
    intro p hp
    have hws := (cand_bounds S hS hσ1 hσ2 hr0 hr1 (candC_le hp) p.2).2.2
    have hw0 := hws0' S hσ1 hσ2 s r (zOf p.1 p.2)
    refine (chi_term hw0 hAs (DZ_eq S hσ1 hσ2 s r _) rfl).trans ?_
    have h1 : ((wZ falcon512S S σq r p.1 p.2 : ℝ) - wsZ S σq r (zOf p.1 p.2)) ^ 2 /
        wsZ S σq r (zOf p.1 p.2) ≤ (8 * epsT p.1 ^ 2 + 1 / 2 ^ 86) *
          wsZ S σq r (zOf p.1 p.2) + 1 / 2 ^ 103 := by
      rw [div_le_iff₀ hw0]; linarith
    have h2 : 10 * (if s + zOf p.1 p.2 = s then ρF else 0) ^ 2 /
        DZ σq s r (s + zOf p.1 p.2) ≤ 80 / 2 ^ 128 := by
      split_ifs with h
      · rw [h, div_le_iff₀ (by linarith)]
        have := pow_le_pow_left₀ hρ0 hρ1 2
        linarith
      · norm_num
    have h3 : 5 / 4 * lam ^ 2 * (1 / 2 ^ 103) / As ≤ 5 / 2 * lam ^ 2 / 2 ^ 103 := by
      rw [div_le_iff₀ hAs]; linarith [mul_le_mul_of_nonneg_left hA1 hl0]
    calc 5 / 4 * lam ^ 2 * (((wZ falcon512S S σq r p.1 p.2 : ℝ) - wsZ S σq r (zOf p.1 p.2)) ^ 2 /
          wsZ S σq r (zOf p.1 p.2)) / As + 10 * (lam - 1) ^ 2 * (wsZ S σq r (zOf p.1 p.2) / As) +
          10 * (if s + zOf p.1 p.2 = s then ρF else 0) ^ 2 / DZ σq s r (s + zOf p.1 p.2) ≤
        5 / 4 * lam ^ 2 * ((8 * epsT p.1 ^ 2 + 1 / 2 ^ 86) * wsZ S σq r (zOf p.1 p.2) +
          1 / 2 ^ 103) / As + 10 * (lam - 1) ^ 2 * (wsZ S σq r (zOf p.1 p.2) / As) +
            80 / 2 ^ 128 := by gcongr
      _ = (10 * lam ^ 2 * ((epsT p.1 : ℝ) ^ 2 * wsZ S σq r (zOf p.1 p.2)) +
          c * wsZ S σq r (zOf p.1 p.2)) / As + 5 / 4 * lam ^ 2 * (1 / 2 ^ 103) / As +
            80 / 2 ^ 128 := by rw [hc]; field_simp; ring
      _ ≤ _ := by linarith
  refine (Finset.sum_le_sum hT).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.sum_div,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsws]
  have hX : 10 * lam ^ 2 * ∑ p ∈ candC, (epsT p.1 : ℝ) ^ 2 * wsZ S σq r (zOf p.1 p.2) ≤
      10 * lam ^ 2 * (As * (5 / 8) / 2 ^ 81) :=
    mul_le_mul_of_nonneg_left (hs2.trans (by linarith)) (by positivity)
  have hY : c * (As * ∑ p ∈ candC, DZ σq s r (s + zOf p.1 p.2)) ≤ c * As :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hAs.le hm2) hc0
  have hdiv : (10 * lam ^ 2 * ∑ p ∈ candC, (epsT p.1 : ℝ) ^ 2 * wsZ S σq r (zOf p.1 p.2) +
      c * (As * ∑ p ∈ candC, DZ σq s r (s + zOf p.1 p.2))) / As ≤
        10 * lam ^ 2 * (5 / 8) / 2 ^ 81 + c := by
    rw [div_le_iff₀ hAs]; linarith
  have hl3 : lam ^ 2 ≤ (1 + 1 / 2 ^ 41) ^ 2 := pow_le_pow_left₀ (by linarith) hl1 2
  have hl4 : (lam - 1) ^ 2 ≤ (1 / 2 ^ 41) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hcv : c ≤ 5 / 4 * (1 + 1 / 2 ^ 41) ^ 2 / 2 ^ 86 + 10 * (1 / 2 ^ 41) ^ 2 := by
    rw [hc]; linarith
  push_cast
  linarith

/-- **Node.** Closeness of `lawZ` at Falcon-512 with shift rejection, both tables: nonnegative,
within `uB` of `D_{σ̄,t̄}` pointwise, `χ² ≤ chi2B`, at every `σ̄ ∈ [σmin, σmax]` and `t̄`. -/
theorem lawZ_close (S : SampChoices) (hS : S.shiftRej = true) (σ t : Fx 64)
    (hσ : inRangeB falcon512S σ = true) :
    (∀ y, 0 ≤ lawZ falcon512S S σ t y) ∧
      (∀ y, (lawZ falcon512S S σ t y : ℝ) ≤
        uB * discreteGaussianPMF σ.toReal t.toReal y) ∧
      ∑' y, ENNReal.ofReal (((lawZ falcon512S S σ t y : ℝ) -
        discreteGaussianPMF σ.toReal t.toReal y) ^ 2 /
          discreteGaussianPMF σ.toReal t.toReal y) ≤ ENNReal.ofReal chi2B := by
  have hσb : falcon512S.σmin ≤ σ.toRat ∧ σ.toRat ≤ falcon512S.σmax := by
    simpa only [inRangeB, Bool.and_eq_true, decide_eq_true_eq] using hσ
  obtain ⟨hσ1, hσ2⟩ := hσb
  have hs : t.toInt .floor = ⌊t.toRat⌋ := toInt_floor_eq t
  have hr0 : 0 ≤ t.toRat - t.toInt .floor := by rw [hs]; exact sub_nonneg.2 (Int.floor_le _)
  have hr1 : t.toRat - t.toInt .floor < 1 := by rw [hs]; linarith [Int.lt_floor_add_one t.toRat]
  have htR : t.toReal = ((t.toInt .floor : ℤ) : ℝ) + ((t.toRat - t.toInt .floor : ℚ) : ℝ) := by
    rw [Fx.toReal_eq_toRat]; push_cast; ring
  have hlaw : ∀ y, lawZ falcon512S S σ t y =
      (if y = t.toInt .floor then (1 - accZ falcon512S S σ.toRat (t.toRat - t.toInt .floor)) ^ 128
        else 0) + (1 - (1 - accZ falcon512S S σ.toRat (t.toRat - t.toInt .floor)) ^ 128) /
          accZ falcon512S S σ.toRat (t.toRat - t.toInt .floor) *
            wZz falcon512S S σ.toRat (t.toRat - t.toInt .floor) (y - t.toInt .floor) :=
    fun y => rfl
  simp only [hlaw]
  rw [Fx.toReal_eq_toRat σ, htR]
  clear hlaw htR hs hσ
  generalize t.toRat - t.toInt .floor = r at hr0 hr1 ⊢
  generalize t.toInt .floor = s
  generalize σ.toRat = σq at hσ1 hσ2 ⊢
  have hDZ : ∀ y, discreteGaussianPMF (σq : ℝ) ((s : ℝ) + r) y = DZ σq s r y := fun y => rfl
  simp only [hDZ]
  obtain ⟨hAlo, hAup⟩ := accZ_bounds S hS hσ1 hσ2 hr0 hr1 s
  obtain ⟨hAs1, -, -, -⟩ := AsZ_mem S hσ1 hσ2 s r
  set As := AsZ S σq s r with hAsd
  set A := accZ falcon512S S σq r with hAd
  have hA0 : (0 : ℝ) < A := by linarith
  have hA1 : (A : ℝ) ≤ 1 := by nlinarith [(AsZ_mem S hσ1 hσ2 s r).2.1]
  have hA0q : (0 : ℚ) < A := by exact_mod_cast hA0
  set ρF : ℚ := (1 - A) ^ 128 with hρF
  have hρF0 : (0 : ℝ) ≤ ρF := by rw [hρF]; push_cast; exact pow_nonneg (by linarith) _
  have hρF1 : (ρF : ℝ) ≤ 1 / 2 ^ 64 := by
    rw [hρF]; push_cast
    calc (1 - (A : ℝ)) ^ 128 ≤ (3 / 5) ^ 128 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 128
      _ ≤ 1 / 2 ^ 64 := by norm_num
  set lam : ℝ := (1 - ρF) * As / A with hlam
  have hlam1 : lam ≤ 1 + 1 / 2 ^ 41 := by
    rw [hlam, div_le_iff₀ hA0]; linarith [mul_nonneg hρF0 (by linarith : (0 : ℝ) ≤ As)]
  have hlam2 : 1 - 1 / 2 ^ 41 ≤ lam := by
    rw [hlam, le_div_iff₀ hA0]
    linarith [mul_le_mul_of_nonneg_right hρF1 (by linarith : (0 : ℝ) ≤ As)]
  have hLeq : ∀ y, ((((if y = s then ρF else 0) + (1 - ρF) / A * wZz falcon512S S σq r (y - s) :
      ℚ)) : ℝ) = lam * (wZz falcon512S S σq r (y - s) : ℝ) / As +
        (if y = s then (ρF : ℝ) else 0) := fun y => by
    rw [hlam]; push_cast; field_simp; split_ifs <;> ring
  set F := candC.image fun p : ℕ × Bool => s + zOf p.1 p.2 with hF
  have hLout : ∀ y, y ∉ F → ((((if y = s then ρF else 0) +
      (1 - ρF) / A * wZz falcon512S S σq r (y - s) : ℚ)) : ℝ) = 0 := fun y hy => by
    have hys : y ≠ s := fun h => hy (Finset.mem_image.2 ⟨(0, false), by simp [candC], by
      simp [zOf, h]⟩)
    rw [wZz_out S σq r (not_mem_candC hy)]
    simp [hys]
  have hwp : ∀ p : ℕ × Bool, wZz falcon512S S σq r (s + zOf p.1 p.2 - s) =
      wZ falcon512S S σq r p.1 p.2 := fun p => by rw [add_sub_cancel_left, wZz_zOf]
  have hDs := DZ_s_ge hσ1 hσ2 s hr0 hr1
  refine ⟨fun y => ?_, fun y => ?_, ?_⟩
  · have hw0 : 0 ≤ wZz falcon512S S σq r (y - s) := by
      unfold wZz wZ; split_ifs <;> positivity
    have hκ : (0 : ℚ) ≤ 1 - ρF := by
      have : (ρF : ℝ) ≤ 1 := hρF1.trans (by norm_num)
      exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - ρF)
    have hρ : (0 : ℚ) ≤ ρF := by exact_mod_cast hρF0
    exact add_nonneg (by split_ifs <;> simp [hρ]) (mul_nonneg (div_nonneg hκ hA0q.le) hw0)
  · have huB : ((uB : ℚ) : ℝ) = 1 + 1 / 2 ^ 40 := by norm_num [uB]
    rw [huB]
    by_cases hy : y ∈ F
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
      rw [hLeq, hwp]
      have hcb := cand_bounds S hS hσ1 hσ2 hr0 hr1 (candC_le hp) p.2
      refine ratio_gen (hws0' S hσ1 hσ2 s r _) (by linarith) (DZ_eq S hσ1 hσ2 s r _)
        (by unfold wZ; positivity) hcb.1 hlam1 ?_
      split_ifs with h
      · rw [h]; linarith
      · exact div_nonneg (DZ_pos hσ1 s r _).le (by norm_num)
    · rw [hLout y hy]
      exact mul_nonneg (by norm_num) (DZ_pos hσ1 s r y).le
  · set f : ℤ → ℝ := fun y => ((((if y = s then ρF else 0) +
      (1 - ρF) / A * wZz falcon512S S σq r (y - s) : ℚ)) - DZ σq s r y) ^ 2 / DZ σq s r y
      with hf
    have hf0 : ∀ y, 0 ≤ f y := fun y => div_nonneg (sq_nonneg _) (DZ_pos hσ1 s r y).le
    have hc := compl_candC hσ1 hσ2 s hr0 hr1
    rw [← ENNReal.sum_add_tsum_compl F (fun y => ENNReal.ofReal (f y))]
    have hcompl : ∑' y : ↥((F : Set ℤ)ᶜ), ENNReal.ofReal (f y) =
        discreteGaussianMeasure σq ((s : ℝ) + r) (F : Set ℤ)ᶜ := by
      rw [tsum_subtype ((F : Set ℤ)ᶜ) fun y => ENNReal.ofReal (f y),
        ← Measure.tsum_indicator_apply_singleton _ _ (Finset.measurableSet F).compl]
      refine tsum_congr fun y => ?_
      by_cases hy : y ∈ (F : Set ℤ)ᶜ
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, discreteGaussianMeasure_singleton]
        refine congrArg ENNReal.ofReal ?_
        simp only [hf]
        rw [hLout y hy]
        change ((0 : ℝ) - DZ σq s r y) ^ 2 / DZ σq s r y = DZ σq s r y
        rw [zero_sub, neg_sq, sq, mul_self_div_self]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    rw [hcompl, ← ENNReal.ofReal_sum_of_nonneg fun y _ => hf0 y]
    have hfin : ∑ y ∈ F, f y ≤ 21 / 2 ^ 81 := by
      rw [Finset.sum_image (candC_inj s)]
      refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_)
        (chi_fin S hS hσ1 hσ2 hr0 hr1 s hlam1 hlam2 hρF0 hρF1)
      simp only [hf]
      rw [hLeq, hwp]
    calc ENNReal.ofReal (∑ y ∈ F, f y) + discreteGaussianMeasure σq ((s : ℝ) + r) (F : Set ℤ)ᶜ ≤
          ENNReal.ofReal (21 / 2 ^ 81) + ENNReal.ofReal (11 / 2 ^ 81) :=
        add_le_add (ENNReal.ofReal_le_ofReal hfin) hc
      _ = ENNReal.ofReal chi2B := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num [chi2B]

omit [LawfulMonad m] in
/-- **Per-call closeness**: the Rényi MGF of order `a ≥ 2` of SamplerZ with shift rejection
against `D_{σ̄,t̄}` is at most `exp((a - 1)·εZ a)`. -/
theorem samplerZ_mgf {a : ℝ} (ha : 2 ≤ a) (S : SampChoices) (hS : S.shiftRej = true)
    (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64) (hσ : inRangeB falcon512S σ = true) :
    renyiMGF a 𝒟[samplerZ falcon512S S ub σ t] (discreteGaussianMeasure σ.toReal t.toReal) ≤
      ENNReal.ofReal (Real.exp ((a - 1) * εZ a)) := by
  obtain ⟨h0, hu, hχ⟩ := lawZ_close S hS σ t hσ
  refine (renyiMGF_le_chi2 ha (by norm_num [uB]) (by norm_num [chi2B]) _ _ _ (falcon512S_σ_pos hσ)
    (fun y => (lawZ falcon512S S σ t y : ℝ)) (fun y => by exact_mod_cast h0 y)
    (samplerZ_law falcon512S S (tab_okB _) ub hub σ t) (evalDist_apply_univ_le_one _) hu
    hχ).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (le_of_eq ?_).trans (Real.add_one_le_exp ((a - 1) * εZ a))
  rw [εZ]
  ring

/-! ## Saturating against rejecting a shift `≥ 64` -/

theorem etvDist_le_of_singleton {μ ν : Measure ℤ} {f g : ℤ → ℝ} (F : Finset ℤ)
    (hμ : ∀ y, μ {y} = ENNReal.ofReal (f y)) (hν : ∀ y, ν {y} = ENNReal.ofReal (g y))
    (hf : ∀ y ∉ F, f y = 0) (hg : ∀ y ∉ F, g y = 0) :
    μ.etvDist ν ≤ ENNReal.ofReal (∑ y ∈ F, |f y - g y|) := by
  have h1 : μ.etvDist ν ≤ ∑' y, ENNReal.absDiff (μ {y}) (ν {y}) := by
    refine iSup_le fun s => ?_
    rw [← Measure.tsum_indicator_apply_singleton μ s.1 s.2,
      ← Measure.tsum_indicator_apply_singleton ν s.1 s.2]
    refine (ENNReal.absDiff_tsum_le _ _).trans (ENNReal.tsum_le_tsum fun y => ?_)
    by_cases hy : y ∈ s.1 <;> simp [Set.indicator, hy]
  refine h1.trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun y _ => abs_nonneg _,
    tsum_eq_sum (s := F) fun y hy => by rw [hμ, hν, hf y hy, hg y hy]; simp]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [hμ, hν, ENNReal.absDiff_le_iff]
  constructor
  · exact (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (f y - g y)])).trans
      ENNReal.ofReal_add_le
  · exact (ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (f y - g y)])).trans
      ENNReal.ofReal_add_le

theorem approxExp_le {x ccs : ℚ} (hx0 : 0 ≤ x) (hx1 : x < falcon512S.ln2) (hc0 : 1 / 2 ≤ ccs)
    (hc1 : ccs ≤ 1) : approxExp x ccs < 3 * 2 ^ 62 := by
  have h := (abs_le.1 (approxExp_err hx0 hx1 hc0 hc1)).2
  have hc1' : (ccs : ℝ) ≤ 1 := by exact_mod_cast hc1
  have hc0' : (0 : ℝ) ≤ ccs := by
    have := (Rat.cast_le (K := ℝ)).2 hc0; push_cast at this; linarith
  have hx0' : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have hE : Real.exp (-(x : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hg : (ccs : ℝ) * Real.exp (-(x : ℝ)) ≤ 1 :=
    (mul_le_mul hc1' hE (Real.exp_pos _).le zero_le_one).trans_eq (one_mul 1)
  have : (approxExp x ccs : ℝ) < 3 * 2 ^ 62 := by nlinarith [Real.exp_pos (-(x : ℝ))]
  exact_mod_cast this

/-- Saturating accepts at least as much as rejecting, at most `2` units more, and the same for
`x < 44` (no shift `≥ 64`). -/
theorem accW_sat {x ccs : ℚ} (hc0 : 1 / 2 ≤ ccs) (hc1 : ccs ≤ 1) :
    accW falcon512S true x ccs ≤ accW falcon512S false x ccs ∧
      accW falcon512S false x ccs ≤ accW falcon512S true x ccs + 2 ∧
      (x < 44 → accW falcon512S false x ccs = accW falcon512S true x ccs) := by
  have hL2 : (0 : ℚ) < falcon512S.ln2 := by norm_num [falcon512S]
  simp only [accW]
  set s := ⌊x / falcon512S.ln2⌋ with hs
  have hsL : (s : ℚ) * falcon512S.ln2 ≤ x := by
    have := Int.floor_le (x / falcon512S.ln2); rwa [le_div_iff₀ hL2] at this
  have hsU : x < ((s : ℚ) + 1) * falcon512S.ln2 := by
    have := Int.lt_floor_add_one (x / falcon512S.ln2); rwa [div_lt_iff₀ hL2] at this
  by_cases h64 : 64 ≤ s
  · simp only [h64, decide_true, Bool.and_self, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, zero_le, zero_add, true_and]
    refine ⟨?_, fun hx44 => ?_⟩
    · rw [min_eq_right (by omega : (63 : ℤ) ≤ s)]
      refine (min_le_left _ _).trans (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul
        (by positivity)).2 ?_))
      have h1 : 0 ≤ x - s * falcon512S.ln2 := by linarith
      have h2 : x - s * falcon512S.ln2 < falcon512S.ln2 := by linarith
      have := approxExp_le h1 h2 hc0 hc1
      norm_num
      omega
    · exfalso
      have : (64 : ℚ) * falcon512S.ln2 ≤ x :=
        le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast h64) hL2.le) hsL
      norm_num [falcon512S] at this
      linarith
  · have h64' : ¬(64 ≤ s) := h64
    simp only [h64', decide_false, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, le_refl, le_add_iff_nonneg_right, zero_le, implies_true, and_self]

theorem xOf_lt_44 {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq) (hr0 : 0 ≤ r) (hr1 : r < 1) {i : ℕ}
    (hi : i ≤ 14) (b : Bool) : xOf falcon512S σq r i b < 44 := by
  have hσ0 : 0 < σq := lt_of_lt_of_le (by norm_num [falcon512S]) hσ1
  have h1 : ((zOf i b : ℚ) - r) ^ 2 / (2 * σq ^ 2) ≤
      ((i : ℚ) + 1) ^ 2 / (2 * falcon512S.σmin ^ 2) :=
    div_le_div₀ (by positivity) (zOf_sub_sq hr0 hr1 i b).2 (by norm_num [falcon512S])
      (by have : (0 : ℚ) ≤ falcon512S.σmin := by norm_num [falcon512S]
          gcongr)
  have h2 : ((i : ℚ) + 1) ^ 2 / (2 * falcon512S.σmin ^ 2) - (i ^ 2 : ℕ) * kS < 44 := by
    interval_cases i <;> norm_num [falcon512S, kS]
  rw [xOf_eq]
  linarith

theorem pdt_tail15 (b : BaseBits) :
    ∑ i ∈ Finset.range 19, (if 15 ≤ i then (pdtZ (falcon512S.tab b) i : ℝ) else 0) /
      2 ^ (falcon512S.tab b).w ≤ 1 / 2 ^ 50 := by
  cases b <;> norm_num [Finset.sum_range_succ, pdtZ, falcon512S, tab72, rcdt72, tab79, rcdt79]

/-- **Per candidate**: saturating adds at most `pdt[i]/2ʷ·2⁻⁶⁴`, and nothing for `i ≤ 14`. -/
theorem wZ_sat (c : Centre) (b0 : BaseBits) {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) (i : ℕ) (b : Bool) :
    (wZ falcon512S ⟨c, true, b0⟩ σq r i b : ℝ) ≤ wZ falcon512S ⟨c, false, b0⟩ σq r i b ∧
      (wZ falcon512S ⟨c, false, b0⟩ σq r i b : ℝ) - wZ falcon512S ⟨c, true, b0⟩ σq r i b ≤
        (if 15 ≤ i then (pdtZ (falcon512S.tab b0) i : ℝ) else 0) /
          2 ^ (falcon512S.tab b0).w / 2 ^ 64 := by
  have hσ0 : (0 : ℚ) < σq := lt_of_lt_of_le (by norm_num [falcon512S]) hσ1
  have hc0 : 1 / 2 ≤ falcon512S.σmin / σq := by
    rw [le_div_iff₀ hσ0]; norm_num [falcon512S] at hσ2 ⊢; linarith
  have hc1 : falcon512S.σmin / σq ≤ 1 := by rw [div_le_one hσ0]; exact hσ1
  obtain ⟨h1, h2, h3⟩ := accW_sat (x := xOf falcon512S σq r i b) hc0 hc1
  simp only [wZ]
  push_cast
  set p : ℝ := (pdtZ (falcon512S.tab b0) i : ℝ) / 2 ^ ((falcon512S.tab b0).w + 1)
  have hp : 0 ≤ p := by positivity
  set a1 := accW falcon512S true (xOf falcon512S σq r i b) (falcon512S.σmin / σq)
  set a2 := accW falcon512S false (xOf falcon512S σq r i b) (falcon512S.σmin / σq)
  have h1' : (a1 : ℝ) ≤ a2 := by exact_mod_cast h1
  have h2' : (a2 : ℝ) ≤ a1 + 2 := by exact_mod_cast h2
  refine ⟨by gcongr, ?_⟩
  split_ifs with hi
  · have : p * ((a2 : ℝ) / 2 ^ 64) - p * ((a1 : ℝ) / 2 ^ 64) ≤ p * (2 / 2 ^ 64) := by
      rw [← mul_sub]; gcongr; rw [← sub_div]; gcongr; linarith
    calc _ ≤ p * (2 / 2 ^ 64) := this
      _ = _ := by simp only [p]; rw [pow_succ]; field_simp
  · have := h3 (xOf_lt_44 hσ1 hr0 hr1 (by omega) b)
    rw [this]; simp

theorem tv_term {e ρ1 ρ2 w1 w2 A1 A2 : ℝ} (he0 : 0 ≤ e) (hρ1 : 0 ≤ ρ1) (hρ2 : 0 ≤ ρ2)
    (hρ2' : ρ2 ≤ 1) (hw2 : 0 ≤ w2) (hw : w2 ≤ w1) (hA2 : 0 < A2) (hA : A2 ≤ A1) :
    |(e * ρ1 + (1 - ρ1) / A1 * w1) - (e * ρ2 + (1 - ρ2) / A2 * w2)| ≤
      e * (ρ1 + ρ2) + (ρ1 + ρ2) * (w1 / A1) + (w1 - w2) / A1 + w2 * (1 / A2 - 1 / A1) := by
  have hA1 : 0 < A1 := by linarith
  have hinv : 1 / A1 ≤ 1 / A2 := one_div_le_one_div_of_le hA2 hA
  have e1 : (e * ρ1 + (1 - ρ1) / A1 * w1) - (e * ρ2 + (1 - ρ2) / A2 * w2) =
      e * (ρ1 - ρ2) + (ρ2 - ρ1) * (w1 / A1) + (1 - ρ2) * ((w1 - w2) / A1) +
        (1 - ρ2) * w2 * (1 / A1 - 1 / A2) := by field_simp; ring
  have hq : 0 ≤ w1 / A1 := div_nonneg (by linarith) hA1.le
  have hd : 0 ≤ (w1 - w2) / A1 := div_nonneg (by linarith) hA1.le
  have t1 : |e * (ρ1 - ρ2)| ≤ e * (ρ1 + ρ2) := by
    rw [abs_mul, abs_of_nonneg he0]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) he0
  have t2 : |(ρ2 - ρ1) * (w1 / A1)| ≤ (ρ1 + ρ2) * (w1 / A1) := by
    rw [abs_mul, abs_of_nonneg hq]
    exact mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) hq
  have t3 : |(1 - ρ2) * ((w1 - w2) / A1)| ≤ (w1 - w2) / A1 := by
    rw [abs_mul, abs_of_nonneg hd, abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_left hd (by linarith)
  have t4 : |(1 - ρ2) * w2 * (1 / A1 - 1 / A2)| ≤ w2 * (1 / A2 - 1 / A1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ρ2), abs_of_nonneg hw2,
      abs_of_nonpos (by linarith), neg_sub]
    calc (1 - ρ2) * w2 * (1 / A2 - 1 / A1) ≤ 1 * w2 * (1 / A2 - 1 / A1) := by
          gcongr
          linarith
      _ = w2 * (1 / A2 - 1 / A1) := by ring
  rw [e1]
  calc _ ≤ |e * (ρ1 - ρ2)| + |(ρ2 - ρ1) * (w1 / A1)| + |(1 - ρ2) * ((w1 - w2) / A1)| +
        |(1 - ρ2) * w2 * (1 / A1 - 1 / A2)| :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

omit [LawfulMonad m] in
/-- **Node.** Saturating a shift `≥ 64` instead of rejecting moves at most `2⁻¹¹⁰` per call. -/
theorem samplerZ_tv (S : SampChoices) (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64)
    (hσ : inRangeB falcon512S σ = true) :
    (𝒟[samplerZ falcon512S S ub σ t]).etvDist
        𝒟[samplerZ falcon512S { S with shiftRej := true } ub σ t] ≤
      ENNReal.ofReal (if S.shiftRej then 0 else 1 / 2 ^ 110) := by
  obtain ⟨c, rej, b0⟩ := S
  cases rej
  swap
  · simp
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hσb : falcon512S.σmin ≤ σ.toRat ∧ σ.toRat ≤ falcon512S.σmax := by
    simpa only [inRangeB, Bool.and_eq_true, decide_eq_true_eq] using hσ
  obtain ⟨hσ1, hσ2⟩ := hσb
  have hs : t.toInt .floor = ⌊t.toRat⌋ := toInt_floor_eq t
  have hr0 : 0 ≤ t.toRat - t.toInt .floor := by rw [hs]; exact sub_nonneg.2 (Int.floor_le _)
  have hr1 : t.toRat - t.toInt .floor < 1 := by rw [hs]; linarith [Int.lt_floor_add_one t.toRat]
  set S1 : SampChoices := ⟨c, false, b0⟩
  set S2 : SampChoices := ⟨c, true, b0⟩
  set s := t.toInt .floor with hsd
  set r := t.toRat - s with hrd
  set F := candC.image fun p : ℕ × Bool => s + zOf p.1 p.2 with hF
  have hlaw : ∀ (S' : SampChoices) y, lawZ falcon512S S' σ t y =
      (if y = s then (1 - accZ falcon512S S' σ.toRat r) ^ 128 else 0) +
        (1 - (1 - accZ falcon512S S' σ.toRat r) ^ 128) / accZ falcon512S S' σ.toRat r *
          wZz falcon512S S' σ.toRat r (y - s) := fun _ _ => rfl
  have hout : ∀ (S' : SampChoices) y, y ∉ F → (lawZ falcon512S S' σ t y : ℝ) = 0 :=
    fun S' y hy => by
      have hys : y ≠ s := fun h => hy (Finset.mem_image.2 ⟨(0, false), by simp [candC], by
        simp [zOf, h]⟩)
      rw [hlaw, wZz_out S' _ r (not_mem_candC hy)]
      simp [hys]
  refine (etvDist_le_of_singleton F (samplerZ_law _ _ (tab_okB _) ub hub σ t)
    (samplerZ_law _ _ (tab_okB _) ub hub σ t) (hout S1) (hout S2)).trans
      (ENNReal.ofReal_le_ofReal ?_)
  simp only [hlaw]
  rw [Finset.sum_image (candC_inj s)]
  clear_value s r F
  generalize σ.toRat = σq at hσ1 hσ2 ⊢
  obtain ⟨hA2lo, hA2up⟩ := accZ_bounds S2 rfl hσ1 hσ2 hr0 hr1 s
  obtain ⟨hAs1, hAs2, -, -⟩ := AsZ_mem S2 hσ1 hσ2 s r
  have hsat : ∀ p : ℕ × Bool, (wZ falcon512S S2 σq r p.1 p.2 : ℝ) ≤
      wZ falcon512S S1 σq r p.1 p.2 ∧
      (wZ falcon512S S1 σq r p.1 p.2 : ℝ) - wZ falcon512S S2 σq r p.1 p.2 ≤
        (if 15 ≤ p.1 then (pdtZ (falcon512S.tab b0) p.1 : ℝ) else 0) /
          2 ^ (falcon512S.tab b0).w / 2 ^ 64 :=
    fun p => wZ_sat c b0 hσ1 hσ2 hr0 hr1 p.1 p.2
  set A1 := accZ falcon512S S1 σq r with hA1d
  set A2 := accZ falcon512S S2 σq r with hA2d
  have hA1s := accZ_candC S1 σq r
  have hA2s := accZ_candC S2 σq r
  rw [← hA1d] at hA1s
  rw [← hA2d] at hA2s
  have hA12 : (A2 : ℝ) ≤ A1 := by
    rw [hA1s, hA2s]; exact Finset.sum_le_sum fun p _ => (hsat p).1
  have hδ : (A1 : ℝ) - A2 ≤ 1 / 2 ^ 113 := by
    rw [hA1s, hA2s, ← Finset.sum_sub_distrib]
    calc ∑ p ∈ candC, ((wZ falcon512S S1 σq r p.1 p.2 : ℝ) - wZ falcon512S S2 σq r p.1 p.2) ≤
          ∑ p ∈ candC, (if 15 ≤ p.1 then (pdtZ (falcon512S.tab b0) p.1 : ℝ) else 0) /
            2 ^ (falcon512S.tab b0).w / 2 ^ 64 := Finset.sum_le_sum fun p _ => (hsat p).2
      _ = 2 * (∑ i ∈ Finset.range 19, (if 15 ≤ i then (pdtZ (falcon512S.tab b0) i : ℝ) else 0) /
            2 ^ (falcon512S.tab b0).w) / 2 ^ 64 := by
          rw [candC, sum_C_pair (f := fun i => (if 15 ≤ i then (pdtZ (falcon512S.tab b0) i : ℝ)
            else 0) / 2 ^ (falcon512S.tab b0).w / 2 ^ 64), ← Finset.sum_div]
          ring
      _ ≤ 2 * (1 / 2 ^ 50) / 2 ^ 64 := by gcongr; exact pdt_tail15 b0
      _ = 1 / 2 ^ 113 := by norm_num
  have hA2pos : (49 / 100 : ℝ) ≤ A2 := by linarith
  have hA1le : (A1 : ℝ) ≤ 1 := by linarith
  have hρ : ∀ A : ℚ, (49 / 100 : ℝ) ≤ A → (A : ℝ) ≤ 1 →
      (0 : ℝ) ≤ ((1 - A) ^ 128 : ℚ) ∧ (((1 - A) ^ 128 : ℚ) : ℝ) ≤ 1 / 2 ^ 120 := fun A h1 h2 => by
    push_cast
    exact ⟨pow_nonneg (by linarith) _, (pow_le_pow_left₀ (by linarith) (by linarith : 1 - (A : ℝ) ≤
      51 / 100) 128).trans (by norm_num)⟩
  obtain ⟨hρ10, hρ11⟩ := hρ A1 (by linarith) hA1le
  obtain ⟨hρ20, hρ21⟩ := hρ A2 hA2pos (by linarith)
  set ρ1 : ℝ := (((1 - A1) ^ 128 : ℚ) : ℝ)
  set ρ2 : ℝ := (((1 - A2) ^ 128 : ℚ) : ℝ)
  have hterm : ∀ p ∈ candC, |((((if s + zOf p.1 p.2 = s then (1 - A1) ^ 128 else 0) +
      (1 - (1 - A1) ^ 128) / A1 * wZz falcon512S S1 σq r (s + zOf p.1 p.2 - s) : ℚ)) : ℝ) -
        ((((if s + zOf p.1 p.2 = s then (1 - A2) ^ 128 else 0) +
          (1 - (1 - A2) ^ 128) / A2 * wZz falcon512S S2 σq r (s + zOf p.1 p.2 - s) : ℚ)) : ℝ)| ≤
      (if s + zOf p.1 p.2 = s then (1 : ℝ) else 0) * (ρ1 + ρ2) + (ρ1 + ρ2) *
        ((wZ falcon512S S1 σq r p.1 p.2 : ℝ) / A1) +
          ((wZ falcon512S S1 σq r p.1 p.2 : ℝ) - wZ falcon512S S2 σq r p.1 p.2) / A1 +
            (wZ falcon512S S2 σq r p.1 p.2 : ℝ) * (1 / A2 - 1 / A1) := fun p _ => by
    rw [add_sub_cancel_left, wZz_zOf, wZz_zOf]
    have h := tv_term (e := if s + zOf p.1 p.2 = s then (1 : ℝ) else 0) (by split_ifs <;> norm_num)
      hρ10 hρ20 (by linarith) (by unfold wZ; positivity) (hsat p).1 (by linarith) hA12
    convert h using 3 <;> push_cast <;> split_ifs <;> simp [ρ1, ρ2]
  refine (Finset.sum_le_sum hterm).trans ?_
  have he : ∑ p ∈ candC, (if s + zOf p.1 p.2 = s then (1 : ℝ) else 0) ≤ 1 := by
    have : ∀ p : ℕ × Bool, (s + zOf p.1 p.2 = s ↔ p = (0, false)) := fun p => by
      constructor
      · intro h
        have h' : zOf p.1 p.2 = zOf 0 false := by
          rw [show zOf 0 false = 0 by simp [zOf]]; omega
        obtain ⟨h1, h2⟩ := zOf_inj h'
        exact Prod.ext h1 h2
      · rintro rfl; simp [zOf]
    simp only [this, Finset.sum_ite_eq', candC]
    split_ifs <;> norm_num
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_div,
    ← hA1s, Finset.sum_sub_distrib, ← hA2s]
  have hA1p : (0 : ℝ) < A1 := by linarith
  rw [div_self hA1p.ne', mul_one, mul_sub, mul_one_div_cancel (by linarith), mul_one_div]
  have hfin : ((A1 : ℝ) - A2) / A1 ≤ 1 / 2 ^ 113 / (49 / 100) := by
    rw [div_le_div_iff₀ hA1p (by norm_num)]; linarith
  have hfin2 : (1 : ℝ) - A2 / A1 = (A1 - A2) / A1 := by field_simp
  rw [hfin2]
  have hρs : 0 ≤ ρ1 + ρ2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right he hρs]

end FalconPrecision.Exec
