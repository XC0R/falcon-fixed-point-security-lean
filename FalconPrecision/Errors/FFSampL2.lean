/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFTL2

/-! # ℓ2 center error of one ffSampling node

One node of ffSampling (ePrint 2026/1531 Alg. 8) at size `2^(L+1)`, errors in ℓ2 over all slots. Per
slot the map `(δt0, δt1) ↦ (δt1, δt0 + ℓ̂·δt1)` has norm `N` whenever `(N² - 1)(N² - 1 - Λ²) ≥ Λ²`,
`N² ≥ 1 + Λ²`, `|ℓ̂| ≤ Λ` (e.g. `N = (Λ + √(Λ² + 4))/2`), and a split has norm `√2(1/2 + δ)`. With
the line-10 extra term `w` (merge error of `ẑ1`, `ℓ̂ - ℓ`, rounding) and split roundings, the ℓ2
error of the four child inputs is at most `√2(1/2 + δ)(N‖δt‖ + ‖w‖) + 2√(2^L)(r + 2δB)`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFSamp

open FalconPrecision.Errors.FFTRec

theorem pair_norm (x0 x1 ℓ : ℂ) (Λ N : ℝ) (hℓ : ‖ℓ‖ ≤ Λ) (hN1 : 1 + Λ ^ 2 ≤ N ^ 2)
    (hN : Λ ^ 2 ≤ (N ^ 2 - 1) * (N ^ 2 - 1 - Λ ^ 2)) :
    ‖x1‖ ^ 2 + ‖x0 + ℓ * x1‖ ^ 2 ≤ N ^ 2 * (‖x0‖ ^ 2 + ‖x1‖ ^ 2) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hℓ
  have h1 : ‖x0 + ℓ * x1‖ ≤ ‖x0‖ + Λ * ‖x1‖ := by
    calc ‖x0 + ℓ * x1‖ ≤ ‖x0‖ + ‖ℓ * x1‖ := norm_add_le _ _
      _ ≤ ‖x0‖ + Λ * ‖x1‖ := by rw [norm_mul]; gcongr
  have h2 : ‖x0 + ℓ * x1‖ ^ 2 ≤ (‖x0‖ + Λ * ‖x1‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  set a := ‖x0‖; set b := ‖x1‖
  set A := N ^ 2 - 1; set C := N ^ 2 - 1 - Λ ^ 2
  have hC : 0 ≤ C := by simp only [C]; linarith
  have hA : 0 ≤ A := by simp only [A]; nlinarith
  -- A a² - 2Λab + C b² ≥ 0
  have hq : 0 ≤ A * a ^ 2 - 2 * Λ * a * b + C * b ^ 2 := by
    rcases hA.lt_or_eq with hA' | hA'
    · have : A * (A * a ^ 2 - 2 * Λ * a * b + C * b ^ 2) = (A * a - Λ * b) ^ 2 + (A * C - Λ ^ 2) *
        b ^ 2 := by ring
      have h0 : 0 ≤ (A * a - Λ * b) ^ 2 + (A * C - Λ ^ 2) * b ^ 2 := by
        have : 0 ≤ A * C - Λ ^ 2 := by linarith
        positivity
      rw [← this] at h0
      exact (mul_nonneg_iff_of_pos_left hA').1 h0
    · have hΛ0 : Λ = 0 := by rw [← hA'] at hN; nlinarith
      rw [hΛ0]; nlinarith [sq_nonneg a, sq_nonneg b]
  nlinarith

theorem split_norm (a b c : ℂ) (δ : ℝ) (hc : ‖c‖ ≤ 1 / 2 + δ) (hδ : 0 ≤ δ) :
    ‖(a + b) / 2‖ ^ 2 + ‖c * (a - b)‖ ^ 2 ≤ 2 * (1 / 2 + δ) ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hp := parallelogram_law_with_norm ℝ a b
  rw [norm_div, norm_mul]
  simp only [Complex.norm_ofNat]
  have h1 : ‖c‖ ^ 2 ≤ (1 / 2 + δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have h2 : (1 / 2 : ℝ) ^ 2 ≤ (1 / 2 + δ) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have e : (‖a + b‖ / 2) ^ 2 + (‖c‖ * ‖a - b‖) ^ 2 = (1 / 2) ^ 2 * ‖a + b‖ ^ 2 + ‖c‖ ^ 2 * ‖a -
      b‖ ^ 2 := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖a - b‖)
  have := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖a + b‖)
  nlinarith

theorem l2_sq {ι : Type} [Fintype ι] (f : ι → ℂ) : l2 f ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem l2_le_of_sq {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → ℂ) (g : κ → ℂ) (K : ℝ)
    (hK : 0 ≤ K)
    (h : ∑ i, ‖f i‖ ^ 2 ≤ K ^ 2 * ∑ j, ‖g j‖ ^ 2) : l2 f ≤ K * l2 g := by
  unfold l2
  rw [← Real.sqrt_sq hK, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- Child inputs of a node, indexed by (slot, child, half). -/
def quad {L : ℕ} (e1 o1 e0 o0 : Out L → ℂ) : Out L × Bool × Bool → ℂ
  | (o, false, false) => e1 o
  | (o, false, true) => o1 o
  | (o, true, false) => e0 o
  | (o, true, true) => o0 o

theorem sum_quad {L : ℕ} (g : Out L × Bool × Bool → ℝ) :
    ∑ i, g i = ∑ o,
        (g (o, false, false) + g (o, false, true) + g (o, true, false) + g (o, true, true)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]; ring

/-- Parent errors `(δt1, δt0')`, indexed by (slot, which). -/
def pairF {L : ℕ} (a y : Out L → ℂ) : Out L × Bool → ℂ
  | (o, false) => a o
  | (o, true) => y o

theorem sum_pairF {L : ℕ} (g : Out L × Bool → ℝ) : ∑ i, g i = ∑ o, (g (o, false) + g (o, true)) :=
    by
  rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl fun o _ => by rw
      [Fintype.sum_bool, add_comm]

/-- **ℓ2 error of one ffSampling node.** -/
theorem node_l2 (L : ℕ) (Λ N δ r' : ℝ) (hN0 : 0 ≤ N) (hN1 : 1 + Λ ^ 2 ≤ N ^ 2)
    (hN : Λ ^ 2 ≤ (N ^ 2 - 1) * (N ^ 2 - 1 - Λ ^ 2)) (hδ : 0 ≤ δ) (hr' : 0 ≤ r')
    (x0 x1 ℓh w : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓh o‖ ≤ Λ) (c : Out L → ℂ)
        (hc : ∀ o, ‖c o‖ ≤ 1 / 2 + δ)
    (e1 o1 e0 o0 : Out L → ℂ)
    (he1 : ∀ o, ‖e1 o - (x1 (o, false) + x1 (o, true)) / 2‖ ≤ r')
    (ho1 : ∀ o, ‖o1 o - c o * (x1 (o, false) - x1 (o, true))‖ ≤ r')
    (he0 : ∀ o, ‖e0 o - ((x0 + ℓh * x1 + w) (o, false) + (x0 + ℓh * x1 + w) (o, true)) / 2‖ ≤ r')
    (ho0 : ∀ o, ‖o0 o - c o * ((x0 + ℓh * x1 + w) (o, false) - (x0 + ℓh * x1 + w) (o, true))‖ ≤ r')
        :
    l2 (quad e1 o1 e0 o0) ≤ √2 * (1 / 2 + δ) * (N * l2 (pairF x0 x1) + l2 w) + 2 * √(2 ^ L) * r' :=
        by
  set y := x0 + ℓh * x1 + w
  set lin :=
      quad (fun o => (x1 (o, false) + x1 (o, true)) / 2)
          (fun o => c o * (x1 (o, false) - x1 (o, true)))
    (fun o => (y (o, false) + y (o, true)) / 2) (fun o => c o * (y (o, false) - y (o, true)))
  have hdec : quad e1 o1 e0 o0 = lin + (quad e1 o1 e0 o0 - lin) := by abel
  have hinj : l2 (quad e1 o1 e0 o0 - lin) ≤ 2 * √(2 ^ L) * r' := by
    have := l2_le_const (quad e1 o1 e0 o0 - lin) r' hr' (by
      rintro ⟨o, (_ | _), (_ | _)⟩
      · exact he1 o
      · exact ho1 o
      · exact he0 o
      · exact ho0 o)
    have hcard : (Fintype.card (Out L × Bool × Bool) : ℝ) = 2 ^ L * 4 := by
      rw [Fintype.card_prod, Fintype.card_prod, card_out, Fintype.card_bool]; push_cast; ring
    rw [hcard, Real.sqrt_mul (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at this
    linarith
  -- linear part
  have hK : 0 ≤ √2 * (1 / 2 + δ) := by positivity
  have hlin : l2 lin ≤ √2 * (1 / 2 + δ) * l2 (pairF x1 y) := by
    apply l2_le_of_sq _ _ _ hK
    rw [sum_quad, sum_pairF,
        sum_out_succ L (fun o => ‖pairF x1 y (o, false)‖ ^ 2 + ‖pairF x1 y (o, true)‖ ^ 2),
      Finset.mul_sum]
    refine Finset.sum_le_sum fun o _ => ?_
    simp only [lin, quad, pairF]
    have h1 := split_norm (x1 (o, false)) (x1 (o, true)) (c o) δ (hc o) hδ
    have h2 := split_norm (y (o, false)) (y (o, true)) (c o) δ (hc o) hδ
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  -- parent: (δt1, δt0') = M (δt0, δt1) + (0, w)
  have hpar : l2 (pairF x1 y) ≤ N * l2 (pairF x0 x1) + l2 w := by
    have hsplit : pairF x1 y = pairF x1 (x0 + ℓh * x1) + pairF 0 w := by
      funext ⟨o, b⟩; cases b <;> simp [pairF, y]
    rw [hsplit]
    refine (l2_add_le _ _).trans (add_le_add ?_ ?_)
    · apply l2_le_of_sq _ _ _ hN0
      rw [sum_pairF, sum_pairF, Finset.mul_sum]
      refine Finset.sum_le_sum fun o _ => ?_
      simp only [pairF, Pi.add_apply, Pi.mul_apply]
      have := pair_norm (x0 o) (x1 o) (ℓh o) Λ N (hℓ o) hN1 hN
      linarith
    · apply le_of_eq
      unfold l2; congr 1
      rw [sum_pairF]; simp [pairF]
  rw [hdec]
  calc l2 (lin + (quad e1 o1 e0 o0 - lin)) ≤ l2 lin + l2 (quad e1 o1 e0 o0 - lin) := l2_add_le _ _
    _ ≤ √2 * (1 / 2 + δ) * (N * l2 (pairF x0 x1) + l2 w) + 2 * √(2 ^ L) * r' := by
        gcongr
        exact hlin.trans (mul_le_mul_of_nonneg_left hpar hK)

end FalconPrecision.Errors.FFSamp
