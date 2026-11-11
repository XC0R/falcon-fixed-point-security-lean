/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFSampRun

/-! # Falcon-512 center-error instance

`run_l2` at Falcon-512 (`n = 512`, ffSampling of size `2^9`) with the Type 2 budgets of ePrint
2026/1531 Table 4 (centers and `ẑ` at tag 21, `p = 63`): split twiddle `ζ̄/2` within `δ ≤ √2/2·2⁻⁶³`
(assumed: the split table at tag 0 is the componentwise round-to-nearest of `ζ̄/2`; `twiddle_err`),
split error `r' ≤ 2.9·2⁻⁴²` (rounding `√2·2⁻⁴²` + twiddle `2δB`, `split512`), `|ℓ̂| ≤ 24.0001` at
the root (`γroot = 24`, keygen-enforced, Alg. 2 l. 14-15, §8.6) and `≤ 0.9923` below (Lemma 8 (16)
at `γhybrid = 4`, keygen-enforced, Alg. 2 l. 8, §8.5: `255/257`), line-10 extra terms `W_L`
(`w512`). Under these budgets (`ETree.Hyp`, a hypothesis here) every ffSampling call has `√(Σ (t̄ -
t)²) ≤ Ā·‖δt̂‖₂ + C̄` over its 1024 SamplerZ calls. `FFSampModel` derives the per-node relations of
`ETree.Hyp` from an execution model on every history and redoes this recursion along executions
(`ffs_pathS`). -/

@[expose] public section

namespace FalconPrecision.Errors.FFSamp

open FalconPrecision.Errors.FFTRec

/-- `coefC` with upper bounds `s2 ≥ √2`, `sq L ≥ √(2^L)`. -/
noncomputable def coefCU (N W : ℕ → ℝ) (K r' s2 : ℝ) (sq : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | L + 1 => coefA N K L * (K * W L + 2 * sq L * r') + s2 * coefCU N W K r' s2 sq L

theorem coefA_mono (N : ℕ → ℝ) (hN : ∀ L, 0 ≤ N L) (K K' : ℝ) (hK : 0 ≤ K) (hKK : K ≤ K') :
    ∀ L, 0 ≤ coefA N K L ∧ coefA N K L ≤ coefA N K' L := by
  intro L; induction L with
  | zero => simp [coefA]
  | succ L ih =>
    simp only [coefA]
    have := hN L
    exact ⟨by have := ih.1; positivity, by
      have h1 := mul_le_mul ih.2 hKK hK (ih.1.trans ih.2)
      exact mul_le_mul_of_nonneg_right h1 this⟩

theorem coefC_le (N W : ℕ → ℝ) (hN : ∀ L, 0 ≤ N L) (hW : ∀ L, 0 ≤ W L) (K K' r' s2 : ℝ) (sq : ℕ → ℝ)
    (hK : 0 ≤ K) (hKK : K ≤ K') (hr : 0 ≤ r') (hs2 : √2 ≤ s2) (hsq : ∀ L, √(2 ^ L) ≤ sq L) :
    ∀ L, 0 ≤ coefC N W K r' L ∧ coefC N W K r' L ≤ coefCU N W K' r' s2 sq L := by
  intro L; induction L with
  | zero => simp [coefC, coefCU]
  | succ L ih =>
    simp only [coefC, coefCU]
    obtain ⟨hA0, hA⟩ := coefA_mono N hN K K' hK hKK L
    have hW0 := hW L
    constructor
    · have := ih.1; positivity
    · gcongr
      all_goals first
        | exact hA0.trans hA | exact hsq L | exact ih.1 | exact ih.2
        | exact (Real.sqrt_nonneg 2).trans hs2

/-- Falcon-512 budgets. -/
noncomputable def lam512 (L : ℕ) : ℝ := if L = 8 then 240001 / 10000 else 9923 / 10000
noncomputable def nn512 (L : ℕ) : ℝ := if L = 8 then 24042 / 1000 else 16125 / 10000
noncomputable def w512 (L : ℕ) : ℝ :=
  (match L with
    | 0 => 712 | 1 => 1614 | 2 => 3497 | 3 => 7374 | 4 => 15286 | 5 => 31334 | 6 => 63744 | 7 =>
        129011
    | _ => 6242973) / 100 / 2 ^ 42
noncomputable def sq512 (L : ℕ) : ℝ :=
    if L % 2 = 0 then 2 ^ (L / 2) else 141422 / 100000 * 2 ^ (L / 2)

theorem sqrt_two_le : √2 ≤ 141422 / 100000 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem sqrt_pow_le (L : ℕ) : √(2 ^ L) ≤ sq512 L := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' L
  · have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    simp only [sq512, h1, h2, ↓reduceIte]
    rw [Real.sqrt_le_left (by positivity), ← pow_mul, mul_comm]
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    simp only [sq512, h1, h2, one_ne_zero, ↓reduceIte]
    rw [Real.sqrt_le_left (by positivity), mul_pow, ← pow_mul, pow_succ, mul_comm k 2]
    have : (2 : ℝ) ≤ (141422 / 100000) ^ 2 := by norm_num
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (2 * k)]

theorem hyp512 (L : ℕ) : 0 ≤ nn512 L ∧ 1 + lam512 L ^ 2 ≤ nn512 L ^ 2 ∧
    lam512 L ^ 2 ≤ (nn512 L ^ 2 - 1) * (nn512 L ^ 2 - 1 - lam512 L ^ 2) := by
  unfold nn512 lam512; split_ifs <;> norm_num

theorem coefA512 : coefA nn512 (70711 / 100000) 9 ≤ 49 := by
  simp only [coefA, nn512]; norm_num

theorem coefC512 : coefCU nn512 w512 (70711 / 100000) (29 / 10 / 2 ^ 42) (141422 / 100000) sq512 9 ≤
    135700 / 2 ^ 42 := by
  simp only [coefCU, coefA, nn512, w512, sq512]; norm_num

theorem w512_nonneg (L : ℕ) : 0 ≤ w512 L := by unfold w512; split <;> positivity

/--
Coefficients of the Falcon-512 instance (arithmetic): `0 ≤ Ā_L`, `0 ≤ C̄_L` at every level, and `Ā₉
≤ 49`, `C̄₉ ≤ 135700·2⁻⁴²`, for `K = √2(1/2 + δ)`, `δ ≤ 0.7072·2⁻⁶³`. -/
theorem coef512 (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 7072 / 10000 / 2 ^ 63) :
    (∀ L, 0 ≤ coefA nn512 (√2 * (1 / 2 + δ)) L ∧ 0 ≤ coefC nn512 w512 (√2 * (1 / 2 + δ))
        (29 / 10 / 2 ^ 42) L) ∧
      coefA nn512 (√2 * (1 / 2 + δ)) 9 ≤ 49 ∧
      coefC nn512 w512 (√2 * (1 / 2 + δ)) (29 / 10 / 2 ^ 42) 9 ≤ 135700 / 2 ^ 42 := by
  have hN := fun L => (hyp512 L).1
  have hK0 : 0 ≤ √2 * (1 / 2 + δ) := by positivity
  have hK : √2 * (1 / 2 + δ) ≤ 70711 / 100000 := by
    have h2 : √2 ≤ 141422 / 100000 := sqrt_two_le
    have h3 : √2 * (1 / 2 + δ) ≤ 141422 / 100000 * (1 / 2 + 1 / 2 ^ 63) := by
      gcongr; exact hδ.trans (by norm_num)
    have h4 : √2 ≤ 1414214 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ 1 / 2 + δ)]
  have hC :=
      coefC_le nn512 w512 hN w512_nonneg _ _ (29 / 10 / 2 ^ 42) (141422 / 100000) sq512 hK0 hK
    (by positivity) sqrt_two_le sqrt_pow_le
  exact ⟨fun L => ⟨(coefA_mono nn512 hN _ _ hK0 hK L).1, (hC L).1⟩,
    (coefA_mono nn512 hN _ _ hK0 hK 9).2.trans coefA512, (hC 9).2.trans coefC512⟩

/--
**Falcon-512 centers.** For every ffSampling call (1024 SamplerZ calls) whose node errors satisfy
the Type 2 budgets (`hT`, a hypothesis: per-node line-10 and split errors within `w512` and
`2.9·2⁻⁴²`), the ℓ2 norm of the center errors is at most `49·‖δt̂‖₂ + 135700·2⁻⁴²`. The reference
centres are those of exact-arithmetic ffSampling with the same stored tree `ℓ̂` (hop A): the line-10
term `(t1 - z1)(ℓ̂ - ℓ)` is then `0`, and `w512` (which also allows `ℓ̂` storage rounding) is an
upper bound. Centres of the true tree (hop B) are not covered. `hT` rests on `|t̂|, |ẑ| < 2²¹`,
which holds only with high probability (Lemma 12) unless the signer clamps or aborts. -/
theorem falcon512_centers (T : ETree 9) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 7072 / 10000 / 2 ^ 63)
    (hT : T.Hyp lam512 nn512 w512 δ (29 / 10 / 2 ^ 42)) :
    √T.leafSq ≤ 49 * l2 (pairF T.x0 T.x1) + 135700 / 2 ^ 42 := by
  obtain ⟨-, hA, hC⟩ := coef512 δ hδ0 hδ
  have h :=
      run_l2 lam512 nn512 w512 δ (29 / 10 / 2 ^ 42) hδ0 (by positivity) (fun L => (hyp512 L).1)
    (fun L => (hyp512 L).2.1) (fun L => (hyp512 L).2.2) w512_nonneg 9 T hT
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hA (l2_nonneg _)) hC)

end FalconPrecision.Errors.FFSamp
