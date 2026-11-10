/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.LDLTree
public import FalconPrecision.Errors.LDLLeaf

/-! # Leaf error `Δσ` of ffLDL⋆ (TASK-009 S7d)

Composition: root diagonal values with relative error `ρ₀`, `L` inner levels with local error `ε`
(`tree_rel`), then the normalisation `σ_i = σ/√D̂` computed with relative error `ρs` (`sqrt_ratio`).
Every computed leaf `σ̄_i` satisfies `|σ̄_i/σ_i - 1| ≤ ρs + w + ρs·w`, `w = ρ/((1 - ρ)(2 - ρ))`, `ρ
= ρ₀ + L·ε/lo`. -/

@[expose] public section

namespace FalconPrecision.Errors.LDL

theorem sigma_rel (σ D Dh σh ρ ρs : ℝ) (hσ : 0 < σ) (hD : 0 < D) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : RelClose ρ D Dh) (hs : |σh - σ / √Dh| ≤ ρs * (σ / √Dh)) :
    |σh / (σ / √D) - 1| ≤ ρs + ρ / ((1 - ρ) * (2 - ρ)) + ρs * (ρ / ((1 - ρ) * (2 - ρ))) := by
  have hDh0 : 0 < Dh := by
    unfold RelClose at h; rw [abs_le] at h; nlinarith [h.1]
  have hw := sqrt_ratio ρ D Dh hD hρ0 hρ1 h
  set w := ρ / ((1 - ρ) * (2 - ρ))
  have hsD : 0 < √D := Real.sqrt_pos.2 hD
  have hsDh : 0 < √Dh := Real.sqrt_pos.2 hDh0
  set s := σ / √Dh
  have hs0 : 0 < s := div_pos hσ hsDh
  have hρs : 0 ≤ ρs := by
    by_contra hn; push Not at hn; nlinarith [abs_nonneg (σh - s)]
  have hid : σh / (σ / √D) - 1 = (σh / s - 1) * (√D / √Dh) + (√D / √Dh - 1) := by
    simp only [s]; field_simp; ring
  have h1 : |σh / s - 1| ≤ ρs := by
    rw [show σh / s - 1 = (σh - s) / s by field_simp, abs_div, abs_of_pos hs0, div_le_iff₀ hs0];
        exact hs
  have h2 : |√D / √Dh| ≤ 1 + w := by
    have := abs_sub_abs_le_abs_sub (√D / √Dh) 1
    simp at this; linarith
  rw [hid]
  calc _ ≤ |(σh / s - 1) * (√D / √Dh)| + |√D / √Dh - 1| := abs_add_le _ _
    _ = |σh / s - 1| * |√D / √Dh| + |√D / √Dh - 1| := by rw [abs_mul]
    _ ≤ ρs * (1 + w) + w := by gcongr
    _ = ρs + w + ρs * w := by ring

/-- **Leaf error of ffLDL⋆.** -/
theorem leaf_sigma_err (lo hi ρ₀ ε ρs σ : ℝ) (hlo : 0 < lo) (hε : 0 ≤ ε) (hσ : 0 < σ)
    (Idx : ℕ → Type)
    (V Vh : (ℓ : ℕ) → Idx ℓ → ℝ)
    (hroot : ∀ i, (lo ≤ V 0 i ∧ V 0 i ≤ hi) ∧ RelClose ρ₀ (V 0 i) (Vh 0 i))
    (hstep : ∀ ℓ j, ∃ i₁ i₂,
      (V (ℓ + 1) j = am (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - am (Vh ℓ i₁) (Vh ℓ i₂)| ≤ ε) ∨
      (V (ℓ + 1) j = hm (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - hm (Vh ℓ i₁) (Vh ℓ i₂)| ≤ ε))
    (hρ0 : 0 ≤ ρ₀) (L : ℕ) (hρ1 : ρ₀ + L * (ε / lo) < 1) (σh : Idx L → ℝ)
    (hs : ∀ j, |σh j - σ / √(Vh L j)| ≤ ρs * (σ / √(Vh L j))) (j : Idx L) :
    (lo ≤ V L j ∧ V L j ≤ hi) ∧
      |σh j / (σ / √(V L j)) - 1| ≤ ρs + (ρ₀ + L * (ε / lo)) /
          ((1 - (ρ₀ + L * (ε / lo))) * (2 - (ρ₀ + L * (ε / lo)))) +
        ρs * ((ρ₀ + L * (ε / lo)) / ((1 - (ρ₀ + L * (ε / lo))) * (2 - (ρ₀ + L * (ε / lo))))) := by
  obtain ⟨hb, hr⟩ := tree_rel lo hi ρ₀ ε hlo hε Idx V Vh hroot hstep hρ0 L hρ1 L le_rfl j
  exact ⟨hb, sigma_rel σ _ _ _ _ ρs hσ (by linarith [hb.1]) (by positivity) hρ1 hr (hs j)⟩

end FalconPrecision.Errors.LDL
