/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.LDLStep

/-! # Relative error of the ffLDL⋆ diagonal down the tree (TASK-009 S7d)

Level `ℓ + 1` diagonal values of ffLDL⋆ are arithmetic or harmonic means of pairs of level-`ℓ`
values (`LDLStep`). If the root values lie in `[lo, hi]` with relative error `ρ₀`, and each computed
value is within `ε` of the mean of the computed pair, then every level-`ℓ` value lies in `[lo, hi]`
(Lemma 8, inner levels) with relative error `ρ₀ + ℓ·ε/lo`. -/

@[expose] public section

namespace FalconPrecision.Errors.LDL

/-- **Tree relative error.** -/
theorem tree_rel (lo hi ρ₀ ε : ℝ) (hlo : 0 < lo) (hε : 0 ≤ ε) (Idx : ℕ → Type)
    (V Vh : (ℓ : ℕ) → Idx ℓ → ℝ)
    (hroot : ∀ i, (lo ≤ V 0 i ∧ V 0 i ≤ hi) ∧ RelClose ρ₀ (V 0 i) (Vh 0 i))
    (hstep : ∀ ℓ j, ∃ i₁ i₂,
      (V (ℓ + 1) j = am (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - am (Vh ℓ i₁) (Vh ℓ i₂)| ≤ ε) ∨
      (V (ℓ + 1) j = hm (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - hm (Vh ℓ i₁) (Vh ℓ i₂)| ≤ ε))
    (hρ0 : 0 ≤ ρ₀) (L : ℕ) (hρ1 : ρ₀ + L * (ε / lo) < 1) :
    ∀ ℓ ≤ L, ∀ j, (lo ≤ V ℓ j ∧ V ℓ j ≤ hi) ∧ RelClose (ρ₀ + ℓ * (ε / lo)) (V ℓ j) (Vh ℓ j) := by
  intro ℓ
  induction ℓ with
  | zero => intro _ j; simpa using hroot j
  | succ ℓ ih =>
    intro hℓ j
    obtain ⟨i₁, i₂, h⟩ := hstep ℓ j
    obtain ⟨hb₁, hr₁⟩ := ih (by omega) i₁
    obtain ⟨hb₂, hr₂⟩ := ih (by omega) i₂
    set ρ := ρ₀ + ℓ * (ε / lo)
    have hρ : 0 ≤ ρ := by positivity
    have hρlt : ρ < 1 := by
      have : (ℓ : ℝ) * (ε / lo) ≤ L * (ε / lo) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : ℓ ≤ L)) (by positivity)
      linarith
    have hstepρ : ρ₀ + ((ℓ + 1 : ℕ) : ℝ) * (ε / lo) = ρ + ε / lo := by push_cast; ring
    rw [hstepρ]
    have fin : ∀ v vh w, lo ≤ v → RelClose ρ v w → |vh - w| ≤ ε → RelClose (ρ + ε / lo) v vh := by
      intro v vh w hv hw hvh
      unfold RelClose at *
      have : ε ≤ ε / lo * v := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlo]; exact mul_le_mul_of_nonneg_left hv hε
      calc |vh - v| = |(vh - w) + (w - v)| := by ring_nf
        _ ≤ |vh - w| + |w - v| := abs_add_le _ _
        _ ≤ (ρ + ε / lo) * v := by nlinarith
    rcases h with ⟨hv, he⟩ | ⟨hv, he⟩
    · have hb := am_mem lo hi _ _ hb₁ hb₂
      rw [hv]
      exact ⟨hb, fin _ _ _ hb.1 (am_rel ρ _ _ _ _ hr₁ hr₂) he⟩
    · have hb := hm_mem lo hi _ _ hlo hb₁ hb₂
      rw [hv]
      exact ⟨hb,
          fin _ _ _ hb.1
              (hm_rel ρ _ _ _ _ hρ hρlt (by linarith [hb₁.1]) (by linarith [hb₂.1]) hr₁ hr₂) he⟩

end FalconPrecision.Errors.LDL
