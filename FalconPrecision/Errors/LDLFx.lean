/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.LDLStep

/-! # Fixed-point error of one inner ffLDL⋆ step

From computed slot values `x̂, ŷ > 0`, the step computes `Ĝ00 ≈ a = (x̂ + ŷ)/2` (error `e₀`), `Ĝ10*
≈ b = ζ̄(x̂ - ŷ)/2` (error `e₁`, from the split), `L̂10 ≈ conj(b̂)/â` (error `eL`, fdiv) and `D̂11 ≈
â - |L̂10|²â` (error `eD`, Alg. 3 line 3). With `e₀, e₁ ≤ a/1024` and `eL ≤ 1/1024`, the computed
`D̂11` is within `2.01(e₀ + e₁ + a·eL) + eD` of the harmonic mean `hm x̂ ŷ`. -/

@[expose] public section

namespace FalconPrecision.Errors.LDL

/-- Real core: `g(a, s) = a - s²/a` is 2-Lipschitz near `s ≤ a`. -/
theorem g_err (a ah s sh e₀ e₁ : ℝ) (ha : 0 < a) (hs0 : 0 ≤ s) (hs : s ≤ a) (hsh0 : 0 ≤ sh)
    (h₀ : |ah - a| ≤ e₀) (h₁ : |sh - s| ≤ e₁) (he₀ : e₀ ≤ a / 1024) (he₁ : e₁ ≤ a / 1024) :
    |(ah - sh ^ 2 / ah) - (a - s ^ 2 / a)| ≤ 201 / 100 * e₀ + 201 / 100 * e₁ := by
  have he₀0 : 0 ≤ e₀ := (abs_nonneg _).trans h₀
  have he₁0 : 0 ≤ e₁ := (abs_nonneg _).trans h₁
  rw [abs_le] at h₀ h₁
  have hah : a * (1023 / 1024) ≤ ah := by linarith
  have hah0 : 0 < ah := lt_of_lt_of_le (by positivity) hah
  have hid : (ah - sh ^ 2 / ah) - (a - s ^ 2 / a) =
      (ah - a) * (1 + s ^ 2 / (a * ah)) - (sh - s) * (sh + s) / ah := by
    field_simp; ring
  rw [hid]
  have hq : s ^ 2 / (a * ah) ≤ 1024 / 1023 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hs hs hs0 ha.le]
  have hq0 : 0 ≤ s ^ 2 / (a * ah) := by positivity
  have hA : |(ah - a) * (1 + s ^ 2 / (a * ah))| ≤ e₀ * (1 + 1024 / 1023) := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + s ^ 2 / (a * ah))]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) (by linarith) (by linarith) he₀0
  have hB : |(sh - s) * (sh + s) / ah| ≤ e₁ * (2049 / 1023) := by
    rw [abs_div, abs_mul, abs_of_pos hah0, abs_of_nonneg (by linarith : 0 ≤ sh + s)]
    rw [div_le_iff₀ hah0]
    have h1 : |sh - s| ≤ e₁ := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : sh + s ≤ 2 * a + a / 1024 := by linarith
    calc |sh - s| * (sh + s) ≤ e₁ * (2 * a + a / 1024) :=
          mul_le_mul h1 h2 (by linarith) he₁0
      _ ≤ e₁ * (2049 / 1023) * ah := by nlinarith
  calc |(ah - a) * (1 + s ^ 2 / (a * ah)) - (sh - s) * (sh + s) / ah|
      ≤ |(ah - a) * (1 + s ^ 2 / (a * ah))| + |(sh - s) * (sh + s) / ah| := abs_sub _ _
    _ ≤ e₀ * (1 + 1024 / 1023) + e₁ * (2049 / 1023) := add_le_add hA hB
    _ ≤ 201 / 100 * e₀ + 201 / 100 * e₁ := by nlinarith

/-- **Inner ffLDL⋆ step in fixed point.** -/
theorem hm_fx_err (xh yh : ℝ) (ζ : ℂ) (hx : 0 < xh) (hy : 0 < yh) (hζ : ‖ζ‖ = 1)
    (ah : ℝ) (bh Lh : ℂ) (Dh e₀ e₁ eL eD : ℝ)
    (h₀ : |ah - am xh yh| ≤ e₀) (h₁ : ‖bh - (starRingEnd ℂ) ζ * ((xh - yh : ℝ) : ℂ) / 2‖ ≤ e₁)
    (hL : ‖Lh - (starRingEnd ℂ) bh / (ah : ℂ)‖ ≤ eL) (hD : |Dh - (ah - ‖Lh‖ ^ 2 * ah)| ≤ eD)
    (he₀ : e₀ ≤ am xh yh / 1024) (he₁ : e₁ ≤ am xh yh / 1024) (heL : eL ≤ 1 / 1024) :
    |Dh - hm xh yh| ≤ 201 / 100 * (e₀ + e₁ + am xh yh * eL) + eD := by
  set a := am xh yh
  set b := (starRingEnd ℂ) ζ * ((xh - yh : ℝ) : ℂ) / 2
  have ha : 0 < a := by simp only [a, am]; linarith
  have he₀0 : 0 ≤ e₀ := (abs_nonneg _).trans h₀
  have heL0 : 0 ≤ eL := (norm_nonneg _).trans hL
  have hah : a * (1023 / 1024) ≤ ah := by linarith [(abs_le.1 h₀).1]
  have hah0 : 0 < ah := lt_of_lt_of_le (by positivity) hah
  have hah1 : ah ≤ a * (1025 / 1024) := by linarith [(abs_le.1 h₀).2]
  obtain ⟨hsplit, hratio⟩ := ldl_split xh yh ζ hx hy hζ
  have hsa : ‖b‖ ≤ a := by
    have : ‖b‖ = a * (|xh - yh| / (xh + yh)) := by
      rw [← hratio]; simp only [a, b]; exact (mul_div_cancel₀ _ ha.ne').symm
    rw [this]
    have : |xh - yh| / (xh + yh) ≤ 1 := by
      rw [div_le_one (by linarith)]; rcases abs_cases (xh - yh) with ⟨h, _⟩ |
          ⟨h, _⟩ <;> rw [h] <;> linarith
    nlinarith
  have hs1 : |‖bh‖ - ‖b‖| ≤ e₁ := (abs_norm_sub_norm_le _ _).trans h₁
  -- step A: exact-in-computed-inputs to the rounded a, b
  have hA := g_err a ah ‖b‖ ‖bh‖ e₀ e₁ ha (norm_nonneg _) hsa (norm_nonneg _) h₀ hs1 he₀ he₁
  rw [hsplit] at hA
  -- step B: rounded L
  set ℓ := (starRingEnd ℂ) bh / (ah : ℂ)
  have hℓ : ‖ℓ‖ = ‖bh‖ / ah := by
    simp only [ℓ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hah0]
  have hℓ2 : ah - ‖ℓ‖ ^ 2 * ah = ah - ‖bh‖ ^ 2 / ah := by rw [hℓ]; field_simp
  have hℓb : ‖ℓ‖ ≤ 1025 / 1023 := by
    rw [hℓ, div_le_iff₀ hah0]
    have : ‖bh‖ ≤ a + e₁ := by linarith [(abs_le.1 hs1).2]
    nlinarith
  have hLl : |‖Lh‖ - ‖ℓ‖| ≤ eL := (abs_norm_sub_norm_le _ _).trans hL
  have hB : |(ah - ‖Lh‖ ^ 2 * ah) - (ah - ‖ℓ‖ ^ 2 * ah)| ≤ a * (1025 / 1024) *
      ((2 * (1025 / 1023) + 1 / 1024) * eL) := by
    have : (ah - ‖Lh‖ ^ 2 * ah) - (ah - ‖ℓ‖ ^ 2 * ah) = -(ah * ((‖Lh‖ - ‖ℓ‖) * (‖Lh‖ + ‖ℓ‖))) :=
        by ring
    rw [this, abs_neg, abs_mul, abs_of_pos hah0, abs_mul]
    have hsum : |‖Lh‖ + ‖ℓ‖| ≤ 2 * (1025 / 1023) + 1 / 1024 := by
      rw [abs_of_nonneg (by positivity)]; linarith [(abs_le.1 hLl).2]
    have := mul_le_mul hLl hsum (abs_nonneg _) heL0
    calc ah * (|‖Lh‖ - ‖ℓ‖| * |‖Lh‖ + ‖ℓ‖|) ≤ a * (1025 / 1024) *
        (eL * (2 * (1025 / 1023) + 1 / 1024)) :=
          mul_le_mul hah1 this (by positivity) (by positivity)
      _ = _ := by ring
  rw [hℓ2] at hB
  have hfin : Dh - hm xh yh = (Dh - (ah - ‖Lh‖ ^ 2 * ah)) +
      ((ah - ‖Lh‖ ^ 2 * ah) - (ah - ‖bh‖ ^ 2 / ah)) + ((ah - ‖bh‖ ^ 2 / ah) - hm xh yh) := by ring
  rw [hfin]
  calc _ ≤ |Dh - (ah - ‖Lh‖ ^ 2 * ah)| + |(ah - ‖Lh‖ ^ 2 * ah) - (ah - ‖bh‖ ^ 2 / ah)| +
        |(ah - ‖bh‖ ^ 2 / ah) - hm xh yh| := abs_add_three _ _ _
    _ ≤ eD + a * (1025 / 1024) * ((2 * (1025 / 1023) + 1 / 1024) * eL) +
        (201 / 100 * e₀ + 201 / 100 * e₁) := by
        gcongr
    _ ≤ 201 / 100 * (e₀ + e₁ + a * eL) + eD := by nlinarith [mul_nonneg ha.le heL0]

end FalconPrecision.Errors.LDL
