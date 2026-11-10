/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.LDLStep

/-! # ffLDL⋆ root and leaf normalisation errors (TASK-009 S7d)

Root (Alg. 4 line 1 with the symplectic `D̂11 = q²/Ĝ00`, §7.3 item 3): `Ĝ00 = |f̂|² + |ĝ|²` from FFT
outputs within `E` has relative error `(2E√(2G) + 2E² + e)/G`; a reciprocal keeps a relative error
`ρ` as `ρ/(1 - ρ)`. Leaves (Keygen line 7): `σ_i = σ/√D̂` has relative error `ρ/((1 - ρ)(2 - ρ))`
when `D̂` has relative error `ρ`. -/

@[expose] public section

namespace FalconPrecision.Errors.LDL

/-- **Root diagonal** `Ĝ00 = |f̂|² + |ĝ|²` from FFT outputs within `E`, sum rounded within `e`. -/
theorem gram_err (f g fh gh : ℂ) (G Gh E e : ℝ) (hG : G = ‖f‖ ^ 2 + ‖g‖ ^ 2) (hf : ‖fh - f‖ ≤ E)
    (hg : ‖gh - g‖ ≤ E)
    (hGh : |Gh - (‖fh‖ ^ 2 + ‖gh‖ ^ 2)| ≤ e) : |Gh - G| ≤ 2 * E * √(2 * G) + 2 * E ^ 2 + e := by
  have hE : 0 ≤ E := (norm_nonneg _).trans hf
  have k : ∀ u uh : ℂ, ‖uh - u‖ ≤ E → |‖uh‖ ^ 2 - ‖u‖ ^ 2| ≤ 2 * E * ‖u‖ + E ^ 2 := by
    intro u uh h
    have h1 : |‖uh‖ - ‖u‖| ≤ E := (abs_norm_sub_norm_le _ _).trans h
    have : ‖uh‖ ^ 2 - ‖u‖ ^ 2 = (‖uh‖ - ‖u‖) * ((‖uh‖ - ‖u‖) + 2 * ‖u‖) := by ring
    rw [this, abs_mul]
    calc |‖uh‖ - ‖u‖| * |(‖uh‖ - ‖u‖) + 2 * ‖u‖| ≤ E * (E + 2 * ‖u‖) := by
          apply mul_le_mul h1 _ (abs_nonneg _) hE
          exact (abs_add_le _ _).trans
              (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ‖u‖)]; linarith)
      _ = 2 * E * ‖u‖ + E ^ 2 := by ring
  have hs : ‖f‖ + ‖g‖ ≤ √(2 * G) := by
    rw [hG]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖f‖ - ‖g‖)]
  calc |Gh - G| = |(Gh - (‖fh‖ ^ 2 + ‖gh‖ ^ 2)) + (‖fh‖ ^ 2 - ‖f‖ ^ 2) + (‖gh‖ ^ 2 - ‖g‖ ^ 2)| := by
        rw [hG]; ring_nf
    _ ≤ |Gh - (‖fh‖ ^ 2 + ‖gh‖ ^ 2)| + |‖fh‖ ^ 2 - ‖f‖ ^ 2| + |‖gh‖ ^ 2 - ‖g‖ ^ 2| :=
        abs_add_three _ _ _
    _ ≤ e + (2 * E * ‖f‖ + E ^ 2) + (2 * E * ‖g‖ + E ^ 2) :=
        by gcongr <;> [exact k _ _ hf; exact k _ _ hg]
    _ ≤ 2 * E * √(2 * G) + 2 * E ^ 2 + e := by nlinarith

/-- **Reciprocal** keeps relative error `ρ` as `ρ/(1 - ρ)`. -/
theorem inv_rel (ρ x xh : ℝ) (hx : 0 < x) (hρ1 : ρ < 1) (h : RelClose ρ x xh) :
    RelClose (ρ / (1 - ρ)) (1 / x) (1 / xh) := by
  unfold RelClose at *
  have hρ : 0 ≤ ρ := by
    by_contra hn; push Not at hn; nlinarith [abs_nonneg (xh - x)]
  rw [abs_le] at h
  have hxh : x * (1 - ρ) ≤ xh := by linarith [h.1]
  have hxh0 : 0 < xh := lt_of_lt_of_le (by nlinarith) hxh
  have h1 : 0 < 1 - ρ := by linarith
  rw [show 1 / xh - 1 / x = (x - xh) / (x * xh) by field_simp, abs_div,
      abs_of_pos (mul_pos hx hxh0),
    abs_sub_comm, div_le_iff₀ (mul_pos hx hxh0)]
  rw [abs_le]
  have key : ρ * x ≤ ρ / (1 - ρ) * (1 / x) * (x * xh) := by
    rw [show ρ / (1 - ρ) * (1 / x) * (x * xh) = ρ * xh / (1 - ρ) by field_simp]
    rw [le_div_iff₀ h1]; nlinarith
  constructor <;> linarith [h.1, h.2]

/-- **Leaf normalisation** `σ/√D̂`: relative error of `√D/√D̂` from that of `D̂`. -/
theorem sqrt_ratio (ρ D Dh : ℝ) (hD : 0 < D) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h : RelClose ρ D Dh) :
    |√D / √Dh - 1| ≤ ρ / ((1 - ρ) * (2 - ρ)) := by
  unfold RelClose at h
  rw [abs_le] at h
  have h1 : 0 < 1 - ρ := by linarith
  have hDh : D * (1 - ρ) ≤ Dh := by linarith [h.1]
  have hDh' : Dh ≤ D * (1 + ρ) := by linarith [h.2]
  have hDh0 : 0 < Dh := lt_of_lt_of_le (by positivity) hDh
  set w := √D / √Dh
  have hw0 : 0 < w := div_pos (Real.sqrt_pos.2 hD) (Real.sqrt_pos.2 hDh0)
  have hw2 : w ^ 2 = D / Dh := by
    simp only [w, div_pow, Real.sq_sqrt hD.le, Real.sq_sqrt hDh0.le]
  have hwlo : 1 - ρ ≤ w := by
    have hw2lo : 1 - ρ ≤ w ^ 2 := by
      rw [hw2, le_div_iff₀ hDh0]; nlinarith
    by_cases hw1 : w ≤ 1
    · nlinarith
    · push Not at hw1; linarith
  have hid : w - 1 = (D - Dh) / (Dh * (w + 1)) := by
    have : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [eq_div_iff (mul_pos hDh0 (by linarith : (0:ℝ) < w + 1)).ne']
    have h2 : (w - 1) * (w + 1) * Dh = D - Dh := by rw [← this, hw2]; field_simp
    linarith [h2]
  rw [hid, abs_div, abs_of_pos (mul_pos hDh0 (by linarith : (0:ℝ) < w + 1)),
    div_le_div_iff₀ (mul_pos hDh0 (by linarith : (0:ℝ) < w + 1)) (by nlinarith)]
  have hnum : |D - Dh| ≤ ρ * D := by rw [abs_sub_comm, abs_le]; constructor <;> linarith
  have hden : D * ((1 - ρ) * (2 - ρ)) ≤ Dh * (w + 1) := by
    have := mul_le_mul hDh (by linarith : 2 - ρ ≤ w + 1) (by linarith) hDh0.le
    nlinarith
  calc |D - Dh| * ((1 - ρ) * (2 - ρ)) ≤ ρ * D * ((1 - ρ) * (2 - ρ)) :=
        mul_le_mul_of_nonneg_right hnum (by nlinarith)
    _ = ρ * (D * ((1 - ρ) * (2 - ρ))) := by ring
    _ ≤ ρ * (Dh * (w + 1)) := mul_le_mul_of_nonneg_left hden hρ0

end FalconPrecision.Errors.LDL
