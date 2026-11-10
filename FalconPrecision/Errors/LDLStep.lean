/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-! # One inner level of ffLDL⋆ on the diagonal (TASK-009 S7d)

At an inner level of ffLDL⋆ (ePrint 2026/1531 Alg. 5, lines 8-11) a diagonal value `D̂` is split by
`splitfft`: for a pair of slots `x = D̂(ζ)`, `y = D̂(-ζ)` (real, self-adjoint) the child Gram matrix
has `Ĝ00 = Ĝ11 = (x + y)/2` and `Ĝ10 = conj(ζ̄(x - y)/2)`, and LDL⋆ (Alg. 3) gives `D̂00 = (x +
y)/2` (arithmetic mean) and `D̂11 = Ĝ00 - |Ĝ10|²/Ĝ00 = 2xy/(x + y)` (harmonic mean), `|L̂10| = |x -
y|/(x + y)`. Both means are monotone and homogeneous, so a relative input error `ρ` stays `ρ`; the
fixed-point step adds a local error. -/

@[expose] public section

namespace FalconPrecision.Errors.LDL

/-- Arithmetic mean. -/
noncomputable def am (x y : ℝ) : ℝ := (x + y) / 2

/-- Harmonic mean. -/
noncomputable def hm (x y : ℝ) : ℝ := 2 * x * y / (x + y)

/-- **LDL⋆ of a split diagonal value.** -/
theorem ldl_split (x y : ℝ) (ζ : ℂ) (hx : 0 < x) (hy : 0 < y) (hζ : ‖ζ‖ = 1) :
    am x y - ‖(starRingEnd ℂ) ζ * ((x - y : ℝ) : ℂ) / 2‖ ^ 2 / am x y = hm x y ∧
      ‖(starRingEnd ℂ) ζ * ((x - y : ℝ) : ℂ) / 2‖ / am x y = |x - y| / (x + y) := by
  have hn : ‖(starRingEnd ℂ) ζ * ((x - y : ℝ) : ℂ) / 2‖ = |x - y| / 2 := by
    rw [norm_div, norm_mul, Complex.norm_conj, hζ, Complex.norm_real, Real.norm_eq_abs]; simp
  rw [hn]
  have hs : 0 < x + y := by linarith
  constructor
  · unfold am hm
    rw [div_pow, sq_abs]
    field_simp
    ring
  · unfold am
    field_simp

theorem am_mem (lo hi x y : ℝ) (hx : lo ≤ x ∧ x ≤ hi)
    (hy : lo ≤ y ∧ y ≤ hi) : lo ≤ am x y ∧ am x y ≤ hi := by
  unfold am; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem hm_mem (lo hi x y : ℝ) (hlo : 0 < lo) (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) :
    lo ≤ hm x y ∧ hm x y ≤ hi := by
  unfold hm
  have hs : 0 < x + y := by linarith [hx.1, hy.1]
  constructor
  · rw [le_div_iff₀ hs]; nlinarith [hx.1, hy.1]
  · rw [div_le_iff₀ hs]; nlinarith [hx.2, hy.2, hx.1, hy.1]

/-- **Lemma 8 (16) shape.** `|L̂10| = |x - y|/(x + y) ≤ (hi - lo)/(hi + lo) < 1`. -/
theorem abs_sub_div_le (lo hi x y : ℝ) (hlo : 0 < lo) (hx : lo ≤ x ∧ x ≤ hi)
    (hy : lo ≤ y ∧ y ≤ hi) :
    |x - y| / (x + y) ≤ (hi - lo) / (hi + lo) := by
  have hs : 0 < x + y := by linarith [hx.1, hy.1]
  rw [div_le_div_iff₀ hs (by linarith [hx.1, hx.2])]
  rcases abs_cases (x - y) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

/-- Relative closeness: `|x̂ - x| ≤ ρ·x`. -/
def RelClose (ρ x xh : ℝ) : Prop := |xh - x| ≤ ρ * x

theorem am_rel (ρ x y xh yh : ℝ) (hx : RelClose ρ x xh) (hy : RelClose ρ y yh) :
    RelClose ρ (am x y) (am xh yh) := by
  unfold RelClose am at *
  rw [abs_le] at *
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem hm_rel (ρ x y xh yh : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hx0 : 0 < x) (hy0 : 0 < y)
    (hx : RelClose ρ x xh) (hy : RelClose ρ y yh) : RelClose ρ (hm x y) (hm xh yh) := by
  unfold RelClose hm at *
  rw [abs_le] at *
  have hxh : x * (1 - ρ) ≤ xh := by linarith [hx.1]
  have hxh' : xh ≤ x * (1 + ρ) := by linarith [hx.2]
  have hyh : y * (1 - ρ) ≤ yh := by linarith [hy.1]
  have hyh' : yh ≤ y * (1 + ρ) := by linarith [hy.2]
  have h1 : 0 < 1 - ρ := by linarith
  have hxp : 0 < xh := lt_of_lt_of_le (by positivity) hxh
  have hyp : 0 < yh := lt_of_lt_of_le (by positivity) hyh
  have hs : 0 < x + y := by linarith
  have hsh : 0 < xh + yh := by linarith
  -- hm is monotone in each argument and homogeneous
  have mono : ∀ a b c d : ℝ, 0 < a → 0 < b → a ≤ c → b ≤ d → 2 * a * b / (a + b) ≤ 2 * c * d /
      (c + d) := by
    intro a b c d ha hb hac hbd
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
        [mul_pos ha hb, mul_le_mul hac hbd hb.le (by linarith), sq_nonneg (a - c),
            mul_nonneg (sub_nonneg.2 hac)
      (sub_nonneg.2 hbd), mul_nonneg (mul_nonneg (sub_nonneg.2 hac) hb.le) hb.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hbd) ha.le) ha.le,
          mul_nonneg (mul_nonneg (sub_nonneg.2 hac) (by linarith : (0:ℝ) ≤ d))
              (by linarith : (0:ℝ) ≤ d),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hbd) (by linarith : (0:ℝ) ≤ c))
          (by linarith : (0:ℝ) ≤ c)]
  have hom : ∀ k a b : ℝ, 0 < k → 0 < a + b → 2 * (a * k) * (b * k) / (a * k + b * k) = k *
      (2 * a * b / (a + b)) := by
    intro k a b hk hab
    field_simp
  have lo := mono _ _ _ _ (by positivity) (by positivity) hxh hyh
  have hi := mono _ _ _ _ hxp hyp hxh' hyh'
  rw [hom _ _ _ h1 hs] at lo
  rw [hom _ _ _ (by linarith) hs] at hi
  constructor <;> nlinarith

end FalconPrecision.Errors.LDL
