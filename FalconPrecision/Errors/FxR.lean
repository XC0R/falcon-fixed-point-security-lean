/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Type 2 fixed-point arithmetic of ePrint 2026/1531 §7 with error bounds (TASK-009 S7a)

`FxR(x, m, p)` denotes `x·2^{m-p}` with `x ∈ ℤ`, `|x| < 2^p` (§7.1). Addition is exact at a common
`m`; multiplication keeps the `p` most significant bits of `a.x·b.x` at tag `a.m + b.m`; retagging
changes `m`. Rounding is any integer within `1/2` of the exact quotient (`IsRound`), which covers
round-half-to-even (§7.2). Each operation is stated with its overflow side condition (enforced by
the reference code) and its value error. -/

@[expose] public section

namespace FalconPrecision.Errors.Fixed

/-- A fixed-point real `x·2^{m-p}`. -/
structure FxR (p : ℕ) where
  x : ℤ
  m : ℤ
  bound : |x| < 2 ^ p

variable {p : ℕ}

/-- The value of a fixed-point real. -/
noncomputable def val (a : FxR p) : ℝ := a.x * (2 : ℝ) ^ (a.m - p)

/-- One unit in the last place at tag `m`. -/
noncomputable def ulp (p : ℕ) (m : ℤ) : ℝ := (2 : ℝ) ^ (m - p)

/-- `r` rounds `y` to an integer within `1/2`. -/
def IsRound (r : ℤ) (y : ℝ) : Prop := |(r : ℝ) - y| ≤ 1 / 2

theorem ulp_pos (m : ℤ) : 0 < ulp p m := zpow_pos (by norm_num) _

theorem abs_val_lt (a : FxR p) : |val a| < (2 : ℝ) ^ a.m := by
  rw [val, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
  have hx : |(a.x : ℝ)| < (2 : ℝ) ^ p := by exact_mod_cast a.bound
  calc |(a.x : ℝ)| * (2 : ℝ) ^ (a.m - p) < (2 : ℝ) ^ p * (2 : ℝ) ^ (a.m - p) :=
        mul_lt_mul_of_pos_right hx (zpow_pos (by norm_num) _)
    _ = (2 : ℝ) ^ a.m := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring

/-- **Addition is exact** at a common tag. -/
theorem add_val (a b : FxR p) (h : a.m = b.m) (hb : |a.x + b.x| < 2 ^ p) :
    val (⟨a.x + b.x, a.m, hb⟩ : FxR p) = val a + val b := by
  simp only [val, h]; push_cast; ring

/-- **Multiplication** at tag `a.m + b.m`: the result is within half an ulp of the exact product. -/
theorem mul_val (a b : FxR p) (r : ℤ) (hr : IsRound r ((a.x * b.x : ℤ) / (2 : ℝ) ^ p))
    (hb : |r| < 2 ^ p) :
    |val (⟨r, a.m + b.m, hb⟩ : FxR p) - val a * val b| ≤ ulp p (a.m + b.m) / 2 := by
  have h2 : (2 : ℝ) ^ (a.m + b.m - p) = (2 : ℝ) ^ (a.m - p) * (2 : ℝ) ^ (b.m - p) * (2 : ℝ) ^ p :=
      by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1; ring
  have hp : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hid : val (⟨r, a.m + b.m, hb⟩ : FxR p) - val a * val b =
      ((r : ℝ) - (a.x * b.x : ℤ) / (2 : ℝ) ^ p) * ulp p (a.m + b.m) := by
    simp only [val, ulp]
    rw [h2]; push_cast; field_simp
  rw [hid, abs_mul, abs_of_pos (ulp_pos _)]
  have := hr
  unfold IsRound at this
  nlinarith [ulp_pos (p := p) (a.m + b.m)]

/-- **Retagging up** (`m ≤ m'`, dropping `m' - m` low bits): within half an ulp at the new tag. -/
theorem retag_up_val (a : FxR p) (m' : ℤ) (k : ℕ) (hk : m' = a.m + k) (r : ℤ)
    (hr : IsRound r (a.x / (2 : ℝ) ^ k))
    (hb : |r| < 2 ^ p) : |val (⟨r, m', hb⟩ : FxR p) - val a| ≤ ulp p m' / 2 := by
  have hid : val (⟨r, m', hb⟩ : FxR p) - val a = ((r : ℝ) - a.x / (2 : ℝ) ^ k) * ulp p m' := by
    simp only [val, ulp, hk]
    have : (2 : ℝ) ^ (a.m + (k : ℤ) - p) = (2 : ℝ) ^ (a.m - p) * (2 : ℝ) ^ k := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [this]; field_simp
  rw [hid, abs_mul, abs_of_pos (ulp_pos _)]
  have := hr
  unfold IsRound at this
  nlinarith [ulp_pos (p := p) m']

/-- **Retagging down** (`m' ≤ m`, shifting left by `m - m'`) is exact when it does not overflow. -/
theorem retag_down_val (a : FxR p) (m' : ℤ) (k : ℕ) (hk : a.m = m' + k)
    (hb : |a.x * 2 ^ k| < 2 ^ p) :
    val (⟨a.x * 2 ^ k, m', hb⟩ : FxR p) = val a := by
  simp only [val, hk]
  have : (2 : ℝ) ^ (m' + (k : ℤ) - p) = (2 : ℝ) ^ (m' - p) * (2 : ℝ) ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [this]; push_cast; ring

end FalconPrecision.Errors.Fixed
