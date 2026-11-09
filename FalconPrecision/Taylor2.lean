/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Second-order Taylor bound with a global second-derivative bound -/

@[expose] public section

namespace FalconPrecision.Taylor2

/-- One side: with `g'' ≤ M` everywhere, `g (x + h) - g x - h g' x ≤ M h² / 2`. -/
theorem sub_le_of_deriv2_le {g g' g'' : ℝ → ℝ} {M : ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hM : ∀ x, g'' x ≤ M) (x h : ℝ) :
    g (x + h) - g x - h * g' x ≤ M * h ^ 2 / 2 := by
  set k : ℝ → ℝ := fun t => g (x + t) - g x - t * g' x - M * t ^ 2 / 2
  set k' : ℝ → ℝ := fun t => g' (x + t) - g' x - M * t
  have hk : ∀ t, HasDerivAt k (k' t) t := fun t => by
    have h1 := (hg (x + t)).comp t ((hasDerivAt_id t).const_add x)
    have h2 := ((hasDerivAt_id t).mul_const (g' x))
    have h3 := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
    have h4 := ((h1.sub_const (g x)).sub h2).sub h3
    convert h4 using 1
    · funext s; simp [k]
    · simp [k']; ring
  have hk' : ∀ t, HasDerivAt k' (g'' (x + t) - M) t := fun t => by
    have h1 := (hg' (x + t)).comp t ((hasDerivAt_id t).const_add x)
    have h4 := (h1.sub_const (g' x)).sub ((hasDerivAt_id t).const_mul M)
    convert h4 using 1
    · funext s; simp [k']
    · simp
  have hk'anti : Antitone k' := antitone_of_deriv_nonpos (fun t => (hk' t).differentiableAt)
    fun t => by rw [(hk' t).deriv]; linarith [hM (x + t)]
  have hk'0 : k' 0 = 0 := by simp [k']
  have hk0 : k 0 = 0 := by simp [k]
  have : k h ≤ 0 := by
    rcases le_total 0 h with h0 | h0
    · have hanti : AntitoneOn k (Set.Ici 0) :=
        antitoneOn_of_deriv_nonpos (convex_Ici 0)
            (fun t _ => (hk t).continuousAt.continuousWithinAt)
          (fun t _ => (hk t).differentiableAt.differentiableWithinAt) fun t ht => by
            rw [interior_Ici] at ht
            rw [(hk t).deriv, ← hk'0]; exact hk'anti (le_of_lt ht)
      exact hk0 ▸ hanti ((Set.mem_Ici.2 le_rfl)) h0 h0
    · have hmono : MonotoneOn k (Set.Iic 0) :=
        monotoneOn_of_deriv_nonneg (convex_Iic 0)
            (fun t _ => (hk t).continuousAt.continuousWithinAt)
          (fun t _ => (hk t).differentiableAt.differentiableWithinAt) fun t ht => by
            rw [interior_Iic] at ht
            rw [(hk t).deriv, ← hk'0]; exact hk'anti (le_of_lt ht)
      exact hk0 ▸ hmono h0 ((Set.mem_Iic.2 le_rfl)) h0
  simp only [k] at this; linarith

/-- **Taylor, order two.** With `|g''| ≤ M` everywhere, `|g (x + h) - g x - h g' x| ≤ M h² / 2`. -/
theorem abs_sub_le_of_abs_deriv2_le {g g' g'' : ℝ → ℝ} {M : ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hM : ∀ x, |g'' x| ≤ M) (x h : ℝ) :
    |g (x + h) - g x - h * g' x| ≤ M * h ^ 2 / 2 := by
  rw [abs_le]
  constructor
  · have := sub_le_of_deriv2_le (g := fun y => -g y) (g' := fun y => -g' y) (g'' := fun y => -g'' y)
      (fun y => (hg y).neg) (fun y => (hg' y).neg) (fun y => by linarith [(abs_le.1 (hM y)).1]) x h
    linarith
  · exact sub_le_of_deriv2_le hg hg' (fun y => (abs_le.1 (hM y)).2) x h

/-- One side, on the segment between `x` and `x + h` only. -/
theorem sub_le_of_deriv2_le_on {g g' g'' : ℝ → ℝ} {M x h : ℝ}
    (hg : ∀ y ∈ Set.uIcc x (x + h), HasDerivAt g (g' y) y)
    (hg' : ∀ y ∈ Set.uIcc x (x + h), HasDerivAt g' (g'' y) y)
    (hM : ∀ y ∈ Set.uIcc x (x + h), g'' y ≤ M) :
    g (x + h) - g x - h * g' x ≤ M * h ^ 2 / 2 := by
  set k : ℝ → ℝ := fun t => g (x + t) - g x - t * g' x - M * t ^ 2 / 2
  set k' : ℝ → ℝ := fun t => g' (x + t) - g' x - M * t
  have hmem : ∀ t ∈ Set.uIcc 0 h, x + t ∈ Set.uIcc x (x + h) := fun t ht => by
    rcases Set.mem_uIcc.1 ht with ⟨a, b⟩ | ⟨a, b⟩ <;>
      [exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩);
       exact Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)]
  have hk : ∀ t ∈ Set.uIcc 0 h, HasDerivAt k (k' t) t := fun t ht => by
    have h1 := (hg (x + t) (hmem t ht)).comp t ((hasDerivAt_id t).const_add x)
    have h4 := ((h1.sub_const (g x)).sub ((hasDerivAt_id t).mul_const (g' x))).sub
      (((hasDerivAt_pow 2 t).const_mul M).div_const 2)
    convert h4 using 1
    · funext s; simp [k]
    · simp [k']; ring
  have hk' : ∀ t ∈ Set.uIcc 0 h, HasDerivAt k' (g'' (x + t) - M) t := fun t ht => by
    have h1 := (hg' (x + t) (hmem t ht)).comp t ((hasDerivAt_id t).const_add x)
    have h4 := (h1.sub_const (g' x)).sub ((hasDerivAt_id t).const_mul M)
    convert h4 using 1
    · funext s; simp [k']
    · simp
  have hk0 : k 0 = 0 := by simp [k]
  have hk'0 : k' 0 = 0 := by simp [k']
  have hconv : Convex ℝ (Set.uIcc 0 h) := convex_uIcc 0 h
  have hk'anti : AntitoneOn k' (Set.uIcc 0 h) :=
    antitoneOn_of_deriv_nonpos hconv (fun t ht => (hk' t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hk' t (interior_subset ht)).differentiableAt.differentiableWithinAt) fun t
          ht => by
        rw [(hk' t (interior_subset ht)).deriv]; linarith [hM (x + t) (hmem t (interior_subset ht))]
  have h0mem : (0 : ℝ) ∈ Set.uIcc 0 h := Set.left_mem_uIcc
  have hhmem : h ∈ Set.uIcc 0 h := Set.right_mem_uIcc
  have : k h ≤ 0 := by
    rcases le_total 0 h with h0 | h0
    · have hanti : AntitoneOn k (Set.uIcc 0 h) :=
        antitoneOn_of_deriv_nonpos hconv (fun t ht => (hk t ht).continuousAt.continuousWithinAt)
          (fun t ht => (hk t (interior_subset ht)).differentiableAt.differentiableWithinAt) fun t
              ht => by
            have ht' := interior_subset ht
            rw [(hk t ht').deriv, ← hk'0]
            have : 0 ≤ t := by rw [Set.uIcc_of_le h0] at ht'; exact ht'.1
            exact hk'anti h0mem ht' this
      exact hk0 ▸ hanti h0mem hhmem h0
    · have hmono : MonotoneOn k (Set.uIcc 0 h) :=
        monotoneOn_of_deriv_nonneg hconv (fun t ht => (hk t ht).continuousAt.continuousWithinAt)
          (fun t ht => (hk t (interior_subset ht)).differentiableAt.differentiableWithinAt) fun t
              ht => by
            have ht' := interior_subset ht
            rw [(hk t ht').deriv, ← hk'0]
            have : t ≤ 0 := by rw [Set.uIcc_of_ge h0] at ht'; exact ht'.2
            exact hk'anti ht' h0mem this
      exact hk0 ▸ hmono hhmem h0mem h0
  simp only [k] at this; linarith

/-- **Taylor, order two, on a segment.** -/
theorem abs_sub_le_of_abs_deriv2_le_on {g g' g'' : ℝ → ℝ} {M x h : ℝ}
    (hg : ∀ y ∈ Set.uIcc x (x + h), HasDerivAt g (g' y) y)
    (hg' : ∀ y ∈ Set.uIcc x (x + h), HasDerivAt g' (g'' y) y)
    (hM : ∀ y ∈ Set.uIcc x (x + h), |g'' y| ≤ M) :
    |g (x + h) - g x - h * g' x| ≤ M * h ^ 2 / 2 := by
  rw [abs_le]
  constructor
  · have :=
      sub_le_of_deriv2_le_on (g := fun y => -g y) (g' := fun y => -g' y) (g'' := fun y => -g'' y)
      (M := M) (x := x) (h := h) (fun y hy => (hg y hy).neg) (fun y hy => (hg' y hy).neg)
      (fun y hy => by linarith [(abs_le.1 (hM y hy)).1])
    linarith
  · exact sub_le_of_deriv2_le_on hg hg' fun y hy => (abs_le.1 (hM y hy)).2

end FalconPrecision.Taylor2
