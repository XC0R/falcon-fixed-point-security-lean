/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFTL2

/-! # Parseval for Falcon's recursive FFT

`Σ_o |f(pt L o)|² = 2^L·Σ_i |a_i|²` over the `2^L` points of the recursion (parallelogram law at
each merge). -/

@[expose] public section

namespace FalconPrecision.Errors.FFTRec

open FalconPrecision.Errors.FFTDef

theorem sum_range_two_mul_real (h : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), h i = ∑ i ∈ Finset.range m, (h (2 * i) + h (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

theorem sum_fin_two_mul (m : ℕ) (g : Fin (2 * m) → ℝ) :
    ∑ i, g i = ∑ j : Fin m, (g ⟨2 * j, by omega⟩ + g ⟨2 * j + 1, by omega⟩) := by
  set h : ℕ → ℝ := fun i => if hi : i < 2 * m then g ⟨i, hi⟩ else 0
  have e1 : ∑ i, g i = ∑ i ∈ Finset.range (2 * m), h i := by
    rw [← Fin.sum_univ_eq_sum_range]; exact Finset.sum_congr rfl fun i _ => by simp [h, i.2]
  have e2 : ∑ j : Fin m, (g ⟨2 * j, by omega⟩ + g ⟨2 * j + 1, by omega⟩) =
      ∑ j ∈ Finset.range m, (h (2 * j) + h (2 * j + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => h (2 * j) + h (2 * j + 1))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : 2 * (j : ℕ) < 2 * m := by omega
    have h2 : 2 * (j : ℕ) + 1 < 2 * m := by omega
    simp [h, h1, h2]
  rw [e1, e2, sum_range_two_mul_real]

theorem sum_castC (L : ℕ) (a : Fin (2 ^ (L + 1)) → ℂ) :
    ∑ i, ‖a i‖ ^ 2 = ∑ j, ‖evens (castC a) j‖ ^ 2 + ∑ j, ‖odds (castC a) j‖ ^ 2 := by
  have : ∑ i, ‖a i‖ ^ 2 = ∑ i, ‖castC a i‖ ^ 2 :=
    (Fintype.sum_equiv (finCongr (by ring)) _ _ fun i => rfl)
  rw [this, sum_fin_two_mul, Finset.sum_add_distrib]
  rfl

/-- **Parseval.** -/
theorem parseval (ζ pt : (L : ℕ) → Out L → ℂ)
    (hpt : ∀ L o b, pt (L + 1) (o, b) = if b then -ζ L o else ζ L o)
    (hsq : ∀ L o, ζ L o ^ 2 = pt L o) (hζ : ∀ L o, ‖ζ L o‖ = 1) :
    ∀ L (a : Fin (2 ^ L) → ℂ), ∑ o, ‖evalAt a (pt L o)‖ ^ 2 = 2 ^ L * ∑ i, ‖a i‖ ^ 2 := by
  intro L
  induction L with
  | zero =>
    intro a
    have : ∀ o, evalAt a (pt 0 o) = a ⟨0, by norm_num⟩ := fun o => by simp [evalAt]
    simp only [this]
    change ∑ _o : Unit, _ = _
    simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero, one_mul]
    rw [Fintype.sum_eq_single (⟨0, by norm_num⟩ : Fin (2 ^ 0)) fun i hi =>
      absurd (Fin.ext (by have := i.2; simp at this; omega)) hi]
  | succ L ih =>
    intro a
    rw [sum_out_succ, sum_castC]
    have hE := ih (evens (castC a))
    have hO := ih (odds (castC a))
    calc _ = ∑ o : Out L, 2 *
        (‖evalAt (evens (castC a)) (pt L o)‖ ^ 2 + ‖evalAt (odds (castC a)) (pt L o)‖ ^ 2) := ?_
      _ = 2 * (∑ o, ‖evalAt (evens (castC a)) (pt L o)‖ ^ 2 + ∑ o, ‖evalAt (odds (castC a))
          (pt L o)‖ ^ 2) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hE, hO, pow_succ]; ring
    refine Finset.sum_congr rfl fun o _ => ?_
    have hsplit := evalAt_split (castC a) (ζ L o)
    have hsplit' := evalAt_split (castC a) (-ζ L o)
    rw [evalAt_castC] at hsplit hsplit'
    rw [neg_sq, hsq] at hsplit'
    rw [hsq] at hsplit
    rw [hpt, hpt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hsplit, hsplit']
    have hp := parallelogram_law_with_norm ℝ (evalAt (evens (castC a)) (pt L o))
      (ζ L o * evalAt (odds (castC a)) (pt L o))
    rw [norm_mul, hζ, one_mul] at hp
    have e : evalAt (evens (castC a)) (pt L o) + -ζ L o * evalAt (odds (castC a)) (pt L o) =
        evalAt (evens (castC a)) (pt L o) - ζ L o * evalAt (odds (castC a)) (pt L o) := by ring
    rw [e]
    nlinarith [hp]

end FalconPrecision.Errors.FFTRec
