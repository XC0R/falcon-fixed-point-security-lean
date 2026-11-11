/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFTRec

/-! # Certified-mode FFT error

ePrint 2026/1531 §7.3 item 1 and footnote 9: the intermediate values of `FFT(f)` are those of
`invFFT(f̂)`, which does not increase the sup norm, so `‖f̂‖∞ ≤ B` bounds every intermediate
evaluation by `B`. With that bound the recursion of `fft_rec_err` becomes `E_{L+1} = (2 + δ)E_L + δB
+ r`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFTRec

open FalconPrecision.Errors.FFTDef

/-- **Footnote 9.** Half-size evaluations are bounded by the full-size bound. -/
theorem half_eval_le (B : ℝ) (L : ℕ) (a : Fin (2 ^ (L + 1)) → ℂ) (ζ pt : Out L → ℂ)
    (ptS : Out (L + 1) → ℂ)
    (hpt : ∀ o b, ptS (o, b) = if b then -ζ o else ζ o) (hsq : ∀ o, ζ o ^ 2 = pt o)
        (hζ : ∀ o, ‖ζ o‖ = 1)
    (hB : ∀ o, ‖evalAt a (ptS o)‖ ≤ B) (o : Out L) :
    ‖evalAt (evens (castC a)) (pt o)‖ ≤ B ∧ ‖evalAt (odds (castC a)) (pt o)‖ ≤ B := by
  have h1 := evalAt_split (castC a) (ζ o)
  have h2 := evalAt_split (castC a) (-ζ o)
  rw [evalAt_castC] at h1 h2
  rw [neg_sq, hsq] at h2
  rw [hsq] at h1
  have hu : ‖evalAt a (ζ o)‖ ≤ B := by have := hB (o, false); rwa [hpt] at this
  have hv : ‖evalAt a (-ζ o)‖ ≤ B := by have := hB (o, true); rwa [hpt] at this
  have hconj : (starRingEnd ℂ) (ζ o) * ζ o = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
  constructor
  · have hx : evalAt (evens (castC a)) (pt o) = (evalAt a (ζ o) + evalAt a (-ζ o)) / 2 := by
      rw [h1, h2]; ring
    rw [hx, norm_div]; simp only [Complex.norm_ofNat]
    linarith [norm_add_le (evalAt a (ζ o)) (evalAt a (-ζ o))]
  · have hx : evalAt (odds (castC a)) (pt o) = (starRingEnd ℂ)
      (ζ o) / 2 * (evalAt a (ζ o) - evalAt a (-ζ o)) := by
      rw [h1, h2]
      linear_combination (-(evalAt (odds (castC a)) (pt o))) * hconj
    rw [hx, norm_mul, norm_div]
    simp only [Complex.norm_conj, hζ, Complex.norm_ofNat]
    linarith [norm_sub_le (evalAt a (ζ o)) (evalAt a (-ζ o))]

/-- **Certified-mode recursive FFT error.** -/
theorem fft_rec_err_cert (δ r B : ℝ) (E : ℕ → ℝ)
    (ζ ζh : (L : ℕ) → Out L → ℂ) (pt : (L : ℕ) → Out L → ℂ)
    (hpt : ∀ L o b, pt (L + 1) (o, b) = if b then -ζ L o else ζ L o)
    (hsq : ∀ L o, ζ L o ^ 2 = pt L o) (hζ : ∀ L o, ‖ζ L o‖ = 1)
    (hδ : ∀ L o, ‖ζh L o - ζ L o‖ ≤ δ)
    (fftH : (L : ℕ) → (Fin (2 ^ L) → ℂ) → Out L → ℂ)
    (h0 : ∀ a o, ‖fftH 0 a o - a ⟨0, by norm_num⟩‖ ≤ E 0)
    (hrec : ∀ L a o, ∃ p : ℂ, ‖p - ζh L o * fftH L (odds (castC a)) o‖ ≤ r ∧
      fftH (L + 1) a (o, false) = fftH L (evens (castC a)) o + p ∧
      fftH (L + 1) a (o, true) = fftH L (evens (castC a)) o - p)
    (hE : ∀ L, E (L + 1) = E L * (2 + δ) + δ * B + r) :
    ∀ L (a : Fin (2 ^ L) → ℂ), (∀ o, ‖evalAt a (pt L o)‖ ≤ B) →
      ∀ o, ‖fftH L a o - evalAt a (pt L o)‖ ≤ E L := by
  intro L
  induction L with
  | zero =>
    intro a _ o
    have : evalAt a (pt 0 o) = a ⟨0, by norm_num⟩ := by simp [evalAt]
    rw [this]; exact h0 a o
  | succ L ih =>
    intro a hB o
    obtain ⟨o, b⟩ := o
    obtain ⟨p, hp, hf, ht⟩ := hrec L a o
    have hsub := fun o' => half_eval_le B L a (ζ L) (pt L) (pt (L + 1)) (hpt L) (hsq L) (hζ L) hB o'
    have hu := ih _ (fun o' => (hsub o').1) o
    have hv := ih _ (fun o' => (hsub o').2) o
    have hB_ :=
        FalconPrecision.Errors.Butterfly.butterfly_err (evalAt (evens (castC a)) (pt L o))
            (fftH L (evens (castC a)) o)
      (ζ L o) (ζh L o) (evalAt (odds (castC a)) (pt L o))
          (fftH L (odds (castC a)) o) p (E L) δ r (hζ L o)
      (hδ L o) hu hv hp
    have hvb : δ * ‖evalAt (odds (castC a)) (pt L o)‖ ≤ δ * B :=
      mul_le_mul_of_nonneg_left (hsub o).2 ((norm_nonneg _).trans (hδ L o))
    have hsplit := evalAt_split (castC a) (ζ L o)
    have hsplit' := evalAt_split (castC a) (-ζ L o)
    rw [evalAt_castC] at hsplit hsplit'
    rw [neg_sq] at hsplit'
    rw [hsq] at hsplit hsplit'
    rw [hE]
    cases b with
    | false =>
      rw [hf, hpt]; simp only [Bool.false_eq_true, ↓reduceIte, hsplit]
      linarith [hB_.1]
    | true =>
      rw [ht, hpt]; simp only [↓reduceIte, hsplit', neg_mul, ← sub_eq_add_neg]
      linarith [hB_.2]

/-- Closed form: `E_L = (2 + δ)^L E₀ + (δB + r)·Σ_{j<L} (2 + δ)^j`. -/
theorem cert_closed (δ r B : ℝ) (E : ℕ → ℝ) (hE : ∀ L, E (L + 1) = E L * (2 + δ) + δ * B + r) :
    ∀ L, E L = (2 + δ) ^ L * E 0 + (δ * B + r) * ∑ j ∈ Finset.range L, (2 + δ) ^ j := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [hE, ih, Finset.sum_range_succ', pow_succ, pow_zero]
    simp only [pow_succ, ← Finset.sum_mul]
    ring

end FalconPrecision.Errors.FFTRec
