/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFTDef
public import FalconPrecision.Errors.FFTErr

/-! # Error of Falcon's recursive FFT in fixed point

Falcon's FFT (`splitfft`/`mergefft`) evaluates `f` with `2^L` coefficients at `2^L` points: level `L
+ 1` pairs the points `±ζ` with `ζ² ` a level-`L` point, and `f(±ζ) = f₀(ζ²) ± ζ·f₁(ζ²)`. Any
computation following this recursion with a twiddle within `δ` of `ζ` and the product `ζ̂·f̂₁`
rounded within `r` has error `E_L` at every output, where `E_{L+1} = (2 + δ)E_L + δ·2^L·A + r` for
coefficients bounded by `A`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFTRec

open FalconPrecision.Errors.FFTDef

/-- Output positions of an `L`-level transform: `L` sign choices. -/
def Out : ℕ → Type
  | 0 => Unit
  | L + 1 => Out L × Bool

/-- Coefficients of size `2^(L+1)` viewed as size `2·2^L`. -/
def castC {L : ℕ} (a : Fin (2 ^ (L + 1)) → ℂ) : Fin (2 * 2 ^ L) → ℂ :=
  fun i => a (Fin.cast (by ring) i)

theorem evalAt_castC {L : ℕ} (a : Fin (2 ^ (L + 1)) → ℂ)
    (z : ℂ) : evalAt (castC a) z = evalAt a z := by
  unfold evalAt castC
  exact Fintype.sum_equiv (finCongr (by ring)) _ _ fun i => rfl

theorem norm_evalAt_le {n : ℕ} (a : Fin n → ℂ) (z : ℂ) (hz : ‖z‖ = 1) (A : ℝ)
    (ha : ∀ i, ‖a i‖ ≤ A) :
    ‖evalAt a z‖ ≤ n * A := by
  unfold evalAt
  calc ‖∑ i, a i * z ^ (i : ℕ)‖ ≤ ∑ i : Fin n, ‖a i * z ^ (i : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, A :=
        Finset.sum_le_sum fun i _ => by rw [norm_mul, norm_pow, hz, one_pow, mul_one]; exact ha i
    _ = n * A := by simp

/-- **Recursive FFT error.** -/
theorem fft_rec_err (δ r A : ℝ) (E : ℕ → ℝ)
    (ζ ζh : (L : ℕ) → Out L → ℂ) (pt : (L : ℕ) → Out L → ℂ)
    (hpt : ∀ L o b, pt (L + 1) (o, b) = if b then -ζ L o else ζ L o)
    (hsq : ∀ L o, ζ L o ^ 2 = pt L o) (hζ : ∀ L o, ‖ζ L o‖ = 1) (hpt0 : ∀ o, ‖pt 0 o‖ = 1)
    (hδ : ∀ L o, ‖ζh L o - ζ L o‖ ≤ δ)
    (fftH : (L : ℕ) → (Fin (2 ^ L) → ℂ) → Out L → ℂ)
    (h0 : ∀ a o, ‖fftH 0 a o - a ⟨0, by norm_num⟩‖ ≤ E 0)
    (hrec : ∀ L a o, ∃ p : ℂ, ‖p - ζh L o * fftH L (odds (castC a)) o‖ ≤ r ∧
      fftH (L + 1) a (o, false) = fftH L (evens (castC a)) o + p ∧
      fftH (L + 1) a (o, true) = fftH L (evens (castC a)) o - p)
    (hE : ∀ L, E (L + 1) = E L * (2 + δ) + δ * (2 ^ L * A) + r) :
    ∀ L (a : Fin (2 ^ L) → ℂ), (∀ i, ‖a i‖ ≤ A) → ∀ o, ‖fftH L a o - evalAt a (pt L o)‖ ≤ E L := by
  intro L
  induction L with
  | zero =>
    intro a _ o
    have : evalAt a (pt 0 o) = a ⟨0, by norm_num⟩ := by
      simp [evalAt]
    rw [this]; exact h0 a o
  | succ L ih =>
    intro a ha o
    obtain ⟨o, b⟩ := o
    obtain ⟨p, hp, hf, ht⟩ := hrec L a o
    have hev : ∀ i, ‖evens (castC a) i‖ ≤ A := fun i => ha _
    have hod : ∀ i, ‖odds (castC a) i‖ ≤ A := fun i => ha _
    have hu := ih _ hev o
    have hv := ih _ hod o
    have hptL : ‖pt L o‖ = 1 := by
      cases L with
      | zero => exact hpt0 o
      | succ L' =>
        obtain ⟨o', b'⟩ := o
        rw [hpt]; split_ifs <;> simp [hζ]
    have hsqL := hsq L o
    have hB :=
        FalconPrecision.Errors.Butterfly.butterfly_err (evalAt (evens (castC a)) (pt L o))
            (fftH L (evens (castC a)) o)
      (ζ L o) (ζh L o) (evalAt (odds (castC a)) (pt L o))
          (fftH L (odds (castC a)) o) p (E L) δ r (hζ L o)
      (hδ L o) hu hv hp
    have hvb : δ * ‖evalAt (odds (castC a)) (pt L o)‖ ≤ δ * (2 ^ L * A) := by
      have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ L o)
      have := norm_evalAt_le (odds (castC a)) (pt L o) hptL A hod
      push_cast at this
      exact mul_le_mul_of_nonneg_left this hδ0
    have hsplit := evalAt_split (castC a) (ζ L o)
    have hsplit' := evalAt_split (castC a) (-ζ L o)
    rw [evalAt_castC] at hsplit hsplit'
    rw [neg_sq] at hsplit'
    rw [hsqL] at hsplit hsplit'
    rw [hE]
    cases b with
    | false =>
      rw [hf, hpt]; simp only [Bool.false_eq_true, ↓reduceIte, hsplit]
      linarith [hB.1]
    | true =>
      rw [ht, hpt]; simp only [↓reduceIte, hsplit', neg_mul, ← sub_eq_add_neg]
      linarith [hB.2]

/--
**Closed form.** Under the hypotheses of `fft_rec_err` with `E` the exact recursion, every output of
the `L`-level computed FFT is within `(2 + δ)^L E₀ + L(2 + δ)^{L-1}(δA + r)` of the exact
evaluation. -/
theorem fft_rec_err_closed (δ r A : ℝ) (hδ0 : 0 ≤ δ) (hr : 0 ≤ r) (hA : 0 ≤ A) (E : ℕ → ℝ)
    (hE : ∀ L, E (L + 1) = E L * (2 + δ) + δ * (2 ^ L * A) + r) :
    ∀ L, E L ≤ (2 + δ) ^ L * E 0 + L * (2 + δ) ^ (L - 1) * (δ * A + r) :=
  FalconPrecision.Errors.FFTErr.fft_err δ r A hδ0 hr hA E (fun ℓ => 2 ^ ℓ * A)
    (fun ℓ => by rw [hE]; ring_nf; rfl) (fun ℓ => le_rfl)

end FalconPrecision.Errors.FFTRec
