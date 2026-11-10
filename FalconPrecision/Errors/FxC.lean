/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FxR
public import FalconPrecision.Errors.FFTRec

/-! # Complex fixed point and the FFT error instantiated (TASK-009 S7c)

`FxC` is a pair of `FxR` at a common tag (ePrint 2026/1531 §7.1). A twiddle rounded componentwise to
tag `mζ` is within `δ = √2·ulp(mζ)/2` of the root; a complex product computed as four rounded real
products combined exactly (§7.2 items 1-2) is within `r = √2·ulp(mζ + m)` of the exact product. With
these, Falcon's recursive FFT at budget `m` has every output within `(2 + δ)^L E₀ + L(2 +
δ)^{L-1}(δA + r)` of the exact evaluation. -/

@[expose] public section

namespace FalconPrecision.Errors.Fixed

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef

variable {p : ℕ}

/-- A fixed-point complex number: real and imaginary parts at a common tag. -/
structure FxC (p : ℕ) where
  re : FxR p
  im : FxR p
  tag : re.m = im.m

/-- The value of a fixed-point complex number. -/
noncomputable def cval (z : FxC p) : ℂ := ⟨val z.re, val z.im⟩

theorem norm_le_of_re_im (z : ℂ) (e : ℝ) (hre : |z.re| ≤ e) (him : |z.im| ≤ e) : ‖z‖ ≤ √2 * e :=
  (Complex.norm_le_sqrt_two_mul_max z).trans
    (mul_le_mul_of_nonneg_left (max_le hre him) (Real.sqrt_nonneg _))

/-- **Twiddle error.** Each component rounded to the nearest integer at tag `mζ`. -/
theorem twiddle_err (ζ : ℂ) (zh : FxC p) (mζ : ℤ) (hm : zh.re.m = mζ)
    (hre : IsRound zh.re.x (ζ.re / ulp p mζ)) (him : IsRound zh.im.x (ζ.im / ulp p mζ)) :
    ‖cval zh - ζ‖ ≤ √2 * (ulp p mζ / 2) := by
  have hu := ulp_pos (p := p) mζ
  have key : ∀ (x : ℤ) (y : ℝ), IsRound x (y / ulp p mζ) →
      |(x : ℝ) * (2 : ℝ) ^ (mζ - p) - y| ≤ ulp p mζ / 2 := by
    intro x y h
    change |(x : ℝ) * ulp p mζ - y| ≤ _
    unfold IsRound at h
    have : (x : ℝ) * ulp p mζ - y = ((x : ℝ) - y / ulp p mζ) * ulp p mζ := by field_simp
    rw [this, abs_mul, abs_of_pos hu]; nlinarith
  subst hm
  apply norm_le_of_re_im
  · simp only [cval, Complex.sub_re, val]; exact key _ _ hre
  · simp only [cval, Complex.sub_im, val, ← zh.tag]; exact key _ _ him

/--
**Rounded complex product.** Four real products, each within `u/2` of exact, combined exactly into
`(ac - bd) + (ad + bc)i`, are within `√2·u` of the exact complex product. -/
theorem cmul_err (z w out : ℂ) (u : ℝ) (q₁ q₂ q₃ q₄ : ℝ)
    (h₁ : |q₁ - z.re * w.re| ≤ u / 2) (h₂ : |q₂ - z.im * w.im| ≤ u / 2)
    (h₃ : |q₃ - z.re * w.im| ≤ u / 2) (h₄ : |q₄ - z.im * w.re| ≤ u / 2)
    (hre : out.re = q₁ - q₂) (him : out.im = q₃ + q₄) : ‖out - z * w‖ ≤ √2 * u := by
  apply norm_le_of_re_im
  · rw [Complex.sub_re, Complex.mul_re, hre]
    calc |q₁ - q₂ - (z.re * w.re - z.im * w.im)| = |(q₁ - z.re * w.re) - (q₂ - z.im * w.im)| :=
        by ring_nf
      _ ≤ |q₁ - z.re * w.re| + |q₂ - z.im * w.im| := abs_sub _ _
      _ ≤ u := by linarith
  · rw [Complex.sub_im, Complex.mul_im, him]
    calc |q₃ + q₄ - (z.re * w.im + z.im * w.re)| = |(q₃ - z.re * w.im) + (q₄ - z.im * w.re)| :=
        by ring_nf
      _ ≤ |q₃ - z.re * w.im| + |q₄ - z.im * w.re| := abs_add_le _ _
      _ ≤ u := by linarith

/-- **Fixed-point complex product** (`FxR` multiplication, §7.2 item 2): four products at tag `z.m +
w.m`, each rounded within half an ulp (`mul_val`), then an exact subtraction and addition. -/
theorem fxc_mul_err (z w : FxC p) (out : FxC p) (r₁ r₂ r₃ r₄ : ℤ)
    (hr₁ : IsRound r₁ ((z.re.x * w.re.x : ℤ) / (2 : ℝ) ^ p)) (hb₁ : |r₁| < 2 ^ p)
    (hr₂ : IsRound r₂ ((z.im.x * w.im.x : ℤ) / (2 : ℝ) ^ p)) (hb₂ : |r₂| < 2 ^ p)
    (hr₃ : IsRound r₃ ((z.re.x * w.im.x : ℤ) / (2 : ℝ) ^ p)) (hb₃ : |r₃| < 2 ^ p)
    (hr₄ : IsRound r₄ ((z.im.x * w.re.x : ℤ) / (2 : ℝ) ^ p)) (hb₄ : |r₄| < 2 ^ p)
    (hore : out.re.x = r₁ - r₂) (hoim : out.im.x = r₃ + r₄) (hom : out.re.m = z.re.m + w.re.m) :
    ‖cval out - cval z * cval w‖ ≤ √2 * ulp p (z.re.m + w.re.m) := by
  have hz := z.tag
  have hw := w.tag
  have e₁ := mul_val z.re w.re r₁ hr₁ hb₁
  have e₂ := mul_val z.im w.im r₂ hr₂ hb₂
  have e₃ := mul_val z.re w.im r₃ hr₃ hb₃
  have e₄ := mul_val z.im w.re r₄ hr₄ hb₄
  rw [← hz, ← hw] at e₂
  rw [← hw] at e₃
  rw [← hz] at e₄
  have hoim' : out.im.m = z.re.m + w.re.m := out.tag ▸ hom
  apply cmul_err (cval z) (cval w) (cval out) (ulp p (z.re.m + w.re.m)) _ _ _ _ e₁ e₂ e₃ e₄
  · simp only [cval, val, hore, hom]; push_cast; ring
  · simp only [cval, val, hoim, hoim']; push_cast; ring

/--
**Fixed-point FFT error.** Falcon's recursive FFT at budget `m` with a twiddle table rounded to tag
`mζ` and products rounded as in `fxc_mul_err` (so `δ = √2·ulp(mζ)/2`, `r = √2·ulp(mζ + m)`), on
coefficients bounded by `A`: every output is within `(2 + δ)^L E₀ + L(2 + δ)^{L-1}(δA + r)` of the
exact evaluation. -/
theorem fft_fxp_err (mζ m : ℤ) (A E₀ : ℝ) (hA : 0 ≤ A)
    (ζ ζh : (L : ℕ) → Out L → ℂ) (pt : (L : ℕ) → Out L → ℂ)
    (hpt : ∀ L o b, pt (L + 1) (o, b) = if b then -ζ L o else ζ L o)
    (hsq : ∀ L o, ζ L o ^ 2 = pt L o) (hζ : ∀ L o, ‖ζ L o‖ = 1) (hpt0 : ∀ o, ‖pt 0 o‖ = 1)
    (hδ : ∀ L o, ‖ζh L o - ζ L o‖ ≤ √2 * (ulp p mζ / 2))
    (fftH : (L : ℕ) → (Fin (2 ^ L) → ℂ) → Out L → ℂ)
    (h0 : ∀ a o, ‖fftH 0 a o - a ⟨0, by norm_num⟩‖ ≤ E₀)
    (hrec : ∀ L a o, ∃ q : ℂ, ‖q - ζh L o * fftH L (odds (castC a)) o‖ ≤ √2 * ulp p (mζ + m) ∧
      fftH (L + 1) a (o, false) = fftH L (evens (castC a)) o + q ∧
      fftH (L + 1) a (o, true) = fftH L (evens (castC a)) o - q) :
    ∀ L (a : Fin (2 ^ L) → ℂ), (∀ i, ‖a i‖ ≤ A) → ∀ o,
      ‖fftH L a o - evalAt a (pt L o)‖ ≤ (2 + √2 * (ulp p mζ / 2)) ^ L * E₀ +
        L * (2 + √2 * (ulp p mζ / 2)) ^ (L - 1) *
          (√2 * (ulp p mζ / 2) * A + √2 * ulp p (mζ + m)) := by
  set δ := √2 * (ulp p mζ / 2)
  set r := √2 * ulp p (mζ + m)
  have hδ0 : 0 ≤ δ := mul_nonneg (Real.sqrt_nonneg _) (by linarith [ulp_pos (p := p) mζ])
  have hr0 : 0 ≤ r := mul_nonneg (Real.sqrt_nonneg _) (ulp_pos _).le
  let E : ℕ → ℝ := fun L => Nat.rec E₀ (fun ℓ e => e * (2 + δ) + δ * (2 ^ ℓ * A) + r) L
  have hE : ∀ L, E (L + 1) = E L * (2 + δ) + δ * (2 ^ L * A) + r := fun L => rfl
  intro L a ha o
  have h1 := fft_rec_err δ r A E ζ ζh pt hpt hsq hζ hpt0 hδ fftH h0 hrec hE L a ha o
  have h2 := fft_rec_err_closed δ r A hδ0 hr0 hA E hE L
  exact h1.trans h2

end FalconPrecision.Errors.Fixed
