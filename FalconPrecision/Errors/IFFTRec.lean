/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFTRec

/-! # Error of Falcon's recursive inverse FFT in fixed point

Falcon's invFFT (`splitfft`, spec Alg. 1) recovers `f₀(ζ²) = (f(ζ) + f(-ζ))/2` and `f₁(ζ²) = ζ̄(f(ζ)
- f(-ζ))/2` (`|ζ| = 1`), recurses on both halves and interleaves the coefficients. The split does
not increase the sup norm, so with values bounded by `B`, a halved conjugate twiddle within `δ` of
`ζ̄/2` and every split output rounded within `r`, an input error `ε` becomes `ε(1 + 2δ) + 2δB + r`
per level (ePrint 2026/1531 §7.3 item 2). -/

@[expose] public section

namespace FalconPrecision.Errors.FFTRec

open FalconPrecision.Errors.FFTDef

/-- The error after `L` split levels from input error `ε`. -/
def ifftBound (δ B r e₀ : ℝ) : ℕ → ℝ → ℝ
  | 0, ε => ε + e₀
  | L + 1, ε => ifftBound δ B r e₀ L (ε * (1 + 2 * δ) + 2 * δ * B + r)

theorem fin_even_or_odd {m : ℕ} (i : Fin (2 * m)) :
    (∃ j : Fin m, i = ⟨2 * j, by omega⟩) ∨ ∃ j : Fin m, i = ⟨2 * j + 1, by omega⟩ := by
  obtain ⟨i, hi⟩ := i
  rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact Or.inl ⟨⟨j, by omega⟩, by ext; simp; ring⟩
  · exact Or.inr ⟨⟨j, by omega⟩, by ext; simp⟩

/-- **Recursive inverse FFT error.** -/
theorem ifft_rec_err (δ B r e₀ : ℝ) (hδ0 : 0 ≤ δ)
    (ζ : (L : ℕ) → Out L → ℂ) (pt : (L : ℕ) → Out L → ℂ)
    (hpt : ∀ L o b, pt (L + 1) (o, b) = if b then -ζ L o else ζ L o)
    (hsq : ∀ L o, ζ L o ^ 2 = pt L o) (hζ : ∀ L o, ‖ζ L o‖ = 1)
    (ifftH : (L : ℕ) → (Out L → ℂ) → Fin (2 ^ L) → ℂ)
    (h0 : ∀ F, ‖ifftH 0 F ⟨0, by norm_num⟩ - F ()‖ ≤ e₀)
    (hrec : ∀ L F, ∃ e d : Out L → ℂ,
      (∀ o, ‖e o - (F (o, false) + F (o, true)) / 2‖ ≤ r) ∧
      (∀ o, ∃ c : ℂ, ‖c - (starRingEnd ℂ)
          (ζ L o) / 2‖ ≤ δ ∧ ‖d o - c * (F (o, false) - F (o, true))‖ ≤ r) ∧
      evens (castC (ifftH (L + 1) F)) = ifftH L e ∧ odds (castC (ifftH (L + 1) F)) = ifftH L d) :
    ∀ L (a : Fin (2 ^ L) → ℂ) (F : Out L → ℂ) (ε : ℝ), (∀ o, ‖evalAt a (pt L o)‖ ≤ B) →
      (∀ o, ‖F o - evalAt a (pt L o)‖ ≤ ε) → ∀ i, ‖ifftH L F i - a i‖ ≤ ifftBound δ B r e₀ L ε := by
  intro L
  induction L with
  | zero =>
    intro a F ε _ hF i
    have hi : i = ⟨0, by norm_num⟩ := Fin.ext (by have := i.2; simp at this; omega)
    subst hi
    have hev : evalAt a (pt 0 ()) = a ⟨0, by norm_num⟩ := by simp [evalAt]
    have := hF ()
    rw [hev] at this
    calc ‖ifftH 0 F ⟨0, _⟩ - a ⟨0, _⟩‖ = ‖(ifftH 0 F ⟨0, by norm_num⟩ - F ()) +
        (F () - a ⟨0, by norm_num⟩)‖ := by
          ring_nf
      _ ≤ ‖ifftH 0 F ⟨0, by norm_num⟩ - F ()‖ + ‖F () - a ⟨0, by norm_num⟩‖ := norm_add_le _ _
      _ ≤ ifftBound δ B r e₀ 0 ε := by simp only [ifftBound]; linarith [h0 F]
  | succ L ih =>
    intro a F ε hB hF i
    obtain ⟨e, d, he, hd, hev, hod⟩ := hrec L F
    set ε' := ε * (1 + 2 * δ) + 2 * δ * B + r
    -- exact half transforms
    have hsplit : ∀ o, evalAt a (ζ L o) = evalAt (evens (castC a))
        (pt L o) + ζ L o * evalAt (odds (castC a)) (pt L o) ∧
        evalAt a (-ζ L o) = evalAt (evens (castC a)) (pt L o) - ζ L o * evalAt (odds (castC a))
            (pt L o) := by
      intro o
      have h1 := evalAt_split (castC a) (ζ L o)
      have h2 := evalAt_split (castC a) (-ζ L o)
      rw [evalAt_castC] at h1 h2
      rw [neg_sq, hsq] at h2
      rw [hsq] at h1
      exact ⟨h1, by rw [h2]; ring⟩
    have hconj : ∀ o, (starRingEnd ℂ) (ζ L o) * ζ L o = 1 := by
      intro o
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
    have hu : ∀ o, F (o, false) = evalAt a (ζ L o) +
        (F (o, false) - evalAt a (pt (L + 1) (o, false))) := by
      intro o; rw [hpt]; simp
    have hv : ∀ o, F (o, true) = evalAt a (-ζ L o) +
        (F (o, true) - evalAt a (pt (L + 1) (o, true))) := by
      intro o; rw [hpt]; simp
    have hBu : ∀ o, ‖evalAt a (ζ L o)‖ ≤ B := fun o => by have := hB (o, false); rwa [hpt] at this
    have hBv : ∀ o, ‖evalAt a (-ζ L o)‖ ≤ B := fun o => by have := hB (o, true); rwa [hpt] at this
    -- even half
    have hE : ∀ o, ‖e o - evalAt (evens (castC a)) (pt L o)‖ ≤ ε' := by
      intro o
      obtain ⟨h1, h2⟩ := hsplit o
      have hx : evalAt (evens (castC a)) (pt L o) = (evalAt a (ζ L o) + evalAt a (-ζ L o)) / 2 := by
        rw [h1, h2]; ring
      have hfu := hF (o, false)
      have hfv := hF (o, true)
      have hid : e o - evalAt (evens (castC a))
          (pt L o) = (e o - (F (o, false) + F (o, true)) / 2) +
          ((F (o, false) - evalAt a (pt (L + 1) (o, false))) +
              (F (o, true) - evalAt a (pt (L + 1) (o, true)))) / 2 := by
        rw [hx, hpt, hpt]; simp; ring
      rw [hid]
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBu o)
      calc _ ≤ ‖e o - (F (o, false) + F (o, true)) / 2‖ +
          ‖((F (o, false) - evalAt a (pt (L + 1) (o, false))) +
            (F (o, true) - evalAt a (pt (L + 1) (o, true)))) / 2‖ := norm_add_le _ _
        _ ≤ r + (ε + ε) / 2 := by
            gcongr
            · exact he o
            · rw [norm_div]; simp only [Complex.norm_ofNat]
              gcongr
              exact (norm_add_le _ _).trans (add_le_add hfu hfv)
        _ ≤ ε' := by
            have hε : 0 ≤ ε := (norm_nonneg _).trans hfu
            simp only [ε']; nlinarith
    -- odd half
    have hD : ∀ o, ‖d o - evalAt (odds (castC a)) (pt L o)‖ ≤ ε' := by
      intro o
      obtain ⟨c, hc, hdo⟩ := hd o
      obtain ⟨h1, h2⟩ := hsplit o
      set u := evalAt a (ζ L o)
      set v := evalAt a (-ζ L o)
      set z := starRingEnd ℂ (ζ L o)
      have hx : evalAt (odds (castC a)) (pt L o) = z / 2 * (u - v) := by
        rw [h1, h2]
        have := hconj o
        linear_combination (-(evalAt (odds (castC a)) (pt L o))) * this
      set eu := F (o, false) - evalAt a (pt (L + 1) (o, false))
      set ev := F (o, true) - evalAt a (pt (L + 1) (o, true))
      have heu : ‖eu‖ ≤ ε := hF (o, false)
      have hev' : ‖ev‖ ≤ ε := hF (o, true)
      have hFu : F (o, false) = u + eu := hu o
      have hFv : F (o, true) = v + ev := hv o
      have hid : d o - evalAt (odds (castC a)) (pt L o) =
          (d o - c * (F (o, false) - F (o, true))) + c * (eu - ev) + (c - z / 2) * (u - v) := by
        rw [hx, hFu, hFv]; ring
      have hzn : ‖z / 2‖ = 1 / 2 := by
        simp only [z, norm_div, Complex.norm_conj, hζ, Complex.norm_ofNat]
      have hcn : ‖c‖ ≤ 1 / 2 + δ := by
        calc ‖c‖ = ‖z / 2 + (c - z / 2)‖ := by ring_nf
          _ ≤ ‖z / 2‖ + ‖c - z / 2‖ := norm_add_le _ _
          _ ≤ 1 / 2 + δ := by rw [hzn]; linarith
      have huv : ‖u - v‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith [hBu o, hBv o])
      have heuv : ‖eu - ev‖ ≤ 2 * ε := (norm_sub_le _ _).trans (by linarith)
      rw [hid]
      calc _ ≤ ‖d o - c * (F (o, false) - F (o, true))‖ + ‖c * (eu - ev)‖ + ‖(c - z / 2) *
          (u - v)‖ :=
            norm_add₃_le
        _ = ‖d o - c * (F (o, false) - F (o, true))‖ + ‖c‖ * ‖eu - ev‖ + ‖c - z / 2‖ * ‖u - v‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ r + (1 / 2 + δ) * (2 * ε) + δ * (2 * B) := by gcongr
        _ = ε' := by simp only [ε']; ring
    have hBe : ∀ o, ‖evalAt (evens (castC a)) (pt L o)‖ ≤ B := by
      intro o
      obtain ⟨h1, h2⟩ := hsplit o
      have hx : evalAt (evens (castC a)) (pt L o) = (evalAt a (ζ L o) + evalAt a (-ζ L o)) / 2 := by
        rw [h1, h2]; ring
      rw [hx, norm_div]; simp only [Complex.norm_ofNat]
      linarith [norm_add_le (evalAt a (ζ L o)) (evalAt a (-ζ L o)), hBu o, hBv o]
    have hBo : ∀ o, ‖evalAt (odds (castC a)) (pt L o)‖ ≤ B := by
      intro o
      obtain ⟨h1, h2⟩ := hsplit o
      have hx : evalAt (odds (castC a)) (pt L o) =
          (starRingEnd ℂ) (ζ L o) / 2 * (evalAt a (ζ L o) - evalAt a (-ζ L o)) := by
        rw [h1, h2]
        linear_combination (-(evalAt (odds (castC a)) (pt L o))) * hconj o
      rw [hx, norm_mul, norm_div]
      simp only [Complex.norm_conj, hζ, Complex.norm_ofNat]
      linarith [norm_sub_le (evalAt a (ζ L o)) (evalAt a (-ζ L o)), hBu o, hBv o]
    have ihE := ih (evens (castC a)) e ε' hBe hE
    have ihD := ih (odds (castC a)) d ε' hBo hD
    simp only [ifftBound]
    have hc : ∀ j, castC (ifftH (L + 1) F) j - castC a j = ifftH (L + 1) F (Fin.cast (by ring) j) -
        a (Fin.cast (by ring) j) := fun j => rfl
    obtain ⟨j, hj⟩ : ∃ j : Fin (2 * 2 ^ L), i = Fin.cast (by ring) j :=
        ⟨Fin.cast (by ring) i, by ext; simp⟩
    rw [hj, ← hc]
    rcases fin_even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have := ihE k
      rw [← hev] at this
      exact this
    · have := ihD k
      rw [← hod] at this
      exact this

/-- **Closed form.** `ifftBound L ε ≤ (1 + 2δ)^L (ε + L(2δB + r)) + e₀`. -/
theorem ifftBound_le (δ B r e₀ : ℝ) (hδ0 : 0 ≤ δ) (hB : 0 ≤ B) (hr : 0 ≤ r) :
    ∀ L ε, ifftBound δ B r e₀ L ε ≤ (1 + 2 * δ) ^ L * (ε + L * (2 * δ * B + r)) + e₀ := by
  intro L
  induction L with
  | zero => intro ε; simp [ifftBound]
  | succ L ih =>
    intro ε
    simp only [ifftBound]
    refine (ih _).trans ?_
    have hc : 0 ≤ 2 * δ * B + r := by positivity
    have hq : 1 ≤ 1 + 2 * δ := by linarith
    have hp : 0 ≤ (1 + 2 * δ) ^ L := by positivity
    push_cast
    have : (1 + 2 * δ) ^ L * ((L + 1) * (2 * δ * B + r)) ≤ (1 + 2 * δ) ^ L * (1 + 2 * δ) *
        ((L + 1) * (2 * δ * B + r)) := by
      have h0 : 0 ≤ (1 + 2 * δ) ^ L * ((L + 1) * (2 * δ * B + r)) := by positivity
      nlinarith
    rw [pow_succ]
    nlinarith

end FalconPrecision.Errors.FFTRec
