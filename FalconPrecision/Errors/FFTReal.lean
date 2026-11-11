/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFSampModel

/-! # Real polynomials in FFT form along ffSampling

`cj L` is the conjugate position: `pt L (cj L o) = conj (pt L o)` (`pt_cj`). `IsReal v` (`v (cj o) =
conj (v o)`) holds for the FFT of a real polynomial (`isReal_evalAt`), is kept by `splitE`
(`isReal_splitE`), `mergeE` of an output with `IsFFT` (`isReal_mergeE`) and `upd` with a real `ℓ̂`
(`isReal_upd`), and at `Out 0` means a real value (`im_eq_zero`). This is what makes the exact
centres of the leaves real when the root targets and every `ℓ̂` of the tree are FFTs of real
polynomials. -/

@[expose] public section

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.Fixed
    FalconPrecision.Errors.FFSamp ComplexConjugate

namespace FalconPrecision.Errors.FFTReal

/-- The conjugate position. -/
def cj : (L : ℕ) → Out L → Out L
  | 0 => id
  | L + 1 => fun x : Out L × Bool => (cj L x.1, if L = 0 then !x.2 else x.2)

theorem pt_pow : ∀ (L : ℕ) (o : Out L), pt L o ^ 2 ^ L = -1
  | 0, _ => by simp [pt]
  | L + 1, x => by
    obtain ⟨o, b⟩ := x
    rw [pow_succ', pow_mul, pt_succ]
    split_ifs
    · rw [← pt_pow L o, ← zeta_sq]; ring
    · rw [← pt_pow L o, ← zeta_sq]

theorem pt_ne_neg_one {L : ℕ} (hL : L ≠ 0) (o : Out L) : pt L o ≠ -1 := fun h => by
  have := pt_pow L o
  rw [h, (Nat.even_pow.2 ⟨even_two, hL⟩).neg_one_pow] at this
  norm_num at this

theorem arg_pt_ne_pi {L : ℕ} (hL : L ≠ 0) (o : Out L) : (pt L o).arg ≠ Real.pi := fun h => by
  obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.1 h
  have hn : (pt L o).re * (pt L o).re + (pt L o).im * (pt L o).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, norm_pt]
    norm_num
  rw [him, mul_zero, add_zero] at hn
  refine pt_ne_neg_one hL o (Complex.ext ?_ (by simpa using him))
  simp only [Complex.neg_re, Complex.one_re]
  nlinarith [hre, hn]

theorem zeta_zero_conj (o : Out 0) : conj (zeta 0 o) = -zeta 0 o := by
  have h : (zeta 0 o - Complex.I) * (zeta 0 o + Complex.I) = 0 := by
    have := zeta_sq 0 o
    simp only [pt] at this
    linear_combination this - Complex.I_sq
  rcases mul_eq_zero.1 h with h | h
  · rw [sub_eq_zero.1 h, Complex.conj_I]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, Complex.conj_I, neg_neg]

theorem zeta_cj {L : ℕ} (hL : L ≠ 0) (o : Out L) (h : pt L (cj L o) = conj (pt L o)) :
    zeta L (cj L o) = conj (zeta L o) := by
  unfold zeta
  rw [h, Complex.conj_cpow _ _ (arg_pt_ne_pi hL o)]
  congr 2
  rw [map_inv₀, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem pt_cj : ∀ (L : ℕ) (o : Out L), pt L (cj L o) = conj (pt L o)
  | 0, _ => by simp [pt]
  | L + 1, x => by
    obtain ⟨o, b⟩ := x
    change pt (L + 1) (cj L o, if L = 0 then !b else b) = conj (pt (L + 1) (o, b))
    rw [pt_succ, pt_succ]
    rcases eq_or_ne L 0 with rfl | hL
    · have hc0 : cj 0 o = o := rfl
      cases b <;> simp [hc0, zeta_zero_conj]
    · simp only [hL, ↓reduceIte, zeta_cj hL o (pt_cj L o)]
      cases b <;> simp

/-- `v` is the FFT of a real polynomial. -/
def IsReal {L : ℕ} (v : Out L → ℂ) : Prop := ∀ o, v (cj L o) = conj (v o)

theorem evalAt_conj {n : ℕ} (a : Fin n → ℂ) (ha : ∀ i, conj (a i) = a i) (z : ℂ) :
    evalAt a (conj z) = conj (evalAt a z) := by
  simp only [evalAt, map_sum, map_mul, map_pow, ha]

theorem isReal_evalAt {L : ℕ} (a : Fin (2 ^ L) → ℂ) (ha : ∀ i, conj (a i) = a i) :
    IsReal fun o => evalAt a (pt L o) := fun o => by
  simp only [pt_cj, evalAt_conj a ha]

theorem im_eq_zero {v : Out 0 → ℂ} (h : IsReal v) (o : Out 0) : (v o).im = 0 :=
  Complex.conj_eq_iff_im.1 (h o).symm

theorem isReal_upd {L : ℕ} {t0 t1 z ℓ : Out L → ℂ} (h0 : IsReal t0) (h1 : IsReal t1) (hz : IsReal z)
    (hℓ : IsReal ℓ) : IsReal (upd t0 t1 z ℓ) := fun o => by
  simp only [upd, h0 o, h1 o, hz o, hℓ o, map_add, map_mul, map_sub]

theorem isReal_splitE {L : ℕ} {t : Out (L + 1) → ℂ} (h : IsReal t) :
    IsReal (splitE t).1 ∧ IsReal (splitE t).2 := by
  rcases eq_or_ne L 0 with rfl | hL
  · refine ⟨fun o => ?_, fun o => ?_⟩ <;> have hf : t (o, true) = conj (t (o, false)) :=
      h (o, false)
    · change (t (o, false) + t (o, true)) / 2 = conj ((t (o, false) + t (o, true)) / 2)
      rw [hf]
      simp only [map_div₀, map_add, Complex.conj_conj, map_ofNat]
      ring
    · change conj (zeta 0 o) / 2 * (t (o, false) - t (o, true)) =
        conj (conj (zeta 0 o) / 2 * (t (o, false) - t (o, true)))
      rw [hf]
      simp only [map_mul, map_div₀, map_sub, map_neg, Complex.conj_conj, map_ofNat, zeta_zero_conj]
      ring
  · have hc : ∀ o b, t (cj L o, b) = conj (t (o, b)) := fun o b => by
      have := h (o, b)
      simp only [cj, hL, ↓reduceIte] at this
      exact this
    refine ⟨fun o => ?_, fun o => ?_⟩ <;>
      simp only [splitE, hc, zeta_cj hL o (pt_cj L o), map_mul, map_div₀, map_add, map_sub,
        map_ofNat, Complex.conj_conj]

theorem mergeE_eq {L : ℕ} {s : Samp L} (hs : IsFFT s) :
    mergeE s = fun x => evalAt (fun i => (ilv s.z0 s.z1 i : ℂ)) (pt (L + 1) x) := by
  rw [← mergeL_ilv]
  unfold mergeE
  congr 1 <;> funext o
  · exact (hs o).1
  · rw [(hs o).2]

theorem isReal_mergeE {L : ℕ} {s : Samp L} (hs : IsFFT s) : IsReal (mergeE s) := by
  rw [mergeE_eq hs]
  exact isReal_evalAt _ fun i => map_intCast (starRingEnd ℂ) _

end FalconPrecision.Errors.FFTReal
