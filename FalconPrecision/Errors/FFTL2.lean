/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFTCert
public import Mathlib.Analysis.Normed.Lp.PiLp

/-! # ℓ2 error of Falcon's recursive FFT (TASK-009 S7c)

With `E₂(L)` the ℓ2 norm (over the `2^L` outputs) of the error of an `L`-level computed FFT, the
butterfly gives `‖(eu + w, eu - w)‖² = 2(‖eu‖² + ‖w‖²)` (parallelogram law) and Minkowski bounds
`w`, so `E₂(L+1) ≤ 2(1 + δ)E₂(L) + √2·√(2^L)·(δB + r)` (certified mode: intermediate values `≤ B`).
Per output, the RMS error is `E₂(L)/√(2^L)`, which grows like `2^{L/2}`, not `2^L`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFTRec

open FalconPrecision.Errors.FFTDef

/-- `Out L` is finite. -/
instance instFintypeOut : (L : ℕ) → Fintype (Out L)
  | 0 => inferInstanceAs (Fintype Unit)
  | L + 1 => @instFintypeProd _ _ (instFintypeOut L) _

theorem card_out : ∀ L, Fintype.card (Out L) = 2 ^ L
  | 0 => rfl
  | L + 1 => by
    change @Fintype.card (Out L × Bool) (@instFintypeProd _ _ (instFintypeOut L) _) = _
    rw [@Fintype.card_prod _ _ (instFintypeOut L), card_out L, Fintype.card_bool, pow_succ]

/-- ℓ2 norm of a finite complex family. -/
noncomputable def l2 {ι : Type} [Fintype ι] (f : ι → ℂ) : ℝ := √(∑ i, ‖f i‖ ^ 2)

theorem l2_eq {ι : Type} [Fintype ι]
    (f : ι → ℂ) : l2 f = ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : ι => ℂ))‖ := by
  rw [PiLp.norm_eq_of_L2]; rfl

theorem l2_add_le {ι : Type} [Fintype ι] (f g : ι → ℂ) : l2 (f + g) ≤ l2 f + l2 g := by
  simp only [l2_eq, WithLp.toLp_add]; exact norm_add_le _ _

theorem l2_mul_le {ι : Type} [Fintype ι] (c f : ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ i, ‖c i‖ ≤ C) :
    l2 (fun i => c i * f i) ≤ C * l2 f := by
  unfold l2
  rw [← Real.sqrt_sq hC0, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC i) 2) (sq_nonneg _)

theorem l2_le_const {ι : Type} [Fintype ι] (f : ι → ℂ) (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ i, ‖f i‖ ≤ R) :
    l2 f ≤ √(Fintype.card ι) * R := by
  unfold l2
  rw [← Real.sqrt_sq hR0, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖f i‖ ^ 2 ≤ ∑ _i : ι, R ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hR i) 2
    _ = Fintype.card ι * R ^ 2 := by simp

/-- A point of `Out L`. -/
def o0 : (L : ℕ) → Out L
  | 0 => ()
  | L + 1 => (o0 L, false)

theorem sum_out_succ (L : ℕ) (g : Out (L + 1) → ℝ) :
    ∑ o, g o = ∑ o : Out L, (g (o, false) + g (o, true)) := by
  have h := Fintype.sum_prod_type (α₁ := Out L) (α₂ := Bool) g
  exact h.trans (Finset.sum_congr rfl fun o _ => by rw [Fintype.sum_bool, add_comm])

/-- **ℓ2 recursive FFT error** (certified mode). -/
theorem fft_rec_err_l2 (δ r B : ℝ) (E : ℕ → ℝ)
    (ζ ζh : (L : ℕ) → Out L → ℂ) (pt : (L : ℕ) → Out L → ℂ)
    (hpt : ∀ L o b, pt (L + 1) (o, b) = if b then -ζ L o else ζ L o)
    (hsq : ∀ L o, ζ L o ^ 2 = pt L o) (hζ : ∀ L o, ‖ζ L o‖ = 1)
    (hδ : ∀ L o, ‖ζh L o - ζ L o‖ ≤ δ)
    (fftH : (L : ℕ) → (Fin (2 ^ L) → ℂ) → Out L → ℂ)
    (h0 : ∀ a, l2 (fun o => fftH 0 a o - a ⟨0, by norm_num⟩) ≤ E 0)
    (hrec : ∀ L a, ∃ p : Out L → ℂ, (∀ o, ‖p o - ζh L o * fftH L (odds (castC a)) o‖ ≤ r) ∧
      ∀ o, fftH (L + 1) a (o, false) = fftH L (evens (castC a)) o + p o ∧
        fftH (L + 1) a (o, true) = fftH L (evens (castC a)) o - p o)
    (hE : ∀ L, E (L + 1) = 2 * (1 + δ) * E L + √2 * (√(2 ^ L) * (δ * B + r))) :
    ∀ L (a : Fin (2 ^ L) → ℂ), (∀ o, ‖evalAt a (pt L o)‖ ≤ B) →
      l2 (fun o => fftH L a o - evalAt a (pt L o)) ≤ E L := by
  intro L
  induction L with
  | zero =>
    intro a _
    have : ∀ o, evalAt a (pt 0 o) = a ⟨0, by norm_num⟩ := fun o => by simp [evalAt]
    simp only [this]; exact h0 a
  | succ L ih =>
    intro a hB
    obtain ⟨p, hp, hpq⟩ := hrec L a
    have hsub := fun o' => half_eval_le B L a (ζ L) (pt L) (pt (L + 1)) (hpt L) (hsq L) (hζ L) hB o'
    have hu := ih _ (fun o' => (hsub o').1)
    have hv := ih _ (fun o' => (hsub o').2)
    set eu := fun o => fftH L (evens (castC a)) o - evalAt (evens (castC a)) (pt L o) with heu
    set ev := fun o => fftH L (odds (castC a)) o - evalAt (odds (castC a)) (pt L o) with hev
    set w := fun o => p o - ζ L o * evalAt (odds (castC a)) (pt L o) with hw_def
    -- exact outputs
    have hex : ∀ o, evalAt a (pt (L + 1) (o, false)) = evalAt (evens (castC a))
        (pt L o) + ζ L o * evalAt (odds (castC a)) (pt L o) ∧
        evalAt a (pt (L + 1) (o, true)) = evalAt (evens (castC a))
            (pt L o) - ζ L o * evalAt (odds (castC a)) (pt L o) := by
      intro o
      have hsplit := evalAt_split (castC a) (ζ L o)
      have hsplit' := evalAt_split (castC a) (-ζ L o)
      rw [evalAt_castC] at hsplit hsplit'
      rw [neg_sq] at hsplit'
      rw [hsq] at hsplit hsplit'
      constructor
      · rw [hpt]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hsplit
      · rw [hpt]; simp only [↓reduceIte]; rw [hsplit']; ring
    have herr : ∀ o, fftH (L + 1) a (o, false) - evalAt a (pt (L + 1) (o, false)) = eu o + w o ∧
        fftH (L + 1) a (o, true) - evalAt a (pt (L + 1) (o, true)) = eu o - w o := by
      intro o
      rw [(hpq o).1, (hpq o).2, (hex o).1, (hex o).2]
      simp only [heu, hw_def]; constructor <;> ring
    -- parallelogram
    have hsq2 : (l2 (fun o => fftH (L + 1) a o - evalAt a (pt (L + 1) o))) ^ 2 =
        2 * ((l2 eu) ^ 2 + (l2 w) ^ 2) := by
      simp only [l2]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      rw [sum_out_succ, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [(herr o).1, (herr o).2]
      have := parallelogram_law_with_norm ℝ (eu o) (w o)
      nlinarith [this]
    -- Minkowski on w
    have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 ())
    have hr0 : 0 ≤ r := (norm_nonneg _).trans (hp (o0 L))
    have hB0 : 0 ≤ B := (norm_nonneg _).trans ((hsub (o0 L)).2)
    have hw : l2 w ≤ √(2 ^ L) * r + (1 + δ) * l2 ev + δ * (√(2 ^ L) * B) := by
      have hdec : w = (fun o => p o - ζh L o * fftH L (odds (castC a)) o) +
          (fun o => ζh L o * ev o) +
          (fun o => (ζh L o - ζ L o) * evalAt (odds (castC a)) (pt L o)) := by
        funext o; simp only [hw_def, hev, Pi.add_apply]; ring
      rw [hdec]
      have h1 : l2 (fun o => p o - ζh L o * fftH L (odds (castC a)) o) ≤ √(2 ^ L) * r := by
        have := l2_le_const _ r hr0 hp; rw [card_out] at this; push_cast at this; exact this
      have h2 : l2 (fun o => ζh L o * ev o) ≤ (1 + δ) * l2 ev := by
        refine l2_mul_le _ _ _ (by linarith) fun o => ?_
        calc ‖ζh L o‖ = ‖ζ L o + (ζh L o - ζ L o)‖ := by rw [add_sub_cancel]
          _ ≤ ‖ζ L o‖ + ‖ζh L o - ζ L o‖ := norm_add_le _ _
          _ ≤ 1 + δ := by rw [hζ]; linarith [hδ L o]
      have h3 : l2 (fun o => (ζh L o - ζ L o) * evalAt (odds (castC a)) (pt L o)) ≤ δ *
          (√(2 ^ L) * B) := by
        calc l2 (fun o => (ζh L o - ζ L o) * evalAt (odds (castC a)) (pt L o)) ≤ δ *
            l2 (fun o => evalAt (odds (castC a)) (pt L o)) := l2_mul_le _ _ _ hδ0 (hδ L)
          _ ≤ δ * (√(2 ^ L) * B) := by
              apply mul_le_mul_of_nonneg_left _ hδ0
              have := l2_le_const (fun o => evalAt (odds (castC a)) (pt L o)) B hB0
                  (fun o => (hsub o).2)
              rw [card_out] at this; push_cast at this; exact this
      calc _ ≤ _ := l2_add_le _ _
        _ ≤ _ := add_le_add (l2_add_le _ _) le_rfl
        _ ≤ √(2 ^ L) * r + (1 + δ) * l2 ev + δ * (√(2 ^ L) * B) := add_le_add (add_le_add h1 h2) h3
    have hl0 : 0 ≤ l2 eu := Real.sqrt_nonneg _
    have hw0 : 0 ≤ l2 w := Real.sqrt_nonneg _
    have hev0 : 0 ≤ l2 ev := Real.sqrt_nonneg _
    have hEL : 0 ≤ E L := hl0.trans hu
    -- conclude: √(2(x² + y²)) ≤ √2 (x + y) and y ≤ (1+δ)E + c
    have hc : 0 ≤ √(2 ^ L) * (δ * B + r) := by
      positivity
    have hy : l2 w ≤ (1 + δ) * E L + √(2 ^ L) * (δ * B + r) := by nlinarith
    have hx : l2 eu ≤ E L := hu
    set X := l2 (fun o => fftH (L + 1) a o - evalAt a (pt (L + 1) o))
    have hX0 : 0 ≤ X := Real.sqrt_nonneg _
    rw [hE]
    have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs2 : 0 ≤ √2 := Real.sqrt_nonneg _
    have hY : 0 ≤ √2 * (√2 * ((1 + δ) * E L) + √(2 ^ L) * (δ * B + r)) := by positivity
    have hbound : X ^ 2 ≤ (√2 * (√2 * ((1 + δ) * E L) + √(2 ^ L) * (δ * B + r))) ^ 2 := by
      rw [hsq2]
      have hxy : l2 eu ≤ (1 + δ) * E L := by nlinarith
      have e1 : (√2 * (√2 * ((1 + δ) * E L) + √(2 ^ L) * (δ * B + r))) ^ 2 =
          2 * (2 * ((1 + δ) * E L) ^ 2 + 2 * √2 * ((1 + δ) * E L) * (√(2 ^ L) * (δ * B + r)) +
            (√(2 ^ L) * (δ * B + r)) ^ 2) := by
        linear_combination
            (√2 ^ 2 * ((1 + δ) * E L) ^ 2 + 2 * √2 * ((1 + δ) * E L) * (√(2 ^ L) * (δ * B + r)) +
          (√(2 ^ L) * (δ * B + r)) ^ 2 + 2 * ((1 + δ) * E L) ^ 2) * h2
      rw [e1]
      have hs2' : 1 ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
      have hq : 0 ≤ (1 + δ) * E L := by positivity
      nlinarith [mul_le_mul hxy hxy hl0 hq, mul_le_mul hy hy hw0 (by positivity),
        mul_le_mul_of_nonneg_right hs2' (mul_nonneg hq hc)]
    have := (pow_le_pow_iff_left₀ hX0 hY (by norm_num : (2:ℕ) ≠ 0)).1 hbound
    have e2 : √2 * (√2 * ((1 + δ) * E L) + √(2 ^ L) * (δ * B + r)) =
        2 * (1 + δ) * E L + √2 * (√(2 ^ L) * (δ * B + r)) := by
      linear_combination ((1 + δ) * E L) * h2
    linarith

end FalconPrecision.Errors.FFTRec
