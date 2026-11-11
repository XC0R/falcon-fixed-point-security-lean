/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FalconCenters

/-! # The line-10 budgets `W_L` of the Falcon-512 instance

Line 10 computes `t̂0' ≈ t̂0 + (t̂1 - ẑ1)·ℓ̂`. Its error splits as `δt0 + ℓ̂·δt1 + w` with `w =
(rounding) - ℓ̂·δẑ1 + (t1 - z1)(ℓ̂ - ℓ)` (`update_decomp`), so `‖w‖₂ ≤ Λ·E_z + √(2^(L+1))(M·eℓ + r)`
(`w_l2`), where `E_z` is the ℓ2 merge error of `ẑ1` (`fft_rec_err_l2` from exact integers). At
Falcon-512 (tag 21, `|t1|, |z1| < 2²¹`, `ℓ̂` at tag 5 at the root and 0 below) the constants satisfy
`ez512`. `ez512` and `split512` are inequalities between constants; `FFSampModel.w_bound` composes
`w_l2` with the merge error of the model (`merge_inv`) into `‖w‖₂ ≤ w512 L`. The range `|t1|, |z1| <
2²¹` holds only with high probability (Lemma 12) unless the signer clamps or aborts. Assumed: the
merge twiddle table at tag 0 is the componentwise round-to-nearest of the exact roots (the paper
gives neither its tag nor its generation), hence within `√2/2·2⁻⁶³` (`twiddle_err`), with the size-2
merge multiplying by `±i` exactly (tag 0 cannot represent `i`). -/

@[expose] public section

namespace FalconPrecision.Errors.FFSamp

open FalconPrecision.Errors.FFTRec

theorem update_decomp (t0 t1 z1 ℓ t0h t1h z1h ℓh out : ℂ) :
    out - (t0 + (t1 - z1) * ℓ) = (t0h - t0) + ℓh * (t1h - t1) +
      ((out - (t0h + (t1h - z1h) * ℓh)) - ℓh * (z1h - z1) + (t1 - z1) * (ℓh - ℓ)) := by ring

theorem w_l2 (L : ℕ) (rnd ℓh dz m dℓ : Out (L + 1) → ℂ) (Λ Ez M eℓ r : ℝ) (hΛ0 : 0 ≤ Λ)
    (hM0 : 0 ≤ M)
    (hr0 : 0 ≤ r) (heℓ0 : 0 ≤ eℓ)
    (hrnd : ∀ o, ‖rnd o‖ ≤ r) (hℓ : ∀ o, ‖ℓh o‖ ≤ Λ) (hdz : l2 dz ≤ Ez) (hm : ∀ o, ‖m o‖ ≤ M)
    (hdℓ : ∀ o, ‖dℓ o‖ ≤ eℓ) :
    l2 (fun o => rnd o - ℓh o * dz o + m o * dℓ o) ≤ Λ * Ez + √(2 ^ (L + 1)) * (M * eℓ + r) := by
  have hdec : (fun o => rnd o - ℓh o * dz o + m o * dℓ o) =
      (fun o => (-ℓh o) * dz o) + ((fun o => m o * dℓ o) + rnd) := by
    funext o; simp only [Pi.add_apply]; ring
  rw [hdec]
  have h1 : l2 (fun o => (-ℓh o) * dz o) ≤ Λ * Ez :=
    (l2_mul_le _ _ _ hΛ0 fun o => by rw [norm_neg]; exact hℓ o).trans
        (mul_le_mul_of_nonneg_left hdz hΛ0)
  have h2 : l2 ((fun o => m o * dℓ o) + rnd) ≤ √(2 ^ (L + 1)) * (M * eℓ + r) := by
    have := l2_le_const ((fun o => m o * dℓ o) + rnd) (M * eℓ + r) (by positivity) fun o => by
      simp only [Pi.add_apply]
      calc ‖m o * dℓ o + rnd o‖ ≤ ‖m o‖ * ‖dℓ o‖ + ‖rnd o‖ :=
          by rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ M * eℓ + r := by gcongr; exacts [hm o, hdℓ o, hrnd o]
    rw [card_out] at this; push_cast at this; exact this
  exact (l2_add_le _ _).trans (add_le_add h1 h2)

/-- Upper recursion for the ℓ2 merge error (`fft_rec_err_l2` with `E₀ = 0`). -/
noncomputable def ezU (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | L + 1 => 2 * (1 + 1 / 2 ^ 63) * ezU c L + 141422 / 100000 * sq512 L * c

theorem ez_le (δ c : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2 ^ 63) (hc : 0 ≤ c) (E : ℕ → ℝ) (h0 : E 0 = 0)
    (hE : ∀ L, E (L + 1) = 2 * (1 + δ) * E L + √2 * (√(2 ^ L) * c)) : ∀ L, 0 ≤ E L ∧ E L ≤
        ezU c L := by
  intro L; induction L with
  | zero => simp [h0, ezU]
  | succ L ih =>
    rw [hE]; simp only [ezU]
    constructor
    · have := ih.1; positivity
    · have h1 : 2 * (1 + δ) * E L ≤ 2 * (1 + 1 / 2 ^ 63) * ezU c L := by
        exact mul_le_mul (by gcongr) ih.2 ih.1 (by positivity)
      have h2 : √2 * (√(2 ^ L) * c) ≤ 141422 / 100000 * (sq512 L * c) :=
        mul_le_mul sqrt_two_le (mul_le_mul_of_nonneg_right (sqrt_pow_le L) hc) (by positivity)
            (by norm_num)
      linarith

/-- Line-10 budgets (arithmetic): `c = δB + r ≤ 2.122·2⁻⁴²` at tag 21. -/
theorem ez512 : ∀ L, L ≤ 8 → lam512 L * ezU (2122 / 1000 / 2 ^ 42) (L + 1) +
    sq512 (L + 1) *
        (2 ^ 22 * ((if L = 8 then 2 ^ 5 else 1) * (7072 / 10000) / 2 ^ 63) + 141422 / 100000 /
            2 ^ 42) ≤
      w512 L := by
  intro L hL
  interval_cases L <;> simp only [ezU, sq512, lam512, w512] <;> norm_num

/--
**Split budget.** The computed odd half `c(û - v̂) + rnd` differs from the exact `ζ̄(u - v)/2` by
`c(δu - δv)` plus at most `2δB + r` (`‖u‖, ‖v‖ ≤ B`). -/
theorem split_budget (u v uh vh c ζ rnd : ℂ) (δ B r : ℝ) (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B)
    (hc : ‖c - (starRingEnd ℂ) ζ / 2‖ ≤ δ) (hrnd : ‖rnd‖ ≤ r) :
    ‖(c * (uh - vh) + rnd - (starRingEnd ℂ) ζ / 2 * (u - v)) - c * ((uh - u) - (vh - v))‖ ≤ 2 * δ *
        B + r := by
  have hid : (c * (uh - vh) + rnd - (starRingEnd ℂ) ζ / 2 * (u - v)) - c * ((uh - u) - (vh - v)) =
      (c - (starRingEnd ℂ) ζ / 2) * (u - v) + rnd := by ring
  rw [hid]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hc
  calc _ ≤ ‖(c - (starRingEnd ℂ) ζ / 2) * (u - v)‖ + ‖rnd‖ := norm_add_le _ _
    _ ≤ δ * (B + B) + r := by
        rw [norm_mul]; gcongr; exact (norm_sub_le _ _).trans (add_le_add hu hv)
    _ = 2 * δ * B + r := by ring

/-- At tag 21 (arithmetic): `2δB + r ≤ 2.9·2⁻⁴²` with `δ ≤ √2/2·2⁻⁶³`, `B = 2²¹`, `r = √2·2⁻⁴²`. -/
theorem split512 : 2 * (7072 / 10000 / 2 ^ 63) * 2 ^ 21 + 141422 / 100000 / 2 ^ 42 ≤
    (29 / 10 / 2 ^ 42 : ℝ) := by
  norm_num

end FalconPrecision.Errors.FFSamp
