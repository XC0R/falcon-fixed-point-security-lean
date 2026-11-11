/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FxC
public import FalconPrecision.Errors.FalconW

/-! # Fixed-point model: per-operation arithmetic, twiddle tables, FFT, merge layer

A register at tag `m` holds a real on the grid `u·ℤ`, `u = 2^(m-p)`, `p = 63` (ePrint 2026/1531
§7.1). `Arith` is the arithmetic of an implementation: one deterministic function per operation,
each with its error bound at output ulp `u`. `mul`, the complex product, is within `√2·u` (four real
products rounded and combined exactly, §7.2 items 1-2, or one rounding per component); `halve`,
`z/2`, within `√2·u/2` (round to nearest with any tie rule, or an arithmetic shift of grid values);
`retag` and `quot` (`c/q` at tag 0) round reals within `u/2` and `2⁻⁶⁴` (round to nearest;
truncation is not an instance); the twiddle tables at tag 0, `tw` (merge, `ζ`) and `tws` (split,
`ζ̄/2`), are within `0.7072·2⁻⁶³` of the exact values (the paper gives neither their tags nor their
generation). The fields need to agree with an implementation only on the values it computes.
Additions and negations are exact. Not instances: Karatsuba products, halve-then-multiply splits,
truncating retags. `Rnd` is a rounding to an integer within `1/2` (any tie rule; §7.2 uses
half-to-even); `Rnd.arith` uses it at every operation, so `Arith` is inhabited.

`tw 0 ()` is within `0.7072·2⁻⁶³` of `i`, which tag 0 cannot hold (`Im = 1` is `2⁶³` ulps): an
implementation is an instance when its size-2 merge multiplies by `±i` exactly.

Register overflow (a component `|x| ≥ 2^p` ulps) is not represented. `FFSampModel.ffs` aborts unless
the computed split inputs `t̄1`, `t̄0'` and odd merge inputs `ẑ1` satisfy `‖·‖ ≤ 2²¹ - 1`, so these
fit a tag-21 register componentwise. Not covered: the sums and differences inside split, merge and
line 10 (up to `2²²` at tag 21 when both operands are within `2²¹`), the products, the merged `ẑ0`
of each child and the root's merged output, and the FFTs of `c/q`, `f`, `F` (footnote 9).

`pt`, `zeta`: the roots of `x^(2^L) + 1` in the order of the split/merge recursion (`pt 0 = -1`, `pt
(L+1) (o, b) = ±zeta L o`, `zeta L o ^ 2 = pt L o`). `Arith.fft` is Falcon's FFT by the merge
recursion with `tw` (§7.3 item 1); `merge_l2` is the ℓ2 error of one merge layer. -/

@[expose] public section

namespace FalconPrecision.Errors.Fixed

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef

/-- A rounding to an integer within `1/2` (round to nearest, any tie rule). -/
structure Rnd where
  R : ℝ → ℤ
  near : ∀ y, IsRound (R y) y

/-- Mathlib's `round` is a `Rnd`. -/
noncomputable def Rnd.half : Rnd := ⟨round, fun y => (abs_sub_comm _ y).trans_le (abs_sub_round y)⟩

variable (ρ : Rnd)

/-- `x` rounded to the grid `u·ℤ`. -/
noncomputable def Rnd.q (u x : ℝ) : ℝ := ρ.R (x / u) * u

theorem Rnd.q_err {u : ℝ} (hu : 0 < u) (x : ℝ) : |ρ.q u x - x| ≤ u / 2 := by
  have h : |(ρ.R (x / u) : ℝ) - x / u| ≤ 1 / 2 := ρ.near (x / u)
  have e : ρ.q u x - x = ((ρ.R (x / u) : ℝ) - x / u) * u := by
    rw [Rnd.q, sub_mul, div_mul_cancel₀ x hu.ne']
  rw [e, abs_mul, abs_of_pos hu]
  calc _ ≤ 1 / 2 * u := mul_le_mul_of_nonneg_right h hu.le
    _ = u / 2 := by ring

/-- A complex number rounded to the grid, part by part. -/
noncomputable def Rnd.cq (u : ℝ) (z : ℂ) : ℂ := ⟨ρ.q u z.re, ρ.q u z.im⟩

theorem Rnd.cq_err {u : ℝ} (hu : 0 < u) (z : ℂ) : ‖ρ.cq u z - z‖ ≤ √2 * (u / 2) :=
  norm_le_of_re_im _ _ (ρ.q_err hu z.re) (ρ.q_err hu z.im)

/-- Product of complex registers at the output ulp `u` (§7.2 items 1-2). -/
noncomputable def Rnd.cmul (u : ℝ) (z w : ℂ) : ℂ :=
  ⟨ρ.q u (z.re * w.re) - ρ.q u (z.im * w.im), ρ.q u (z.re * w.im) + ρ.q u (z.im * w.re)⟩

theorem Rnd.cmul_err {u : ℝ} (hu : 0 < u) (z w : ℂ) : ‖ρ.cmul u z w - z * w‖ ≤ √2 * u :=
  FalconPrecision.Errors.Fixed.cmul_err z w _ u _ _ _ _ (ρ.q_err hu _) (ρ.q_err hu _)
      (ρ.q_err hu _) (ρ.q_err hu _) rfl rfl

/-- The roots of `x^(2^L) + 1` in the order of the split/merge recursion. -/
noncomputable def pt : (L : ℕ) → Out L → ℂ
  | 0 => fun _ => -1
  | L + 1 => fun x : Out L × Bool => if x.2 then -pt L x.1 ^ (2⁻¹ : ℂ) else pt L x.1 ^ (2⁻¹ : ℂ)

/-- The twiddle `ζ` at `o`: `ζ² = pt L o`. -/
noncomputable def zeta (L : ℕ) (o : Out L) : ℂ := pt L o ^ (2⁻¹ : ℂ)

theorem pt_succ (L : ℕ) (o : Out L) (b : Bool) : pt (L + 1)
    (o, b) = if b then -zeta L o else zeta L o := rfl

theorem zeta_sq (L : ℕ) (o : Out L) : zeta L o ^ 2 = pt L o := Complex.cpow_ofNat_inv_pow _ _

theorem norm_eq_one_of_sq {z w : ℂ} (h : z ^ 2 = w) (hw : ‖w‖ = 1) : ‖z‖ = 1 := by
  rw [← h, norm_pow] at hw
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hw

theorem norm_pt : ∀ (L : ℕ) (o : Out L), ‖pt L o‖ = 1
  | 0, _ => by simp [pt]
  | L + 1, x => by
    obtain ⟨o, b⟩ := x
    have h := norm_eq_one_of_sq (zeta_sq L o) (norm_pt L o)
    rw [pt_succ]; split_ifs <;> simp [h]

theorem norm_zeta (L : ℕ) (o : Out L) : ‖zeta L o‖ = 1 :=
    norm_eq_one_of_sq (zeta_sq L o) (norm_pt L o)

/-- Merge twiddle table at tag 0. -/
noncomputable def Rnd.tw (L : ℕ) (o : Out L) : ℂ := ρ.cq (1 / 2 ^ 63) (zeta L o)

/-- Split twiddle table at tag 0 (`ζ̄/2`). -/
noncomputable def Rnd.tws (L : ℕ) (o : Out L) : ℂ :=
    ρ.cq (1 / 2 ^ 63) (starRingEnd ℂ (zeta L o) / 2)

theorem sqrt_two_half_ulp : √2 * (1 / 2 ^ 63 / 2) ≤ (7072 / 10000 / 2 ^ 63 : ℝ) :=
  (mul_le_mul_of_nonneg_right FalconPrecision.Errors.FFSamp.sqrt_two_le (by positivity)).trans
      (by norm_num)

theorem Rnd.tw_err (L : ℕ) (o : Out L) : ‖ρ.tw L o - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 63 :=
  (ρ.cq_err (by positivity) _).trans sqrt_two_half_ulp

theorem Rnd.tws_err (L : ℕ) (o : Out L) :
    ‖ρ.tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 63 :=
  (ρ.cq_err (by positivity) _).trans sqrt_two_half_ulp

/-- Fixed-point arithmetic: one function per operation, each with its error bound at output ulp `u`.
-/
structure Arith where
  mul : ℝ → ℂ → ℂ → ℂ
  mul_err : ∀ {u : ℝ}, 0 < u → ∀ z w, ‖mul u z w - z * w‖ ≤ √2 * u
  halve : ℝ → ℂ → ℂ
  halve_err : ∀ {u : ℝ}, 0 < u → ∀ z, ‖halve u z - z / 2‖ ≤ √2 * (u / 2)
  retag : ℝ → ℝ → ℝ
  retag_err : ∀ {u : ℝ}, 0 < u → ∀ x, |retag u x - x| ≤ u / 2
  quot : ℝ → ℝ
  quot_err : ∀ x, |quot x - x| ≤ 1 / 2 ^ 64
  tw : (L : ℕ) → Out L → ℂ
  tw_err : ∀ L o, ‖tw L o - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 63
  tws : (L : ℕ) → Out L → ℂ
  tws_err : ∀ L o, ‖tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 63

/-- The rounding `ρ` at every operation. -/
noncomputable def Rnd.arith : Arith where
  mul := ρ.cmul
  mul_err := ρ.cmul_err
  halve u z := ρ.cq u (z / 2)
  halve_err hu _ := ρ.cq_err hu _
  retag := ρ.q
  retag_err := ρ.q_err
  quot := ρ.q (1 / 2 ^ 63)
  quot_err x := (ρ.q_err (by positivity) x).trans_eq (by norm_num)
  tw := ρ.tw
  tw_err := ρ.tw_err
  tws := ρ.tws
  tws_err := ρ.tws_err

theorem Arith.norm_tws (A : Arith) (L : ℕ)
    (o : Out L) : ‖A.tws L o‖ ≤ 1 / 2 + 7072 / 10000 / 2 ^ 63 := by
  have h : ‖starRingEnd ℂ (zeta L o) / 2‖ = 1 / 2 := by
    rw [norm_div, Complex.norm_conj, norm_zeta, Complex.norm_ofNat]
  calc ‖A.tws L o‖ = ‖starRingEnd ℂ (zeta L o) / 2 + (A.tws L o - starRingEnd ℂ (zeta L o) / 2)‖ :=
      by
        rw [add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by rw [h]; linarith [A.tws_err L o]

/--
Falcon's FFT in fixed point at output ulp `u`: the merge recursion with the table `tw` (§7.3 item
1). -/
noncomputable def Arith.fft (A : Arith) (u : ℝ) : (L : ℕ) → (Fin (2 ^ L) → ℂ) → Out L → ℂ
  | 0, a => fun _ => a ⟨0, by norm_num⟩
  | L + 1, a => fun x : Out L × Bool =>
    if x.2 then A.fft u L (evens (castC a)) x.1 - A.mul u (A.tw L x.1)
        (A.fft u L (odds (castC a)) x.1)
    else A.fft u L (evens (castC a)) x.1 + A.mul u (A.tw L x.1) (A.fft u L (odds (castC a)) x.1)

/-- One merge layer `(u, p) ↦ (u + p, u - p)` at `±ζ`. -/
def mergeL {L : ℕ} (u p : Out L → ℂ) : Out (L + 1) → ℂ :=
  fun x : Out L × Bool => if x.2 then u x.1 - p x.1 else u x.1 + p x.1

theorem mergeL_sub {L : ℕ} (u p u' p' : Out L → ℂ) :
    mergeL u p - mergeL u' p' = mergeL (u - u') (p - p') := by
  funext x; obtain ⟨o, b⟩ := x
  change mergeL u p (o, b) - mergeL u' p' (o, b) = mergeL (u - u') (p - p') (o, b)
  cases b <;> simp only [mergeL, Pi.sub_apply, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem l2_mergeL_sq {L : ℕ} (u p : Out L → ℂ) : l2 (mergeL u p) ^ 2 = 2 * (l2 u ^ 2 + l2 p ^ 2) :=
    by
  rw [FalconPrecision.Errors.FFSamp.l2_sq, FalconPrecision.Errors.FFSamp.l2_sq,
      FalconPrecision.Errors.FFSamp.l2_sq, sum_out_succ, mul_add,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  have := parallelogram_law_with_norm ℝ (u o) (p o)
  simp only [mergeL, Bool.false_eq_true, ↓reduceIte]
  linarith

/-- **ℓ2 error of one merge layer.** Halves within `E` in ℓ2, the exact odd half bounded by `B`, a
twiddle within `δ` of `ζ` (`|ζ| = 1`), the product rounded within `r`. -/
theorem merge_l2 (L : ℕ) (u v uh vh ζ ζh q : Out L → ℂ) (δ r B E : ℝ) (hζ : ∀ o, ‖ζ o‖ = 1)
    (hδ : ∀ o, ‖ζh o - ζ o‖ ≤ δ) (hr0 : 0 ≤ r) (hB0 : 0 ≤ B) (hq : ∀ o, ‖q o - ζh o * vh o‖ ≤ r)
    (hv : ∀ o, ‖v o‖ ≤ B) (hu : l2 (uh - u) ≤ E) (hvE : l2 (vh - v) ≤ E) :
    l2 (mergeL uh q - mergeL u fun o => ζ o * v o) ≤ 2 * (1 + δ) * E + √2 *
        (√(2 ^ L) * (δ * B + r)) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ (o0 L))
  have hE0 : 0 ≤ E := (Real.sqrt_nonneg _).trans hu
  set w : Out L → ℂ := q - fun o => ζ o * v o
  have hw : l2 w ≤ √(2 ^ L) * r + (1 + δ) * E + δ * (√(2 ^ L) * B) := by
    have hdec : w = (fun o => q o - ζh o * vh o) + (fun o => ζh o * (vh - v) o) +
        fun o => (ζh o - ζ o) * v o := by
      funext o; simp only [w, Pi.add_apply, Pi.sub_apply]; ring
    have hcard : √(Fintype.card (Out L) : ℝ) = √(2 ^ L) := by rw [card_out]; push_cast; rfl
    have h1 := l2_le_const _ r hr0 hq
    have h2 : l2 (fun o => ζh o * (vh - v) o) ≤ (1 + δ) * E := by
      refine (l2_mul_le _ _ _ (by linarith) fun o => ?_).trans
          (mul_le_mul_of_nonneg_left hvE (by linarith))
      calc ‖ζh o‖ = ‖ζ o + (ζh o - ζ o)‖ := by rw [add_sub_cancel]
        _ ≤ ‖ζ o‖ + ‖ζh o - ζ o‖ := norm_add_le _ _
        _ ≤ 1 + δ := by rw [hζ]; linarith [hδ o]
    have h3 : l2 (fun o => (ζh o - ζ o) * v o) ≤ δ * (√(2 ^ L) * B) := by
      refine (l2_mul_le _ _ _ hδ0 hδ).trans (mul_le_mul_of_nonneg_left ?_ hδ0)
      rw [← hcard]; exact l2_le_const _ B hB0 hv
    rw [hcard] at h1
    rw [hdec]
    exact (l2_add_le _ _).trans (add_le_add ((l2_add_le _ _).trans (add_le_add h1 h2)) h3)
  rw [mergeL_sub]
  set a := (1 + δ) * E
  set c := √(2 ^ L) * (δ * B + r)
  have ha : 0 ≤ a := by positivity
  have hc : 0 ≤ c := by positivity
  have hx : l2 (uh - u) ≤ a := hu.trans (le_mul_of_one_le_left hE0 (by linarith))
  have hy : l2 w ≤ a + c := by simp only [a, c]; nlinarith
  have hs1 : 1 ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hX : l2 (mergeL (uh - u) w) ^ 2 ≤ (2 * a + √2 * c) ^ 2 := by
    rw [l2_mergeL_sq]
    have hx0 := Real.sqrt_nonneg (∑ o, ‖(uh - u) o‖ ^ 2)
    have hw0 := Real.sqrt_nonneg (∑ o, ‖w o‖ ^ 2)
    have e : (2 * a + √2 * c) ^ 2 = 2 * (2 * a ^ 2 + 2 * √2 * a * c + c ^ 2) := by
      linear_combination (c ^ 2) * h2
    rw [e]
    nlinarith
        [mul_le_mul hx hx hx0 ha, mul_le_mul hy hy hw0 (by positivity),
            mul_le_mul_of_nonneg_right hs1
      (mul_nonneg ha hc)]
  have := (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 hX
  calc _ ≤ 2 * a + √2 * c := this
    _ = _ := by simp only [a, c]; ring

end FalconPrecision.Errors.Fixed
