/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Ball

/-! # Executable twiddle tables with certified bounds

`zeta L o` (`FxModel`) is the principal square root of the FFT point `pt L o`: `zeta 0 = i`, and
`pt (L+1) (o, b) = ±zeta L o`. `twHi rc h L o` computes it at `h` fractional bits by the same
recursion: `Cx.usqrt` takes a square root of a value near the unit circle, and `CB.sqrtU`
certifies the result from its residual alone: for `w` with `Re w > 0` and `‖w² - p‖ ≤ s`,
`(w - √p)(w + √p) = w² - p` and `Re √p ≥ 0` give `‖w - √p‖ ≤ s/Re w =: e₁`, then
`‖w + √p‖ ≥ 2‖w‖ - e₁` gives `‖w - √p‖ ≤ s/(2‖w‖ - e₁)`. How `w` was computed does not enter
the bound. `twB rc f L o` (`ζ`) and `twsB rc f L o` (`ζ̄/2`) round the `f + 64`-bit values once
per part to `f` fractional bits by `rc`. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.Fixed ComplexConjugate

namespace Cx

variable {h : ℕ}

/-- A square root of `c` for `‖c‖ ≈ 1`: `x = √((1 + Re c)/2)`, `y = Im c/(2x)`. -/
def usqrt (rm : RMode) (c : Cx h) : Cx h :=
  let x := (((Fx.ofInt 1 : Fx h).add c.re).half rm).sqrt rm
  ⟨x, c.im.div rm (x.add x)⟩

theorem norm_sq_sub_le (w c : Cx h) : ‖w.toC ^ 2 - c.toC‖ ≤ (sqrtUB (CB.K h)
    ((w.re.toRat ^ 2 - w.im.toRat ^ 2 - c.re.toRat) ^ 2 +
      (2 * w.re.toRat * w.im.toRat - c.im.toRat) ^ 2) : ℝ) := by
  refine le_trans (le_of_eq ?_) (sqrt_le_sqrtUB _ _)
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp only [Cx.toC, Fx.toReal_eq_toRat, sq, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im]
  push_cast; ring

end Cx

namespace Fx

variable {f : ℕ}

/-- A value with `f + k` fractional bits rounded once to `f`. -/
def lower (rm : RMode) (k : ℕ) (x : Fx (f + k)) : Fx f := ⟨rm.rdiv x.m (2 ^ k)⟩

/-- Half of a value with `f + k` fractional bits rounded once to `f`. -/
def lowerHalf (rm : RMode) (k : ℕ) (x : Fx (f + k)) : Fx f := ⟨rm.rdiv x.m (2 ^ (k + 1))⟩

theorem lower_err (rm : RMode) (k : ℕ) (x : Fx (f + k)) :
    |(x.lower rm k).toReal - x.toReal| ≤ rm.e / 2 ^ f := by
  have e : x.toReal * 2 ^ f = (x.m : ℝ) / ((2 ^ k : ℤ) : ℝ) := by
    rw [Fx.toReal, pow_add]; push_cast; field_simp
  have h := Fx.rnd_scale_err (f := f) rm x.toReal
  rw [e, ← RMode.rdiv_eq_rnd rm x.m (2 ^ k) (by positivity)] at h
  exact h

theorem lowerHalf_err (rm : RMode) (k : ℕ) (x : Fx (f + k)) :
    |(x.lowerHalf rm k).toReal - x.toReal / 2| ≤ rm.e / 2 ^ f := by
  have e : x.toReal / 2 * 2 ^ f = (x.m : ℝ) / ((2 ^ (k + 1) : ℤ) : ℝ) := by
    rw [Fx.toReal, pow_add]; push_cast; field_simp; ring
  have h := Fx.rnd_scale_err (f := f) rm (x.toReal / 2)
  rw [e, ← RMode.rdiv_eq_rnd rm x.m (2 ^ (k + 1)) (by positivity)] at h
  exact h

end Fx

/-- A root `w` of `z` up to the residual `s`: `‖√z - w‖ ≤ s/(2n - s/Re w)` for `n ≤ ‖w‖`. -/
theorem norm_cpow_inv_two_sub_le {w z : ℂ} {s n : ℝ} (hwr : 0 < w.re) (hs : ‖w ^ 2 - z‖ ≤ s)
    (hn : n ≤ ‖w‖) (hden : 0 < 2 * n - s / w.re) :
    ‖z ^ (2⁻¹ : ℂ) - w‖ ≤ s / (2 * n - s / w.re) := by
  have hv : (z ^ (2⁻¹ : ℂ)) ^ 2 = z := Complex.cpow_ofNat_inv_pow _ _
  have hvr : 0 ≤ (z ^ (2⁻¹ : ℂ)).re := by rw [Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hm : ‖w - z ^ (2⁻¹ : ℂ)‖ * ‖w + z ^ (2⁻¹ : ℂ)‖ = ‖w ^ 2 - z‖ := by
    rw [← norm_mul]; congr 1; linear_combination -hv
  have hre : w.re ≤ ‖w + z ^ (2⁻¹ : ℂ)‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    rw [Complex.add_re]; linarith
  have he : ‖w - z ^ (2⁻¹ : ℂ)‖ ≤ s / w.re := by
    rw [le_div_iff₀ hwr]
    exact (mul_le_mul_of_nonneg_left hre (norm_nonneg _)).trans (hm.trans_le hs)
  have hlow : 2 * n - s / w.re ≤ ‖w + z ^ (2⁻¹ : ℂ)‖ := by
    have := norm_sub_norm_le (2 * w) (w - z ^ (2⁻¹ : ℂ))
    rw [norm_mul, Complex.norm_two, show 2 * w - (w - z ^ (2⁻¹ : ℂ)) = w + z ^ (2⁻¹ : ℂ) by
      ring] at this
    linarith
  rw [norm_sub_rev, le_div_iff₀ hden]
  exact (mul_le_mul_of_nonneg_left hlow (norm_nonneg _)).trans (hm.trans_le hs)

namespace CB

variable {h : ℕ}

/-- The principal square root of a value near the unit circle, certified from its residual. -/
def sqrtU (rm : RMode) (p : CB h) : CB h :=
  let w := p.c.usqrt rm
  ⟨w, do
    let rp ← p.r
    let wr := w.re.toRat
    let wi := w.im.toRat
    let dr := wr ^ 2 - wi ^ 2 - p.c.re.toRat
    let di := 2 * wr * wi - p.c.im.toRat
    let s := sqrtUB (K h) (dr ^ 2 + di ^ 2) + rp
    if 0 < wr then
      let den := 2 * w.nLB - s / wr
      if 0 < den then pure (up (K h) (s / den)) else none
    else none⟩

theorem Holds.sqrtU (rm : RMode) {p : CB h} {z : ℂ} (hp : p.Holds z) :
    (p.sqrtU rm).Holds (z ^ (2⁻¹ : ℂ)) := by
  intro r hr
  cases hx : p.r with
  | none => simp only [CB.sqrtU, hx] at hr; cases hr
  | some x =>
  simp only [CB.sqrtU, hx, Option.mem_def, Option.bind_eq_bind, Option.bind_some] at hr
  split_ifs at hr with h1 h2
  all_goals try cases hr
  have hw : (p.c.usqrt rm).toC.re = ((p.c.usqrt rm).re.toRat : ℝ) := Fx.toReal_eq_toRat _
  have hwr : 0 < (p.c.usqrt rm).toC.re := by rw [hw]; exact_mod_cast h1
  have hs := (norm_sub_le_norm_sub_add_norm_sub _ p.c.toC z).trans
    (add_le_add (Cx.norm_sq_sub_le (p.c.usqrt rm) p.c) ((norm_sub_rev _ _).trans_le (hp x hx)))
  have hden := Rat.cast_lt (K := ℝ) |>.2 h2
  rw [← Rat.cast_add] at hs
  push_cast at hden
  rw [← hw] at hden
  refine (norm_cpow_inv_two_sub_le hwr hs (Cx.nLB_le_norm _) ?_).trans ?_
  · push_cast; exact hden
  · rw [hw]; exact_mod_cast le_up _ _

/-- Both parts rounded once from `f + k` to `f` fractional bits. -/
def lower {f : ℕ} (rc : RMode) (k : ℕ) (b : CB (f + k)) : CB f :=
  ⟨⟨b.c.re.lower rc k, b.c.im.lower rc k⟩,
    (fun x => up (K f) (x + sqrt2Q * rc.eQ * ulp f)) <$> b.r⟩

/-- `z̄/2`, both parts rounded once from `f + k` to `f` fractional bits. -/
def lowerConjHalf {f : ℕ} (rc : RMode) (k : ℕ) (b : CB (f + k)) : CB f :=
  ⟨⟨b.c.re.lowerHalf rc k, b.c.im.neg.lowerHalf rc k⟩,
    (fun x => up (K f) (x / 2 + sqrt2Q * rc.eQ * ulp f)) <$> b.r⟩

theorem Holds.lower {f : ℕ} (rc : RMode) (k : ℕ) {b : CB (f + k)} {z : ℂ} (hb : b.Holds z) :
    (b.lower rc k).Holds z := by
  intro r hr
  cases hx : b.r with
  | none => simp only [CB.lower, hx] at hr; cases hr
  | some x =>
  simp only [CB.lower, hx] at hr; cases hr
  refine le_up_of (hb x hx) (norm_sub_le_sqrt_two (ε := rc.e / 2 ^ f) ?_ ?_) ?_
  · rw [abs_sub_comm]; exact Fx.lower_err rc k b.c.re
  · rw [abs_sub_comm]; exact Fx.lower_err rc k b.c.im
  · push_cast; linarith [sqrt_two_e_le (f := f) rc]

theorem Holds.lowerConjHalf {f : ℕ} (rc : RMode) (k : ℕ) {b : CB (f + k)} {z : ℂ}
    (hb : b.Holds z) : (b.lowerConjHalf rc k).Holds (starRingEnd ℂ z / 2) := by
  intro r hr
  cases hx : b.r with
  | none => simp only [CB.lowerConjHalf, hx] at hr; cases hr
  | some x =>
  simp only [CB.lowerConjHalf, hx] at hr; cases hr
  refine le_up_of (X := starRingEnd ℂ b.c.toC / 2) (A := x / 2) ?_
    (norm_sub_le_sqrt_two (ε := rc.e / 2 ^ f) ?_ ?_) ?_
  · rw [← sub_div, ← map_sub, norm_div, Complex.norm_conj, Complex.norm_two]
    exact div_le_div_of_nonneg_right (hb x hx) two_pos.le
  · rw [abs_sub_comm]
    simpa [Cx.toC, CB.lowerConjHalf] using Fx.lowerHalf_err rc k b.c.re
  · rw [abs_sub_comm]
    simpa [Cx.toC, CB.lowerConjHalf, Fx.toReal_neg, neg_div] using
      Fx.lowerHalf_err rc k b.c.im.neg
  · push_cast; linarith [sqrt_two_e_le (f := f) rc]

end CB

/-- `ζ` at `h` fractional bits: `i` at level `0`, then the certified root of `±ζ`. -/
def twHi (rc : RMode) (h : ℕ) : (L : ℕ) → Out L → CB h
  | 0 => fun _ => CB.exact ⟨⟨0⟩, Fx.ofInt 1⟩
  | L + 1 =>
    let t := twHi rc h L
    memo (L + 1) fun x =>
      CB.sqrtU rc (if (x : Out L × Bool).2 then (t (x : Out L × Bool).1).neg
        else t (x : Out L × Bool).1)

/-- Merge table `ζ` at `f` fractional bits. -/
def twB (rc : RMode) (f L : ℕ) : Out L → CB f :=
  let t := twHi rc (f + 64) L
  fun o => (t o).lower rc 64

/-- Split table `ζ̄/2` at `f` fractional bits. -/
def twsB (rc : RMode) (f L : ℕ) : Out L → CB f :=
  let t := twHi rc (f + 64) L
  fun o => (t o).lowerConjHalf rc 64

theorem zeta_zero (o : Out 0) : zeta 0 o = Complex.I := by
  have h : zeta 0 o = (-1 : ℂ) ^ (2⁻¹ : ℂ) := rfl
  apply Complex.ext
  · rw [h, Complex.cpow_inv_two_re]; norm_num
  · rw [h, Complex.cpow_inv_two_im_eq_sqrt (by norm_num)]; norm_num

theorem twHi_holds (rc : RMode) (h : ℕ) : ∀ (L : ℕ) (o : Out L), (twHi rc h L o).Holds (zeta L o)
  | 0, o => by
    refine (CB.exact_holds _).congr ?_
    rw [zeta_zero]
    apply Complex.ext <;> simp [Cx.toC, Fx.toReal, Fx.ofInt]
  | L + 1, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    simp only [twHi, memo_eq]
    have e : zeta (L + 1) (o, b) = (if b then -zeta L o else zeta L o) ^ (2⁻¹ : ℂ) := rfl
    rw [e]
    refine CB.Holds.sqrtU rc ?_
    cases b
    · exact twHi_holds rc h L o
    · exact (twHi_holds rc h L o).neg

theorem twB_holds (rc : RMode) (f L : ℕ) (o : Out L) : (twB rc f L o).Holds (zeta L o) :=
  (twHi_holds rc (f + 64) L o).lower rc 64

theorem twsB_holds (rc : RMode) (f L : ℕ) (o : Out L) :
    (twsB rc f L o).Holds (starRingEnd ℂ (zeta L o) / 2) :=
  (twHi_holds rc (f + 64) L o).lowerConjHalf rc 64

end FalconPrecision.Exec
