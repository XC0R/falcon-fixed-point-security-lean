/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FxModel

/-! # Type 1 fixed-point arithmetic with 64 fractional bits

ePrint 2026/2431 §2.2: a Type 1 format `i.64` holds every value on the grid `2⁻⁶⁴·ℤ` (one ulp for
every value); additions and negations are exact and a real product is rounded once to 64 fractional
bits. With the same rounding and no overflow, 32.64 and 64.64 give identical bits (§5). `Arith64 εq`
is an `Arith` used at `u = 2⁻⁶⁴` with:
- twiddle tables `tw` (merge, `ζ`) and `tws` (split, `ζ̄/2`) within `0.7072·2⁻⁶⁴` of the exact
  values (componentwise round to nearest at 64 fractional bits, `√2·2⁻⁶⁵`); the size-2 merge twiddle
  `i` is on the grid;
- `divq`, the product by a stored constant `1/q` (`q = 12289`) rounded once per component, within
  `εq·‖z‖ + √2·2⁻⁶⁵`, `εq` the error of the stored constant: `2⁻⁶⁵` when `1/q` is stored at 64
  fractional bits (baseline), `2⁻⁷⁸` when stored normalized as `⌊2⁷⁷/q⌉·2⁻⁷⁷` (§3.4, "Wide 1/q").

`Rnd.arith64` is the rounding `ρ` at every operation, so `Arith64 εq` is inhabited for every `εq ≥
v/2`, `v` the storage ulp of `1/q`. The single-rounding complex product of §3.5 (`≤ √2·2⁻⁶⁵`) is an
instance of `mul_err` (`≤ √2·2⁻⁶⁴`); its tighter bound is not used. The fields `retag`, `quot` of
`Arith` are not used by the Type 1 chain. -/

@[expose] public section

namespace FalconPrecision.Errors.Fixed

open FalconPrecision.Errors.FFTRec

/-- Type 1 arithmetic (64 fractional bits): `Arith` with twiddle tables within `0.7072·2⁻⁶⁴` and the
product by `1/q` within `εq·‖z‖ + √2·2⁻⁶⁵`. -/
structure Arith64 (εq : ℝ) extends Arith where
  tw_err64 : ∀ L o, ‖tw L o - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 64
  tws_err64 : ∀ L o, ‖tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 64
  divq : ℂ → ℂ
  divq_err : ∀ z, ‖divq z - z / 12289‖ ≤ εq * ‖z‖ + √2 * (1 / 2 ^ 65)

variable (ρ : Rnd)

theorem sqrt_two_half_ulp64 : √2 * (1 / 2 ^ 64 / 2) ≤ (7072 / 10000 / 2 ^ 64 : ℝ) :=
  (mul_le_mul_of_nonneg_right FalconPrecision.Errors.FFSamp.sqrt_two_le (by positivity)).trans
      (by norm_num)

/-- The product by `1/q` stored at ulp `v`, rounded once per component at 64 fractional bits. -/
noncomputable def Rnd.divq (v : ℝ) (z : ℂ) : ℂ :=
    ρ.cq (1 / 2 ^ 64) (z * ((ρ.q v (1 / 12289) : ℝ) : ℂ))

theorem Rnd.divq_err {v εq : ℝ} (hv : 0 < v) (h : v / 2 ≤ εq) (z : ℂ) :
    ‖ρ.divq v z - z / 12289‖ ≤ εq * ‖z‖ + √2 * (1 / 2 ^ 65) := by
  set w := z * ((ρ.q v (1 / 12289) : ℝ) : ℂ)
  have h1 := ρ.cq_err (u := 1 / 2 ^ 64) (by positivity) w
  have h2 := (ρ.q_err hv (1 / 12289)).trans h
  have e : ρ.divq v z - z / 12289 = (ρ.cq (1 / 2 ^ 64) w - w) + z *
      ((ρ.q v (1 / 12289) - 1 / 12289 : ℝ) : ℂ) := by
    simp only [Rnd.divq, w]; push_cast; ring
  rw [e]
  have h3 : ‖z * ((ρ.q v (1 / 12289) - 1 / 12289 : ℝ) : ℂ)‖ ≤ εq * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have h4 : √2 * (1 / 2 ^ 64 / 2) = √2 * (1 / 2 ^ 65 : ℝ) := by norm_num
  linarith [norm_add_le (ρ.cq (1 / 2 ^ 64) w - w) (z * ((ρ.q v (1 / 12289) - 1 / 12289 : ℝ) : ℂ))]

/--
The rounding `ρ` at every operation, twiddle tables at 64 fractional bits, `1/q` stored at ulp `v`.
-/
noncomputable def Rnd.arith64 (v εq : ℝ) (hv : 0 < v) (h : v / 2 ≤ εq) : Arith64 εq where
  mul := ρ.cmul
  mul_err := ρ.cmul_err
  halve u z := ρ.cq u (z / 2)
  halve_err hu _ := ρ.cq_err hu _
  retag := ρ.q
  retag_err := ρ.q_err
  quot := ρ.q (1 / 2 ^ 64)
  quot_err x := (ρ.q_err (by positivity) x).trans (by norm_num)
  tw L o := ρ.cq (1 / 2 ^ 64) (zeta L o)
  tw_err L o := ((ρ.cq_err (by positivity) _).trans sqrt_two_half_ulp64).trans (by norm_num)
  tws L o := ρ.cq (1 / 2 ^ 64) (starRingEnd ℂ (zeta L o) / 2)
  tws_err L o := ((ρ.cq_err (by positivity) _).trans sqrt_two_half_ulp64).trans (by norm_num)
  tw_err64 L o := (ρ.cq_err (by positivity) _).trans sqrt_two_half_ulp64
  tws_err64 L o := (ρ.cq_err (by positivity) _).trans sqrt_two_half_ulp64
  divq := ρ.divq v
  divq_err := ρ.divq_err hv h

end FalconPrecision.Errors.Fixed
