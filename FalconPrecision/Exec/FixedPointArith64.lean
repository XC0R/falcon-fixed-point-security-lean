/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FxModel64
public import FalconPrecision.Exec.FixedPoint

/-! # The executable 64.64 arithmetic as an `Arith64 (1/2⁷⁸)`

A nearest rule `r` (ties to even, up or away) is a `Rnd` (`RMode.toRnd`), and `RMode.arith64` is
`Rnd.arith64` at `v = 2⁻⁷⁷`, `εq = 2⁻⁷⁸` (the arithmetic of the S8 and hop B headlines). On values
of `Cx 64` its fields `mul`, `halve` (at `u = 2⁻⁶⁴`) and `divq` are the executable `Cx.mul`,
`Cx.half` and `Cx.divq` (`arith64_mul`, `arith64_halve`, `arith64_divq`). Not executable here: the
twiddle tables `tw`, `tws` are `ζ` and `ζ̄/2` rounded by `r` at 64 fractional bits, as values in
`ℂ`; an executable table equal to them is not provided. `floor` is not a `Rnd`
(`RMode.not_isRound_floor`), so `RMode.arith64` requires `r ≠ floor`. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.Fixed

/-- A nearest rounding rule as a `Rnd`. -/
noncomputable def RMode.toRnd (r : RMode) (hr : r ≠ .floor) : Rnd := ⟨r.rnd, r.rnd_near hr⟩

/-- The arithmetic with rule `r` at every operation and `1/q` stored at 77 fractional bits. -/
noncomputable def RMode.arith64 (r : RMode) (hr : r ≠ .floor) : Arith64 (1 / 2 ^ 78) :=
  (r.toRnd hr).arith64 (1 / 2 ^ 77) (1 / 2 ^ 78) (by positivity) (by norm_num)

variable (r : RMode) (hr : r ≠ .floor)

theorem RMode.toRnd_q (f : ℕ) (y : ℝ) :
    (r.toRnd hr).q (1 / 2 ^ f) y = r.rnd (y * 2 ^ f) / 2 ^ f := by
  rw [Rnd.q, div_div_eq_mul_div, div_one, mul_one_div]; rfl

theorem RMode.mul_toC {f : ℕ} (z w : Cx f) :
    (z.mul r w).toC = (r.toRnd hr).cmul (1 / 2 ^ f) z.toC w.toC := by
  apply Complex.ext <;>
    simp only [Cx.mul, Cx.toC, Rnd.cmul, Fx.toReal_sub, Fx.toReal_add, Fx.toReal_mul,
      RMode.toRnd_q]

theorem RMode.half_toC {f : ℕ} (z : Cx f) :
    (z.half r).toC = (r.toRnd hr).cq (1 / 2 ^ f) (z.toC / 2) := by
  apply Complex.ext <;>
    simp only [Cx.half, Cx.toC, Rnd.cq, Fx.toReal_half, RMode.toRnd_q, Complex.div_ofNat_re,
      Complex.div_ofNat_im]

theorem RMode.divq_toC (z : Cx 64) :
    (z.divq r).toC = (r.toRnd hr).divq (1 / 2 ^ 77) z.toC := by
  apply Complex.ext <;>
    simp only [Cx.divq, Cx.toC, Rnd.divq, Rnd.cq, Fx.toReal_mulTo, Cx.toReal_qinv,
      RMode.toRnd_q, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_add]

/-- **`mul` is executable.** -/
theorem RMode.arith64_mul (z w : Cx 64) :
    (r.arith64 hr).mul (1 / 2 ^ 64) z.toC w.toC = (z.mul r w).toC :=
  (r.mul_toC hr z w).symm

/-- **`halve` is executable.** -/
theorem RMode.arith64_halve (z : Cx 64) :
    (r.arith64 hr).halve (1 / 2 ^ 64) z.toC = (z.half r).toC :=
  (r.half_toC hr z).symm

/-- **`divq` is executable.** -/
theorem RMode.arith64_divq (z : Cx 64) : (r.arith64 hr).divq z.toC = (z.divq r).toC :=
  (r.divq_toC hr z).symm

include hr in
/-- **Complex product error** (`Arith.mul_err` at `u = 2⁻⁶⁴`). -/
theorem RMode.cmul_err (z w : Cx 64) : ‖(z.mul r w).toC - z.toC * w.toC‖ ≤ √2 * (1 / 2 ^ 64) := by
  rw [← r.arith64_mul hr]; exact (r.arith64 hr).mul_err (by positivity) _ _

include hr in
/-- **Product by `1/q` error** (`Arith64.divq_err` at `εq = 2⁻⁷⁸`). -/
theorem RMode.cdivq_err (z : Cx 64) :
    ‖(z.divq r).toC - z.toC / 12289‖ ≤ 1 / 2 ^ 78 * ‖z.toC‖ + √2 * (1 / 2 ^ 65) := by
  rw [← r.arith64_divq hr]; exact (r.arith64 hr).divq_err _

end FalconPrecision.Exec
