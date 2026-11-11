/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFSampModel
public import FalconPrecision.Errors.FxModel64

/-! # ffSampling budgets in Type 1 arithmetic at Falcon-512

`b64` is the `Budget` of `ffsU` for Type 1 arithmetic with 64 fractional bits (ePrint 2026/2431
§2.2, `Arith64`): every operation at ulp `u = 2⁻⁶⁴`, twiddle tables within `δ = 0.7072·2⁻⁶⁴` (64-bit
tables, as 2026/2431 §3.5 pins them), range checks `‖·‖ ≤ R64 - 1` on the computed split inputs and
odd merge inputs, exact values in `‖·‖ ≤ R64 = 2²⁴`. `R64` is the one constant used by the checks
(`SignModel64.sign164`) and the budgets. The per-node budgets follow from the same lemmas as at tag
21 (`split_budget`, `merge_l2`, `w_l2`):
- split: `2δR + √2u ≤ 1.4145·2⁻⁴⁰` (`r'`; at tag 21: `2.9·2⁻⁴²`), `halve` within `√2u/2`;
- merge: `δR + √2u ≤ 0.70721·2⁻⁴⁰` per level (`c`; at tag 21: `2.122·2⁻⁴²`), merge errors `ezU c`;
- line 10: `W_L ≥ Λ_L·ezU c (L + 1) + sq512 (L + 1)·√2u` (`w64`); the product by `ℓ̂` rounds at
  `2⁻⁶⁴`, and the stored `ℓ̂` is the reference of hop A, so no storage term enters;
- coefficients: `Ā₉ ≤ 49` (unchanged: it depends on the tree, not the arithmetic), `C̄₉ ≤
  43700·2⁻⁴⁰` (at tag 21: `135700·2⁻⁴²`). The twiddle term `δR` dominates `r'` and `c`: the absolute
  table error times the range, so `C̄₉` doubles with each bit of `R`.

`R64 = 2²⁴` is three bits above the `m = 21` budget of `t̂, ẑ` at Falcon-512 (2026/2431 Table 1,
non-split). In 32.64 (`m ≤ 31`) the checked values (the split inputs `t̄1`, `t̄0'` and the odd merge
inputs) and their sums inside a split (`< 2²⁵`) fit the integer bits on paper. The even merge inputs
(each child's merged `ẑ0`, at the leaves `z`) are never checked, so merge sums, the line-10 operand
`t̄1 - ẑ1` and its product by `ℓ̂` are not covered (the `FxModel` list); this is not formalised
(register overflow is not represented). -/

@[expose] public section

namespace FalconPrecision.Errors.FFSamp

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.Fixed
    FalconPrecision.RenyiPath

/--
The range of exact values of the Type 1 model; computed checked values are checked against `R64 -
1`. -/
noncomputable def R64 : ℝ := 2 ^ 24

/-- Type 1 line-10 budgets `W_L` at range `R64`. -/
noncomputable def w64 (L : ℕ) : ℝ :=
  (match L with
    | 0 => 101 | 1 => 340 | 2 => 878 | 3 => 2035 | 4 => 4465 | 5 => 9489 | 6 => 19771 | 7 => 40663
    | _ => 2005302) / 100 / 2 ^ 40

theorem w64_nonneg (L : ℕ) : 0 ≤ w64 L := by unfold w64; split <;> positivity

theorem w64_le (L : ℕ) : w64 L ≤ 1 / 2 ^ 20 := by unfold w64; split <;> norm_num

theorem sqrt_two_ulp64 : √2 * (1 / 2 ^ 64) ≤ (141422 / 100000 / 2 ^ 64 : ℝ) :=
  (mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num)

/-- Line-10 budgets (arithmetic): merge constant `c = 0.70721·2⁻⁴⁰`, rounding `√2·2⁻⁶⁴`. -/
theorem ez64 : ∀ L, L ≤ 8 → lam512 L * ezU (70721 / 100000 / 2 ^ 40) (L + 1) +
    sq512 (L + 1) * (141422 / 100000 / 2 ^ 64) ≤ w64 L := by
  intro L hL
  interval_cases L <;> simp only [ezU, sq512, lam512, w64] <;> norm_num

theorem ezU64_le (L : ℕ) (hL : L ≤ 8) : ezU (70721 / 100000 / 2 ^ 40) L ≤ 1 := by
  interval_cases L <;> simp only [ezU, sq512] <;> norm_num

/-- The Type 1 budget of `ffsU`: ulp `2⁻⁶⁴`, range `R64`, twiddle tables within `0.7072·2⁻⁶⁴`. -/
noncomputable def b64 : Budget where
  u := 1 / 2 ^ 64
  R := R64
  δ := 7072 / 10000 / 2 ^ 64
  r' := 14145 / 10000 / 2 ^ 40
  c := 70721 / 100000 / 2 ^ 40
  W := w64
  hu := by positivity
  hδ0 := by positivity
  hδ := by norm_num
  hR := by unfold R64; positivity
  hhalve := by linarith [sqrt_two_le]
  hsplit := by unfold R64; linarith [sqrt_two_le]
  hc := by unfold R64; linarith [sqrt_two_le]
  hW0 := w64_nonneg
  hW1 := w64_le
  hW L hL := by
    have := mul_le_mul_of_nonneg_left sqrt_two_ulp64
        ((Real.sqrt_nonneg _).trans (sqrt_pow_le (L + 1)))
    linarith [ez64 L hL]
  hez := ezU64_le

theorem coefC64 : coefCU nn512 w64 (70711 / 100000) (14145 / 10000 / 2 ^ 40)
    (141422 / 100000) sq512 9 ≤
    43700 / 2 ^ 40 := by
  simp only [coefCU, coefA, nn512, w64, sq512]; norm_num

/-- Coefficients of the Type 1 instance (arithmetic): `Ā₉ ≤ 49`, `C̄₉ ≤ 43700·2⁻⁴⁰`. -/
theorem coef64 : coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) 9 ≤ 49 ∧
    coefC nn512 w64 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63))
        (14145 / 10000 / 2 ^ 40) 9 ≤ 43700 / 2 ^ 40 := by
  have hN := fun L => (hyp512 L).1
  have hK : √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) ≤ 70711 / 100000 := by
    have h4 : √2 ≤ 1414214 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
        [mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ 1 / 2 + 7072 / 10000 / 2 ^ 63)]
  have hC :=
      coefC_le nn512 w64 hN w64_nonneg _ _ (14145 / 10000 / 2 ^ 40)
          (141422 / 100000) sq512 K512_nonneg
    hK (by positivity) sqrt_two_le sqrt_pow_le 9
  exact ⟨(coefA_mono nn512 hN _ _ K512_nonneg hK 9).2.trans coefA512, hC.2.trans coefC64⟩

theorem budget64 (e : ℝ) (he0 : 0 ≤ e) :
    coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) 9 * e +
      coefC nn512 w64 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) (14145 / 10000 / 2 ^ 40) 9 ≤
      49 * e + 43700 / 2 ^ 40 := by
  linarith [mul_le_mul_of_nonneg_right coef64.1 he0, coef64.2]

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/--
**Path budget of one Type 1 ffSampling call** at Falcon-512 (hop A): input errors of ℓ2 norm `≤ e`
with `49 e + 43700·2⁻⁴⁰ ≤ 2⁻¹⁰` give, along every execution, `Σ (t̄ - t)² ≤ (49 e + 43700·2⁻⁴⁰)²`.
-/
theorem ffs64_pathS {εq : ℝ} (ρ : Arith64 εq) (T : FTree 9) (t0 t1 t0h t1h : Out 9 → ℂ) (e : ℝ)
    (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) :
    PathSum wS (ffsU (aux := aux) ρ.toArith (1 / 2 ^ 64) R64 T t0 t1 t0h t1h)
      ((49 * e + 43700 / 2 ^ 40) ^ 2) := by
  have he0 : 0 ≤ e := (l2_nonneg _).trans he
  have hC0 : 0 ≤ coefC nn512 w64 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63))
      (14145 / 10000 / 2 ^ 40) 9 :=
    (coef_nonnegU b64 9).2
  exact (ffs_pathSU b64 ρ.toArith ρ.tw_err64 ρ.tws_err64 T le_rfl t0 t1 t0h t1h e he
    ((budget64 e he0).trans he1)).toPathSum.weaken
    (pow_le_pow_left₀ (add_nonneg (mul_nonneg (coef_nonnegU b64 9).1 he0) hC0) (budget64 e he0) 2)

/-- **SamplerZ queries of one Type 1 ffSampling call**: at most `1024`. -/
theorem ffs64_pathN {εq : ℝ} (ρ : Arith64 εq) (T : FTree 9) (t0 t1 t0h t1h : Out 9 → ℂ) :
    PathSum w1 (ffsU (aux := aux) ρ.toArith (1 / 2 ^ 64) R64 T t0 t1 t0h t1h) 1024 :=
  (ffs_pathNU ρ.toArith _ _ T t0 t1 t0h t1h).weaken (by norm_num)

/-- **Check margins of Type 1 ffSampling at `R64`**: with input errors of ℓ2 norm `≤ e`, `49 e +
43700·2⁻⁴⁰ ≤ 2⁻¹⁰`, while the earlier checks pass every checked computed value (`t̄1`, `t̄0'`, the
odd merge inputs `ẑ1` of both children, at every node) is within `1` of its exact value slotwise:
the range checks `‖vh‖ ≤ R64 - 1` may be replaced by `chkM R64` (`ffsU_eq_margin`). Exact checked
values in `‖·‖ ≤ R64 - 2` pass `chkM R64` (`InBR.chkM`). -/
theorem ffs64_eq_margin {εq : ℝ} (ρ : Arith64 εq) (T : FTree 9) (t0 t1 t0h t1h : Out 9 → ℂ) (e : ℝ)
    (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) :
    ffsU (aux := aux) ρ.toArith (1 / 2 ^ 64) R64 T t0 t1 t0h t1h =
      ffsG ρ.toArith (1 / 2 ^ 64) (chkM R64) T t0 t1 t0h t1h :=
  ffsU_eq_margin b64 ρ.toArith ρ.tw_err64 ρ.tws_err64 T le_rfl t0 t1 t0h t1h e he
    ((budget64 e ((l2_nonneg _).trans he)).trans he1)

end FalconPrecision.Errors.FFSamp
