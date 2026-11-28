/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.SignModel64

/-! # Type 1 fixed-point signing at Falcon-1024 (tree depth 10): centre-error budgets

The Type 1 model of `FFSampModel64` and `SignModel64` (every value at 64 fractional bits, `Arith64`)
at Falcon-1024: `n = 1024`, ffSampling of depth 10, `σmin = 1.298280334` (spec Table 3.3).

* Stored tree (`FTree1024`): leaves in `[σmin, σmax] = [1.298280334, 1.8205]`, `‖ℓ̂‖∞ ≤ lam1024 L`:
  `32.0001` at the root (`γroot = 32`, ePrint 2026/2431 §3.3, their tuple B) and `0.9990` below
  (`≥ (α⁴ - 1)/(α⁴ + 1) = 0.99890…` at `α = γhybrid = 6.53`, the same tuple; Lemma 8 (16) of ePrint
  2026/1531, pen-and-paper only). These are checks added by the model, as at Falcon-512; nothing
  ties the tree to the key.
* Key (`Key1024`): `‖f̂‖∞ ≤ 256`, `‖F̂‖∞ ≤ 7365` on the exact FFTs (`γf,g`, `γF,G` of the same
  tuple, with `≤` where 2026/2431 uses `<`).
* Range `R64_1024 = 2²⁷`: the route B′ bounds on the checked exact values at depth 10
  (`Falcon1024Abort`) reach about `9.04·10⁷` (a computed value, above `2²⁶`), so the abort argument
  does not go through with `R64 = 2²⁴` of Falcon-512; `2²⁷ - 2` is proved to suffice. The twiddle
  term `δR` of the split and merge budgets grows with `R`: `r' = 1.4145·2⁻³⁷`,
  `c = 0.70721·2⁻³⁷`.
* Coefficients: `Ā₁₀ ≤ 76`, `C̄₁₀ ≤ 1084900·2⁻⁴⁰` (`coef64_1024`).
* Input error (`input_err64_1024`, the scale-first target as at Falcon-512): `‖ĉ‖∞ ≤ 1024·12288`,
  `‖ĉ/q‖₂ ≤ 1024`, `inp64_1024 2⁻⁶⁵ ≤ 15.6·2⁻³²`, `inp64_1024 2⁻⁷⁸ ≤ 4.4·2⁻³²`.
* Per call `Σ (t̄ - t)² ≤ (76 e + 1084900·2⁻⁴⁰)²` (`ffs64_pathS1024`, `sign1024_pathS`); `2⁻¹⁰` fits
  `K = 2²⁹` calls at either input bound (`centers_budget1024`, `centers_budget1024n`).

What is not proved here: hop A and hop B (proved in `Falcon1024Abort` and `Falcon1024HopB`), the
key check, and that the 64-bit twiddle tables meet `0.7072·2⁻⁶⁴` at level 9 (a hypothesis of
`ρ : Arith64`, as every table bound is). The range checks are the model's; deployed signers run
none. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath

namespace FalconPrecision.Errors.FFSamp

/-- Falcon-1024 node bounds: `32.0001` at the root (level 9), `0.9990` below. -/
noncomputable def lam1024 (L : ℕ) : ℝ := if L = 9 then 320001 / 10000 else 9990 / 10000

/-- Falcon-1024 norm factors (`1 + Λ² ≤ N²`, `Λ² ≤ (N² - 1)(N² - 1 - Λ²)`). -/
noncomputable def nn1024 (L : ℕ) : ℝ := if L = 9 then 32032 / 1000 else 16175 / 10000

theorem tb1024 : TreeBounds lam1024 nn1024 :=
  ⟨fun L => by unfold lam1024; split_ifs <;> norm_num,
    fun L => by unfold lam1024; split_ifs <;> norm_num,
    fun L => by unfold nn1024; split_ifs <;> norm_num,
    fun L => by unfold nn1024 lam1024; split_ifs <;> norm_num,
    fun L => by unfold nn1024 lam1024; split_ifs <;> norm_num⟩

theorem σmin1024_ok : (12778 / 10000 : ℝ) ≤ 1298280334 / 10 ^ 9 := by norm_num

/-- The stored tree at Falcon-1024: leaves in `[1.298280334, 1.8205]` (spec Table 3.3),
`‖ℓ̂‖∞ ≤ lam1024 L`. -/
abbrev FTree1024 : ℕ → Type := FTreeP (1298280334 / 10 ^ 9) σmin1024_ok lam1024

/-- A Falcon-1024 key: `f, F` of degree 1024 with `‖f̂‖∞ ≤ 256`, `‖F̂‖∞ ≤ 7365`, and a stored tree
of depth 10. -/
abbrev Key1024 : Type := KeyP 10 256 7365 (1298280334 / 10 ^ 9) σmin1024_ok lam1024

/-- The range of exact values of the Type 1 model at Falcon-1024. -/
noncomputable def R64_1024 : ℝ := 2 ^ 27

/-- Type 1 line-10 budgets `W_L` at range `R64_1024`. -/
noncomputable def w64_1024 (L : ℕ) : ℝ :=
  (match L with
    | 0 => 801 | 1 => 2731 | 2 => 7058 | 3 => 16376 | 4 => 35947 | 5 => 76415 | 6 => 159223
    | 7 => 327488 | 8 => 667764 | _ => 43359063) / 100 / 2 ^ 40

theorem w64_1024_nonneg (L : ℕ) : 0 ≤ w64_1024 L := by unfold w64_1024; split <;> positivity

theorem w64_1024_le (L : ℕ) : w64_1024 L ≤ 1 / 2 ^ 20 := by unfold w64_1024; split <;> norm_num

/-- Line-10 budgets (arithmetic): merge constant `c = 0.70721·2⁻³⁷`, rounding `√2·2⁻⁶⁴`. -/
theorem ez64_1024 : ∀ L, L ≤ 9 → lam1024 L * ezU (70721 / 100000 / 2 ^ 37) (L + 1) +
    sq512 (L + 1) * (141422 / 100000 / 2 ^ 64) ≤ w64_1024 L := by
  intro L hL
  interval_cases L <;> simp only [ezU, sq512, lam1024, w64_1024] <;> norm_num

theorem ezU64_1024_le (L : ℕ) (hL : L ≤ 9) : ezU (70721 / 100000 / 2 ^ 37) L ≤ 1 := by
  interval_cases L <;> simp only [ezU, sq512] <;> norm_num

/-- The Type 1 budget at Falcon-1024: ulp `2⁻⁶⁴`, range `2²⁷`, twiddle tables within
`0.7072·2⁻⁶⁴`, root at level 9. -/
noncomputable def b64_1024 : Budget lam1024 9 where
  u := 1 / 2 ^ 64
  R := R64_1024
  δ := 7072 / 10000 / 2 ^ 64
  r' := 14145 / 10000 / 2 ^ 37
  c := 70721 / 100000 / 2 ^ 37
  W := w64_1024
  hu := by positivity
  hδ0 := by positivity
  hδ := by norm_num
  hR := by unfold R64_1024; positivity
  hhalve := by linarith [sqrt_two_le]
  hsplit := by unfold R64_1024; linarith [sqrt_two_le]
  hc := by unfold R64_1024; linarith [sqrt_two_le]
  hW0 := w64_1024_nonneg
  hW1 := w64_1024_le
  hW L hL := by
    have := mul_le_mul_of_nonneg_left sqrt_two_ulp64
        ((Real.sqrt_nonneg _).trans (sqrt_pow_le (L + 1)))
    linarith [ez64_1024 L hL]
  hez := ezU64_1024_le

theorem coefA64_1024 : coefA nn1024 (70711 / 100000) 10 ≤ 76 := by
  simp only [coefA, nn1024]; norm_num

theorem coefC64_1024 : coefCU nn1024 w64_1024 (70711 / 100000) (14145 / 10000 / 2 ^ 37)
    (141422 / 100000) sq512 10 ≤ 1084900 / 2 ^ 40 := by
  simp only [coefCU, coefA, nn1024, w64_1024, sq512]; norm_num

/-- Coefficients of the Falcon-1024 Type 1 instance (arithmetic): `Ā₁₀ ≤ 76`,
`C̄₁₀ ≤ 1084900·2⁻⁴⁰`. -/
theorem coef64_1024 : coefA nn1024 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) 10 ≤ 76 ∧
    coefC nn1024 w64_1024 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63))
        (14145 / 10000 / 2 ^ 37) 10 ≤ 1084900 / 2 ^ 40 := by
  have hK : √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) ≤ 70711 / 100000 := by
    have h4 : √2 ≤ 1414214 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
        [mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ 1 / 2 + 7072 / 10000 / 2 ^ 63)]
  have hC := coefC_le nn1024 w64_1024 tb1024.nn_nonneg w64_1024_nonneg _ _
    (14145 / 10000 / 2 ^ 37) (141422 / 100000) sq512 K512_nonneg hK (by positivity) sqrt_two_le
    sqrt_pow_le 10
  exact ⟨(coefA_mono nn1024 tb1024.nn_nonneg _ _ K512_nonneg hK 10).2.trans coefA64_1024,
    hC.2.trans coefC64_1024⟩

theorem budget64_1024 (e : ℝ) (he0 : 0 ≤ e) :
    coefA nn1024 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) 10 * e +
      coefC nn1024 w64_1024 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) (14145 / 10000 / 2 ^ 37) 10 ≤
      76 * e + 1084900 / 2 ^ 40 := by
  linarith [mul_le_mul_of_nonneg_right coef64_1024.1 he0, coef64_1024.2]

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/--
**Path budget of one Type 1 ffSampling call at Falcon-1024** (depth 10, hop A): input errors of ℓ2
norm `≤ e` with `76 e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰` give, along every execution,
`Σ (t̄ - t)² ≤ (76 e + 1084900·2⁻⁴⁰)²` over the SamplerZ queries. -/
theorem ffs64_pathS1024 {εq : ℝ} (ρ : Arith64 εq) (T : FTree1024 10)
    (t0 t1 t0h t1h : Out 10 → ℂ) (e : ℝ) (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10) :
    PathSum wS (ffsU (aux := aux) ρ.toArith (1 / 2 ^ 64) R64_1024 T t0 t1 t0h t1h)
      ((76 * e + 1084900 / 2 ^ 40) ^ 2) := by
  have he0 : 0 ≤ e := (l2_nonneg _).trans he
  have hC := coef_nonnegP b64_1024 tb1024.nn_nonneg 10
  exact (ffs_pathSP b64_1024 tb1024 ρ.toArith ρ.tw_err64 ρ.tws_err64 T le_rfl t0 t1 t0h t1h e he
    ((budget64_1024 e he0).trans he1)).toPathSum.weaken
    (pow_le_pow_left₀ (add_nonneg (mul_nonneg hC.1 he0) hC.2) (budget64_1024 e he0) 2)

/-- **SamplerZ queries of one Type 1 ffSampling call at Falcon-1024**: at most `2048`. -/
theorem ffs64_pathN1024 {εq : ℝ} (ρ : Arith64 εq) (T : FTree1024 10)
    (t0 t1 t0h t1h : Out 10 → ℂ) :
    PathSum w1 (ffsU (aux := aux) ρ.toArith (1 / 2 ^ 64) R64_1024 T t0 t1 t0h t1h) 2048 :=
  (ffs_pathNGP ρ.toArith _ _ T t0 t1 t0h t1h).weaken (by norm_num)

/-- **Check margins of Type 1 ffSampling at Falcon-1024**: with input errors of ℓ2 norm `≤ e`,
`76 e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰`, the range checks `‖vh‖ ≤ R64_1024 - 1` may be replaced by
`chkM R64_1024`. -/
theorem ffs64_eq_margin1024 {εq : ℝ} (ρ : Arith64 εq) (T : FTree1024 10)
    (t0 t1 t0h t1h : Out 10 → ℂ) (e : ℝ) (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10) :
    ffsU (aux := aux) ρ.toArith (1 / 2 ^ 64) R64_1024 T t0 t1 t0h t1h =
      ffsG ρ.toArith (1 / 2 ^ 64) (chkM R64_1024) T t0 t1 t0h t1h :=
  ffsU_eq_marginP b64_1024 tb1024 ρ.toArith ρ.tw_err64 ρ.tws_err64 T le_rfl t0 t1 t0h t1h e he
    ((budget64_1024 e ((l2_nonneg _).trans he)).trans he1)

/-! ## The input of ffSampling at Falcon-1024 -/

variable {εq : ℝ}

/-- `E_ĉ` at Falcon-1024 (arithmetic): `ezU` at `c = δ·1024·12288 + √2·2⁻⁶⁴`, depth 10. -/
theorem ec64_1024 :
    ezU (7072 / 10000 / 2 ^ 64 * (1024 * 12288) + 141422 / 100000 / 2 ^ 64) 10 ≤
      10655741000 / 2 ^ 63 := by
  simp only [ezU, sq512]; norm_num

/-- The computed `ĉ = FFT(c)` at Falcon-1024 is within `10655741000·2⁻⁶³` in ℓ2. -/
theorem chC64_err1024 (ρ : Arith64 εq) (c : Fin (2 ^ 10) → ℤ) (hc : ∀ i, |c i| < 12289) :
    l2 (chC64 ρ c - fun o => fftE (fun i => (c i : ℂ)) o) ≤ 10655741000 / 2 ^ 63 := by
  set E : ℕ → ℝ := fun L => Nat.rec (motive := fun _ => ℝ) 0
    (fun L e => 2 * (1 + 7072 / 10000 / 2 ^ 64) * e +
      √2 * (√(2 ^ L) * (7072 / 10000 / 2 ^ 64 * (1024 * 12288) + 141422 / 100000 / 2 ^ 64))) L
  have hu : (0 : ℝ) < 1 / 2 ^ 64 := by positivity
  have ha : ∀ i, ‖((c i : ℤ) : ℂ)‖ ≤ 12288 := fun i => by
    obtain ⟨h1, h2⟩ := abs_lt.1 (hc i)
    rw [Complex.norm_intCast, abs_le]
    exact ⟨by exact_mod_cast (by omega : (-12288 : ℤ) ≤ c i),
        by exact_mod_cast (by omega : c i ≤ 12288)⟩
  have h :=
      fft_rec_err_l2 (7072 / 10000 / 2 ^ 64) (141422 / 100000 / 2 ^ 64) (1024 * 12288) E zeta
    ρ.tw pt pt_succ zeta_sq norm_zeta ρ.tw_err64 (fun L a => ρ.fft (1 / 2 ^ 64) L a)
    (fun a => by
      rw [l2_out0]
      change ‖a ⟨0, by norm_num⟩ - a ⟨0, by norm_num⟩‖ ≤ (0 : ℝ)
      simp)
    (fun L a => ⟨_, fun o => (ρ.mul_err hu _ _).trans sqrt_two_ulp64, fun o => ⟨rfl, rfl⟩⟩)
        (fun L => rfl) 10
    (fun i => (c i : ℂ)) fun o => (norm_evalAt_le _ _ (norm_pt 10 o) 12288 ha).trans (by norm_num)
  have he :=
      (ez_le (7072 / 10000 / 2 ^ 64)
          (7072 / 10000 / 2 ^ 64 * (1024 * 12288) + 141422 / 100000 / 2 ^ 64)
    (by positivity) (by norm_num) (by positivity) E rfl (fun L => rfl) 10).2
  exact h.trans (he.trans ec64_1024)

/-- Error bound of the computed `ĉ/q` at Falcon-1024. -/
noncomputable def ecq64_1024 (εq : ℝ) : ℝ :=
  10655741000 / 2 ^ 63 / 12289 + εq * (12289 * 1024 + 10655741000 / 2 ^ 63) + 2 ^ 5 *
      (141422 / 100000 / 2 ^ 65)

/-- The computed `ĉ/q` at Falcon-1024 is within `ecq64_1024 εq` of `FFT(c/q)` in ℓ2. -/
theorem cqC64_err1024 (ρ : Arith64 εq) (hεq : 0 ≤ εq) (c : Fin (2 ^ 10) → ℤ)
    (hc : ∀ i, |c i| < 12289) :
    l2 (fun o => cqC64 ρ c o - fftE (cdq c) o) ≤ ecq64_1024 εq := by
  set ch := chC64 ρ c
  set C : Out 10 → ℂ := fun o => fftE (fun i => (c i : ℂ)) o
  have hE := chC64_err1024 ρ c hc
  have hC : l2 C ≤ 12289 * 1024 := by
    have hC' : C = fun o => (fun _ => (12289 : ℂ)) o * fftE (cdq c) o := by
      funext o; simp only [C, fftE_cdqP]; ring
    rw [hC']
    exact (l2_mul_le _ _ 12289 (by norm_num) fun _ => by norm_num).trans
      (mul_le_mul_of_nonneg_left ((fftE_l2P c hc).trans (by norm_num)) (by norm_num))
  have hch : l2 ch ≤ 12289 * 1024 + 10655741000 / 2 ^ 63 := by
    have := l2_add_le C (ch - C)
    rw [add_sub_cancel] at this
    linarith
  have e : (fun o => cqC64 ρ c o - fftE (cdq c) o) =
      (fun o => ρ.divq (ch o) - ch o / 12289) + fun o => (fun _ => (1 / 12289 : ℂ)) o *
          (ch - C) o := by
    funext o; simp only [cqC64, Pi.add_apply, Pi.sub_apply, fftE_cdqP, C, ch]; ring
  rw [e]
  have ha := l2_le_affine _ ch εq _ hεq (by positivity) fun o => ρ.divq_err (ch o)
  have hb := (l2_mul_le (fun _ => (1 / 12289 : ℂ)) (ch - C) (1 / 12289) (by norm_num) fun _ => by
    rw [norm_div, norm_one, Complex.norm_ofNat]).trans
    (mul_le_mul_of_nonneg_left hE (by norm_num))
  have hcard : √(Fintype.card (Out 10) : ℝ) ≤ 2 ^ 5 := by
    rw [card_out, Real.sqrt_le_left (by norm_num)]; norm_num
  have hk : √(Fintype.card (Out 10) : ℝ) * (√2 * (1 / 2 ^ 65)) ≤ 2 ^ 5 *
      (141422 / 100000 / 2 ^ 65) :=
    mul_le_mul hcard ((mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num))
      (by positivity) (by norm_num)
  have := mul_le_mul_of_nonneg_left hch hεq
  unfold ecq64_1024
  linarith
      [l2_add_le (fun o => ρ.divq (ch o) - ch o / 12289) fun o => (fun _ => (1 / 12289 : ℂ)) o *
          (ch - C) o]

/-- `F̂` by the certified FFT at Falcon-1024 (`‖F̂‖∞ ≤ 7365`): sup error `≤ 2664886·2⁻⁶³`
(arithmetic). -/
theorem fftF64_err1024 : (7072 / 10000 / 2 ^ 64 * 7365 + 141422 / 100000 / 2 ^ 64) *
    ∑ j ∈ Finset.range 10, (2 + 7072 / 10000 / 2 ^ 64 : ℝ) ^ j ≤ 2664886 / 2 ^ 63 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

/-- `f̂` by the certified FFT at Falcon-1024 (`‖f̂‖∞ ≤ 256`): sup error `≤ 93327·2⁻⁶³`
(arithmetic). -/
theorem fftf64_err1024 : (7072 / 10000 / 2 ^ 64 * 256 + 141422 / 100000 / 2 ^ 64) *
    ∑ j ∈ Finset.range 10, (2 + 7072 / 10000 / 2 ^ 64 : ℝ) ^ j ≤ 93327 / 2 ^ 63 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

/-- The input-error bound of the Type 1 chain at Falcon-1024. -/
noncomputable def inp64_1024 (εq : ℝ) : ℝ :=
  (7365 * ecq64_1024 εq + 2664886 / 2 ^ 63 * 1024 + 2664886 / 2 ^ 63 * ecq64_1024 εq + 2 ^ 5 *
      (141422 / 100000 / 2 ^ 64)) +
    (256 * ecq64_1024 εq + 93327 / 2 ^ 63 * 1024 + 93327 / 2 ^ 63 * ecq64_1024 εq + 2 ^ 5 *
        (141422 / 100000 / 2 ^ 64))

/-- `1/q` stored at 64 fractional bits: input error `≤ 15.6·2⁻³²` (arithmetic). -/
theorem inp64_1024_base : inp64_1024 (1 / 2 ^ 65) ≤ 156 / 10 / 2 ^ 32 := by
  simp only [inp64_1024, ecq64_1024]; norm_num

/-- `1/q` stored normalized (within `2⁻⁷⁸`): input error `≤ 4.4·2⁻³²` (arithmetic). -/
theorem inp64_1024_norm : inp64_1024 (1 / 2 ^ 78) ≤ 44 / 10 / 2 ^ 32 := by
  simp only [inp64_1024, ecq64_1024]; norm_num

/--
**Input error of ffSampling in Type 1 at Falcon-1024** (scale-first target, 2026/2431 §3.1):
`‖(t̂0, t̂1) computed - exact‖₂ ≤ inp64_1024 εq`. -/
theorem input_err64_1024 (ρ : Arith64 εq) (hεq : 0 ≤ εq) (k : Key1024) (c : Fin (2 ^ 10) → ℤ)
    (hc : ∀ i, |c i| < 12289) :
    l2 (pairF (t0C64 ρ k c - t0E k c) (t1C64 ρ k c - t1E k c)) ≤ inp64_1024 εq := by
  have hcard : √(Fintype.card (Out 10) : ℝ) ≤ 2 ^ 5 := by
    rw [card_out, Real.sqrt_le_left (by norm_num)]; norm_num
  have hq := cqC64_err1024 ρ hεq c hc
  have hn : l2 (fun o => fftE (cdq c) o) ≤ 1024 := (fftE_l2P c hc).trans (by norm_num)
  have hr : ∀ z w, ‖ρ.mul (1 / 2 ^ 64) z w - z * w‖ ≤ 141422 / 100000 / 2 ^ 64 := fun z w =>
    (ρ.mul_err (by positivity) z w).trans sqrt_two_ulp64
  have h0 := prod_l2 (fun o => -fftE (cdq c) o) (fun o => -cqC64 ρ c o)
    (fftE fun i => (k.F i : ℂ)) (ρ.fft (1 / 2 ^ 64) 10 fun i => (k.F i : ℂ))
    (fun o => ρ.mul (1 / 2 ^ 64) (-cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 10 (fun i => (k.F i : ℂ)) o))
        7365
    (2664886 / 2 ^ 63) (ecq64_1024 εq) 1024 (141422 / 100000 / 2 ^ 64) (by norm_num)
        (by positivity) (by positivity)
    k.hF (fun o => (fft_cert64P ρ 7365 _ k.hF o).trans fftF64_err1024)
    (by
      have e : (fun o => -cqC64 ρ c o) - (fun o => -fftE (cdq c) o) =
          fun o => -(cqC64 ρ c o - fftE (cdq c) o) := by
        funext o; simp only [Pi.sub_apply]; ring
      rw [e, l2_neg]; exact hq)
    (by rw [l2_neg]; exact hn) (fun o => hr _ _)
  have h1 := prod_l2 (fun o => fftE (cdq c) o) (fun o => cqC64 ρ c o)
    (fftE fun i => (k.f i : ℂ)) (ρ.fft (1 / 2 ^ 64) 10 fun i => (k.f i : ℂ))
    (fun o => ρ.mul (1 / 2 ^ 64) (cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 10 (fun i => (k.f i : ℂ)) o))
        256
    (93327 / 2 ^ 63) (ecq64_1024 εq) 1024 (141422 / 100000 / 2 ^ 64) (by norm_num)
        (by positivity) (by positivity)
    k.hf (fun o => (fft_cert64P ρ 256 _ k.hf o).trans fftf64_err1024) hq hn (fun o => hr _ _)
  have e0 : t0C64 ρ k c - t0E k c = fun o =>
      ρ.mul (1 / 2 ^ 64) (-cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 10 (fun i => (k.F i : ℂ)) o) -
        (fun o => -fftE (cdq c) o) o * fftE (fun i => (k.F i : ℂ)) o := by
    funext o; simp only [Pi.sub_apply, t0C64, t0E]; ring
  have e1 : t1C64 ρ k c - t1E k c = fun o =>
      ρ.mul (1 / 2 ^ 64) (cqC64 ρ c o) (ρ.fft (1 / 2 ^ 64) 10 (fun i => (k.f i : ℂ)) o) -
        (fun o => fftE (cdq c) o) o * fftE (fun i => (k.f i : ℂ)) o := by
    funext o; simp only [Pi.sub_apply, t1C64, t1E]
  refine (l2_pairF_le _ _).trans ?_
  rw [e0, e1]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ 141422 / 100000 / 2 ^ 64)
  unfold inp64_1024
  linarith

/-! ## Type 1 signing at Falcon-1024 -/

/-- **Check margins of Type 1 signing at Falcon-1024**: for an input bound `inp64_1024 εq ≤ e` with
`76 e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰`, the range checks `‖vh‖ ≤ R64_1024 - 1` may be replaced by
`chkM R64_1024`. -/
theorem sign1024_eq_margin (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64_1024 εq ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10) (k : Key1024) (c : Fin (2 ^ 10) → ℤ) :
    sign164R (aux := aux) R64_1024 ρ k c = sign164G ρ (chkM R64_1024) k c := by
  unfold sign164R sign164G
  split_ifs with hc
  · rw [ffs64_eq_margin1024 ρ k.tree _ _ _ _ e ((input_err64_1024 ρ hεq k c hc).trans he) he1]
  · rfl

/-- **Centre-error budget of one Type 1 ffSampling call at Falcon-1024**, for an input bound
`inp64_1024 εq ≤ e`. -/
theorem sign1024_pathS (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64_1024 εq ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10) (k : Key1024) (c : Fin (2 ^ 10) → ℤ) :
    PathSum wS (sign164R (aux := aux) R64_1024 ρ k c) ((76 * e + 1084900 / 2 ^ 40) ^ 2) := by
  unfold sign164R
  split_ifs with hc
  · rw [map_eq_bind_pure_comp]
    exact (PathSum.bind (ffs64_pathS1024 ρ k.tree _ _ _ _ e
      ((input_err64_1024 ρ hεq k c hc).trans he) he1)
      (T := 0) fun _ => .pure _ le_rfl).weaken (le_of_eq (add_zero _))
  · exact .pure _ (sq_nonneg _)

/-- **SamplerZ calls of one Type 1 ffSampling call at Falcon-1024**: at most `2048`. -/
theorem sign1024_pathN (ρ : Arith64 εq) (k : Key1024) (c : Fin (2 ^ 10) → ℤ) :
    PathSum w1 (sign164R (aux := aux) R64_1024 ρ k c) 2048 := by
  unfold sign164R
  split_ifs
  · rw [map_eq_bind_pure_comp]
    exact (PathSum.bind (ffs64_pathN1024 ρ k.tree _ _ _ _) (T := 0) fun _ => .pure _ le_rfl).weaken
      (le_of_eq (add_zero _))
  · exact .pure _ (by norm_num)

/-- `oa` calls Type 1 signing at Falcon-1024 at most `K` times along every execution; every other
query is auxiliary. -/
abbrev Uses1024 (ρ : Arith64 εq) : ℕ → {α : Type} →
    OracleComp (FalconGame.spec aux Falcon.CallP) α → Prop :=
  UsesGP 10 256 7365 (1298280334 / 10 ^ 9) σmin1024_ok lam1024 (sign164R R64_1024 ρ)

/-- **Centre-error budget of an experiment at Falcon-1024**: `K` calls give
`Σ (t̄ - t)² ≤ K·(76 e + 1084900·2⁻⁴⁰)²` along every execution. -/
theorem Uses1024.pathS {ρ : Arith64 εq} (hεq : 0 ≤ εq) (e : ℝ) (he : inp64_1024 εq ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10) {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α} (h : Uses1024 ρ K oa) :
    PathSum wS oa (K * (76 * e + 1084900 / 2 ^ 40) ^ 2) :=
  UsesGP.path h wS (fun _ => rfl) _ (sq_nonneg _) (sign1024_pathS ρ hεq e he he1)

/-- **SamplerZ calls of an experiment at Falcon-1024**: at most `2048 K`. -/
theorem Uses1024.pathN {ρ : Arith64 εq} {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α} (h : Uses1024 ρ K oa) :
    PathSum w1 oa (K * 2048) :=
  UsesGP.path h w1 (fun _ => rfl) _ (by norm_num) (sign1024_pathN ρ)

/-- `2²⁹` Type 1 calls at Falcon-1024 with `1/q` at 64 fractional bits sum to `≤ 2⁻¹⁰`. -/
theorem centers_budget1024 :
    (2 : ℝ) ^ 29 * (76 * (156 / 10 / 2 ^ 32) + 1084900 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 10 := by
  norm_num

/-- `2²⁹` Type 1 calls at Falcon-1024 with normalized `1/q` sum to `≤ 2⁻¹⁰`. -/
theorem centers_budget1024n :
    (2 : ℝ) ^ 29 * (76 * (44 / 10 / 2 ^ 32) + 1084900 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 10 := by
  norm_num

end FalconPrecision.Errors.FFSamp
