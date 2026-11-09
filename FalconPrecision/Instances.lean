/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Security

/-! # Theorems 1 and 2 at Falcon-512 and Falcon-1024 with explicit error budgets

A SamplerZ call (`Call`) carries the exact leaf `σ ∈ [1.2778, 1.8205]` (Falcon-512: `σmin =
1.27783…`; Falcon-1024: `σmin = 1.29828…`; both `σmax = 1.8205`), the fixed-point leaf `σ̄` with
relative error `|σ̄/σ - 1| ≤ 2⁻⁴⁷` (item 1), and the two centers. The experiment `oa` (key
generation, adversary, salts, hashing, signing) computes them; the type records the hypotheses.
Thresholds carry a parameter `T ≥ 1` (read as running time, bit security `log₂(T/ε)`).

The experiment is a finite `OracleComp` term: signing restarts are capped, and the per-call and
per-execution hypotheses range over every history, including out-of-range samples, so `oa` must
abort (or clamp) on those identically in the three worlds. Relating this experiment to uncapped
Falcon is not formalised (the paper's `c` and "for any history" leave the same gap).

- `falcon512`, `falcon1024` (Theorem 1, worst case, every `3 ≤ λ ≤ 128`, resp. `≤ 256`): `|t̄ - t| ≤
  2⁻⁴³` (resp. `2⁻⁴⁴`) per call and at most `2⁷⁵` (resp. `2⁷⁶`) SamplerZ calls along every execution
  (`2n·Qs·(1 + c)`, `Qs = 2⁶⁴`, `c < 1`). These budgets are sufficient conditions chosen here; they
  are not claimed to be met by any implementation (the paper's measured center RMSE `2⁻³⁹·⁵` does
  not meet `2⁻⁴³`).
- `falcon512_rmse` (Theorem 2 at the paper's §5 operating point, every `3 ≤ λ ≤ 128`): relative leaf
  error `2⁻⁴⁷` per call, at most `2⁷¹` SamplerZ calls (`2n·Qs·(1 + c)`, `Qs = 2⁶⁰`, `c < 1`) and
  squared center errors summing to at most `2⁻⁹` along every execution. `2⁻⁹ = 2·512·2⁶⁰·(2⁻³⁹·⁵)²`
  is the sum at the paper's measured center RMSE over `2n·Qs = 2⁷⁰` calls (the normalisation of
  (34), no restarts); the RMSE is a sample average (§7.5), here the sum is a hypothesis on every
  execution. The leaf sum is derived from the per-call leaf error and the call count (`≤ 2⁷¹·2⁻⁹⁰ =
  2⁻¹⁹`). The `N` of Lemma 15 only enters through `(1 + 1/(4N))ᴺ ≥ 5/4`. -/

@[expose] public section

open MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Falcon

theorem exp_le_one_add_two_mul (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  linarith [le_abs_self (Real.exp x - 1)]

theorem exp_le_inv_one_sub (x : ℝ) (h1 : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  rw [le_div_iff₀ (by linarith)]
  have h := Real.add_one_le_exp (-x)
  have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

theorem five_quarters_le (N : ℕ) (hN : 0 < N) : (5 / 4 : ℝ) ≤ (1 + 1 / (4 * N)) ^ N := by
  have h0 : (0 : ℝ) ≤ 1 / (4 * N) := by positivity
  have h := one_add_mul_le_pow (a := 1 / (4 * (N : ℝ))) (by linarith) N
  have : (N : ℝ) * (1 / (4 * N)) = 1 / 4 := by field_simp
  linarith

/-- Relative leaf error `2⁻⁴⁷` gives `|1/σ̄² - 1/σ²| ≤ 2⁻⁴⁵` on `σ ≥ 1`. -/
theorem inv_sq_sub_le (s sb : ℝ) (hs : 1 ≤ s) (hsb : 0 < sb) (h : |sb / s - 1| ≤ 1 / 2 ^ 47) :
    |1 / sb ^ 2 - 1 / s ^ 2| ≤ 1 / 2 ^ 45 := by
  have hs0 : 0 < s := by linarith
  set r := sb / s with hr
  have hsb' : sb = r * s := by rw [hr]; field_simp
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrlo : 1 - 1 / 2 ^ 47 ≤ r := by linarith
  have hid : 1 / sb ^ 2 - 1 / s ^ 2 = (1 - r) * (1 + r) / (r ^ 2 * s ^ 2) := by
    rw [hsb']; field_simp; ring
  rw [hid, abs_div, abs_mul, abs_of_pos (by positivity : 0 < r ^ 2 * s ^ 2),
      abs_of_pos (by linarith : 0 < 1 + r)]
  rw [div_le_iff₀ (by positivity)]
  have hrs : (1 - 1 / 2 ^ 47) ^ 2 ≤ r ^ 2 * s ^ 2 := by
    have : (1 - 1 / 2 ^ 47 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hrlo 2
    nlinarith [one_le_pow₀ (n := 2) hs]
  have hab : |1 - r| ≤ 1 / 2 ^ 47 := by rw [abs_sub_comm]; exact h
  calc |1 - r| * (1 + r) ≤ 1 / 2 ^ 47 * (2 + 1 / 2 ^ 47) :=
        mul_le_mul hab (by linarith) (by linarith) (by norm_num)
    _ ≤ 1 / 2 ^ 45 * (1 - 1 / 2 ^ 47) ^ 2 := by norm_num
    _ ≤ 1 / 2 ^ 45 * (r ^ 2 * s ^ 2) := by gcongr

/-- A SamplerZ call at a Falcon leaf, with the item-1 relative leaf error. -/
structure Call where
  σ : ℝ
  σbar : ℝ
  t : ℝ
  tbar : ℝ
  hσ : 12778 / 10000 ≤ σ ∧ σ ≤ 18205 / 10000
  hσbar : 0 < σbar
  hΔσ : |σbar / σ - 1| ≤ 1 / 2 ^ 47

theorem Call.hτ (c : Call) : |1 / c.σbar ^ 2 - 1 / c.σ ^ 2| ≤ 1 / 2 ^ 45 :=
  inv_sq_sub_le _ _ (by linarith [c.hσ.1]) c.hσbar c.hΔσ

theorem Call.hτi (c : Call) : 3017 / 10000 ≤ 1 / c.σ ^ 2 ∧ 1 / c.σ ^ 2 ≤ 6125 / 10000 := by
  obtain ⟨h1, h2⟩ := c.hσ
  have hp : 0 < c.σ := by linarith
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

theorem Call.hleaf (c : Call) (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 511) :
    3 / 10 ≤ 1 / c.σ ^ 2 ∧ 1 / c.σ ^ 2 ≤ (1000 / 1277) ^ 2 ∧
      3 / 10 ≤ 1 / c.σ ^ 2 + a * (1 / c.σbar ^ 2 - 1 / c.σ ^ 2) ∧
      1 / c.σ ^ 2 + a * (1 / c.σbar ^ 2 - 1 / c.σ ^ 2) ≤ (1000 / 1277) ^ 2 := by
  obtain ⟨h1, h2⟩ := c.hτi
  obtain ⟨h3, h4⟩ := abs_le.1 c.hτ
  refine ⟨by linarith, h2.trans (by norm_num), ?_, ?_⟩ <;> nlinarith

theorem Call.hσbar_ge (c : Call) : 1277 / 1000 ≤ c.σbar := by
  obtain ⟨h1, -⟩ := c.hσ
  have := abs_le.1 c.hΔσ
  have hp : 0 < c.σ := by linarith
  have : c.σbar = c.σ * (c.σbar / c.σ) := by field_simp
  nlinarith


theorem one_div_four_mul_le_one (N : ℕ) : 1 / (4 * (N : ℝ)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith

/-- `(2λ-1)(2λ)/(2(2λ-2)) ≤ λ + 1` for `λ ≥ 2`. -/
theorem order_bound₁ (lam x : ℝ) (h : 2 ≤ lam) (hx : 0 ≤ x) :
    (2 * lam - 1) * (2 * lam) * x / (2 * (2 * lam - 2)) ≤ (lam + 1) * x := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `(2λ-3)(2λ-2)/(2(2λ-4)) ≤ λ` for `λ ≥ 3`. -/
theorem order_bound₂ (lam x : ℝ) (h : 3 ≤ lam) (hx : 0 ≤ x) :
    (2 * lam - 3) * (2 * lam - 2) * x / (2 * (2 * lam - 4)) ≤ lam * x := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- Calls whose centers are within `Δt`. -/
abbrev CallΔ (Δt : ℝ) := {c : Call // |c.tbar - c.t| ≤ Δt}

/--
**Theorem 1 at Falcon leaves, every `3 ≤ λ ≤ Lmax`**: the per-call conditions (26), (27) are checked
once at `Lmax` (`h26`, `h27`). -/
theorem falcon_theorem1 (lam Lmax N : ℕ) (hlam : 3 ≤ lam) (hL : lam ≤ Lmax) (hLmax : Lmax ≤ 256)
    (Δt : ℝ)
    (h26 : 2 * ((Lmax + 1) * (1 / 2 ^ 45) ^ 2 * ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2)) ≤
      1 / (4 * (N : ℝ)))
    (h27 : 2 * ((2 * Lmax - 3) * Δt ^ 2 / (2 * (1277 / 1000) ^ 2) + Lmax * Δt ^ 2 * (1 / 2 ^ 30)) ≤
      1 / (4 * (N : ℝ)))
    (T : ℝ≥0∞) (hT : 1 ≤ T) (implA : QueryImpl aux m)
    (implE implM implF : QueryImpl (FalconGame.spec aux (CallΔ Δt)) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.1.σ q.1.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux (CallΔ Δt)) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa N)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have hl3 : (3 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlL : (lam : ℝ) ≤ Lmax := by exact_mod_cast hL
  have hL256 : (Lmax : ℝ) ≤ 256 := by exact_mod_cast hLmax
  have h1 := one_div_four_mul_le_one N
  have hK : (0 : ℝ) ≤ (1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2 := by positivity
  refine FalconGame.theorem1 (Q := CallΔ Δt) lam N hlam T hT (fun q => q.1.σ) (fun q => q.1.σbar)
    (fun q => q.1.t) (fun q => q.1.tbar) (3 / 10) (1277 / 1000) (1 / 2 ^ 45) Δt
    implA implE implM implF hAE hAM hAF (by exact hE) (by exact hM) (by exact hF)
    (fun q => by linarith [q.1.hσ.1]) (by norm_num)
    (fun q => q.1.hleaf (2 * lam - 1) (by linarith) (by linarith)) le_rfl (fun q => q.1.hσbar_ge)
    (fun q => by simpa using q.1.hτ) (fun q => q.2) oa hN ?_ ?_ hs hwin
  · set E :=
      (2 * (lam : ℝ) - 1) * (2 * lam) * (1 / 2 ^ 45) ^ 2 * ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2) /
      (2 * (2 * lam - 2)) with hE'
    have hb : E ≤ (Lmax + 1) * ((1 / 2 ^ 45) ^ 2 * ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2)) := by
      have := order_bound₁ lam ((1 / 2 ^ 45) ^ 2 * ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2))
          (by linarith)
        (by positivity)
      rw [hE']
      calc _ = (2 * (lam : ℝ) - 1) * (2 * lam) *
          ((1 / 2 ^ 45) ^ 2 * ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2)) /
            (2 * (2 * lam - 2)) := by ring
        _ ≤ _ := this
        _ ≤ _ := by gcongr
    have hE0 : 0 ≤ E := by
      rw [hE']
      exact div_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity))
        (by positivity)) (by linarith)
    have hX : 2 * E ≤ 1 / (4 * (N : ℝ)) := by nlinarith
    exact (exp_le_one_add_two_mul E hE0 (by linarith)).trans (by linarith)
  · set E := (2 * (lam : ℝ) - 3) * Δt ^ 2 / (2 * (1277 / 1000) ^ 2) +
      (2 * lam - 3) * (2 * lam - 2) * Δt ^ 2 * (1 / 2 ^ 30) / (2 * (2 * lam - 4)) with hE'
    have hb1 : (2 * (lam : ℝ) - 3) * Δt ^ 2 / (2 * (1277 / 1000) ^ 2) ≤
        (2 * Lmax - 3) * Δt ^ 2 / (2 * (1277 / 1000) ^ 2) := by
      gcongr
    have hb2 : (2 * (lam : ℝ) - 3) * (2 * lam - 2) * Δt ^ 2 * (1 / 2 ^ 30) / (2 * (2 * lam - 4)) ≤
        Lmax * Δt ^ 2 * (1 / 2 ^ 30) := by
      have := order_bound₂ lam (Δt ^ 2 * (1 / 2 ^ 30)) hl3 (by positivity)
      calc _ = (2 * (lam : ℝ) - 3) * (2 * lam - 2) * (Δt ^ 2 * (1 / 2 ^ 30)) /
          (2 * (2 * lam - 4)) := by
            ring
        _ ≤ lam * (Δt ^ 2 * (1 / 2 ^ 30)) := this
        _ ≤ Lmax * (Δt ^ 2 * (1 / 2 ^ 30)) := by gcongr
        _ = _ := by ring
    have hE0 : 0 ≤ E := by
      rw [hE']
      have : 0 ≤ (2 * (lam : ℝ) - 3) * Δt ^ 2 / (2 * (1277 / 1000) ^ 2) :=
        div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
      have : 0 ≤ (2 * (lam : ℝ) - 3) * (2 * lam - 2) * Δt ^ 2 * (1 / 2 ^ 30) /
          (2 * (2 * lam - 4)) :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _))
          (by positivity)) (by linarith)
      linarith
    have hX : 2 * E ≤ 1 / (4 * (N : ℝ)) := by rw [hE']; linarith
    exact (exp_le_one_add_two_mul E hE0 (by linarith)).trans (by linarith)

/-- **Theorem 1 at Falcon-512**, every `3 ≤ λ ≤ 128`. -/
theorem falcon512 (lam : ℕ) (hlam : 3 ≤ lam) (hL : lam ≤ 128) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m)
        (implE implM implF : QueryImpl (FalconGame.spec aux (CallΔ (1 / 2 ^ 43))) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.1.σ q.1.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux (CallΔ (1 / 2 ^ 43))) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa ((2 ^ 75 : ℕ) : ℝ))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s :=
  falcon_theorem1 lam 128 (2 ^ 75) hlam hL (by norm_num) (1 / 2 ^ 43) (by norm_num)
      (by norm_num) T hT
    implA implE implM implF hAE hAM hAF hE hM hF oa hN hs hwin

/-- **Theorem 1 at Falcon-1024**, every `3 ≤ λ ≤ 256`. -/
theorem falcon1024 (lam : ℕ) (hlam : 3 ≤ lam) (hL : lam ≤ 256) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m)
        (implE implM implF : QueryImpl (FalconGame.spec aux (CallΔ (1 / 2 ^ 44))) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.1.σ q.1.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux (CallΔ (1 / 2 ^ 44))) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa ((2 ^ 76 : ℕ) : ℝ))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s :=
  falcon_theorem1 lam 256 (2 ^ 76) hlam hL le_rfl (1 / 2 ^ 44) (by norm_num) (by norm_num) T hT
    implA implE implM implF hAE hAM hAF hE hM hF oa hN hs hwin

/--
**Theorem 2 at Falcon-512, every `3 ≤ λ ≤ 128`**, at the paper's §5 operating point: at most `2⁷¹`
SamplerZ calls along every execution (`2n·Qs·(1 + c)`, `Qs = 2⁶⁰`, `c < 1`), relative leaf error
`2⁻⁴⁷` per call, and squared center errors summing to at most `2⁻⁹` along every execution. -/
theorem falcon512_rmse (lam : ℕ) (hlam : 3 ≤ lam) (hL : lam ≤ 128) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Call) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux Call) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa (2 ^ 71))
    (hS₂ : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun q : Call => (q.tbar - q.t) ^ 2) oa
        (1 / 2 ^ 9))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have hl3 : (3 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlL : (lam : ℝ) ≤ 128 := by exact_mod_cast hL
  refine FalconGame.theorem2 lam (2 ^ 71) hlam T hT Call.σ Call.σbar Call.t Call.tbar (3 / 10)
    (1277 / 1000) ((1 / 2 ^ 45) ^ 2 * 2 ^ 71)
        (1 / 2 ^ 9) implA implE implM implF hAE hAM hAF hE hM hF
    (fun q => by linarith [q.hσ.1]) (by norm_num)
        (fun q => q.hleaf (2 * lam - 1) (by linarith) (by linarith))
    le_rfl (fun q => q.hσbar_ge) oa
    (hN.mono (sq_nonneg _) fun x => by
      cases x with
      | inl _ => simp
      | inr q => simpa using sq_le_sq' (abs_le.1 q.hτ).1 (abs_le.1 q.hτ).2) hS₂ ?_ ?_ hs hwin
  · refine le_trans ?_ (five_quarters_le _ (by positivity))
    set x : ℝ := (1 / 2 ^ 45) ^ 2 * 2 ^ 71 * ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2) with hx
    have hb := order_bound₁ lam x (by linarith) (by positivity)
    have : (2 * (lam : ℝ) - 1) * (2 * lam) * ((1 / 2 ^ 45) ^ 2 * 2 ^ 71) *
        ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2) / (2 * (2 * lam - 2)) ≤ 129 * x := by
      calc _ = (2 * (lam : ℝ) - 1) * (2 * lam) * x / (2 * (2 * lam - 2)) := by rw [hx]; ring
        _ ≤ (lam + 1) * x := hb
        _ ≤ 129 * x := by gcongr; linarith
    have hx1 : 129 * x ≤ 1 / 100 := by rw [hx]; norm_num
    have hE0 : 0 ≤ (2 * (lam : ℝ) - 1) * (2 * lam) * ((1 / 2 ^ 45) ^ 2 * 2 ^ 71) *
        ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2) / (2 * (2 * lam - 2)) := by
      exact div_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity))
        (by positivity)) (by linarith)
    refine (exp_le_one_add_two_mul _ hE0 (by linarith)).trans ?_
    linarith
  · refine le_trans ?_ (five_quarters_le _ (by positivity))
    have hb1 : (2 * (lam : ℝ) - 3) * (1 / 2 ^ 9) / (2 * (1277 / 1000) ^ 2) ≤
        (2 * 128 - 3) * (1 / 2 ^ 9) / (2 * (1277 / 1000) ^ 2) := by
      gcongr
    have hb2 : (2 * (lam : ℝ) - 3) * (2 * lam - 2) * (1 / 2 ^ 9) * (1 / 2 ^ 30) /
        (2 * (2 * lam - 4)) ≤
        128 * (1 / 2 ^ 9) * (1 / 2 ^ 30) := by
      have := order_bound₂ lam ((1 / 2 ^ 9) * (1 / 2 ^ 30)) hl3 (by positivity)
      calc _ = (2 * (lam : ℝ) - 3) * (2 * lam - 2) * ((1 / 2 ^ 9) * (1 / 2 ^ 30)) /
          (2 * (2 * lam - 4)) := by
            ring
        _ ≤ lam * ((1 / 2 ^ 9) * (1 / 2 ^ 30)) := this
        _ ≤ 128 * ((1 / 2 ^ 9) * (1 / 2 ^ 30)) := by gcongr
        _ = _ := by ring
    have hsum : (2 * 128 - 3) * (1 / 2 ^ 9) / (2 * (1277 / 1000) ^ 2) + 128 * (1 / 2 ^ 9) *
        (1 / 2 ^ 30) ≤
        16 / 100 := by norm_num
    refine (exp_le_inv_one_sub _ (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith

end FalconPrecision.Falcon
