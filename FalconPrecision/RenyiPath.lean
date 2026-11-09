/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.RenyiHybrid

/-! # Chain rule along executions and joint-divergence probability preservation

Lemma 16 of ePrint 2026/1531 in budget form: if every query `t` has Rényi MGF at most `exp(c·w t)`
and the weights of the queries made along every execution sum to at most `S` (`PathSum`,
answer-dependent), the simulated outputs have MGF at most `exp(c·S)`. Lemma 15 (B.6), per adversary,
with a parameter `T ≥ 1` (any running-time bound; no cost model ties it to the computation): a joint
bound `renyiMGF (2λ-1) Q P ≤ ((1 + 1/(4N))^N)^(2λ-2)`, i.e. `R_{2λ-1}(Q, P) ≤ (1 + 1/(4N))^N`, turns
success `> T·2^{-(λ-1)}` under `Q` into success `> T·2^{-λ}` under `P`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory OracleSpec OracleComp
open scoped ENNReal

namespace FalconPrecision.RenyiPath

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Along every execution of `oa`, the weights `w t` of the queries made sum to at most `S`. -/
inductive PathSum (w : ι → ℝ) : {α : Type} → OracleComp spec α → ℝ → Prop
  | pure {α : Type} (x : α) {S : ℝ} (h : 0 ≤ S) : PathSum w (pure x) S
  | query_bind {α : Type} (t : ι) (k : spec.Range t → OracleComp spec α) {S : ℝ}
      (h : ∀ u, PathSum w (k u) (S - w t)) : PathSum w (liftM (OracleSpec.query t) >>= k) S

/-- Raising the budget keeps a path sum. -/
theorem PathSum.weaken {w : ι → ℝ} {α : Type} {oa : OracleComp spec α} {S S' : ℝ}
    (h : PathSum w oa S)
    (hS : S ≤ S') : PathSum w oa S' := by
  induction h generalizing S' with
  | pure x h0 => exact .pure x (h0.trans hS)
  | query_bind t k _ ih => exact .query_bind t k fun u => ih u (by linarith)

/-- Path sums scale with the weights. -/
theorem PathSum.mono {w w' : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hw : ∀ t, w' t ≤ C * w t) {α : Type}
    {oa : OracleComp spec α} {S : ℝ} (h : PathSum w oa S) : PathSum w' oa (C * S) := by
  induction h with
  | pure x hS => exact .pure x (mul_nonneg hC hS)
  | @query_bind t k S _ ih =>
    refine .query_bind t k fun u => (ih u).weaken ?_
    have := hw t
    nlinarith

variable [∀ t, Countable (spec.Range t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Lemma 16 (budget form).** -/
theorem renyiMGF_simulateQ_le_path {a : ℝ} (ha : 1 < a) (implQ implP : QueryImpl spec m) {c : ℝ}
    (hc : 0 ≤ c)
    (w : ι → ℝ) (hB : ∀ t, @renyiMGF _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (Real.exp (c * w t)))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {oa : OracleComp spec α} {S : ℝ} (h : PathSum w oa S) :
    renyiMGF a 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] ≤ ENNReal.ofReal (Real.exp (c * S)) := by
  induction h with
  | pure x hS =>
    simp only [simulateQ_pure, evalDist_pure]
    rw [renyiMGF_self, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hc hS))
  | query_bind t k _ ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    have : MeasurableSingletonClass (spec.Range t) := ⟨fun _ => trivial⟩
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    calc renyiMGF a ((𝒟[implQ t]).bind fun u => 𝒟[simulateQ implQ (k u)])
          ((𝒟[implP t]).bind fun u => 𝒟[simulateQ implP (k u)])
        ≤ renyiMGF a 𝒟[implQ t] 𝒟[implP t] * ENNReal.ofReal (Real.exp (c * (_ - w t))) :=
          RenyiHybrid.renyiMGF_bind_le ha _ _ _ _ (fun _ => evalDist_apply_univ_le_one _)
            (fun _ => evalDist_apply_univ_le_one _) ih
      _ ≤ ENNReal.ofReal (Real.exp (c * w t)) * ENNReal.ofReal (Real.exp (c * (_ - w t))) := by
          gcongr; exact hB t
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2; ring

/-- A subprobability measure on a countable space has Rényi MGF at most `1` against itself. -/
theorem renyiMGF_self_le {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {a : ℝ}
    (ha : 1 < a) (μ : Measure α) [IsFiniteMeasure μ] (h1 : μ Set.univ ≤ 1) : renyiMGF a μ μ ≤ 1 :=
        by
  rw [RenyiHybrid.renyiMGF_eq_tsum ha]
  calc ∑' x, μ {x} ^ a * μ {x} ^ (1 - a) ≤ ∑' x, μ {x} := by
        refine ENNReal.tsum_le_tsum fun x => le_of_eq ?_
        by_cases h0 : μ {x} = 0
        · rw [h0, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]
        · rw [← ENNReal.rpow_add _ _ h0 (measure_ne_top _ _), add_sub_cancel, ENNReal.rpow_one]
    _ = μ Set.univ := by rw [← lintegral_one, lintegral_countable']; simp
    _ ≤ 1 := h1

/-- **Lemma 15, per adversary**, with a parameter `T ≥ 1`: success `> T·2^{-(λ-1)}` under `μ` gives
success `> T·2^{-λ}` under `ν` (bit security `log₂(T/ε)`). -/
theorem lemma15 {α : Type} [MeasurableSpace α] (lam : ℕ) (hlam : 2 ≤ lam) (N : ℕ) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : renyiMGF (2 * lam - 1) μ ν ≤
        (ENNReal.ofReal (1 + 1 / (4 * N)) ^ N) ^ ((2 * lam - 1 : ℝ) - 1))
    {s : Set α} (hs : MeasurableSet s) (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) < μ s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < ν s := by
  set a : ℝ := 2 * lam - 1 with ha_def
  have hlam' : (2 : ℝ) ≤ lam := by exact_mod_cast hlam
  have ha : 1 < a := by rw [ha_def]; linarith
  have ham : a - 1 ≠ 0 := by linarith
  have hD : renyiDiv a μ ν ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
    rw [renyiDiv_eq_rpow ha]
    refine le_trans ?_ (RenyiHybrid.one_add_pow_le N)
    calc renyiMGF a μ ν ^ (a - 1)⁻¹ ≤
        ((ENNReal.ofReal (1 + 1 / (4 * N)) ^ N) ^ (a - 1)) ^ (a - 1)⁻¹ :=
          ENNReal.rpow_le_rpow h (inv_nonneg.2 (by linarith))
      _ = _ := ENNReal.rpow_rpow_inv ham _
  have hP := measure_rpow_div_renyiDiv_le ha μ ν hs
  have he : 0 < a / (a - 1) := div_pos (by linarith) (by linarith)
  have hQ := ENNReal.rpow_lt_rpow hwin he
  have h2 : ((2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1))) ^ (a / (a - 1)) =
      (2 : ℝ≥0∞) ^ (-(lam : ℝ)) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    congr 1
    rw [ha_def]
    have : (lam : ℝ) - 1 ≠ 0 := by linarith
    rw [show (2 * (lam : ℝ) - 1 - 1) = 2 * ((lam : ℝ) - 1) by ring]
    field_simp
    ring
  rw [ENNReal.mul_rpow_of_nonneg _ _ he.le, h2] at hQ
  have hTe : T ≤ T ^ (a / (a - 1)) := by
    have : 1 ≤ a / (a - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
    calc T = T ^ (1 : ℝ) := (ENNReal.rpow_one T).symm
      _ ≤ T ^ (a / (a - 1)) := ENNReal.rpow_le_rpow_of_exponent_le hT this
  have hQ' : T * ((2 : ℝ≥0∞) ^ (-(lam : ℝ)) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ)) < μ s ^ (a / (a - 1)) :=
    lt_of_le_of_lt (by gcongr) hQ
  have hs2 : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  have hs2' : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
  calc T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) = T * ((2 : ℝ≥0∞) ^ (-(lam : ℝ)) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ)) /
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by rw [← mul_assoc, ENNReal.mul_div_cancel_right hs2 hs2']
    _ < μ s ^ (a / (a - 1)) / (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := ENNReal.div_lt_div_right hs2 hs2' hQ'
    _ ≤ μ s ^ (a / (a - 1)) / renyiDiv a μ ν := ENNReal.div_le_div_left hD _
    _ ≤ _ := hP

/-- **Lemma 14 of ePrint 2026/1531 ([HPRR20, Lemma 11]), per adversary**: if every query answer
satisfies `R_{2λ-1}(Q | P) ≤ 1 + 1/(4n)` and the computation makes at most `n` queries, an event of
probability `> T·2^{-(λ-1)}` under `implQ` has probability `> T·2^{-λ}` under `implP`. -/
theorem lemma14 (lam : ℕ) (hlam : 2 ≤ lam) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implQ implP : QueryImpl spec m) (n : ℕ)
    (hR : ∀ t, @renyiDiv _ ⊤ (2 * lam - 1 : ℝ) (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (1 + 1 / (4 * n)))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp spec α) (hn : IsTotalQueryBound oa n) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) < 𝒟[simulateQ implQ oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implP oa] s := by
  set a : ℝ := 2 * lam - 1 with ha_def
  have hlam' : (2 : ℝ) ≤ lam := by exact_mod_cast hlam
  have ha : 1 < a := by rw [ha_def]; linarith
  have ham : a - 1 ≠ 0 := by linarith
  set r := ENNReal.ofReal (1 + 1 / (4 * n)) with hr
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) ≤ 1 / (4 * n) := by positivity
    rw [hr, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hB : ∀ t, @renyiMGF _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ r ^ (a - 1) := fun t => by
    let : MeasurableSpace (spec.Range t) := ⊤
    have h := hR t
    rw [renyiDiv_eq_rpow ha] at h
    calc renyiMGF a 𝒟[implQ t] 𝒟[implP t]
        = (renyiMGF a 𝒟[implQ t] 𝒟[implP t] ^ (a - 1)⁻¹) ^ (a - 1) :=
            (ENNReal.rpow_inv_rpow ham _).symm
      _ ≤ r ^ (a - 1) := ENNReal.rpow_le_rpow h (by linarith)
  have hM :=
      RenyiHybrid.renyiMGF_simulateQ_le ha implQ implP (ENNReal.one_le_rpow hr1 (by linarith)) hB
    oa hn
  have hC : (r ^ (a - 1)) ^ n = (r ^ n) ^ (a - 1) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_comm]
  exact lemma15 lam hlam n T hT _ _ (hM.trans_eq hC) hs hwin

end FalconPrecision.RenyiPath
