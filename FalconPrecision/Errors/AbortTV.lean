/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.GaussTail
public import FalconPrecision.Errors.FalconProved
public import VCVio.EvalDist.MeasureTVDist.Bind

/-! # Truncated SamplerZ answers and total variation along executions

`etvDist_map_self_le`: post-processing by `f` moves at most the mass of `{f ≠ id}`.
`etvDist_clamp_le`: clamping a SamplerZ answer `z ~ D_{Z,σ,t}` (`σ ∈ [1.277, 1.825]`) to `round t`
when `|z - t| ≥ y` moves at most `p y = 2(1 + 2⁻³⁶)·exp(-y²/(2·1.825²))` (`GaussTail`).
`etvDist_simulateQ_le_path`: if every query `t` has total variation at most `c·w t` between two
implementations and the weights of the queries made along every execution sum to at most `S`
(`PathSum`), the simulated outputs are within `c·S` (`Measure.etvDist`, the largest event
discrepancy). With `w` one per SamplerZ query this bounds the distance between exact signing and
exact signing with clamped answers by `N·p y` for `N` SamplerZ queries. -/

@[expose] public section

open MeasureTheory OracleSpec OracleComp LatticeCrypto FalconPrecision.ThetaTail
    FalconPrecision.RenyiPath
open scoped ENNReal

namespace FalconPrecision.Errors.AbortTV

/-- **Post-processing moves at most the mass where it acts.** -/
theorem etvDist_map_self_le {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α)
    (f : α → α) : μ.etvDist (μ.map f) ≤ μ {a | f a ≠ a} := by
  have h := Measure.etvDist_bind_bind_le_of_bad μ Measure.dirac (fun a => Measure.dirac (f a))
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable
    (MeasurableSet.of_discrete (s := {a | f a ≠ a})) 0
    (ae_of_all _ fun a (ha : ¬f a ≠ a) => by rw [not_not.1 ha, Measure.etvDist_self])
  rwa [zero_mul, add_zero, Measure.bind_dirac, Measure.bind_dirac_eq_map _ Measurable.of_discrete]
      at h

/-- A SamplerZ answer clamped to `round t` unless it lies within `y` of the centre `t`. -/
noncomputable def clamp (y t : ℝ) (z : ℤ) : ℤ := if |(z : ℝ) - t| < y then z else round t

/-- `p y = 2(1 + 2⁻³⁶)·exp(-y²/(2·1.825²))`. -/
noncomputable def pclamp (y : ℝ) : ℝ :=
    2 * (1 + 1 / 2 ^ 36) * Real.exp (-(y ^ 2 / (2 * (1825 / 1000) ^ 2)))

/-- **Clamping a Falcon leaf sample** moves at most `p y`. -/
theorem etvDist_clamp_le (σ t y : ℝ) (hσ : 1277 / 1000 ≤ σ) (hσ' : σ ≤ 1825 / 1000) (hy : 0 ≤ y) :
    (discreteGaussianMeasure σ t).etvDist ((discreteGaussianMeasure σ t).map (clamp y t)) ≤
      ENNReal.ofReal (pclamp y) := by
  have hsub : {z : ℤ | clamp y t z ≠ z} ⊆ {z : ℤ | y ≤ |(z : ℝ) - t|} :=
    fun z (hz : clamp y t z ≠ z) => by
      change y ≤ |(z : ℝ) - t|
      by_contra h
      exact hz (by simp [clamp, not_le.1 h])
  refine (etvDist_map_self_le _ _).trans ((measure_mono hsub).trans
    ((FalconPrecision.Errors.GaussTail.measure_abs_ge_falcon σ t y hσ hy).trans
        (ENNReal.ofReal_le_ofReal ?_)))
  have hσ0 : 0 < σ := by linarith
  unfold pclamp
  gcongr

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Total variation along executions (budget form).** Also: a negative budget leaves no execution.
-/
theorem etvDist_simulateQ_le_path (implQ implP : QueryImpl spec m) {c : ℝ} (hc : 0 ≤ c) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t)
    (hB : ∀ t, @Measure.etvDist _ ⊤ (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (c * w t))
    {α : Type} [MeasurableSpace α] {oa : OracleComp spec α} {S : ℝ} (h : PathSum w oa S) :
    (S < 0 → 𝒟[simulateQ implQ oa] = 0 ∧ 𝒟[simulateQ implP oa] = 0) ∧
      (𝒟[simulateQ implQ oa]).etvDist 𝒟[simulateQ implP oa] ≤ ENNReal.ofReal (c * S) := by
  induction h with
  | pure x hS =>
    refine ⟨fun h => absurd hS (not_le.2 h), ?_⟩
    simp only [simulateQ_pure, Measure.etvDist_self, zero_le]
  | @query_bind t k S _ ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    have : DiscreteMeasurableSpace (spec.Range t) := ⟨fun _ => trivial⟩
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    by_cases hS : S - w t < 0
    · have e1 : (fun u => 𝒟[simulateQ implQ (k u)]) = 0 := funext fun u => ((ih u).1 hS).1
      have e2 : (fun u => 𝒟[simulateQ implP (k u)]) = 0 := funext fun u => ((ih u).1 hS).2
      rw [e1, e2, Measure.bind_zero_right, Measure.bind_zero_right, Measure.etvDist_self]
      exact ⟨fun _ => ⟨rfl, rfl⟩, bot_le⟩
    · have hS' : 0 ≤ S - w t := not_lt.1 hS
      refine ⟨fun h => absurd h (not_lt.2 (by linarith [hw t])), ?_⟩
      refine (Measure.etvDist_bind_bind_le_add_lintegral _ _ _ _ Measurable.of_discrete
        Measurable.of_discrete.aemeasurable (fun _ => ENNReal.ofReal (c * (S - w t)))
        (ae_of_all _ fun u => (ih u).2)).trans ?_
      rw [lintegral_const]
      have h1 : 𝒟[implP t] Set.univ ≤ 1 := evalDist_apply_univ_le_one _
      refine (add_le_add (hB t) (mul_le_of_le_one_right' h1)).trans_eq ?_
      rw [← ENNReal.ofReal_add (mul_nonneg hc (hw t)) (mul_nonneg hc hS')]
      congr 1
      ring

theorem pclamp_nonneg (y : ℝ) : 0 ≤ pclamp y := by unfold pclamp; positivity

theorem etvDist_map_clamp_le (mx : m ℤ) {σ t y : ℝ} (hmx : 𝒟[mx] = discreteGaussianMeasure σ t)
    (hσ : 1277 / 1000 ≤ σ) (hσ' : σ ≤ 1825 / 1000) (hy : 0 ≤ y) :
    𝒟[mx].etvDist 𝒟[clamp y t <$> mx] ≤ ENNReal.ofReal (pclamp y) := by
  rw [evalDist_map mx Measurable.of_discrete, hmx]
  exact etvDist_clamp_le σ t y hσ hσ' hy

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- Exact signing with clamped SamplerZ answers: world T. -/
noncomputable def implT (y : ℝ) (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m) :
    QueryImpl (FalconGame.spec aux Falcon.CallP) m
  | .inl x => implE (.inl x)
  | .inr q => (clamp y q.t <$> implE (.inr q) : m ℤ)

/-- **Exact signing against world T**: within `p y` per SamplerZ query along every execution. -/
theorem etvDist_implT_le (y : ℝ) (hy : 0 ≤ y)
    (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (w : ιA ⊕ Falcon.CallP → ℝ) (hw : ∀ t, 0 ≤ w t) (hw1 : ∀ q, 1 ≤ w (.inr q))
    {α : Type} [MeasurableSpace α] {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α} {N : ℝ}
    (h : PathSum w oa N) :
    (𝒟[simulateQ implE oa]).etvDist 𝒟[simulateQ (implT y implE) oa] ≤
      ENNReal.ofReal (pclamp y * N) := by
  refine (etvDist_simulateQ_le_path implE (implT y implE) (pclamp_nonneg y) w hw ?_ h).2
  rintro (x | q)
  · exact (@Measure.etvDist_self _ ⊤ _).trans_le bot_le
  · refine (etvDist_map_clamp_le (implE (.inr q)) (hE q) (by linarith [q.hσ.1]) q.hσ.2 hy).trans
      (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [pclamp_nonneg y, hw1 q]

end FalconPrecision.Errors.AbortTV
