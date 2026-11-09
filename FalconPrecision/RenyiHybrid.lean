/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ToMathlib.Probability.Divergence.Renyi
public import VCVio.OracleComp.SimSemantics.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Adaptive Rényi hybrid over oracle calls

The Rényi step of ePrint 2026/1531, Lemma 14 ([HPRR20, Lemma 11]; iterated [HPRR20, Proposition 4]):
if every query answer of `implQ` is within Rényi MGF `B` of the answer of `implP`, uniformly over
the query, then a computation making at most `n` queries, possibly adaptively, is within `Bⁿ`.
Discrete answers and outputs. The bind step pairs each step with its continuation (`μ ⊗ₘ κ`),
computes the joint Hellinger sum exactly, and drops the first coordinate by data processing
(`renyiMGF_map_le`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory OracleSpec OracleComp
open scoped ENNReal

namespace FalconPrecision.RenyiHybrid

section Discrete

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- On a countable space, for `a > 1`, the Rényi MGF of finite measures is the Hellinger sum of the
point masses (`⊤` exactly when some point charged by `μ` is not charged by `ν`). -/
theorem renyiMGF_eq_tsum {a : ℝ} (ha : 1 < a) (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    renyiMGF a μ ν = ∑' x, μ {x} ^ a * ν {x} ^ (1 - a) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 - a < 0 := by linarith
  by_cases hac : μ ≪ ν
  · have hwd : ν.withDensity (fun x => μ {x} / ν {x}) = μ := by
      refine Measure.ext_of_singleton fun x => ?_
      rw [withDensity_apply _ (measurableSet_singleton x), Measure.restrict_singleton,
          lintegral_smul_measure,
        lintegral_dirac, smul_eq_mul]
      by_cases h0 : ν {x} = 0
      · rw [h0, zero_mul, hac h0]
      · rw [ENNReal.mul_div_cancel h0 (measure_ne_top _ _)]
    have hrn : μ.rnDeriv ν =ᵐ[ν] fun x => μ {x} / ν {x} := by
      conv_lhs => rw [← hwd]
      exact Measure.rnDeriv_withDensity ν (measurable_of_countable _)
    rw [renyiMGF_of_ac hac, lintegral_congr_ae (hrn.mono fun x hx => by rw [hx]),
        lintegral_countable']
    refine tsum_congr fun x => ?_
    by_cases h0 : ν {x} = 0
    · rw [h0, mul_zero, hac h0, ENNReal.zero_rpow_of_pos ha0, zero_mul]
    · rw [ENNReal.div_rpow_of_nonneg _ _ ha0.le, ENNReal.rpow_sub _ _ h0 (measure_ne_top _ _),
        ENNReal.rpow_one]
      simp only [div_eq_mul_inv]
      ring
  · rw [renyiMGF_of_not_ac hac, eq_comm, ← top_le_iff]
    obtain ⟨x, hμx, hνx⟩ : ∃ x, μ {x} ≠ 0 ∧ ν {x} = 0 := by
      by_contra hne
      simp only [not_exists, not_and] at hne
      refine hac (Measure.AbsolutelyContinuous.mk fun s _ hs => ?_)
      rw [← Set.biUnion_of_singleton s]
      refine measure_biUnion_null_iff (Set.to_countable s) |>.2 fun x hx => ?_
      by_contra h
      exact hne x h (measure_mono_null (Set.singleton_subset_iff.2 hx) hs)
    calc ⊤ = μ {x} ^ a * ν {x} ^ (1 - a) := by
          rw [hνx, ENNReal.zero_rpow_of_neg ha1, ENNReal.mul_top (by simpa [ha0] using hμx)]
      _ ≤ _ := ENNReal.le_tsum (f := fun x => μ {x} ^ a * ν {x} ^ (1 - a)) x

end Discrete

section Bind

variable {ι α : Type*} [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] in
theorem compProd_singleton (μ : Measure ι) [IsFiniteMeasure μ] (f : ι → Measure α)
    [IsFiniteKernel (Kernel.ofFunOfCountable f)] (u : ι) (x : α) :
    (μ ⊗ₘ Kernel.ofFunOfCountable f) {(u, x)} = μ {u} * f u {x} := by
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod (measurableSet_singleton u)
    (measurableSet_singleton x), Measure.restrict_singleton, lintegral_smul_measure,
        lintegral_dirac, smul_eq_mul]
  rfl

/-- The joint Hellinger sum factors through the first step. -/
theorem renyiMGF_compProd {a : ℝ} (ha : 1 < a) (μ ν : Measure ι) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (fQ fP : ι → Measure α) [IsFiniteKernel (Kernel.ofFunOfCountable fQ)]
    [IsFiniteKernel (Kernel.ofFunOfCountable fP)] :
    renyiMGF a (μ ⊗ₘ Kernel.ofFunOfCountable fQ) (ν ⊗ₘ Kernel.ofFunOfCountable fP) =
      ∑' u, μ {u} ^ a * ν {u} ^ (1 - a) * renyiMGF a (fQ u) (fP u) := by
  have hQ : ∀ u, IsFiniteMeasure (fQ u) := fun u => by
    have : IsFiniteMeasure (Kernel.ofFunOfCountable fQ u) := inferInstance
    exact this
  have hP : ∀ u, IsFiniteMeasure (fP u) := fun u => by
    have : IsFiniteMeasure (Kernel.ofFunOfCountable fP u) := inferInstance
    exact this
  rw [renyiMGF_eq_tsum ha, ENNReal.tsum_prod']
  refine tsum_congr fun u => ?_
  rw [renyiMGF_eq_tsum ha, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [compProd_singleton, compProd_singleton,
    ENNReal.mul_rpow_of_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.mul_rpow_of_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/--
**Chain rule, one step.** If every continuation pair is within `B`, the composed pair is within the
first step's MGF times `B`. -/
theorem renyiMGF_bind_le {a : ℝ} (ha : 1 < a) (μ ν : Measure ι) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (fQ fP : ι → Measure α) (hQ1 : ∀ u, fQ u Set.univ ≤ 1) (hP1 : ∀ u, fP u Set.univ ≤ 1) {B : ℝ≥0∞}
    (hB : ∀ u, renyiMGF a (fQ u) (fP u) ≤ B) :
    renyiMGF a (μ.bind fQ) (ν.bind fP) ≤ renyiMGF a μ ν * B := by
  have : IsFiniteKernel (Kernel.ofFunOfCountable fQ) := ⟨⟨1, ENNReal.one_lt_top, hQ1⟩⟩
  have : IsFiniteKernel (Kernel.ofFunOfCountable fP) := ⟨⟨1, ENNReal.one_lt_top, hP1⟩⟩
  have hsnd : ∀ (ρ : Measure ι) (f : ι → Measure α) [IsFiniteMeasure ρ]
      [IsFiniteKernel (Kernel.ofFunOfCountable f)],
      (ρ ⊗ₘ Kernel.ofFunOfCountable f).map Prod.snd = ρ.bind f := fun ρ f _ _ => by
    rw [← Measure.snd, Measure.snd_compProd]
    rfl
  calc renyiMGF a (μ.bind fQ) (ν.bind fP)
      = renyiMGF a ((μ ⊗ₘ Kernel.ofFunOfCountable fQ).map Prod.snd)
          ((ν ⊗ₘ Kernel.ofFunOfCountable fP).map Prod.snd) := by rw [hsnd, hsnd]
    _ ≤ renyiMGF a (μ ⊗ₘ Kernel.ofFunOfCountable fQ) (ν ⊗ₘ Kernel.ofFunOfCountable fP) :=
        renyiMGF_map_le a ha _ _ measurable_snd
    _ = ∑' u, μ {u} ^ a * ν {u} ^ (1 - a) * renyiMGF a (fQ u) (fP u) :=
        renyiMGF_compProd ha μ ν fQ fP
    _ ≤ ∑' u, μ {u} ^ a * ν {u} ^ (1 - a) * B := by gcongr with u; exact hB u
    _ = renyiMGF a μ ν * B := by rw [ENNReal.tsum_mul_right, renyiMGF_eq_tsum ha]

end Bind

section Simulate

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [∀ t, Countable (spec.Range t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Adaptive hybrid.** Answers measured with the discrete structure. If every query's answer under
`implQ` is within Rényi MGF `B ≥ 1` of its answer under `implP`, a computation making at most `n`
queries has its simulated outputs within `Bⁿ`. -/
theorem renyiMGF_simulateQ_le {a : ℝ} (ha : 1 < a) (implQ implP : QueryImpl spec m) {B : ℝ≥0∞}
    (hB1 : 1 ≤ B)
    (hB : ∀ t, @renyiMGF _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ B)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] {n : ℕ}
    (oa : OracleComp spec α) (hn : IsTotalQueryBound oa n) :
    renyiMGF a 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] ≤ B ^ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
    simp only [simulateQ_pure, evalDist_pure]
    rw [renyiMGF_self]
    exact one_le_pow₀ hB1
  | query_bind t k ih =>
    obtain ⟨hn0, hk⟩ := isTotalQueryBound_query_bind_iff.1 hn
    let : MeasurableSpace (spec.Range t) := ⊤
    have : MeasurableSingletonClass (spec.Range t) := ⟨fun _ => trivial⟩
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    calc renyiMGF a ((𝒟[implQ t]).bind fun u => 𝒟[simulateQ implQ (k u)])
          ((𝒟[implP t]).bind fun u => 𝒟[simulateQ implP (k u)])
        ≤ renyiMGF a 𝒟[implQ t] 𝒟[implP t] * B ^ (n - 1) :=
          renyiMGF_bind_le ha _ _ _ _ (fun _ => evalDist_apply_univ_le_one _)
            (fun _ => evalDist_apply_univ_le_one _) fun u => ih u (hk u)
      _ ≤ B * B ^ (n - 1) := by gcongr; exact hB t
      _ = B ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn0]

/-- **Probability preservation across the hybrid** (the probability step of [HPRR20, Lemma 11]): an
event of probability `p` under `implQ` keeps probability at least `p^(a/(a-1)) / Bⁿ^(1/(a-1))` under
`implP`. -/
theorem measure_simulateQ_ge {a : ℝ} (ha : 1 < a) (implQ implP : QueryImpl spec m) {B : ℝ≥0∞}
    (hB1 : 1 ≤ B)
    (hB : ∀ t, @renyiMGF _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ B)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] {n : ℕ}
    (oa : OracleComp spec α) (hn : IsTotalQueryBound oa n) {s : Set α} (hs : MeasurableSet s) :
    𝒟[simulateQ implQ oa] s ^ (a / (a - 1)) / (B ^ n) ^ (a - 1)⁻¹ ≤ 𝒟[simulateQ implP oa] s := by
  refine le_trans ?_
      (measure_rpow_div_renyiDiv_le ha 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] hs)
  gcongr
  rw [renyiDiv_eq_rpow ha]
  exact ENNReal.rpow_le_rpow (renyiMGF_simulateQ_le ha implQ implP hB1 hB oa hn)
    (inv_nonneg.2 (by linarith))

/-- `(1 + 1/(4n))ⁿ ≤ √2`. -/
theorem one_add_pow_le (n : ℕ) :
    ENNReal.ofReal (1 + 1 / (4 * n)) ^ n ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero]; exact ENNReal.one_le_rpow (by norm_num) (by norm_num)
  have hx : (0 : ℝ) ≤ 1 + 1 / (4 * n) := by positivity
  rw [← ENNReal.ofReal_pow hx, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : (1 + 1 / (4 * n) : ℝ) ^ n ≤ Real.exp (1 / 4) := by
    calc (1 + 1 / (4 * n) : ℝ) ^ n ≤ Real.exp (1 / (4 * n)) ^ n := by
          gcongr; linarith [Real.add_one_le_exp (1 / (4 * (n : ℝ)))]
      _ = Real.exp (1 / 4) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h2 : Real.exp (1 / 4) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (Real.exp_pos _).le (by norm_num)]
    have e1 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have e2 : Real.exp (1 / 4) ^ 2 * Real.exp (1 / 4) ^ 2 = Real.exp 1 := by
      rw [← pow_add, ← Real.exp_nat_mul]; norm_num
    nlinarith [pow_pos (Real.exp_pos (1 / 4)) 2]
  exact h1.trans h2

end Simulate

end FalconPrecision.RenyiHybrid
