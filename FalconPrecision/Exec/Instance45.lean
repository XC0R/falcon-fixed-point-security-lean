/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.KeyCheck

/-! # The checked instance at the uniform tree error `2⁻⁴⁵`

`δ45 L = 2⁻⁴⁵` at every level `L` (root included). `s2B_falcon45`: `2³⁹·s2B 30.5 δ45 ≤ 2⁻⁹`, by
the coarse bound `s2B_le` (value of that bound `≈ 2⁻⁹·¹⁶⁴`). `falcon512_fixed_vs_true45_checked`:
`falcon512_fixed_vs_true_checked` at `δq = δ45q` with `K·s2B 30.5 δ ≤ 2⁻⁹` discharged for every
`K ≤ 2³⁹`. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

/-- Uniform tree error `2⁻⁴⁵` at every level. -/
noncomputable def δ45 (_L : ℕ) : ℝ := 1 / 2 ^ 45

/-- `δ45` as a rational. -/
def δ45q (_L : ℕ) : ℚ := 1 / 2 ^ 45

theorem δ45q_eq : (fun j => (δ45q j : ℝ)) = δ45 := by
  funext j; unfold δ45q δ45; norm_num

/-- The uniform `2⁻⁴⁵` tree supports `2³⁹` signing-oracle calls at `y = 30.5` (value of the
`s2B_le` bound times `2³⁹` `≈ 2⁻⁹·¹⁶⁴`). -/
theorem s2B_falcon45 : (2 : ℝ) ^ 39 * s2B (61 / 2) δ45 ≤ 1 / 2 ^ 9 := by
  have h := s2B_le (δ := δ45) (fun j _ => by norm_num [δ45]) (by norm_num [δ45])
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, δ45, sq512]
  norm_num

variable (P : XChoices) (n : ℕ) {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
    {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- **Instance** at the uniform tree error `δ45` (`2⁻⁴⁵` at every level), `K ≤ 2³⁹`
(`s2B_falcon45`): `falcon512_fixed_vs_true_checked` at `δq = δ45q` with its condition
`K·s2B 30.5 δ ≤ 2⁻⁹` proved. That a key passes `check P n δ45q` is a hypothesis on every signing
key (`specK`); it is not proved for any key here (`#eval` runs of `checkFast` are not kernel
proofs). Hypotheses and what is not proved otherwise (word size: unbounded `Int`, `InRange` not
checked; `FTree.Real`, the true leaf range): those of `falcon512_fixed_vs_true_checked`. -/
theorem falcon512_fixed_vs_true45_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK P n aux δ45q) α) (hq : PathSum (wKC P n δ45q) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ (embed P n δ45q oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed P n δ45q oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  refine falcon512_fixed_vs_true_checked P n δ45q ρ K hK ?_ T hT implA implE implM implF hAE hAM
    hAF hE hM hF oe hq hs hwin
  rw [δ45q_eq]
  exact (mul_le_mul_of_nonneg_right hK' (s2B_nonneg _ _)).trans s2B_falcon45

end FalconPrecision.Exec
