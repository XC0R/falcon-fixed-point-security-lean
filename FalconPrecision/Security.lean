/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.RenyiPath
public import FalconPrecision.NumK
public import FalconPrecision.Lemma4

/-! # Theorems 1 and 2 of ePrint 2026/1531, conditional, with explicit constants: the game

The whole UF-CMA experiment (key generation, adversary coins, salts, hashing, signing) is one
computation `oa : OracleComp (spec aux Q) α`. Its oracles are auxiliary oracles `aux` (all
randomness other than SamplerZ, answered by the same `implA` in the three worlds) and SamplerZ calls
`q : Q`; a call carries the exact leaf `σ q`, the fixed-point leaf `σ̄ q`, the exact center `t q`
and the fixed-point center `t̄ q`, all computed by `oa` from its history. The three worlds answer
SamplerZ by `D_{σ,t}` (exact), `D_{σ̄,t}` (intermediate), `D_{σ̄,t̄}` (fixed point), perfect
samplers as in the paper. Everything other than SamplerZ's parameters is one computation shared by
the three worlds: signature assembly, the norm test, compression, the restart decision and
key-generation rejection are the same function of the history in the exact and the fixed-point
world. This is an assumption on the implementation (integer recomputation, or fixed-point error
small enough to round to the exact result), in addition to the leaf and center error bounds. `oa` is
a finite term: restarts are capped, and the hypotheses quantify over every history (all integer
answers), so out-of-range samples must abort or clamp identically in the three worlds; relating this
to uncapped Falcon is not formalised.

`theorem2` (RMSE, the paper's Theorem 2): the squared leaf and center errors sum to at most `S₁`,
`S₂` along every execution ((33), (34), "for any history"). Two hops, Lemma 5 at order `2λ - 1`,
Lemma 4 at order `2(λ - 1) - 1`, each through Lemma 16 (`RenyiPath.renyiMGF_simulateQ_le_path`,
auxiliary queries weigh `0`) and Lemma 15 with a parameter `T ≥ 1` (`RenyiPath.lemma15`). `theorem1`
(worst case): per-call bounds `Δτ`, `Δt` and at most `N` SamplerZ calls along every execution. -/

@[expose] public section

open MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.FalconGame

/-- The experiment's oracles: auxiliary oracles and SamplerZ calls (integer answers). -/
@[reducible] def spec {ιA : Type} (aux : OracleSpec.{0, 0} ιA) (Q : Type) : OracleSpec (ιA ⊕ Q) :=
  Sum.elim aux fun _ => ℤ

/-- A Rényi divergence bound `exp E` is an MGF bound `exp((a-1)E)`. -/
theorem renyiMGF_le_of_renyiDiv_le {α : Type*} [MeasurableSpace α] {a : ℝ} (ha : 1 < a)
    {μ ν : Measure α} {E : ℝ}
    (h : renyiDiv a μ ν ≤ ENNReal.ofReal (Real.exp E)) :
    renyiMGF a μ ν ≤ ENNReal.ofReal (Real.exp ((a - 1) * E)) := by
  have ham : a - 1 ≠ 0 := by linarith
  rw [renyiDiv_eq_rpow ha] at h
  calc renyiMGF a μ ν = (renyiMGF a μ ν ^ (a - 1)⁻¹) ^ (a - 1) := (ENNReal.rpow_inv_rpow ham _).symm
    _ ≤ ENNReal.ofReal (Real.exp E) ^ (a - 1) := ENNReal.rpow_le_rpow h (by linarith)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith), ← Real.exp_mul,
            mul_comm]

/-- `exp E ≤ rᴺ` gives the joint MGF budget of Lemma 15. -/
theorem budget {a : ℝ} (ha : 1 < a) {E r : ℝ} (hr : 0 ≤ r) {N : ℕ} (h : Real.exp E ≤ r ^ N) :
    ENNReal.ofReal (Real.exp ((a - 1) * E)) ≤ (ENNReal.ofReal r ^ N) ^ (a - 1) := by
  rw [← ENNReal.ofReal_pow hr, ENNReal.ofReal_rpow_of_nonneg (by positivity)
      (by linarith), mul_comm,
    Real.exp_mul]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Real.exp_pos _).le h (by linarith))

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [hA : ∀ t, Countable (aux t)] {Q : Type}
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

instance countable_range : ∀ x, Countable ((spec aux Q).Range x)
  | .inl t => hA t
  | .inr _ => inferInstanceAs (Countable ℤ)

omit [Monad m] [LawfulMonad m] [LawfulEvalDistSemantics m] in
/-- An auxiliary query answered identically in two worlds has MGF at most `1 = exp(c·0)`. -/
theorem aux_le {a : ℝ} (ha : 1 < a) (implA : QueryImpl aux m)
    (impl₁ impl₂ : QueryImpl (spec aux Q) m)
    (h₁ : ∀ t, impl₁ (.inl t) = implA t) (h₂ : ∀ t, impl₂ (.inl t) = implA t) (c : ℝ) (w : Q → ℝ)
    (t : ιA) :
    @renyiMGF _ ⊤ a (@evalDist m _ ((spec aux Q).Range (.inl t)) ⊤ (impl₁ (.inl t)))
      (@evalDist m _ ((spec aux Q).Range (.inl t)) ⊤ (impl₂ (.inl t))) ≤
      ENNReal.ofReal (Real.exp (c * (Sum.elim (fun _ => (0 : ℝ)) w (.inl t : ιA ⊕ Q)))) := by
  rw [h₁, h₂]
  let : MeasurableSpace (aux.Range t) := ⊤
  have : MeasurableSingletonClass (aux.Range t) := ⟨fun _ => trivial⟩
  have : Countable (aux.Range t) := hA t
  have h := RenyiPath.renyiMGF_self_le ha _ (evalDist_apply_univ_le_one (implA t))
  simp only [Sum.elim_inl, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  exact h

/-- **Theorem 2 (RMSE, conditional, explicit).** -/
theorem theorem2 (lam N : ℕ) (hlam : 3 ≤ lam) (T : ℝ≥0∞) (hT : 1 ≤ T) (σ σbar t tbar : Q → ℝ)
    (τlo σlo S₁ S₂ : ℝ) (implA : QueryImpl aux m) (implE implM implF : QueryImpl (spec aux Q) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implE (.inr q)) =
        discreteGaussianMeasure (σ q) (t q))
    (hM : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implM (.inr q)) =
        discreteGaussianMeasure (σbar q) (t q))
    (hF : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implF (.inr q)) =
        discreteGaussianMeasure (σbar q) (tbar q))
    (hσ : ∀ q, 0 < σ q) (hτlo : 1 / 4 ≤ τlo)
    (hleaf : ∀ q, τlo ≤ 1 / σ q ^ 2 ∧ 1 / σ q ^ 2 ≤ (1000 / 1277) ^ 2 ∧
      τlo ≤ 1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ∧
      1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ≤ (1000 / 1277) ^ 2)
    (hσlo : 1277 / 1000 ≤ σlo) (hσbar : ∀ q, σlo ≤ σbar q)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (spec aux Q) α)
    (hS₁ : RenyiPath.PathSum
        (Sum.elim (fun _ => 0) fun q => (1 / σbar q ^ 2 - 1 / σ q ^ 2) ^ 2) oa S₁)
    (hS₂ : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun q => (tbar q - t q) ^ 2) oa S₂)
    (h35 : Real.exp
        ((2 * lam - 1) * (2 * lam) * S₁ * ((1 / 2 + 1 / 2 ^ 19) / τlo ^ 2) / (2 * (2 * lam - 2))) ≤
      (1 + 1 / (4 * N)) ^ N)
    (h36 : Real.exp ((2 * lam - 3) * S₂ / (2 * σlo ^ 2) +
      (2 * lam - 3) * (2 * lam - 2) * S₂ * (1 / 2 ^ 30) / (2 * (2 * lam - 4))) ≤
          (1 + 1 / (4 * N)) ^ N)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have hlam' : (3 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hσlo0 : 0 < σlo := lt_of_lt_of_le (by norm_num) hσlo
  have hσbar0 : ∀ q, 0 < σbar q := fun q => lt_of_lt_of_le hσlo0 (hσbar q)
  have hr : (0 : ℝ) ≤ 1 + 1 / (4 * N) := by positivity
  set K : ℝ := (1 / 2 + 1 / 2 ^ 19) / τlo ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  -- first hop: exact → intermediate (Lemma 5 per call, Lemma 16 along executions), order `2λ - 1`
  set a : ℝ := 2 * lam - 1 with ha
  have ha1 : 1 < a := by rw [ha]; linarith
  set κ₁ : ℝ := a * (a + 1) * K / (2 * (a - 1)) with hκ₁
  have hκ₁0 : 0 ≤ κ₁ :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0) (by linarith)
  have hop1 := RenyiPath.renyiMGF_simulateQ_le_path ha1 implM implE (c := (a - 1) * κ₁)
    (mul_nonneg (by linarith) hκ₁0) _ (fun x => by
      cases x with
      | inl x => exact aux_le ha1 implA implM implE hAM hAE _ _ x
      | inr q =>
        rw [hM, hE]
        have h :=
            FalconPrecision.NumK.renyiDiv_scale_le_falcon (σ q) (σbar q) (t q) a τlo (hσ q)
                (hσbar0 q) ha1
          hτlo ⟨(hleaf q).1, (hleaf q).2.1⟩ ⟨(hleaf q).2.2.1, (hleaf q).2.2.2⟩
        refine (renyiMGF_le_of_renyiDiv_le ha1 h).trans (le_of_eq ?_)
        simp only [Sum.elim_inr]
        congr 2
        rw [hκ₁, hK]; ring) hS₁
  have hP1 : renyiMGF a 𝒟[simulateQ implM oa] 𝒟[simulateQ implE oa] ≤
      (ENNReal.ofReal (1 + 1 / (4 * N)) ^ N) ^ (a - 1) := by
    refine hop1.trans (le_trans (le_of_eq ?_) (budget ha1 hr (E := κ₁ * S₁) ?_))
    · congr 2; ring
    · convert h35 using 2; rw [hκ₁, ha]; ring
  -- second hop: intermediate → fixed point (Lemma 4 per call), order `2(λ - 1) - 1`
  set a' : ℝ := 2 * lam - 3 with ha'
  have ha'1 : 1 < a' := by rw [ha']; linarith
  set κ₂ : ℝ := a' / (2 * σlo ^ 2) + a' * (a' + 1) * (1 / 2 ^ 30) / (2 * (a' - 1)) with hκ₂
  have hκ₂0 : 0 ≤ κ₂ := by
    rw [hκ₂]
    have : 0 ≤ a' * (a' + 1) * (1 / 2 ^ 30) / (2 * (a' - 1)) := by apply div_nonneg <;> nlinarith
    have : 0 ≤ a' / (2 * σlo ^ 2) := by apply div_nonneg <;> nlinarith
    linarith
  have hop2 := RenyiPath.renyiMGF_simulateQ_le_path ha'1 implF implM (c := (a' - 1) * κ₂)
    (mul_nonneg (by linarith) hκ₂0) _ (fun x => by
      cases x with
      | inl x => exact aux_le ha'1 implA implF implM hAF hAM _ _ x
      | inr q =>
        rw [hF, hM]
        have hT := FalconPrecision.NumTail.falcon_tail (σbar q) (hσlo.trans (hσbar q))
        have h :=
            FalconPrecision.Lemma4.renyiDiv_shift_le (σbar q) (t q)
                (tbar q - t q) a' (hσbar0 q) ha'1 hT.1
        rw [add_sub_cancel] at h
        refine (renyiMGF_le_of_renyiDiv_le ha'1 h).trans
            (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
        simp only [Sum.elim_inr]
        have hσ2 : σlo ^ 2 ≤ σbar q ^ 2 := pow_le_pow_left₀ hσlo0.le (hσbar q) 2
        have hd : 0 < 2 * (a' - 1) := by linarith
        have h1 : a' * (tbar q - t q) ^ 2 / (2 * σbar q ^ 2) ≤ a' / (2 * σlo ^ 2) *
            (tbar q - t q) ^ 2 := by
          rw [show a' / (2 * σlo ^ 2) * (tbar q - t q) ^ 2 = a' * (tbar q - t q) ^ 2 /
              (2 * σlo ^ 2) by ring]
          gcongr
        have h2 : a' * (a' + 1) * (tbar q - t q) ^ 2 * FalconPrecision.ThetaTail.M (σbar q) /
            (2 * (a' - 1)) ≤
            a' * (a' + 1) * (1 / 2 ^ 30) / (2 * (a' - 1)) * (tbar q - t q) ^ 2 := by
          rw [show a' * (a' + 1) * (1 / 2 ^ 30) / (2 * (a' - 1)) * (tbar q - t q) ^ 2 =
            a' * (a' + 1) * ((tbar q - t q) ^ 2 * (1 / 2 ^ 30)) / (2 * (a' - 1)) by ring,
            show a' * (a' + 1) * (tbar q - t q) ^ 2 * FalconPrecision.ThetaTail.M (σbar q) =
              a' * (a' + 1) * ((tbar q - t q) ^ 2 * FalconPrecision.ThetaTail.M (σbar q)) by ring]
          have : 0 ≤ a' * (a' + 1) := by nlinarith
          gcongr
          exact hT.2
        have : (a' - 1) * (a' * (tbar q - t q) ^ 2 / (2 * σbar q ^ 2) +
            a' * (a' + 1) * (tbar q - t q) ^ 2 * FalconPrecision.ThetaTail.M (σbar q) /
                (2 * (a' - 1))) ≤
            (a' - 1) * (κ₂ * (tbar q - t q) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          rw [hκ₂, add_mul]; linarith
        linarith) hS₂
  have hP2 : renyiMGF a' 𝒟[simulateQ implF oa] 𝒟[simulateQ implM oa] ≤
      (ENNReal.ofReal (1 + 1 / (4 * N)) ^ N) ^ (a' - 1) := by
    refine hop2.trans (le_trans (le_of_eq ?_) (budget ha'1 hr (E := κ₂ * S₂) ?_))
    · congr 2; ring
    · convert h36 using 2; rw [hκ₂, ha']; ring
  have hc1 : ((lam - 1 : ℕ) : ℝ) = lam - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hmid := RenyiPath.lemma15 (lam - 1) (by omega) N T hT _ _
    (by rw [hc1, show 2 * ((lam : ℝ) - 1) - 1 = a' by rw [ha']; ring]; exact hP2) hs
    (by rw [hc1]; convert hwin using 4; ring)
  rw [hc1] at hmid
  exact RenyiPath.lemma15 lam (by omega) N T hT _ _ hP1 hs (by convert hmid using 4)

/--
**Theorem 1 (worst case, conditional, explicit)**: per-call `|1/σ̄² - 1/σ²| ≤ Δτ`, `|t̄ - t| ≤ Δt`,
at most `N` SamplerZ calls along every execution, and explicit-constant forms of conditions (26),
(27) per call. -/
theorem theorem1 (lam N : ℕ) (hlam : 3 ≤ lam) (T : ℝ≥0∞) (hT : 1 ≤ T) (σ σbar t tbar : Q → ℝ)
    (τlo σlo Δτ Δt : ℝ) (implA : QueryImpl aux m) (implE implM implF : QueryImpl (spec aux Q) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implE (.inr q)) =
        discreteGaussianMeasure (σ q) (t q))
    (hM : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implM (.inr q)) =
        discreteGaussianMeasure (σbar q) (t q))
    (hF : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implF (.inr q)) =
        discreteGaussianMeasure (σbar q) (tbar q))
    (hσ : ∀ q, 0 < σ q) (hτlo : 1 / 4 ≤ τlo)
    (hleaf : ∀ q, τlo ≤ 1 / σ q ^ 2 ∧ 1 / σ q ^ 2 ≤ (1000 / 1277) ^ 2 ∧
      τlo ≤ 1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ∧
      1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ≤ (1000 / 1277) ^ 2)
    (hσlo : 1277 / 1000 ≤ σlo) (hσbar : ∀ q, σlo ≤ σbar q)
    (hΔτ : ∀ q, |1 / σbar q ^ 2 - 1 / σ q ^ 2| ≤ Δτ) (hΔt : ∀ q, |tbar q - t q| ≤ Δt)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (spec aux Q) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa N)
    (h26 : Real.exp ((2 * lam - 1) * (2 * lam) * Δτ ^ 2 * ((1 / 2 + 1 / 2 ^ 19) / τlo ^ 2) /
      (2 * (2 * lam - 2))) ≤ 1 + 1 / (4 * N))
    (h27 : Real.exp ((2 * lam - 3) * Δt ^ 2 / (2 * σlo ^ 2) +
      (2 * lam - 3) * (2 * lam - 2) * Δt ^ 2 * (1 / 2 ^ 30) / (2 * (2 * lam - 4))) ≤ 1 + 1 /
          (4 * N))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have hsq : ∀ {x D : ℝ}, |x| ≤ D → x ^ 2 ≤ D ^ 2 :=
      fun h => sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  have hpow : ∀ E : ℝ, Real.exp E ≤ 1 + 1 / (4 * N) → Real.exp (N * E) ≤ (1 + 1 / (4 * N)) ^ N :=
    fun E h => by rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (Real.exp_pos _).le h N
  refine theorem2 lam N hlam T hT σ σbar t tbar τlo σlo (Δτ ^ 2 * N)
      (Δt ^ 2 * N) implA implE implM implF hAE hAM hAF
    hE hM hF hσ hτlo hleaf hσlo hσbar oa
    (hN.mono (sq_nonneg _) fun x => by
      cases x with
      | inl _ => simp
      | inr q => simpa using hsq (hΔτ q))
    (hN.mono (sq_nonneg _) fun x => by
      cases x with
      | inl _ => simp
      | inr q => simpa using hsq (hΔt q))
    ((le_of_eq (by congr 1; ring)).trans (hpow _ h26))
    ((le_of_eq (by congr 1; ring)).trans (hpow _ h27)) hs hwin

end FalconPrecision.FalconGame
