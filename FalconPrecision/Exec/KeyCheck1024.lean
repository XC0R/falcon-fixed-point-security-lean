/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.CheckFast
public import FalconPrecision.Errors.Falcon1024HopB

/-! # The per-key check at Falcon-1024, proved sound

`check1024 P n δq k` is `check` at `logn = 10` with the thresholds of `Key1024`: FFTs of `f` and
`F` within `256` and `7365`, stored leaves in `[1.298280334, 1.8205]`, stored factors
`‖ℓ̂‖ ≤ lam1024 L` (`lam1024q`), leaves of key expansion at `σ1024` (`σ1024q`); as at Falcon-512
every stored `ℓ̂` conjugate-symmetric, rounded factor radii `≤ δq L`, rounded leaf balls inside
`[1.2778, 1.825]` with relative radius `≤ 2⁻⁴²`, and `fG - gF = q` in `ℤ[x]/(x¹⁰²⁴ + 1)`.

`check1024_sound`: `check1024 P n δq k = true` gives `KeyBP.Good σ1024 δ` (`δ j = δq j`) for the
`KeyB1024` key `toKeyB1024` built from `k` (stored tree `storeC` at 64 fraction bits, true tree
exact ffLDL⋆ of `B·B⋆` at `σ1024`), by `check_soundP` at `params1024`.

`falcon1024_fixed_vs_true_checked`, `falcon1024_fixed_vs_true256_checked` and their instances at
`δ43q_1024`, `δ127q_1024`: the Falcon-1024 statements of `Falcon1024HopB` for experiments whose
signing queries carry raw keys passing `check1024` (`specK1024`), embedded by `embed1024`.
Not proved here: that any Falcon-1024 key passes `check1024` at a given `δq` and `n` (`#eval` runs
of `checkFast` on round-3 KAT keys are evidence, not kernel proofs); the word size (key expansion
in unbounded `Int`); and what the Falcon-1024 statements do not prove apart from
`KeyBP.Good σ1024 δ`. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

/-- `lam1024` as a rational. -/
def lam1024q (L : ℕ) : ℚ := if L = 9 then 320001 / 10000 else 9990 / 10000

theorem lam1024q_eq (L : ℕ) : (lam1024q L : ℝ) = lam1024 L := by
  unfold lam1024q lam1024; split_ifs <;> norm_num

theorem lam1024q_bounds (L : ℕ) : 0 ≤ lam1024q L ∧ (lam1024q L : ℝ) ≤ lam1024 L :=
  ⟨by unfold lam1024q; split_ifs <;> norm_num, (lam1024q_eq L).le⟩

/-- Falcon-1024's `σ = 168.388571447` as a rational. -/
def σ1024q : ℚ := 168388571447 / 10 ^ 9

theorem σ1024_eq : σ1024 = (σ1024q : ℝ) := by norm_num [σ1024, σ1024q]

/-- The thresholds of the Falcon-1024 check and the bounds of `KeyB1024`. -/
noncomputable def params1024 : CheckParams where
  fB := 256
  FB := 7365
  σlo := 1298280334 / 10 ^ 9
  Λq := lam1024q
  σq := σ1024q
  γf := 256
  γF := 7365
  σl := 1298280334 / 10 ^ 9
  hlo := σmin1024_ok
  Λ := lam1024
  σ := σ1024
  hf := by norm_num
  hF := by norm_num
  hσl := by norm_num
  hΛ L := ⟨by unfold lam1024q; split_ifs <;> norm_num, (lam1024q_eq L).le⟩
  hσ := σ1024_eq
  hσ0 := by norm_num [σ1024q]

variable (P : XChoices) (n : ℕ)

/-- **The per-key check at Falcon-1024** (working precision `64 + n` fraction bits). That a key
passes it is not proved for any key (`#eval` runs of `checkFast` on round-3 KAT keys are not
kernel proofs). -/
def check1024 (δq : ℕ → ℚ) (k : RawKey 10) : Bool :=
  check P n δq k 256 7365 (1298280334 / 10 ^ 9) lam1024q σ1024q

/-- `checkFast` at the Falcon-1024 thresholds is `check1024`. -/
theorem checkFast_eq1024 (δq : ℕ → ℚ) (k : RawKey 10) :
    checkFast P n δq k 256 7365 (1298280334 / 10 ^ 9) lam1024q σ1024q = check1024 P n δq k :=
  checkFast_eqP P n δq k _ _ _ _ _

/-- The `KeyB1024` of a raw key passing `check1024`: stored tree `storeC` (64 fraction bits). -/
noncomputable def toKeyB1024 (δq : ℕ → ℚ) (k : RawKey 10) (h : check1024 P n δq k = true) :
    KeyB1024 :=
  toKeyBP P n params1024 δq k h

/-- **Soundness of the Falcon-1024 check**: a raw key passing `check1024 P n δq` gives a key
passing `KeyBP.Good σ1024 δ` (`δ j = δq j`): stored tree at 64 fraction bits `storeC` real and
`Close δ` to the true tree. `check1024 … = true` is not proved for any key (`#eval` runs of
`checkFast` are not kernel proofs). -/
theorem check1024_sound (δq : ℕ → ℚ) (k : RawKey 10) (h : check1024 P n δq k = true) :
    (toKeyB1024 P n δq k h).Good σ1024 (fun j => (δq j : ℝ)) :=
  check_soundP P n params1024 δq k h

/-- Raw Falcon-1024 keys passing `check1024 P n δq`. -/
abbrev CheckedKey1024 (δq : ℕ → ℚ) : Type := CheckedKeyP P n params1024 δq 9

/-- A checked Falcon-1024 key as a key passing `KeyBP.Good σ1024`. -/
noncomputable def CheckedKey1024.toGood {P : XChoices} {n : ℕ} {δq : ℕ → ℚ}
    (k : CheckedKey1024 P n δq) : GoodKey1024 (fun j => (δq j : ℝ)) :=
  CheckedKeyP.toGood k

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- Experiment oracles at Falcon-1024: auxiliary oracles and a signing oracle on (checked raw
key, hash). -/
abbrev specK1024 (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (CheckedKey1024 P n δq × (Fin (2 ^ 10) → ℤ))) :=
  specKP P n aux params1024 δq 9

/-- One per signing query. -/
noncomputable abbrev wKC1024 (δq : ℕ → ℚ) : ιA ⊕ (CheckedKey1024 P n δq × (Fin (2 ^ 10) → ℤ)) → ℝ :=
  wKCP P n params1024 δq 9

/-- An experiment on checked raw Falcon-1024 keys as an experiment on `GoodKey1024`s. -/
noncomputable def embed1024 (δq : ℕ → ℚ) {α : Type} (oe : OracleComp (specK1024 P n aux δq) α) :
    OracleComp (specS1024 aux fun j => (δq j : ℝ)) α :=
  embedP P n params1024 δq 9 oe

theorem pathSum_embed1024 (δq : ℕ → ℚ) {α : Type} {oe : OracleComp (specK1024 P n aux δq) α}
    {K : ℝ} (h : PathSum (wKC1024 P n δq) oe K) : PathSum (wK1024 _) (embed1024 P n δq oe) K :=
  pathSum_embedP P n params1024 δq 9 h

/-- `δ43_1024` as a rational. -/
def δ43q_1024 (_L : ℕ) : ℚ := 1 / 2 ^ 43

theorem δ43q_1024_eq : (fun j => (δ43q_1024 j : ℝ)) = δ43_1024 := by
  funext j; unfold δ43q_1024 δ43_1024; norm_num

/-- `δ127_1024` as a rational. -/
def δ127q_1024 (L : ℕ) : ℚ := if L = 9 then 1 / 2 ^ 58 else 1 / 2 ^ 63

theorem δ127q_1024_eq : (fun j => (δ127q_1024 j : ℝ)) = δ127_1024 := by
  funext j; unfold δ127q_1024 δ127_1024; split_ifs <;> norm_num

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- **Fixed-point signing against exact Falcon at Falcon-1024 on checked keys**:
`falcon1024_fixed_vs_true` with the key condition `KeyBP.Good σ1024 δ` replaced by
`check1024 P n δq k = true` on every raw signing key (`δ j = δq j`, stored tree at 64 fraction
bits, key expansion at `64 + n`). Hypotheses: those of `falcon1024_fixed_vs_true` (`ρ`, `K ≤ 2²⁹`
signing-oracle calls along every execution, `K·s2B1024 41.5 δ ≤ 2⁻⁹`, SamplerZ perfect in every
world). Not proved: that a given Falcon-1024 key passes `check1024` (not proved for any key:
`#eval` runs of `checkFast` on round-3 KAT keys are not kernel proofs), at any `δq` and `n`; the
word size (unbounded `Int`); and what `falcon1024_fixed_vs_true` does not prove apart from
`KeyBP.Good σ1024 δ`. -/
theorem falcon1024_fixed_vs_true_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (δq : ℕ → ℚ) (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29)
    (hδ : (K : ℝ) * s2B1024 (83 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 P n aux δq) α) (hq : PathSum (wKC1024 P n δq) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ (embed1024 P n δq oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT1024 _ (embed1024 P n δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_fixed_vs_true ρ K hK hδ T hT implA implE implM implF hAE hAM hAF hE hM hF
    (embed1024 P n δq oe) (pathSum_embed1024 P n δq hq) hs hwin

/-- **Instance** at the uniform tree error `2⁻⁴³` (`δ43q_1024`), `K ≤ 2²⁹` (`s2B1024_43`). That a
key passes `check1024 P n δ43q_1024` is a hypothesis on every signing key (`specK1024`), not
proved for any key (`#eval` runs of `checkFast` are not kernel proofs). Other hypotheses, and what
is not proved: those of `falcon1024_fixed_vs_true_checked`. -/
theorem falcon1024_fixed_vs_true43_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 P n aux δ43q_1024) α) (hq : PathSum (wKC1024 P n δ43q_1024) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ (embed1024 P n δ43q_1024 oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 P n δ43q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
  have h0 : 0 ≤ s2B1024 (83 / 2) δ43_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true_checked P n δ43q_1024 ρ K hK ?_ T hT implA implE implM implF
    hAE hAM hAF hE hM hF oe hq hs hwin
  rw [δ43q_1024_eq]
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_43]

/-- **Instance** at the tree error `δ127q_1024` (`2⁻⁵⁸` at the root, `2⁻⁶³` below), `K ≤ 2²⁹`
(`s2B1024_127`). That a key passes `check1024 P n δ127q_1024` is a hypothesis on every signing key
(`specK1024`), not proved for any key (`#eval` runs of `checkFast` are not kernel proofs). Other
hypotheses, and what is not proved: those of `falcon1024_fixed_vs_true_checked`. -/
theorem falcon1024_fixed_vs_true127_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 P n aux δ127q_1024) α)
    (hq : PathSum (wKC1024 P n δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ (embed1024 P n δ127q_1024 oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 P n δ127q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by
    have : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
    linarith
  have h0 : 0 ≤ s2B1024 (83 / 2) δ127_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true_checked P n δ127q_1024 ρ K hK ?_ T hT implA implE implM implF
    hAE hAM hAF hE hM hF oe hq hs hwin
  rw [δ127q_1024_eq]
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_127]

/-- **Fixed-point signing against exact Falcon at Falcon-1024 on checked keys, `λ = 256` level**:
`falcon1024_fixed_vs_true256` with the key condition `KeyBP.Good σ1024 δ` replaced by
`check1024 P n δq k = true` on every raw signing key (`δ j = δq j`). Hypotheses: those of
`falcon1024_fixed_vs_true256` (`ρ`, `K ≤ 2²⁹` signing-oracle calls along every execution,
`K·s2B1024 41.5 δ ≤ 2⁻¹⁰`, SamplerZ perfect in every world). Not proved: that a given Falcon-1024
key passes `check1024` (not proved for any key: `#eval` runs of `checkFast` on round-3 KAT keys
are not kernel proofs), at any `δq` and `n`; the word size (unbounded `Int`); and what
`falcon1024_fixed_vs_true256` does not prove apart from `KeyBP.Good σ1024 δ`. -/
theorem falcon1024_fixed_vs_true256_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (δq : ℕ → ℚ) (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29)
    (hδ : (K : ℝ) * s2B1024 (83 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 10) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 P n aux δq) α) (hq : PathSum (wKC1024 P n δq) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ (embed1024 P n δq oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) < 𝒟[simulateQ implE (runT1024 _ (embed1024 P n δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_fixed_vs_true256 ρ K hK hδ T hT implA implE implM implF hAE hAM hAF hE hM hF
    (embed1024 P n δq oe) (pathSum_embed1024 P n δq hq) hs hwin

/-- **Instance** at the uniform tree error `2⁻⁴³` (`δ43q_1024`), `K ≤ 2²⁹` (`s2B1024_43`), at the
`λ = 256` level. That a key passes `check1024 P n δ43q_1024` is a hypothesis on every signing key
(`specK1024`), not proved for any key (`#eval` runs of `checkFast` are not kernel proofs). Other
hypotheses, and what is not proved: those of `falcon1024_fixed_vs_true256_checked`. -/
theorem falcon1024_fixed_vs_true256_43_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 P n aux δ43q_1024) α) (hq : PathSum (wKC1024 P n δ43q_1024) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ (embed1024 P n δ43q_1024 oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 P n δ43q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
  have h0 : 0 ≤ s2B1024 (83 / 2) δ43_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true256_checked P n δ43q_1024 ρ K hK ?_ T hT implA implE implM implF
    hAE hAM hAF hE hM hF oe hq hs hwin
  rw [δ43q_1024_eq]
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_43]

/-- **Instance** at the tree error `δ127q_1024` (`2⁻⁵⁸` at the root, `2⁻⁶³` below), `K ≤ 2²⁹`
(`s2B1024_127`), at the `λ = 256` level. That a key passes `check1024 P n δ127q_1024` is a
hypothesis on every signing key (`specK1024`), not proved for any key (`#eval` runs of `checkFast`
are not kernel proofs). Other hypotheses, and what is not proved: those of
`falcon1024_fixed_vs_true256_checked`. -/
theorem falcon1024_fixed_vs_true256_127_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 P n aux δ127q_1024) α)
    (hq : PathSum (wKC1024 P n δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ (embed1024 P n δ127q_1024 oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 P n δ127q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by
    have : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
    linarith
  have h0 : 0 ≤ s2B1024 (83 / 2) δ127_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true256_checked P n δ127q_1024 ρ K hK ?_ T hT implA implE implM
    implF hAE hAM hAF hE hM hF oe hq hs hwin
  rw [δ127q_1024_eq]
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_127]

end FalconPrecision.Exec
