/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerHop1024
public import FalconPrecision.Exec.SignWordHop
public import FalconPrecision.Exec.SignRange1024

/-! # 32.64 and 64.64 signing inside the composed security theorem at Falcon-1024

`falcon1024_exec_sampler_vs_true(256)` (`Exec.SamplerHop1024`) are stated for unbounded words
(`AdmN 10 C`: `C.word = none`). `RKey1024 C i δq`: `SampKey1024`s passing
`checkRange C i 19 · σ1024q`. On experiments over such keys the world of the signer whose attempts
run on `(i + 64)`-bit words (`27 ≤ i ≤ 64`) with the executable SamplerZ is the unbounded one on
the embedded experiment (`execR_word1024`, from `signX_word1024` and `clampS_samplerZ1024`), so
the composed theorems hold for it unchanged: `falcon1024_exec_word_sampler_vs_true`,
`falcon1024_exec_word_sampler_vs_true256` (at `i = 32`: 32.64; at `i = 64`: 64.64). The λ = 256
statement is meaningful only with shift rejection, as `falcon1024_exec_sampler_vs_true256`.
On keys passing `check1024` and `checkRange … σ1024q`:
`falcon1024_exec_word_sampler_vs_true(256)_checked` (`Exec.SampKeyCheck`).

Not proved here: what `falcon1024_exec_sampler_vs_true(256)` do not prove; that any key passes
`checkRange … σ1024q` (not proved for any key; `#eval` runs of `checkRangeA` on round-3 KAT keys are
evidence, E25); `i < 27` or `i > 64`; that a word implementation of each operation computes
`Fx.wrap` of the unbounded result; key expansion `storeC` on words (unbounded `Int`: words reduce
only the attempt `signX`, not the whole signer `signMsgX`; the signer on words: `signMsgX_word1024`,
`Exec.SignEquiv1024`). -/

@[expose] public section

open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.FFTRec
open scoped ENNReal

namespace FalconPrecision.Exec

theorem clamp_samplerLoop1024 {m : Type → Type*} [Monad m] [LawfulMonad m] (S : SampChoices)
    (ub : ℕ → m ℕ) (σ r : ℚ) (s : ℤ) :
    ∀ n, clampZ s 19 <$> samplerLoop falcon1024S S ub σ r s n =
      samplerLoop falcon1024S S ub σ r s n
  | 0 => by simp [samplerLoop, clampZ_of_abs_le]
  | n + 1 => by
    simp only [samplerLoop, map_bind]
    refine congrArg (ub 72 >>= ·) (funext fun u => congrArg (ub 8 >>= ·) (funext fun c =>
      congrArg (_ >>= ·) (funext fun a => ?_)))
    split
    · rw [map_pure, clampZ_of_abs_le (by
        rw [add_sub_cancel_left]; exact_mod_cast abs_zOf_le (z0Of_le S u c) _)]
    · exact clamp_samplerLoop1024 S ub σ r s n

/-- **SamplerZ at Falcon-1024 answers within `19` of `⌊t̄⌋`** (the tables of `falcon512S`), so
clamping it at `W = 19` changes nothing. -/
theorem clampS_samplerZ1024 {m : Type → Type*} [Monad m] [LawfulMonad m] (S : SampChoices)
    (ub : ℕ → m ℕ) : clampS 19 (samplerZ falcon1024S S ub) = samplerZ falcon1024S S ub := by
  funext σ t
  exact clamp_samplerLoop1024 S ub _ _ _ _

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- `SampKey1024`s whose signing attempt fits `(i + 64)`-bit words (`checkRange C i 19`). -/
def RKey1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) : Type :=
  {k : SampKey1024 C.x C.xn δq // checkRange C i 19 k.1.1 σ1024q = true}

/-- Experiment oracles: auxiliary oracles and a signing oracle on `RKey1024`s. -/
@[reducible] def specKR1024 (C : Choices) (i : ℕ) (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (RKey1024 C i δq × (Fin (2 ^ 10) → ℤ))) :=
  Sum.elim aux fun _ => Sig 10

/-- One per signing query. -/
def wKR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) : ιA ⊕ (RKey1024 C i δq × (Fin (2 ^ 10) → ℤ)) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

/-- `RKey1024` queries as `SampKey1024` queries. -/
def embedRImpl1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKR1024 C i aux δq) (OracleComp (specKS1024 C.x C.xn aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specKS1024 C.x C.xn aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specKS1024 C.x C.xn aux δq) (.inr (kc.1.1, kc.2)))

/-- An experiment on `RKey1024`s as one on `SampKey1024`s. -/
def embedR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specKR1024 C i aux δq) α) : OracleComp (specKS1024 C.x C.xn aux δq) α :=
  simulateQ (embedRImpl1024 C i δq) oe

/-- The signer whose attempts run on `(i + 64)`-bit words, on `RKey1024`s. -/
def execImplR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) : QueryImpl (specKR1024 C i aux δq) m
  | .inl x => implA x
  | .inr kc => signX { C with word := some i } samp (storeC C.x C.xn kc.1.1.1.1 σ1024q)
      kc.1.1.1.1 kc.2

/-- **The word world is the unbounded world** on `RKey1024` experiments, with SamplerZ at
Falcon-1024 (`27 ≤ i ≤ 64`). -/
theorem execR_word1024 (C : Choices) (hw : C.word = none) (i : ℕ) (hi27 : 27 ≤ i) (hi64 : i ≤ 64)
    (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m] (implA : QueryImpl aux m)
    (S : SampChoices) (ub : ℕ → m ℕ) {α : Type} (oe : OracleComp (specKR1024 C i aux δq) α) :
    simulateQ (execImplR1024 C i δq implA (samplerZ falcon1024S S ub)) oe =
      simulateQ (execImplS1024 C δq implA (samplerZ falcon1024S S ub)) (embedR1024 C i δq oe) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := execImplR1024 C i δq implA (samplerZ falcon1024S S ub)) (fun t => ?_) oe).symm
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := execImplS1024 C δq implA _) (Sum.inl x)
  · refine (simulateQ_spec_query (impl := execImplS1024 C δq implA _)
      (Sum.inr (kc.1.1, kc.2))).trans ?_
    have e := signX_word1024 C δq i 19 hi27 hi64 kc.1.1.1.1 kc.1.1.1.2 kc.1.2
      (samplerZ falcon1024S S ub) kc.2
    rw [clampS_samplerZ1024, with_word_none C hw] at e
    exact e.symm

/-- Forgetting the range check keeps the signing-query count. -/
theorem pathSum_embedR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKR1024 C i aux δq) α} {S : ℝ} (h : PathSum (wKR1024 C i δq) oe S) :
    PathSum (wKS1024 C.x C.xn δq) (embedR1024 C i δq oe) S := by
  have h1 := pathSum_simulateQ_impl (embedRImpl1024 C i δq) (w := wKS1024 C.x C.xn δq) (c := 1)
    zero_le_one
    (fun t => by rcases t with x | kc <;> exact pathSum_query _ (by simp [wKS1024, wKR1024])) h
  rwa [one_mul] at h1

section Hop

variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **The composed theorem at Falcon-1024 on `(i + 64)`-bit words** (`i = 32`: 32.64; `i = 64`:
64.64; `27 ≤ i ≤ 64`): `falcon1024_exec_sampler_vs_true` for experiments on keys passing
`checkRange C i 19 · σ1024q`, the executable signer whose attempts run on `(i + 64)`-bit words
running `samplerZ falcon1024S C.samp ub`. Same hypotheses, same constants. -/
theorem falcon1024_exec_word_sampler_vs_true [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (i : ℕ)
    (hi27 : 27 ≤ i) (hi64 : i ≤ 64) (δq : ℕ → ℚ) (K : ℕ) (hK : K ≤ 2 ^ 29)
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
    (sampI : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = sampI σ t)
    (hI : ∀ σ t, inRangeB falcon1024S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    (ub : ℕ → m ℕ) (hub : UnifBits ub)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specKR1024 C i aux δq) α) (hq : PathSum (wKR1024 C i δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplR1024 C i δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq
        (embedS1024 C.x C.xn δq (embedR1024 C i δq oe))))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  rw [execR_word1024 C hC.word i hi27 hi64] at hwin
  exact falcon1024_exec_sampler_vs_true C hC hR hq77 δq K hK hδ T hT implA implE implM implF
    hAE hAM hAF hE hM hF sampI hsamp hI ub hub (embedR1024 C i δq oe)
    (pathSum_embedR1024 C i δq hq) hs hwin

/-- **The composed theorem at Falcon-1024 on `(i + 64)`-bit words, `λ = 256` level**
(`27 ≤ i ≤ 64`): `falcon1024_exec_sampler_vs_true256` for experiments on keys passing
`checkRange C i 19 · σ1024q`, the signer on `(i + 64)`-bit words running
`samplerZ falcon1024S C.samp ub`. Same hypotheses, same constants; meaningful only with shift
rejection (with saturated shifts the additive `2⁻⁷⁰` makes it empty for success `≤ 2⁻⁷⁰`). -/
theorem falcon1024_exec_word_sampler_vs_true256 [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (i : ℕ)
    (hi27 : 27 ≤ i) (hi64 : i ≤ 64) (δq : ℕ → ℚ) (K : ℕ) (hK : K ≤ 2 ^ 29)
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
    (sampI : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = sampI σ t)
    (hI : ∀ σ t, inRangeB falcon1024S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    (ub : ℕ → m ℕ) (hub : UnifBits ub)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specKR1024 C i aux δq) α) (hq : PathSum (wKR1024 C i δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplR1024 C i δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq
        (embedS1024 C.x C.xn δq (embedR1024 C i δq oe))))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  rw [execR_word1024 C hC.word i hi27 hi64] at hwin
  exact falcon1024_exec_sampler_vs_true256 C hC hR hq77 δq K hK hδ T hT implA implE implM implF
    hAE hAM hAF hE hM hF sampI hsamp hI ub hub (embedR1024 C i δq oe)
    (pathSum_embedR1024 C i δq hq) hs hwin

end Hop

end FalconPrecision.Exec
