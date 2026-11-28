/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignWordHop1024

/-! # Keys passing the check are `SampKey`s

`CTree.leavesB_of_okB`: a stored tree passing `CTree.okB σlo Λq` has its leaves in the range of
every `P : SampParams` with `P.σmin = σlo` and `P.σmax = 18205 / 10000` (the leaf test of `okB` is
the range test `inRangeB P`). So a key passing `check` (resp. `check1024`) has its stored leaves in
`falcon512S`'s (resp. `falcon1024S`'s) range: `CheckedKey.toSampKey`,
`sampKeyEquiv : SampKey P n δq ≃ CheckedKey P n δq` and `CheckedKey1024.toSampKey1024`,
`sampKey1024Equiv : SampKey1024 P n δq ≃ CheckedKey1024 P n δq`.

`toSamp`, `toSamp1024`: an experiment on checked keys as one on `SampKey`s (resp. `SampKey1024`s);
forgetting the range again gives the experiment back (`embedS_toSamp`, `embedS_toSamp1024`), with
the same signing-query count (`pathSum_toSamp`, `pathSum_toSamp1024`) and the same executable
world (`exec_toSamp`, `exec_toSamp1024`).

`falcon512_exec_sampler_vs_true_checked`, `falcon1024_exec_sampler_vs_true_checked`,
`falcon1024_exec_sampler_vs_true256_checked` and the instances `falcon1024_exec_sampler_vs_true43`,
`…127`, `…256_43`, `…256_127` with suffix `_checked`: the composed theorems of `Exec.SamplerHop`
and `Exec.SamplerHop1024` for experiments on checked raw keys (`specK`, `specK1024`), with the
executable signer's world `execImpl` (resp. `execImpl1024`) and the embedding `embed`
(resp. `embed1024`); no hypothesis on the stored leaves. Every other hypothesis and caveat is that
of the original theorem (the λ = 256 statements are meaningful only with shift rejection).

Word signers: `rKeyEquiv : RKey C i δq ≃ CheckedRKey C i δq` (keys passing `check` and
`checkRange C i 19`) and `rKey1024Equiv` (keys passing `check1024` and
`checkRange C i 19 · σ1024q`); `toR`, `toR1024` with `embedR_toR`, `pathSum_toR`, `exec_toR` (and
`1024`); the word theorems of `Exec.SignWordHop` and `Exec.SignWordHop1024` on such keys:
`falcon512_exec_word_sampler_vs_true`, `falcon1024_exec_word_sampler_vs_true`,
`falcon1024_exec_word_sampler_vs_true256` with suffix `_checked` (`1 ≤ i ≤ 64` at Falcon-512,
`27 ≤ i ≤ 64` at Falcon-1024; every other hypothesis and caveat of the original).

Not proved here: that any key passes `check` or `check1024` (`#eval` runs of `checkFast` on
round-3 KAT keys are not kernel proofs), nor `checkRange`. -/

@[expose] public section

open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact
  FalconPrecision.Errors.FFTRec
open scoped ENNReal

namespace FalconPrecision.Exec

/-- **The leaf test of `okB` is a range test**: a stored tree passing `CTree.okB σlo Λq` has
every leaf in the range of `P` when `P.σmin = σlo` and `P.σmax = 18205 / 10000`. -/
theorem CTree.leavesB_of_okB {σlo : ℚ} {Λq : ℕ → ℚ} {P : SampParams} (hlo : P.σmin = σlo)
    (hhi : P.σmax = 18205 / 10000) : {L : ℕ} → (T : CTree 64 L) → T.okB σlo Λq = true →
    T.leavesB (inRangeB P) = true
  | _, .leaf σ, h => by simpa only [CTree.okB, CTree.leavesB, inRangeB, hlo, hhi] using h
  | _, .node _ T0 T1, h => by
    simp only [CTree.okB, Bool.and_eq_true] at h
    simp only [CTree.leavesB, Bool.and_eq_true]
    exact ⟨leavesB_of_okB hlo hhi T0 h.1.2, leavesB_of_okB hlo hhi T1 h.2⟩

/-- A key passing `check` has its stored leaves in `falcon512S`'s range. -/
theorem CheckedKey.leavesB_inRange {P : XChoices} {n : ℕ} {δq : ℕ → ℚ} (k : CheckedKey P n δq) :
    (storeC P n k.1).leavesB (inRangeB falcon512S) = true :=
  CTree.leavesB_of_okB (by norm_num [falcon512S]) rfl (storeC P n k.1 σ512q)
    (storeB_centreP P n k.1 σ512q ▸ (check_ok P n k.2).ok)

/-- A key passing `check` as a `SampKey`. -/
def CheckedKey.toSampKey {P : XChoices} {n : ℕ} {δq : ℕ → ℚ} (k : CheckedKey P n δq) :
    SampKey P n δq :=
  ⟨k, k.leavesB_inRange⟩

/-- **`SampKey`s are the keys passing `check`.** -/
def sampKeyEquiv (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) : SampKey P n δq ≃ CheckedKey P n δq where
  toFun k := k.1
  invFun k := k.toSampKey
  left_inv _ := rfl
  right_inv _ := rfl

/-- A key passing `check1024` has its stored leaves in `falcon1024S`'s range. -/
theorem CheckedKey1024.leavesB_inRange {P : XChoices} {n : ℕ} {δq : ℕ → ℚ}
    (k : CheckedKey1024 P n δq) :
    (storeC P n k.1 σ1024q).leavesB (inRangeB falcon1024S) = true :=
  CTree.leavesB_of_okB (by norm_num [falcon1024S, sampS, params1024]) rfl
    (storeC P n k.1 params1024.σq) (storeB_centreP P n k.1 params1024.σq ▸ (check_ok P n k.2).ok)

/-- A key passing `check1024` as a `SampKey1024`. -/
def CheckedKey1024.toSampKey1024 {P : XChoices} {n : ℕ} {δq : ℕ → ℚ}
    (k : CheckedKey1024 P n δq) : SampKey1024 P n δq :=
  ⟨k, k.leavesB_inRange⟩

/-- **`SampKey1024`s are the keys passing `check1024`.** -/
def sampKey1024Equiv (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) :
    SampKey1024 P n δq ≃ CheckedKey1024 P n δq where
  toFun k := k.1
  invFun k := k.toSampKey1024
  left_inv _ := rfl
  right_inv _ := rfl

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-! ## Experiments on checked keys as experiments on `SampKey`s -/

/-- `CheckedKey` queries as `SampKey` queries. -/
def toSampImpl (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specK P n aux δq) (OracleComp (specKS P n aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specKS P n aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specKS P n aux δq) (.inr (kc.1.toSampKey, kc.2)))

/-- An experiment on `CheckedKey`s as one on `SampKey`s. -/
def toSamp (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type} (oe : OracleComp (specK P n aux δq) α) :
    OracleComp (specKS P n aux δq) α :=
  simulateQ (toSampImpl P n δq) oe

/-- **Node.** Forgetting the leaf range of `toSamp` gives the experiment back. -/
theorem embedS_toSamp (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specK P n aux δq) α) : embedS P n δq (toSamp P n δq oe) = oe := by
  induction oe using OracleComp.inductionOn with
  | pure x => simp only [embedS, toSamp, simulateQ_pure]
  | query_bind t k ih =>
    simp only [embedS, toSamp] at ih
    simp only [embedS, toSamp, simulateQ_bind, simulateQ_spec_query, ih]
    rcases t with x | kc
    · exact congrArg (· >>= k)
        (simulateQ_spec_query (impl := embedSImpl P n δq) (Sum.inl x))
    · exact congrArg (· >>= k)
        (simulateQ_spec_query (impl := embedSImpl P n δq) (Sum.inr (kc.1.toSampKey, kc.2)))

/-- **Node.** `toSamp` keeps the signing-query count. -/
theorem pathSum_toSamp (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specK P n aux δq) α} {S : ℝ} (h : PathSum (wKC P n δq) oe S) :
    PathSum (wKS P n δq) (toSamp P n δq oe) S := by
  have h1 := pathSum_simulateQ_impl (toSampImpl P n δq) (w := wKS P n δq) (c := 1) zero_le_one
    (fun t => by rcases t with x | kc <;> exact pathSum_query _ (by simp [wKC, wKS])) h
  rwa [one_mul] at h1

/-- **Node.** The executable world on `toSamp oe` is the executable world on `oe`. -/
theorem exec_toSamp (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specK C.x C.xn aux δq) α) :
    simulateQ (execImplS C δq implA samp) (toSamp C.x C.xn δq oe) =
      simulateQ (execImpl C δq implA samp) oe := by
  rw [embedS_exec, embedS_toSamp]

/-- `CheckedKey1024` queries as `SampKey1024` queries. -/
def toSampImpl1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specK1024 P n aux δq) (OracleComp (specKS1024 P n aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specKS1024 P n aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specKS1024 P n aux δq)
      (.inr (kc.1.toSampKey1024, kc.2)))

/-- An experiment on `CheckedKey1024`s as one on `SampKey1024`s. -/
def toSamp1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specK1024 P n aux δq) α) : OracleComp (specKS1024 P n aux δq) α :=
  simulateQ (toSampImpl1024 P n δq) oe

/-- **Node.** Forgetting the leaf range of `toSamp1024` gives the experiment back. -/
theorem embedS_toSamp1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specK1024 P n aux δq) α) :
    embedS1024 P n δq (toSamp1024 P n δq oe) = oe := by
  induction oe using OracleComp.inductionOn with
  | pure x => simp only [embedS1024, toSamp1024, simulateQ_pure]
  | query_bind t k ih =>
    simp only [embedS1024, toSamp1024] at ih
    simp only [embedS1024, toSamp1024, simulateQ_bind, simulateQ_spec_query, ih]
    rcases t with x | kc
    · exact congrArg (· >>= k)
        (simulateQ_spec_query (impl := embedSImpl1024 P n δq) (Sum.inl x))
    · exact congrArg (· >>= k)
        (simulateQ_spec_query (impl := embedSImpl1024 P n δq)
          (Sum.inr (kc.1.toSampKey1024, kc.2)))

/-- **Node.** `toSamp1024` keeps the signing-query count. -/
theorem pathSum_toSamp1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specK1024 P n aux δq) α} {S : ℝ} (h : PathSum (wKC1024 P n δq) oe S) :
    PathSum (wKS1024 P n δq) (toSamp1024 P n δq oe) S := by
  have h1 := pathSum_simulateQ_impl (toSampImpl1024 P n δq) (w := wKS1024 P n δq) (c := 1)
    zero_le_one (fun t => by
      rcases t with x | kc <;> exact pathSum_query _ (by simp [wKCP, wKS1024])) h
  rwa [one_mul] at h1

/-- **Node.** The executable world on `toSamp1024 oe` is the executable world on `oe`. -/
theorem exec_toSamp1024 (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specK1024 C.x C.xn aux δq) α) :
    simulateQ (execImplS1024 C δq implA samp) (toSamp1024 C.x C.xn δq oe) =
      simulateQ (execImpl1024 C δq implA samp) oe := by
  rw [embedS_exec1024, embedS_toSamp1024]

section Hop

variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **`falcon512_exec_sampler_vs_true` on keys passing `check`**: the same statement for every
experiment `oe` on checked raw keys (`specK`), the executable signer's world `execImpl` and the
embedding `embed`; the leaf range of `SampKey` is derived from `check` (`CheckedKey.toSampKey`,
`toSamp`, `embedS_toSamp`). Every other hypothesis, and what is not proved, are those of
`falcon512_exec_sampler_vs_true`: `K ≤ 2³⁹`, `hδ`; with saturated shifts the additive `2⁻⁶¹` makes
the statement empty for success `≤ 2⁻⁶¹` and is most of the threshold for `T ≤ 2⁶⁴`; hypotheses on
ideal worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes `check`, what
`falcon512_exec_vs_true` does not prove otherwise, the PRNG (`ub` is ideal), the unbounded loop
(`fuel = 128`), SamplerZ's floating/fixed-point arithmetic (exact in `ℚ`), NIST's 79-bit table
(`tab79` is ours). -/
theorem falcon512_exec_sampler_vs_true_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : Adm C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9)
    (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (hI : ∀ σ t, inRangeB falcon512S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    (ub : ℕ → m ℕ) (hub : UnifBits ub)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK C.x C.xn aux δq) α) (hq : PathSum (wKC C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 61) <
      𝒟[simulateQ (execImpl C δq implA (samplerZ falcon512S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT _ (embed C.x C.xn δq oe))] s + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  have h := falcon512_exec_sampler_vs_true C hC hR hq77 δq K hK hδ T hT implA implE implM implF
    hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toSamp C.x C.xn δq oe)
    (pathSum_toSamp C.x C.xn δq hq) hs (by rwa [exec_toSamp])
  rwa [embedS_toSamp] at h

/-- **`falcon1024_exec_sampler_vs_true` on keys passing `check1024`**: the same statement for every
experiment `oe` on checked raw Falcon-1024 keys (`specK1024`), the executable signer's world
`execImpl1024` and the embedding `embed1024`; the leaf range of `SampKey1024` is derived from
`check1024` (`CheckedKey1024.toSampKey1024`, `toSamp1024`, `embedS_toSamp1024`). With saturated
shifts the additive `2⁻⁷⁰` makes the statement empty for success `≤ 2⁻⁷⁰` and is most of the
threshold for `T ≤ 2⁵⁵`. Every other hypothesis, and what is not proved, are those of
`falcon1024_exec_sampler_vs_true`: `AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`, `hδ`; hypotheses on
ideal worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes `check1024`,
what `falcon1024_exec_vs_true` does not prove otherwise, the PRNG (`ub` is ideal), the unbounded
loop (`fuel = 128`), SamplerZ's floating/fixed-point arithmetic (exact in `ℚ`), NIST's 79-bit table
(`tab79` is ours), more than `2²⁹` signing queries. -/
theorem falcon1024_exec_sampler_vs_true_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 29)
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
    (oe : OracleComp (specK1024 C.x C.xn aux δq) α) (hq : PathSum (wKC1024 C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImpl1024 C δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq oe))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_sampler_vs_true C hC hR hq77 δq K hK hδ T hT implA implE implM implF
    hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toSamp1024 C.x C.xn δq oe)
    (pathSum_toSamp1024 C.x C.xn δq hq) hs (by rwa [exec_toSamp1024])
  rwa [embedS_toSamp1024] at h

/-- **`falcon1024_exec_sampler_vs_true43` on keys passing `check1024`**: the same statement for
every experiment `oe` on checked raw Falcon-1024 keys (`specK1024`), the executable signer's world
`execImpl1024` and the embedding `embed1024`; the leaf range of `SampKey1024` is derived from
`check1024` (`CheckedKey1024.toSampKey1024`, `toSamp1024`, `embedS_toSamp1024`). With saturated
shifts the additive `2⁻⁷⁰` makes the statement empty for success `≤ 2⁻⁷⁰` and is most of the
threshold for `T ≤ 2⁵⁵`. Every other hypothesis, and what is not proved, are those of
`falcon1024_exec_sampler_vs_true43`: `AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`; hypotheses on ideal
worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes `check1024`, what
`falcon1024_exec_vs_true` does not prove otherwise, the PRNG (`ub` is ideal), the unbounded loop
(`fuel = 128`), SamplerZ's floating/fixed-point arithmetic (exact in `ℚ`), NIST's 79-bit table
(`tab79` is ours), more than `2²⁹` signing queries. -/
theorem falcon1024_exec_sampler_vs_true43_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77)
    (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 C.x C.xn aux δ43q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ43q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImpl1024 C δ43q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ43q_1024 oe))] s
        + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_sampler_vs_true43 C hC hR hq77 K hK T hT implA implE implM implF hAE
    hAM hAF hE hM hF sampI hsamp hI ub hub (toSamp1024 C.x C.xn δ43q_1024 oe)
    (pathSum_toSamp1024 C.x C.xn δ43q_1024 hq) hs (by rwa [exec_toSamp1024])
  rwa [embedS_toSamp1024] at h

/-- **`falcon1024_exec_sampler_vs_true127` on keys passing `check1024`**: the same statement for
every experiment `oe` on checked raw Falcon-1024 keys (`specK1024`), the executable signer's world
`execImpl1024` and the embedding `embed1024`; the leaf range of `SampKey1024` is derived from
`check1024` (`CheckedKey1024.toSampKey1024`, `toSamp1024`, `embedS_toSamp1024`). With saturated
shifts the additive `2⁻⁷⁰` makes the statement empty for success `≤ 2⁻⁷⁰` and is most of the
threshold for `T ≤ 2⁵⁵`. Every other hypothesis, and what is not proved, are those of
`falcon1024_exec_sampler_vs_true127`: `AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`; hypotheses on ideal
worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes `check1024`, what
`falcon1024_exec_vs_true` does not prove otherwise, the PRNG (`ub` is ideal), the unbounded loop
(`fuel = 128`), SamplerZ's floating/fixed-point arithmetic (exact in `ℚ`), NIST's 79-bit table
(`tab79` is ours), more than `2²⁹` signing queries. -/
theorem falcon1024_exec_sampler_vs_true127_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77)
    (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 C.x C.xn aux δ127q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImpl1024 C δ127q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ127q_1024 oe))] s
        + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_sampler_vs_true127 C hC hR hq77 K hK T hT implA implE implM implF hAE
    hAM hAF hE hM hF sampI hsamp hI ub hub (toSamp1024 C.x C.xn δ127q_1024 oe)
    (pathSum_toSamp1024 C.x C.xn δ127q_1024 hq) hs (by rwa [exec_toSamp1024])
  rwa [embedS_toSamp1024] at h

/-- **`falcon1024_exec_sampler_vs_true256` on keys passing `check1024`**: the same statement for
every experiment `oe` on checked raw Falcon-1024 keys (`specK1024`), the executable signer's world
`execImpl1024` and the embedding `embed1024`; the leaf range of `SampKey1024` is derived from
`check1024` (`CheckedKey1024.toSampKey1024`, `toSamp1024`, `embedS_toSamp1024`). Meaningful only
with shift rejection (`C.samp.shiftRej = true`, additive `0`): with saturated shifts the additive
`2⁻⁷⁰` makes the statement empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2¹⁸³`.
Every other hypothesis, and what is not proved, are those of `falcon1024_exec_sampler_vs_true256`:
`AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`, `hδ`; hypotheses on ideal worlds only (`hE`, `hM`, `hF`,
`hsamp`, `hI`); not proved: that any key passes `check1024`, what `falcon1024_exec_vs_true256`
does not prove otherwise, the PRNG (`ub` is ideal), the unbounded loop (`fuel = 128`), SamplerZ's
floating/fixed-point arithmetic (exact in `ℚ`), NIST's 79-bit table (`tab79` is ours), more than
`2²⁹` signing queries. -/
theorem falcon1024_exec_sampler_vs_true256_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 29)
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
    (oe : OracleComp (specK1024 C.x C.xn aux δq) α) (hq : PathSum (wKC1024 C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImpl1024 C δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq oe))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_sampler_vs_true256 C hC hR hq77 δq K hK hδ T hT implA implE implM
    implF hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toSamp1024 C.x C.xn δq oe)
    (pathSum_toSamp1024 C.x C.xn δq hq) hs (by rwa [exec_toSamp1024])
  rwa [embedS_toSamp1024] at h

/-- **`falcon1024_exec_sampler_vs_true256_43` on keys passing `check1024`**: the same statement for
every experiment `oe` on checked raw Falcon-1024 keys (`specK1024`), the executable signer's world
`execImpl1024` and the embedding `embed1024`; the leaf range of `SampKey1024` is derived from
`check1024` (`CheckedKey1024.toSampKey1024`, `toSamp1024`, `embedS_toSamp1024`). Meaningful only
with shift rejection (`C.samp.shiftRej = true`, additive `0`): with saturated shifts the additive
`2⁻⁷⁰` makes the statement empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2¹⁸³`.
Every other hypothesis, and what is not proved, are those of
`falcon1024_exec_sampler_vs_true256_43`: `AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`; hypotheses on
ideal worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes `check1024`,
what `falcon1024_exec_vs_true256` does not prove otherwise, the PRNG (`ub` is ideal), the
unbounded loop (`fuel = 128`), SamplerZ's floating/fixed-point arithmetic (exact in `ℚ`), NIST's
79-bit table (`tab79` is ours), more than `2²⁹` signing queries. -/
theorem falcon1024_exec_sampler_vs_true256_43_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77)
    (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 C.x C.xn aux δ43q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ43q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImpl1024 C δ43q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ43q_1024 oe))] s
        + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_sampler_vs_true256_43 C hC hR hq77 K hK T hT implA implE implM implF
    hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toSamp1024 C.x C.xn δ43q_1024 oe)
    (pathSum_toSamp1024 C.x C.xn δ43q_1024 hq) hs (by rwa [exec_toSamp1024])
  rwa [embedS_toSamp1024] at h

/-- **`falcon1024_exec_sampler_vs_true256_127` on keys passing `check1024`**: the same statement for
every experiment `oe` on checked raw Falcon-1024 keys (`specK1024`), the executable signer's world
`execImpl1024` and the embedding `embed1024`; the leaf range of `SampKey1024` is derived from
`check1024` (`CheckedKey1024.toSampKey1024`, `toSamp1024`, `embedS_toSamp1024`). Meaningful only
with shift rejection (`C.samp.shiftRej = true`, additive `0`): with saturated shifts the additive
`2⁻⁷⁰` makes the statement empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2¹⁸³`.
Every other hypothesis, and what is not proved, are those of
`falcon1024_exec_sampler_vs_true256_127`: `AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`; hypotheses on
ideal worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes `check1024`,
what `falcon1024_exec_vs_true256` does not prove otherwise, the PRNG (`ub` is ideal), the
unbounded loop (`fuel = 128`), SamplerZ's floating/fixed-point arithmetic (exact in `ℚ`), NIST's
79-bit table (`tab79` is ours), more than `2²⁹` signing queries. -/
theorem falcon1024_exec_sampler_vs_true256_127_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : AdmN 10 C) (hR : C.rchk = none) (hq77 : C.qinv = .w77)
    (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specK1024 C.x C.xn aux δ127q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImpl1024 C δ127q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ127q_1024 oe))] s
        + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_sampler_vs_true256_127 C hC hR hq77 K hK T hT implA implE implM implF
    hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toSamp1024 C.x C.xn δ127q_1024 oe)
    (pathSum_toSamp1024 C.x C.xn δ127q_1024 hq) hs (by rwa [exec_toSamp1024])
  rwa [embedS_toSamp1024] at h

end Hop

/-! ## Word signers on checked keys -/

/-- Raw keys passing `check` and `checkRange C i 19`. -/
def CheckedRKey (C : Choices) (i : ℕ) (δq : ℕ → ℚ) : Type :=
  {k : RawKey // check C.x C.xn δq k = true ∧ checkRange C i 19 k = true}

/-- A key passing `check` and `checkRange C i 19` as an `RKey`. -/
def CheckedRKey.toRKey {C : Choices} {i : ℕ} {δq : ℕ → ℚ} (k : CheckedRKey C i δq) :
    RKey C i δq :=
  ⟨CheckedKey.toSampKey ⟨k.1, k.2.1⟩, k.2.2⟩

/-- **`RKey`s are the keys passing `check` and `checkRange C i 19`.** -/
def rKeyEquiv (C : Choices) (i : ℕ) (δq : ℕ → ℚ) : RKey C i δq ≃ CheckedRKey C i δq where
  toFun k := ⟨k.1.1.1, k.1.1.2, k.2⟩
  invFun := CheckedRKey.toRKey
  left_inv _ := rfl
  right_inv _ := rfl

/-- Experiment oracles: auxiliary oracles and a signing oracle on `CheckedRKey`s. -/
@[reducible] def specKCR (C : Choices) (i : ℕ) (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (CheckedRKey C i δq × (Fin (2 ^ 9) → ℤ))) :=
  Sum.elim aux fun _ => Sig

/-- One per signing query. -/
def wKCR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    ιA ⊕ (CheckedRKey C i δq × (Fin (2 ^ 9) → ℤ)) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

/-- `CheckedRKey` queries as `CheckedKey` queries. -/
def embedCRImpl (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKCR C i aux δq) (OracleComp (specK C.x C.xn aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specK C.x C.xn aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specK C.x C.xn aux δq)
      (.inr (⟨kc.1.1, kc.1.2.1⟩, kc.2)))

/-- An experiment on `CheckedRKey`s as one on `CheckedKey`s. -/
def embedCR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specKCR C i aux δq) α) : OracleComp (specK C.x C.xn aux δq) α :=
  simulateQ (embedCRImpl C i δq) oe

/-- The signer whose attempts run on `(i + 64)`-bit words, on `CheckedRKey`s. -/
def execImplCR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) : QueryImpl (specKCR C i aux δq) m
  | .inl x => implA x
  | .inr kc => signX { C with word := some i } samp (storeC C.x C.xn kc.1.1) kc.1.1 kc.2

/-- `CheckedRKey` queries as `RKey` queries. -/
def toRImpl (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKCR C i aux δq) (OracleComp (specKR C i aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specKR C i aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specKR C i aux δq)
      (.inr (CheckedRKey.toRKey kc.1, kc.2)))

/-- An experiment on `CheckedRKey`s as one on `RKey`s. -/
def toR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type} (oe : OracleComp (specKCR C i aux δq) α) :
    OracleComp (specKR C i aux δq) α :=
  simulateQ (toRImpl C i δq) oe

/-- **Node.** Forgetting the leaf range and the range check of `toR` gives `embedCR`. -/
theorem embedR_toR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specKCR C i aux δq) α) :
    embedS C.x C.xn δq (embedR C i δq (toR C i δq oe)) = embedCR C i δq oe := by
  induction oe using OracleComp.inductionOn with
  | pure x => simp only [embedS, embedR, toR, embedCR, simulateQ_pure]
  | query_bind t k ih =>
    simp only [embedS, embedR, toR, embedCR] at ih
    simp only [embedS, embedR, toR, embedCR, simulateQ_bind,
      simulateQ_spec_query, ih]
    rcases t with x | kc
    · exact congrArg (· >>= fun u => simulateQ (embedCRImpl C i δq) (k u))
        ((congrArg (simulateQ (embedSImpl C.x C.xn δq))
          (simulateQ_spec_query (embedRImpl C i δq) (Sum.inl x))).trans
          (simulateQ_spec_query (embedSImpl C.x C.xn δq) (Sum.inl x)))
    · exact congrArg (· >>= fun u => simulateQ (embedCRImpl C i δq) (k u))
        ((congrArg (simulateQ (embedSImpl C.x C.xn δq))
          (simulateQ_spec_query (embedRImpl C i δq)
            (Sum.inr (CheckedRKey.toRKey kc.1, kc.2)))).trans
          (simulateQ_spec_query (embedSImpl C.x C.xn δq)
            (Sum.inr ((CheckedRKey.toRKey kc.1).1, kc.2))))

/-- **Node.** `toR` keeps the signing-query count. -/
theorem pathSum_toR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKCR C i aux δq) α} {S : ℝ} (h : PathSum (wKCR C i δq) oe S) :
    PathSum (wKR C i δq) (toR C i δq oe) S := by
  have h1 := pathSum_simulateQ_impl (toRImpl C i δq) (w := wKR C i δq) (c := 1) zero_le_one
    (fun t => by rcases t with x | kc <;> exact pathSum_query _ (by simp [wKCR, wKR])) h
  rwa [one_mul] at h1

/-- **Node.** The word signer's world on `toR oe` is the word signer's world on `oe`. -/
theorem exec_toR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    [LawfulMonad m] (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specKCR C i aux δq) α) :
    simulateQ (execImplR C i δq implA samp) (toR C i δq oe) =
      simulateQ (execImplCR C i δq implA samp) oe := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := execImplCR C i δq implA samp)
    (fun t => ?_) oe
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := execImplR C i δq implA samp) (Sum.inl x)
  · exact simulateQ_spec_query (impl := execImplR C i δq implA samp)
      (Sum.inr (CheckedRKey.toRKey kc.1, kc.2))

/-- Raw keys passing `check1024` and `checkRange C i 19 · σ1024q`. -/
def CheckedRKey1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) : Type :=
  {k : RawKey 10 // check1024 C.x C.xn δq k = true ∧ checkRange C i 19 k σ1024q = true}

/-- A key passing `check1024` and `checkRange C i 19 · σ1024q` as an `RKey1024`. -/
def CheckedRKey1024.toRKey1024 {C : Choices} {i : ℕ} {δq : ℕ → ℚ} (k : CheckedRKey1024 C i δq) :
    RKey1024 C i δq :=
  ⟨CheckedKey1024.toSampKey1024 ⟨k.1, k.2.1⟩, k.2.2⟩

/-- **`RKey1024`s are the keys passing `check1024` and `checkRange C i 19 · σ1024q`.** -/
def rKey1024Equiv (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    RKey1024 C i δq ≃ CheckedRKey1024 C i δq where
  toFun k := ⟨k.1.1.1, k.1.1.2, k.2⟩
  invFun := CheckedRKey1024.toRKey1024
  left_inv _ := rfl
  right_inv _ := rfl

/-- Experiment oracles: auxiliary oracles and a signing oracle on `CheckedRKey1024`s. -/
@[reducible] def specKCR1024 (C : Choices) (i : ℕ) (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (CheckedRKey1024 C i δq × (Fin (2 ^ 10) → ℤ))) :=
  Sum.elim aux fun _ => Sig 10

/-- One per signing query. -/
def wKCR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    ιA ⊕ (CheckedRKey1024 C i δq × (Fin (2 ^ 10) → ℤ)) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

/-- `CheckedRKey1024` queries as `CheckedKey1024` queries. -/
def embedCRImpl1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKCR1024 C i aux δq) (OracleComp (specK1024 C.x C.xn aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specK1024 C.x C.xn aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specK1024 C.x C.xn aux δq)
      (.inr (⟨kc.1.1, kc.1.2.1⟩, kc.2)))

/-- An experiment on `CheckedRKey1024`s as one on `CheckedKey1024`s. -/
def embedCR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specKCR1024 C i aux δq) α) : OracleComp (specK1024 C.x C.xn aux δq) α :=
  simulateQ (embedCRImpl1024 C i δq) oe

/-- The signer whose attempts run on `(i + 64)`-bit words, on `CheckedRKey1024`s. -/
def execImplCR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) :
    QueryImpl (specKCR1024 C i aux δq) m
  | .inl x => implA x
  | .inr kc => signX { C with word := some i } samp (storeC C.x C.xn kc.1.1 σ1024q) kc.1.1 kc.2

/-- `CheckedRKey1024` queries as `RKey1024` queries. -/
def toRImpl1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKCR1024 C i aux δq) (OracleComp (specKR1024 C i aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specKR1024 C i aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specKR1024 C i aux δq)
      (.inr (CheckedRKey1024.toRKey1024 kc.1, kc.2)))

/-- An experiment on `CheckedRKey1024`s as one on `RKey1024`s. -/
def toR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specKCR1024 C i aux δq) α) : OracleComp (specKR1024 C i aux δq) α :=
  simulateQ (toRImpl1024 C i δq) oe

/-- **Node.** Forgetting the leaf range and the range check of `toR1024` gives `embedCR1024`. -/
theorem embedR_toR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specKCR1024 C i aux δq) α) :
    embedS1024 C.x C.xn δq (embedR1024 C i δq (toR1024 C i δq oe)) = embedCR1024 C i δq oe := by
  induction oe using OracleComp.inductionOn with
  | pure x => simp only [embedS1024, embedR1024, toR1024, embedCR1024, simulateQ_pure]
  | query_bind t k ih =>
    simp only [embedS1024, embedR1024, toR1024, embedCR1024] at ih
    simp only [embedS1024, embedR1024, toR1024, embedCR1024, simulateQ_bind,
      simulateQ_spec_query, ih]
    rcases t with x | kc
    · exact congrArg (· >>= fun u => simulateQ (embedCRImpl1024 C i δq) (k u))
        ((congrArg (simulateQ (embedSImpl1024 C.x C.xn δq))
          (simulateQ_spec_query (embedRImpl1024 C i δq) (Sum.inl x))).trans
          (simulateQ_spec_query (embedSImpl1024 C.x C.xn δq) (Sum.inl x)))
    · exact congrArg (· >>= fun u => simulateQ (embedCRImpl1024 C i δq) (k u))
        ((congrArg (simulateQ (embedSImpl1024 C.x C.xn δq))
          (simulateQ_spec_query (embedRImpl1024 C i δq)
            (Sum.inr (CheckedRKey1024.toRKey1024 kc.1, kc.2)))).trans
          (simulateQ_spec_query (embedSImpl1024 C.x C.xn δq)
            (Sum.inr ((CheckedRKey1024.toRKey1024 kc.1).1, kc.2))))

/-- **Node.** `toR1024` keeps the signing-query count. -/
theorem pathSum_toR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKCR1024 C i aux δq) α} {S : ℝ} (h : PathSum (wKCR1024 C i δq) oe S) :
    PathSum (wKR1024 C i δq) (toR1024 C i δq oe) S := by
  have h1 := pathSum_simulateQ_impl (toRImpl1024 C i δq) (w := wKR1024 C i δq) (c := 1)
    zero_le_one
    (fun t => by rcases t with x | kc <;> exact pathSum_query _ (by simp [wKCR1024, wKR1024])) h
  rwa [one_mul] at h1

/-- **Node.** The word signer's world on `toR1024 oe` is the word signer's world on `oe`. -/
theorem exec_toR1024 (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    [LawfulMonad m] (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specKCR1024 C i aux δq) α) :
    simulateQ (execImplR1024 C i δq implA samp) (toR1024 C i δq oe) =
      simulateQ (execImplCR1024 C i δq implA samp) oe := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := execImplCR1024 C i δq implA samp)
    (fun t => ?_) oe
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := execImplR1024 C i δq implA samp) (Sum.inl x)
  · exact simulateQ_spec_query (impl := execImplR1024 C i δq implA samp)
      (Sum.inr (CheckedRKey1024.toRKey1024 kc.1, kc.2))

section HopWord

variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **`falcon512_exec_word_sampler_vs_true` on keys passing `check` and `checkRange C i 19`**
(`1 ≤ i ≤ 64`; `i = 32`: 32.64; `i = 64`: 64.64): the same statement for every experiment `oe` on
such keys (`specKCR`), the signer whose attempts run on `(i + 64)`-bit words `execImplCR` and the
embedding `embedCR`; the leaf range of `SampKey` is derived from `check` (`rKeyEquiv`, `toR`,
`embedR_toR`). Every other hypothesis, and what is not proved, are those of
`falcon512_exec_word_sampler_vs_true`: `K ≤ 2³⁹`, `hδ`; with saturated shifts the additive `2⁻⁶¹`
makes the statement empty for success `≤ 2⁻⁶¹` and is most of the threshold for `T ≤ 2⁶⁴`;
hypotheses on ideal worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes
`check` or `checkRange` (computed for round-3 KAT keys, not proved), what
`falcon512_exec_sampler_vs_true` does not prove otherwise, key expansion `storeC` on words
(unbounded `Int`: words reduce only the attempt `signX`). -/
theorem falcon512_exec_word_sampler_vs_true_checked [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : Adm C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (i : ℕ) (hi : 1 ≤ i)
    (hi64 : i ≤ 64) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9)
    (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (hI : ∀ σ t, inRangeB falcon512S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    (ub : ℕ → m ℕ) (hub : UnifBits ub)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specKCR C i aux δq) α) (hq : PathSum (wKCR C i δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 61) <
      𝒟[simulateQ (execImplCR C i δq implA (samplerZ falcon512S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT _ (embed C.x C.xn δq (embedCR C i δq oe)))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  have h := falcon512_exec_word_sampler_vs_true C hC hR hq77 i hi hi64 δq K hK hδ T hT implA
    implE implM implF hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toR C i δq oe)
    (pathSum_toR C i δq hq) hs (by rwa [exec_toR])
  rwa [embedR_toR] at h

/-- **`falcon1024_exec_word_sampler_vs_true` on keys passing `check1024` and
`checkRange C i 19 · σ1024q`** (`i = 32`: 32.64; `i = 64`: 64.64; `27 ≤ i ≤ 64`): the same
statement for every experiment `oe` on such keys (`specKCR1024`), the signer whose attempts run on
`(i + 64)`-bit words `execImplCR1024` and the embedding `embedCR1024`; the leaf range of
`SampKey1024` is derived from `check1024` (`rKey1024Equiv`, `toR1024`, `embedR_toR1024`). With
saturated shifts the additive `2⁻⁷⁰` makes the statement empty for success `≤ 2⁻⁷⁰` and is most of
the threshold for `T ≤ 2⁵⁵`. Every other hypothesis, and what is not proved, are those of
`falcon1024_exec_word_sampler_vs_true`: `AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`, `hδ`;
hypotheses on ideal worlds only (`hE`, `hM`, `hF`, `hsamp`, `hI`); not proved: that any key passes
`check1024` or `checkRange … σ1024q` (`#eval` runs on round-3 KAT keys are evidence), `i < 27` or
`i > 64`, what `falcon1024_exec_sampler_vs_true` does not prove otherwise, that a word
implementation of each operation computes `Fx.wrap` of the unbounded result, key expansion `storeC`
on words (words reduce only the attempt `signX`, not the whole signer `signMsgX`). -/
theorem falcon1024_exec_word_sampler_vs_true_checked [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKCR1024 C i aux δq) α) (hq : PathSum (wKCR1024 C i δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplCR1024 C i δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq (embedCR1024 C i δq oe)))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_word_sampler_vs_true C hC hR hq77 i hi27 hi64 δq K hK hδ T hT implA
    implE implM implF hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toR1024 C i δq oe)
    (pathSum_toR1024 C i δq hq) hs (by rwa [exec_toR1024])
  rwa [embedR_toR1024] at h

/-- **`falcon1024_exec_word_sampler_vs_true256` on keys passing `check1024` and
`checkRange C i 19 · σ1024q`** (`27 ≤ i ≤ 64`): the same statement for every experiment `oe` on
such keys (`specKCR1024`), the signer whose attempts run on `(i + 64)`-bit words `execImplCR1024`
and the embedding `embedCR1024`; the leaf range of `SampKey1024` is derived from `check1024`
(`rKey1024Equiv`, `toR1024`, `embedR_toR1024`). Meaningful only with shift rejection
(`C.samp.shiftRej = true`, additive `0`): with saturated shifts the additive `2⁻⁷⁰` makes the
statement empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2¹⁸³`. Every other
hypothesis, and what is not proved, are those of `falcon1024_exec_word_sampler_vs_true256`:
`AdmN 10 C` (by `#eval` only), `K ≤ 2²⁹`, `hδ`; hypotheses on ideal worlds only (`hE`, `hM`, `hF`,
`hsamp`, `hI`); not proved: that any key passes `check1024` or `checkRange … σ1024q` (`#eval` runs
on round-3 KAT keys are evidence), `i < 27` or `i > 64`, what `falcon1024_exec_sampler_vs_true256`
does not prove otherwise, that a word implementation of each operation computes `Fx.wrap` of the
unbounded result, key expansion `storeC` on words (words reduce only the attempt `signX`, not the
whole signer `signMsgX`). -/
theorem falcon1024_exec_word_sampler_vs_true256_checked [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKCR1024 C i aux δq) α) (hq : PathSum (wKCR1024 C i δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplCR1024 C i δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq (embedCR1024 C i δq oe)))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have h := falcon1024_exec_word_sampler_vs_true256 C hC hR hq77 i hi27 hi64 δq K hK hδ T hT
    implA implE implM implF hAE hAM hAF hE hM hF sampI hsamp hI ub hub (toR1024 C i δq oe)
    (pathSum_toR1024 C i δq hq) hs (by rwa [exec_toR1024])
  rwa [embedR_toR1024] at h

end HopWord

end FalconPrecision.Exec
