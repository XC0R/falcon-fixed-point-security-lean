/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerHop
public import FalconPrecision.Exec.SignRefine1024

/-! # The executable signer with the executable SamplerZ against exact Falcon at Falcon-1024

`SampKey1024`: raw Falcon-1024 keys passing `check1024` whose stored leaves (`storeC … σ1024q`)
are in the range `[1.298280334, 1.8205]` of `falcon1024S`. `specKS1024`, `execImplS1024`:
experiments on such keys and the executable signer's world with a sampler `samp`. `execZ1024`
factors that world through the SamplerZ oracle `specZP falcon1024S` (`exec_factor1024`); a signing
attempt makes at most `2048` SamplerZ calls (`pathSum_execZ1024`). `exec_sampler_step1024`: along
executions with at most `K ≤ 2²⁹` signing queries (`2048K ≤ 2⁴⁰` calls), success `> 2^(1/64)·θ`
(plus `2⁻⁷⁰` when shifts saturate) with `samplerZ falcon1024S C.samp ub` gives success `> θ` with an
ideal sampler, for every `θ ≥ 2⁻ᵉ`, `e ≤ 254` (`sampler_hop1024`, `thresh_samplerE`,
`samplerZ_tv1024`).

`falcon1024_exec_sampler_vs_true`, `falcon1024_exec_sampler_vs_true256`: `falcon1024_exec_vs_true`,
`falcon1024_exec_vs_true256` (`Exec.SignRefine1024`) for the executable signer running
`samplerZ falcon1024S C.samp ub` on uniform bits `ub`, with instances at `δ43q_1024` and
`δ127q_1024`. The sampler costs a factor `2^(1/64)` on the threshold and, with saturated shifts (the
spec's own SamplerZ), the additive `2⁻⁷⁰` (`2⁻¹¹⁰` per call over `2048·2²⁹` calls). That additive
makes the statements empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2⁵⁵` at the
128-bit type and for `T ≤ 2¹⁸³` at the λ = 256 level, so the λ = 256 statement is meaningful only
with shift rejection (`C.samp.shiftRej = true`, additive `0`). `exec_sampler_worlds_exist1024`
states that the ideal-world hypotheses hold together with `UnifBits` in one monad.

Not proved here: what `falcon1024_exec_vs_true(256)` do not prove, among them: `AdmN 10 C` holds
only by `#eval` (E24) and excludes multiply-first; that any key passes `check1024` is not proved for
any key (every key passing it is a `SampKey1024`: `sampKey1024Equiv`, `Exec.SampKeyCheck`); the
restart loop and the whole signer `signMsgX`; range checks; the split path and
half-spectrum storage; words (here `C.word = none`; `(i + 64)`-bit words are
`Exec.SignWordHop1024`). Also: the PRNG (`ub` is ideal); the unbounded loop (`fuel = 128`);
SamplerZ's floating/fixed-point arithmetic (`x`, `ccs`, `r` exact in `ℚ`); NIST's 79-bit table
(`tab79` is ours); more than `2²⁹` signing queries (Falcon's bound is `2⁶⁴`). -/

@[expose] public section

open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact
  FalconPrecision.Errors.FFTRec
open scoped ENNReal

namespace FalconPrecision.Exec

/-- Checked Falcon-1024 raw keys whose stored leaves are in the range of `falcon1024S`. -/
def SampKey1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) : Type :=
  {k : CheckedKey1024 P n δq // (storeC P n k.1 σ1024q).leavesB (inRangeB falcon1024S) = true}

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- Experiment oracles at Falcon-1024: auxiliary oracles and a signing oracle on `SampKey1024`s. -/
@[reducible] def specKS1024 (P : XChoices) (n : ℕ) (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (SampKey1024 P n δq × (Fin (2 ^ 10) → ℤ))) :=
  Sum.elim aux fun _ => Sig 10

/-- One per signing query. -/
def wKS1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) :
    ιA ⊕ (SampKey1024 P n δq × (Fin (2 ^ 10) → ℤ)) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

/-- `SampKey1024` queries as `CheckedKey1024` queries. -/
def embedSImpl1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKS1024 P n aux δq) (OracleComp (specK1024 P n aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specK1024 P n aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specK1024 P n aux δq) (.inr (kc.1.1, kc.2)))

/-- An experiment on `SampKey1024`s as one on `CheckedKey1024`s. -/
def embedS1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    (oe : OracleComp (specKS1024 P n aux δq) α) : OracleComp (specK1024 P n aux δq) α :=
  simulateQ (embedSImpl1024 P n δq) oe

/-- The executable signer's world on `SampKey1024`s. -/
def execImplS1024 (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) :
    QueryImpl (specKS1024 C.x C.xn aux δq) m
  | .inl x => implA x
  | .inr kc => signX C samp (storeC C.x C.xn kc.1.1.1 σ1024q) kc.1.1.1 kc.2

/-- The executable signer at Falcon-1024 with SamplerZ calls left as queries of
`specZP falcon1024S`. -/
def execZ1024 (C : Choices) (δq : ℕ → ℚ) :
    QueryImpl (specKS1024 C.x C.xn aux δq) (OracleComp (specZP falcon1024S aux))
  | .inl x => liftM (OracleSpec.query (spec := specZP falcon1024S aux) (.inl x))
  | .inr kc => signX C (sampQP falcon1024S) (storeC C.x C.xn kc.1.1.1 σ1024q) kc.1.1.1 kc.2

/-- **Node.** The executable world at Falcon-1024 factors through the SamplerZ oracle. -/
theorem exec_factor1024 (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specKS1024 C.x C.xn aux δq) α) :
    simulateQ (execImplS1024 C δq implA samp) oe =
      simulateQ (implZP falcon1024S implA samp) (simulateQ (execZ1024 C δq) oe) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := execImplS1024 C δq implA samp)
    (fun t => ?_) oe).symm
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := implZP falcon1024S implA samp) (Sum.inl x)
  · change simulateQ (implZP falcon1024S implA samp)
        (signX C (sampQP falcon1024S) (storeC C.x C.xn kc.1.1.1 σ1024q) kc.1.1.1 kc.2) =
      signX C samp (storeC C.x C.xn kc.1.1.1 σ1024q) kc.1.1.1 kc.2
    unfold signX
    split_ifs
    · rw [simulateQ_map, simulateQ_ffsXP falcon1024S C implA samp _ kc.1.2]
    · rfl

/-- **Node.** Forgetting the leaf range at Falcon-1024. -/
theorem embedS_exec1024 (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specKS1024 C.x C.xn aux δq) α) :
    simulateQ (execImplS1024 C δq implA samp) oe =
      simulateQ (execImpl1024 C δq implA samp) (embedS1024 C.x C.xn δq oe) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := execImplS1024 C δq implA samp)
    (fun t => ?_) oe).symm
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := execImpl1024 C δq implA samp) (Sum.inl x)
  · exact simulateQ_spec_query (impl := execImpl1024 C δq implA samp) (Sum.inr (kc.1.1, kc.2))

/-- **Node.** Forgetting the leaf range keeps the signing-query count. -/
theorem pathSum_embedS1024 (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKS1024 P n aux δq) α} {S : ℝ} (h : PathSum (wKS1024 P n δq) oe S) :
    PathSum (wKC1024 P n δq) (embedS1024 P n δq oe) S := by
  have h1 := pathSum_simulateQ_impl (embedSImpl1024 P n δq) (w := wKC1024 P n δq) (c := 1)
    zero_le_one (fun t => by
      rcases t with x | kc <;> exact pathSum_query _ (by simp [wKCP, wKS1024])) h
  rwa [one_mul] at h1

/-- **Node.** A signing attempt at Falcon-1024 makes at most `2048` SamplerZ calls. -/
theorem pathSum_execZ1024 (C : Choices) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKS1024 C.x C.xn aux δq) α} {K : ℝ}
    (h : PathSum (wKS1024 C.x C.xn δq) oe K) :
    PathSum (Sum.elim (fun _ => (0 : ℝ)) fun _ => 1) (simulateQ (execZ1024 C δq) oe)
      (2048 * K) := by
  refine pathSum_simulateQ_impl (execZ1024 C δq) (by norm_num) (fun t => ?_) h
  rcases t with x | kc
  · exact pathSum_query _ (by simp [wKS1024])
  · change PathSum _
      (signX C (sampQP falcon1024S) (storeC C.x C.xn kc.1.1.1 σ1024q) kc.1.1.1 kc.2) _
    unfold signX
    split_ifs
    · exact (pathSum_map _ (pathSum_ffsXP falcon1024S C _ _ _)).weaken
        (by simp [wKS1024]; norm_num)
    · exact .pure _ (by simp [wKS1024])

section Hop

variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Node** (the sampler step at Falcon-1024). Every experiment `oe` on `SampKey1024`s with at
most `K ≤ 2²⁹` signing queries along every execution, `ub` uniform bits, an ideal sampler `sampI`
on `falcon1024S`'s range (`hI`), every `θ ≥ 2⁻ᵉ`, `e ≤ 254`: success `> 2^(1/64)·θ` (plus `2⁻⁷⁰`
when shifts saturate) with the executable signer running `samplerZ falcon1024S C.samp ub` gives
success `> θ` with the executable signer's world `execImpl1024` running `sampI` on the embedded
experiment. -/
theorem exec_sampler_step1024 (C : Choices) (δq : ℕ → ℚ) (K : ℕ) (hK : K ≤ 2 ^ 29)
    (implA : QueryImpl aux m) (sampI : Fx 64 → Fx 64 → m ℤ)
    (hI : ∀ σ t, inRangeB falcon1024S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    (ub : ℕ → m ℕ) (hub : UnifBits ub)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specKS1024 C.x C.xn aux δq) α) (hq : PathSum (wKS1024 C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s) (θ : ℝ≥0∞) (e : ℕ) (he : e ≤ 254)
    (hθ : (2 : ℝ≥0∞) ^ (-(e : ℝ)) ≤ θ)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * θ +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplS1024 C δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    θ < 𝒟[simulateQ (execImpl1024 C δq implA sampI) (embedS1024 C.x C.xn δq oe)] s := by
  set S' : SampChoices := { C.samp with shiftRej := true }
  have hN := pathSum_execZ1024 C δq hq
  have hK' : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
  have hw : ∀ t, 0 ≤ (Sum.elim (fun _ => (0 : ℝ)) fun _ => 1 : ιA ⊕ SQP falcon1024S → ℝ) t :=
    fun t => by rcases t with _ | _ <;> simp
  have hεs : (0 : ℝ) ≤ if C.samp.shiftRej then 0 else 1 / 2 ^ 110 := by split_ifs <;> norm_num
  have htv := (etvDist_simulateQ_le_path (implZP falcon1024S implA (samplerZ falcon1024S C.samp ub))
    (implZP falcon1024S implA (samplerZ falcon1024S S' ub)) hεs _ hw (fun x => by
      cases x with
      | inl x =>
        exact (@Measure.etvDist_self _ ⊤ _).le.trans bot_le
      | inr p =>
        refine (samplerZ_tv1024 C.samp ub hub p.1.1 p.1.2 p.2).trans
          (ENNReal.ofReal_le_ofReal (le_of_eq (by simp))))
    hN).2
  have hle : 𝒟[simulateQ (implZP falcon1024S implA (samplerZ falcon1024S C.samp ub))
      (simulateQ (execZ1024 C δq) oe)] s ≤
      𝒟[simulateQ (implZP falcon1024S implA (samplerZ falcon1024S S' ub))
        (simulateQ (execZ1024 C δq) oe)] s +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) := by
    refine (le_add_etvDist _ _ hs).trans (add_le_add le_rfl (htv.trans
      (ENNReal.ofReal_le_ofReal ?_)))
    split_ifs
    · simp
    · calc (1 : ℝ) / 2 ^ 110 * (2048 * K) ≤ 1 / 2 ^ 110 * (2048 * 2 ^ 29) := by gcongr
        _ = 1 / 2 ^ 70 := by norm_num
  rw [exec_factor1024] at hwin
  have hR' : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * θ <
      𝒟[simulateQ (implZP falcon1024S implA (samplerZ falcon1024S S' ub))
        (simulateQ (execZ1024 C δq) oe)] s :=
    (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).1 (hwin.trans_le hle)
  have hhop := sampler_hop1024 (a := 2 ^ 14) (by norm_num) S' rfl implA ub hub sampI hI _ hN hs
  have he' : (e : ℝ) ≤ 254 := by exact_mod_cast he
  have hθ' := thresh_samplerE θ e (by omega) hθ _ (by linarith) _ _ hhop hR'
  rw [← exec_factor1024, embedS_exec1024] at hθ'
  exact hθ'

/-- **The executable signer with the executable SamplerZ against exact Falcon at Falcon-1024.**
For choices with `AdmN 10 C`, no range checks, `1/q` at 77 bits and every SamplerZ choice
`C.samp`; every experiment `oe` on `SampKey1024`s with at most `K ≤ 2²⁹` signing queries along
every execution, `K·s2B1024 41.5 δ ≤ 2⁻⁹`; `ub` uniform bits: success
`> 2^(1/64)·(T·2⁻¹²⁶ + 2⁻²⁸⁰)` (plus `2⁻⁷⁰` when shifts saturate) with the executable signer
running `samplerZ falcon1024S C.samp ub` gives success `> T·2⁻¹³¹ - 2⁻²⁸¹` with exact Falcon
signing on the true tree. With saturated shifts (the spec's own SamplerZ) the additive `2⁻⁷⁰` makes
the statement empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2⁵⁵`. Hypotheses on
ideal worlds only: those of `falcon1024_exec_vs_true` for an ideal sampler `sampI` (`hE`, `hM`,
`hF`, `hsamp`), and `hI`. Not proved: what `falcon1024_exec_vs_true` does not prove (`AdmN 10 C` by
`#eval` only; no key is proved to pass `check1024`; keys passing it are `SampKey1024`s,
`sampKey1024Equiv`); the PRNG (`ub` is ideal); the unbounded loop
(`fuel = 128`); SamplerZ's floating/fixed-point arithmetic (`x`, `ccs`, `r` exact in `ℚ`); NIST's
79-bit table (`tab79` is ours); more than `2²⁹` signing queries (Falcon's bound is `2⁶⁴`).
On checked keys: `falcon1024_exec_sampler_vs_true_checked` (`Exec.SampKeyCheck`). -/
theorem falcon1024_exec_sampler_vs_true [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKS1024 C.x C.xn aux δq) α) (hq : PathSum (wKS1024 C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplS1024 C δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq (embedS1024 C.x C.xn δq oe)))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_exec_vs_true C hC hR hq77 δq K hK hδ T hT implA implE implM implF hAE hAM hAF hE hM
    hF sampI hsamp (embedS1024 C.x C.xn δq oe) (pathSum_embedS1024 C.x C.xn δq hq) hs
    (exec_sampler_step1024 C δq K hK implA sampI hI ub hub oe hq hs _ 126 (by norm_num)
      (by rw [Nat.cast_ofNat]; exact le_add_right (le_mul_of_one_le_left (by positivity) hT))
      hwin)

/-- **Instance** of `falcon1024_exec_sampler_vs_true` at the uniform tree error `2⁻⁴³`
(`δ43q_1024`), `K ≤ 2²⁹`, by `falcon1024_exec_vs_true43`. Hypotheses, and what is not proved:
those of `falcon1024_exec_sampler_vs_true` (without `hδ`). -/
theorem falcon1024_exec_sampler_vs_true43 [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKS1024 C.x C.xn aux δ43q_1024) α)
    (hq : PathSum (wKS1024 C.x C.xn δ43q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplS1024 C δ43q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ43q_1024
        (embedS1024 C.x C.xn δ43q_1024 oe)))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_exec_vs_true43 C hC hR hq77 K hK T hT implA implE implM implF hAE hAM hAF hE hM hF
    sampI hsamp (embedS1024 C.x C.xn δ43q_1024 oe) (pathSum_embedS1024 C.x C.xn δ43q_1024 hq) hs
    (exec_sampler_step1024 C δ43q_1024 K hK implA sampI hI ub hub oe hq hs _ 126 (by norm_num)
      (by rw [Nat.cast_ofNat]; exact le_add_right (le_mul_of_one_le_left (by positivity) hT))
      hwin)

/-- **Instance** of `falcon1024_exec_sampler_vs_true` at the tree error `δ127q_1024` (`2⁻⁵⁸` at
the root, `2⁻⁶³` below), `K ≤ 2²⁹`, by `falcon1024_exec_vs_true127`. Hypotheses, and what is not
proved: those of `falcon1024_exec_sampler_vs_true` (without `hδ`). -/
theorem falcon1024_exec_sampler_vs_true127 [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKS1024 C.x C.xn aux δ127q_1024) α)
    (hq : PathSum (wKS1024 C.x C.xn δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplS1024 C δ127q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ127q_1024
        (embedS1024 C.x C.xn δ127q_1024 oe)))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_exec_vs_true127 C hC hR hq77 K hK T hT implA implE implM implF hAE hAM hAF hE hM hF
    sampI hsamp (embedS1024 C.x C.xn δ127q_1024 oe) (pathSum_embedS1024 C.x C.xn δ127q_1024 hq)
    hs (exec_sampler_step1024 C δ127q_1024 K hK implA sampI hI ub hub oe hq hs _ 126
      (by norm_num)
      (by rw [Nat.cast_ofNat]; exact le_add_right (le_mul_of_one_le_left (by positivity) hT))
      hwin)

/-- **The executable signer with the executable SamplerZ against exact Falcon at Falcon-1024,
`λ = 256` level**: `falcon1024_exec_vs_true256` for the executable signer running
`samplerZ falcon1024S C.samp ub` on uniform bits `ub`; `K ≤ 2²⁹`, `K·s2B1024 41.5 δ ≤ 2⁻¹⁰`: success
`> 2^(1/64)·(T·2⁻²⁵⁴ + 2⁻²⁸⁰)` (plus `2⁻⁷⁰` when shifts saturate) with the executable signer gives
success `> T·2⁻²⁵⁹ - 2⁻²⁸¹` with exact Falcon signing on the true tree. Meaningful only with shift
rejection (`C.samp.shiftRej = true`, additive `0`): with saturated shifts (the spec's own SamplerZ)
the additive `2⁻⁷⁰` is `2¹⁸⁴` times the threshold's term `2⁻²⁵⁴` at `T = 1`, makes the statement
empty for success `≤ 2⁻⁷⁰` and is most of the threshold for `T ≤ 2¹⁸³`. Other hypotheses and what is
not proved: those of `falcon1024_exec_sampler_vs_true`, with `falcon1024_exec_vs_true256` in place
of `falcon1024_exec_vs_true`. On checked keys: `falcon1024_exec_sampler_vs_true256_checked`. -/
theorem falcon1024_exec_sampler_vs_true256 [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKS1024 C.x C.xn aux δq) α) (hq : PathSum (wKS1024 C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplS1024 C δq implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq (embedS1024 C.x C.xn δq oe)))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_exec_vs_true256 C hC hR hq77 δq K hK hδ T hT implA implE implM implF hAE hAM hAF hE
    hM hF sampI hsamp (embedS1024 C.x C.xn δq oe) (pathSum_embedS1024 C.x C.xn δq hq) hs
    (exec_sampler_step1024 C δq K hK implA sampI hI ub hub oe hq hs _ 254 le_rfl
      (by rw [Nat.cast_ofNat]; exact le_add_right (le_mul_of_one_le_left (by positivity) hT))
      hwin)

/-- **Instance** of `falcon1024_exec_sampler_vs_true256` at the uniform tree error `2⁻⁴³`
(`δ43q_1024`), `K ≤ 2²⁹`, by `falcon1024_exec_vs_true256_43`. Meaningful only with shift
rejection (as `falcon1024_exec_sampler_vs_true256`). Hypotheses, and what is not proved: those of
`falcon1024_exec_sampler_vs_true256` (without `hδ`). -/
theorem falcon1024_exec_sampler_vs_true256_43 [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKS1024 C.x C.xn aux δ43q_1024) α)
    (hq : PathSum (wKS1024 C.x C.xn δ43q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplS1024 C δ43q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ43q_1024
        (embedS1024 C.x C.xn δ43q_1024 oe)))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_exec_vs_true256_43 C hC hR hq77 K hK T hT implA implE implM implF hAE hAM hAF hE hM
    hF sampI hsamp (embedS1024 C.x C.xn δ43q_1024 oe) (pathSum_embedS1024 C.x C.xn δ43q_1024 hq)
    hs (exec_sampler_step1024 C δ43q_1024 K hK implA sampI hI ub hub oe hq hs _ 254 le_rfl
      (by rw [Nat.cast_ofNat]; exact le_add_right (le_mul_of_one_le_left (by positivity) hT))
      hwin)

/-- **Instance** of `falcon1024_exec_sampler_vs_true256` at the tree error `δ127q_1024` (`2⁻⁵⁸` at
the root, `2⁻⁶³` below), `K ≤ 2²⁹`, by `falcon1024_exec_vs_true256_127`. Meaningful only with
shift rejection (as `falcon1024_exec_sampler_vs_true256`). Hypotheses, and what is not proved:
those of `falcon1024_exec_sampler_vs_true256` (without `hδ`). -/
theorem falcon1024_exec_sampler_vs_true256_127 [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKS1024 C.x C.xn aux δ127q_1024) α)
    (hq : PathSum (wKS1024 C.x C.xn δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(254 : ℝ)) + 2 ^ (-(280 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 70) <
      𝒟[simulateQ (execImplS1024 C δ127q_1024 implA (samplerZ falcon1024S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
      𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ127q_1024
        (embedS1024 C.x C.xn δ127q_1024 oe)))] s + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) :=
  falcon1024_exec_vs_true256_127 C hC hR hq77 K hK T hT implA implE implM implF hAE hAM hAF hE
    hM hF sampI hsamp (embedS1024 C.x C.xn δ127q_1024 oe)
    (pathSum_embedS1024 C.x C.xn δ127q_1024 hq) hs
    (exec_sampler_step1024 C δ127q_1024 K hK implA sampI hI ub hub oe hq hs _ 254 le_rfl
      (by rw [Nat.cast_ofNat]; exact le_add_right (le_mul_of_one_le_left (by positivity) hT))
      hwin)

end Hop

/-- **Node** (non-vacuity). In `OracleComp (wspecU aux)` the ideal-world hypotheses of
`falcon1024_exec_sampler_vs_true(256)` (the range `hI` at `falcon1024S`) and `UnifBits` hold
together. -/
theorem exec_sampler_worlds_exist1024 [OracleSpec.AnswerMeasure aux] :
    ∃ (implA : QueryImpl aux (OracleComp (wspecU aux)))
      (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) (OracleComp (wspecU aux)))
      (sampI : Fx 64 → Fx 64 → OracleComp (wspecU aux) ℤ) (ub : ℕ → OracleComp (wspecU aux) ℕ),
      (∀ x, implE (.inl x) = implA x) ∧ (∀ x, implM (.inl x) = implA x) ∧
      (∀ x, implF (.inl x) = implA x) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
        discreteGaussianMeasure q.σ q.t) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
        discreteGaussianMeasure q.σbar q.t) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
        discreteGaussianMeasure q.σbar q.tbar) ∧
      (∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
        (implF (.inr q) : OracleComp (wspecU aux) ℤ) = sampI σ t) ∧
      (∀ σ t, inRangeB falcon1024S σ = true →
        𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal) ∧
      UnifBits ub := by
  have hσ : ∀ q : Falcon.CallP, 0 < q.σ := fun q => lt_of_lt_of_le (by norm_num) q.hσ.1
  refine ⟨fun t => liftM (OracleSpec.query (spec := wspecU aux) (.inl (.inl t))),
    worldU (·.σ) (·.t) hσ, worldU (·.σbar) (·.t) (·.hσbar), worldU (·.σbar) (·.tbar) (·.hσbar),
    sampU, fun k => liftM (OracleSpec.query (spec := wspecU aux) (.inr k)),
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun q => evalDist_gaussU _ _ _,
    fun q => evalDist_gaussU _ _ _, fun q => evalDist_gaussU _ _ _, fun σ t q h1 h2 => ?_,
    fun σ t h => ?_, ⟨fun k n => ?_⟩⟩
  · have h : 0 < σ.toReal := h1 ▸ q.hσbar
    rw [sampU, dite_eq_left_of_eq_true (eq_true h)]
    exact gaussU_congr _ _ h1 h2
  · rw [sampU, dite_eq_left_of_eq_true (eq_true (sampS_σ_pos sminOk1024 h))]
    exact evalDist_gaussU _ _ _
  · have e : 𝒟[(liftM (OracleSpec.query (spec := wspecU aux) (.inr k)) :
        OracleComp (wspecU aux) ℕ)] = Measure.uniformOfFinset (Finset.range (2 ^ k)) :=
      (@evalDist_liftM_query _ (wspecU aux) _ (.inr k) ⊤).trans (@MeasureTheory.trim_eq_self _ ⊤ _)
    rw [e, Measure.uniformOfFinset_apply_singleton]
    simp [Finset.mem_range]

end FalconPrecision.Exec
