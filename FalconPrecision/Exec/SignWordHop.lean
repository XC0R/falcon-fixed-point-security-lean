/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerHop
public import FalconPrecision.Exec.SignEquiv

/-! # 32.64 and 64.64 signing inside the composed security theorem

`falcon512_exec_sampler_vs_true` (`Exec.SamplerHop`) is stated for unbounded words (`Adm C`:
`C.word = none`).
`RKey C i δq`: `SampKey`s passing `checkRange C i 19`. On experiments over such keys the world of
the signer whose attempts run on `(i + 64)`-bit words with the executable SamplerZ is the unbounded
one on the embedded experiment (`execR_word`, from `signX_word` and `clampS_samplerZ`), so the
composed theorem holds for it unchanged: `falcon512_exec_word_sampler_vs_true` (at `i = 32`: 32.64;
at `i = 64`: 64.64).

Not proved here: what `falcon512_exec_sampler_vs_true` does not prove; that any key passes
`checkRange` (computed for round-3 KAT keys, not proved); key expansion `storeC` on words (unbounded
`Int`: words reduce only the attempt `signX`). -/

@[expose] public section

open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.FFTRec
open scoped ENNReal

namespace FalconPrecision.Exec

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- `SampKey`s whose signing attempt fits `(i + 64)`-bit words (`checkRange C i 19`). -/
def RKey (C : Choices) (i : ℕ) (δq : ℕ → ℚ) : Type :=
  {k : SampKey C.x C.xn δq // checkRange C i 19 k.1.1 = true}

/-- Experiment oracles: auxiliary oracles and a signing oracle on `RKey`s. -/
@[reducible] def specKR (C : Choices) (i : ℕ) (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (RKey C i δq × (Fin (2 ^ 9) → ℤ))) :=
  Sum.elim aux fun _ => Sig

/-- One per signing query. -/
def wKR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) : ιA ⊕ (RKey C i δq × (Fin (2 ^ 9) → ℤ)) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

/-- `RKey` queries as `SampKey` queries. -/
def embedRImpl (C : Choices) (i : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKR C i aux δq) (OracleComp (specKS C.x C.xn aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specKS C.x C.xn aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specKS C.x C.xn aux δq) (.inr (kc.1.1, kc.2)))

/-- An experiment on `RKey`s as one on `SampKey`s. -/
def embedR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type} (oe : OracleComp (specKR C i aux δq) α) :
    OracleComp (specKS C.x C.xn aux δq) α :=
  simulateQ (embedRImpl C i δq) oe

/-- The signer whose attempts run on `(i + 64)`-bit words, on `RKey`s. -/
def execImplR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) : QueryImpl (specKR C i aux δq) m
  | .inl x => implA x
  | .inr kc => signX { C with word := some i } samp (storeC C.x C.xn kc.1.1.1.1) kc.1.1.1.1 kc.2

theorem with_word_none (C : Choices) (hw : C.word = none) : { C with word := none } = C := by
  cases C
  simp only at hw
  subst hw
  rfl

/-- **The word world is the unbounded world** on `RKey` experiments, with SamplerZ. -/
theorem execR_word (C : Choices) (hw : C.word = none) (i : ℕ) (hi : 1 ≤ i) (hi64 : i ≤ 64)
    (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m] (implA : QueryImpl aux m)
    (S : SampChoices) (ub : ℕ → m ℕ) {α : Type} (oe : OracleComp (specKR C i aux δq) α) :
    simulateQ (execImplR C i δq implA (samplerZ falcon512S S ub)) oe =
      simulateQ (execImplS C δq implA (samplerZ falcon512S S ub)) (embedR C i δq oe) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := execImplR C i δq implA (samplerZ falcon512S S ub)) (fun t => ?_) oe).symm
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := execImplS C δq implA _) (Sum.inl x)
  · refine (simulateQ_spec_query (impl := execImplS C δq implA _) (Sum.inr (kc.1.1, kc.2))).trans ?_
    have e := signX_word C δq i 19 hi hi64 kc.1.1.1.1 kc.1.1.1.2 kc.1.2
      (samplerZ falcon512S S ub) kc.2
    rw [clampS_samplerZ, with_word_none C hw] at e
    exact e.symm

/-- Forgetting the range check keeps the signing-query count. -/
theorem pathSum_embedR (C : Choices) (i : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKR C i aux δq) α} {S : ℝ} (h : PathSum (wKR C i δq) oe S) :
    PathSum (wKS C.x C.xn δq) (embedR C i δq oe) S := by
  have h1 := pathSum_simulateQ_impl (embedRImpl C i δq) (w := wKS C.x C.xn δq) (c := 1)
    zero_le_one (fun t => by rcases t with x | kc <;> exact pathSum_query _ (by simp [wKS, wKR]))
    h
  rwa [one_mul] at h1

section Hop

variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **The composed theorem on `(i + 64)`-bit words** (`i = 32`: 32.64; `i = 64`: 64.64):
`falcon512_exec_sampler_vs_true` (`Exec.SamplerHop`) for experiments on keys passing
`checkRange C i 19`, the executable signer whose attempts run on `(i + 64)`-bit words running
`samplerZ falcon512S C.samp ub`. Same hypotheses, same constants. -/
theorem falcon512_exec_word_sampler_vs_true [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKR C i aux δq) α) (hq : PathSum (wKR C i δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 61) <
      𝒟[simulateQ (execImplR C i δq implA (samplerZ falcon512S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT _ (embed C.x C.xn δq (embedS C.x C.xn δq (embedR C i δq oe))))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  rw [execR_word C hC.word i hi hi64] at hwin
  exact falcon512_exec_sampler_vs_true C hC hR hq77 δq K hK hδ T hT implA implE implM implF hAE
    hAM hAF hE hM hF sampI hsamp hI ub hub (embedR C i δq oe) (pathSum_embedR C i δq hq) hs hwin

end Hop

end FalconPrecision.Exec
