/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerClose
public import FalconPrecision.Exec.SignRefine
public import FalconPrecision.Witness
public import Mathlib.Probability.Distributions.Uniform

/-! # The executable signer with the executable SamplerZ against exact Falcon

`SampKey`: raw keys passing `check` whose stored leaves are in SamplerZ's range `[σmin, σmax]`
(`leavesB`; `check` admits `[1.2778, 1.825]`). `specKS`, `execImplS`: experiments on such keys
and the executable signer's world with a sampler `samp`. `execZ` factors that world through a
SamplerZ oracle `specZ` (`exec_factor`), so the sampler can be swapped per call:
`sampler_hop` (Rényi, order `a`, path budget `N` calls, `samplerZ_mgf`) and, without shift
rejection, `samplerZ_tv` along executions.

`falcon512_exec_sampler_vs_true`: `falcon512_exec_vs_true` (`Exec.SignRefine`) for the executable
signer running `samplerZ falcon512S C.samp ub` on uniform bits `ub`, for every SamplerZ choice; the
sampler costs a factor `2^(1/64)` on the threshold (order `2¹⁴`, `N = 1024K ≤ 2⁴⁹` calls) and,
with saturated shifts (the spec's own SamplerZ), `2⁻⁶¹`, which makes the statement empty for success
`≤ 2⁻⁶¹` and is most of the threshold for `T ≤ 2⁶⁴`. The perfect-sampler hypotheses remain only on
ideal worlds (`hE`, `hM`, `hF`, the ideal sampler `sampI` with `hI`, `hsamp`);
`exec_sampler_worlds_exist` states that they hold together with `UnifBits` in one monad.

Not proved here: what `falcon512_exec_vs_true` does not prove; the PRNG (`ub` is ideal); the
unbounded loop (`fuel = 128`); SamplerZ's floating/fixed-point arithmetic (`x`, `ccs`, `r` exact in
`ℚ`); NIST's 79-bit table (`tab79` is ours). -/

@[expose] public section

open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact
  FalconPrecision.Errors.FFTRec
open scoped ENNReal

namespace FalconPrecision.Exec

/-- Every leaf of a stored tree passes `p`. -/
def CTree.leavesB (p : Fx 64 → Bool) : {L : ℕ} → CTree 64 L → Bool
  | _, .leaf σ => p σ
  | _, .node _ T0 T1 => leavesB p T0 && leavesB p T1

/-- Checked raw keys whose stored leaves are in SamplerZ's range. -/
def SampKey (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) : Type :=
  {k : CheckedKey P n δq // (storeC P n k.1).leavesB (inRangeB falcon512S) = true}

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- Experiment oracles: auxiliary oracles and a signing oracle on `SampKey`s. -/
@[reducible] def specKS (P : XChoices) (n : ℕ) (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (SampKey P n δq × (Fin (2 ^ 9) → ℤ))) :=
  Sum.elim aux fun _ => Sig

/-- One per signing query. -/
def wKS (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) : ιA ⊕ (SampKey P n δq × (Fin (2 ^ 9) → ℤ)) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

/-- `SampKey` queries as `CheckedKey` queries. -/
def embedSImpl (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) :
    QueryImpl (specKS P n aux δq) (OracleComp (specK P n aux δq))
  | .inl x => liftM (OracleSpec.query (spec := specK P n aux δq) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specK P n aux δq) (.inr (kc.1.1, kc.2)))

/-- An experiment on `SampKey`s as one on `CheckedKey`s. -/
def embedS (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type} (oe : OracleComp (specKS P n aux δq) α) :
    OracleComp (specK P n aux δq) α :=
  simulateQ (embedSImpl P n δq) oe

/-- The executable signer's world on `SampKey`s. -/
def execImplS (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] (implA : QueryImpl aux m)
    (samp : Fx 64 → Fx 64 → m ℤ) : QueryImpl (specKS C.x C.xn aux δq) m
  | .inl x => implA x
  | .inr kc => signX C samp (storeC C.x C.xn kc.1.1.1) kc.1.1.1 kc.2

/-- SamplerZ queries `(σ̄, t̄)` with `σ̄` in range. -/
def SQ : Type := {p : Fx 64 × Fx 64 // inRangeB falcon512S p.1 = true}

/-- Auxiliary oracles and a SamplerZ oracle. -/
@[reducible] def specZ (aux : OracleSpec.{0, 0} ιA) : OracleSpec (ιA ⊕ SQ) :=
  FalconGame.spec aux SQ

/-- A world of `specZ`: auxiliary queries by `implA`, SamplerZ by `samp`. -/
def implZ {m : Type → Type*} (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) :
    QueryImpl (specZ aux) m
  | .inl x => implA x
  | .inr p => samp p.1.1 p.1.2

/-- A SamplerZ call as a query (`0` out of range: never reached on `SampKey`s). -/
def sampQ (σ t : Fx 64) : OracleComp (specZ aux) ℤ :=
  if h : inRangeB falcon512S σ = true then
    liftM (OracleSpec.query (spec := specZ aux) (.inr ⟨(σ, t), h⟩))
  else pure 0

/-- The executable signer with SamplerZ calls left as queries. -/
def execZ (C : Choices) (δq : ℕ → ℚ) :
    QueryImpl (specKS C.x C.xn aux δq) (OracleComp (specZ aux))
  | .inl x => liftM (OracleSpec.query (spec := specZ aux) (.inl x))
  | .inr kc => signX C sampQ (storeC C.x C.xn kc.1.1.1) kc.1.1.1 kc.2

theorem simulateQ_sampQ {m : Type → Type*} [Monad m] [LawfulMonad m] (implA : QueryImpl aux m)
    (samp : Fx 64 → Fx 64 → m ℤ) {σ : Fx 64} (h : inRangeB falcon512S σ = true) (t : Fx 64) :
    simulateQ (implZ implA samp) (sampQ (aux := aux) σ t) = samp σ t := by
  rw [sampQ, dite_eq_left_of_eq_true (eq_true h)]
  exact simulateQ_spec_query (impl := implZ implA samp) (Sum.inr ⟨(σ, t), h⟩)

/-- On a tree with leaves in range, `ffsX` with SamplerZ queries, run in `implZ`, is `ffsX`. -/
theorem simulateQ_ffsX (C : Choices) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) :
    ∀ {L : ℕ} (T : CTree 64 L), T.leavesB (inRangeB falcon512S) = true →
      ∀ t0 t1 : Out L → Cx 64,
        simulateQ (implZ implA samp) (ffsX C (sampQ (aux := aux)) T t0 t1) = ffsX C samp T t0 t1
  | _, .leaf σ, hT, t0, t1 => by
    simp only [ffsX, simulateQ_bind, simulateQ_pure, simulateQ_sampQ implA samp hT]
  | _, @CTree.node _ L ℓ T0 T1, hT, t0, t1 => by
    simp only [CTree.leavesB, Bool.and_eq_true] at hT
    simp only [ffsX]
    by_cases c1 : chkX C.rchk (L + 1) t1 = true
    swap
    · simp only [c1, Bool.false_eq_true, ↓reduceIte, simulateQ_pure]
    simp only [c1, ↓reduceIte]
    rw [simulateQ_bind, simulateQ_ffsX C implA samp T1 hT.2]
    refine bind_congr fun r1 => ?_
    rcases r1 with _ | s1
    · rfl
    by_cases c2 : (chkX C.rchk L s1.c1 && chkX C.rchk (L + 1)
      (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)) = true
    swap
    · simp only [c2, Bool.false_eq_true, ↓reduceIte, simulateQ_pure]
    simp only [c2, ↓reduceIte]
    rw [simulateQ_bind, simulateQ_ffsX C implA samp T0 hT.1]
    refine bind_congr fun r0 => ?_
    rcases r0 with _ | s0
    · rfl
    by_cases c3 : chkX C.rchk L s0.c1 = true <;>
      simp only [c3, Bool.false_eq_true, ↓reduceIte, simulateQ_pure]

/-- **Node.** The executable world factors through the SamplerZ oracle. -/
theorem exec_factor (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specKS C.x C.xn aux δq) α) :
    simulateQ (execImplS C δq implA samp) oe =
      simulateQ (implZ implA samp) (simulateQ (execZ C δq) oe) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := execImplS C δq implA samp)
    (fun t => ?_) oe).symm
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := implZ implA samp) (Sum.inl x)
  · change simulateQ (implZ implA samp) (signX C sampQ (storeC C.x C.xn kc.1.1.1) kc.1.1.1 kc.2) =
      signX C samp (storeC C.x C.xn kc.1.1.1) kc.1.1.1 kc.2
    unfold signX
    split_ifs
    · rw [simulateQ_map, simulateQ_ffsX C implA samp _ kc.1.2]
    · rfl

/-- **Node.** Forgetting the leaf range. -/
theorem embedS_exec (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) {α : Type}
    (oe : OracleComp (specKS C.x C.xn aux δq) α) :
    simulateQ (execImplS C δq implA samp) oe =
      simulateQ (execImpl C δq implA samp) (embedS C.x C.xn δq oe) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := execImplS C δq implA samp)
    (fun t => ?_) oe).symm
  rcases t with x | kc
  · exact simulateQ_spec_query (impl := execImpl C δq implA samp) (Sum.inl x)
  · exact simulateQ_spec_query (impl := execImpl C δq implA samp) (Sum.inr (kc.1.1, kc.2))

/-- **Node.** Forgetting the leaf range keeps the signing-query count. -/
theorem pathSum_embedS (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKS P n aux δq) α} {S : ℝ} (h : PathSum (wKS P n δq) oe S) :
    PathSum (wKC P n δq) (embedS P n δq oe) S := by
  have h1 := pathSum_simulateQ_impl (embedSImpl P n δq) (w := wKC P n δq) (c := 1) zero_le_one
    (fun t => by rcases t with x | kc <;> exact pathSum_query _ (by simp [wKC, wKS])) h
  rwa [one_mul] at h1

theorem pathSum_sampQ (σ t : Fx 64) :
    PathSum (Sum.elim (fun _ => (0 : ℝ)) fun _ => 1) (sampQ (aux := aux) σ t) 1 := by
  unfold sampQ
  split
  · exact pathSum_query _ (by change (0 : ℝ) ≤ 1 - 1; norm_num)
  · exact .pure _ zero_le_one

/-- `ffsX` on a tree of depth `L` makes at most `2^(L+1)` SamplerZ calls. -/
theorem pathSum_ffsX (C : Choices) :
    ∀ {L : ℕ} (T : CTree 64 L) (t0 t1 : Out L → Cx 64),
      PathSum (Sum.elim (fun _ => (0 : ℝ)) fun _ => 1) (ffsX C (sampQ (aux := aux)) T t0 t1)
        (2 ^ (L + 1))
  | _, .leaf σ, t0, t1 =>
    ((pathSum_sampQ _ _).bind (T := 1) fun _ => ((pathSum_sampQ _ _).bind (T := 0)
      fun _ => .pure _ le_rfl).weaken (by norm_num)).weaken (by norm_num)
  | _, @CTree.node _ L ℓ T0 T1, t0, t1 => by
    simp only [ffsX]
    split
    · refine ((pathSum_ffsX C T1 _ _).bind (T := 2 ^ (L + 1)) fun r1 => ?_).weaken
        (le_of_eq (by ring))
      rcases r1 with _ | s1
      · exact .pure _ (by positivity)
      · dsimp only
        split
        · refine ((pathSum_ffsX C T0 _ _).bind (T := 0) fun r0 => ?_).weaken (by simp)
          rcases r0 with _ | s0
          · exact .pure _ le_rfl
          · dsimp only
            split <;> exact .pure _ le_rfl
        · exact .pure _ (by positivity)
    · exact .pure _ (by positivity)

/-- **Node.** A signing attempt makes at most `1024` SamplerZ calls. -/
theorem pathSum_execZ (C : Choices) (δq : ℕ → ℚ) {α : Type}
    {oe : OracleComp (specKS C.x C.xn aux δq) α} {K : ℝ} (h : PathSum (wKS C.x C.xn δq) oe K) :
    PathSum (Sum.elim (fun _ => (0 : ℝ)) fun _ => 1) (simulateQ (execZ C δq) oe) (1024 * K) := by
  refine pathSum_simulateQ_impl (execZ C δq) (by norm_num) (fun t => ?_) h
  rcases t with x | kc
  · exact pathSum_query _ (by simp [wKS])
  · change PathSum _ (signX C sampQ (storeC C.x C.xn kc.1.1.1) kc.1.1.1 kc.2) _
    unfold signX
    split_ifs
    · exact (pathSum_map _ (pathSum_ffsX C _ _ _)).weaken (by simp [wKS]; norm_num)
    · exact .pure _ (by simp [wKS])

section Hop

variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **The sampler hop** (Rényi, order `a ≥ 2`): along executions with at most `N` SamplerZ
calls, SamplerZ with shift rejection against an ideal sampler `sampI`. -/
theorem sampler_hop {a : ℝ} (ha : 2 ≤ a) (S : SampChoices) (hS : S.shiftRej = true)
    (implA : QueryImpl aux m) (ub : ℕ → m ℕ) (hub : UnifBits ub) (sampI : Fx 64 → Fx 64 → m ℤ)
    (hI : ∀ σ t, inRangeB falcon512S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oz : OracleComp (specZ aux) α) {N : ℝ} (hN : PathSum (Sum.elim (fun _ => 0) fun _ => 1) oz N)
    {s : Set α} (hs : MeasurableSet s) :
    𝒟[simulateQ (implZ implA (samplerZ falcon512S S ub)) oz] s ^ (a / (a - 1)) /
        ENNReal.ofReal (Real.exp (N * εZ a)) ≤
      𝒟[simulateQ (implZ implA sampI) oz] s := by
  have ha1 : 1 < a := by linarith
  have hε : 0 ≤ εZ a := by
    have hu : (0 : ℝ) ≤ uB := by norm_num [uB]
    exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hu _)) (by norm_num [chi2B])
  have hM := renyiMGF_simulateQ_le_path ha1 (implZ implA (samplerZ falcon512S S ub))
    (implZ implA sampI) (c := (a - 1) * εZ a) (mul_nonneg (by linarith) hε) _ (fun x => by
      cases x with
      | inl x => exact FalconGame.aux_le ha1 implA _ _ (fun _ => rfl) (fun _ => rfl) _ _ x
      | inr p =>
        refine le_of_le_of_eq ?_ (by rw [Sum.elim_inr, mul_one])
        change renyiMGF a 𝒟[samplerZ falcon512S S ub p.1.1 p.1.2] 𝒟[sampI p.1.1 p.1.2] ≤ _
        rw [hI _ _ p.2]
        exact samplerZ_mgf ha S hS ub hub _ _ p.2) hN
  refine le_trans ?_ (measure_rpow_div_renyiDiv_le ha1
    𝒟[simulateQ (implZ implA (samplerZ falcon512S S ub)) oz] 𝒟[simulateQ (implZ implA sampI) oz] hs)
  refine ENNReal.div_le_div_left ?_ _
  rw [renyiDiv_eq_rpow ha1]
  refine (ENNReal.rpow_le_rpow hM (inv_nonneg.2 (by linarith))).trans_eq ?_
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  have ham : a - 1 ≠ 0 := by linarith
  congr 2
  field_simp

/-- **Node** (arithmetic): with `R_{2¹⁴} ≤ exp(1024K·εZ)` along executions, `K ≤ 2³⁹`,
success `> 2^(1/64)·θ` before the hop is success `> θ` after it, `θ = T·2⁻¹²⁶ + 2⁻¹⁴⁰`. -/
theorem thresh_sampler (T : ℝ≥0∞) (hT : 1 ≤ T) (K : ℕ) (hK : K ≤ 2 ^ 39) (x y : ℝ≥0∞)
    (hxy : x ^ ((2 : ℝ) ^ 14 / ((2 : ℝ) ^ 14 - 1)) /
      ENNReal.ofReal (Real.exp (1024 * K * εZ (2 ^ 14))) ≤ y)
    (hx : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) < x) :
    T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ)) < y := by
  set θ := T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ)) with hθ
  set p : ℝ := (2 : ℝ) ^ 14 / ((2 : ℝ) ^ 14 - 1) with hp
  set c : ℝ := 1024 * K * εZ (2 ^ 14) with hc
  have hp' : p = 1 / 16383 + 1 := by rw [hp]; norm_num
  have h2 : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) = ENNReal.ofReal (2 ^ (1 / 64 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hθt : θ ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'] at hx
    exact not_top_lt hx
  have h126 : (2 : ℝ≥0∞) ^ (-(126 : ℝ)) ≤ θ :=
    le_add_right (le_mul_of_one_le_left (by positivity) hT)
  set θr := θ.toReal
  have hθr : (2 : ℝ) ^ (-(126 : ℝ)) ≤ θr := by
    have := ENNReal.toReal_mono hθt h126
    rwa [← ENNReal.toReal_rpow, ENNReal.toReal_ofNat] at this
  have hθ0 : 0 < θr := lt_of_lt_of_le (by positivity) hθr
  have hε0 : 0 ≤ εZ (2 ^ 14) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num [uB]) _))
      (by norm_num [chi2B])
  have hu : ((uB : ℚ) : ℝ) ^ ((2 : ℝ) ^ 14 - 2) ≤ 3 := by
    rw [show (2 : ℝ) ^ 14 - 2 = ((16382 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc ((uB : ℚ) : ℝ) ^ 16382 ≤ Real.exp (1 / 2 ^ 40) ^ 16382 := by
          gcongr
          · norm_num [uB]
          · have := Real.add_one_le_exp (1 / 2 ^ 40 : ℝ)
            push_cast [uB]
            linarith
      _ = Real.exp (16382 * (1 / 2 ^ 40)) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
      _ ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have hε : εZ (2 ^ 14) ≤ 3 / 2 ^ 63 := by
    calc εZ (2 ^ 14) ≤ (2 : ℝ) ^ 14 / 2 * 3 * (chi2B : ℝ) := by
          rw [εZ]; gcongr; norm_num [chi2B]
      _ = 3 / 2 ^ 63 := by norm_num [chi2B]
  have hc3 : c ≤ 3 / 2 ^ 14 := by
    have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
    calc c ≤ 1024 * 2 ^ 39 * (3 / 2 ^ 63) := by rw [hc]; gcongr
      _ = 3 / 2 ^ 14 := by norm_num
  have hlow : Real.exp c < 2 ^ (130 / 16383 : ℝ) := by
    rw [Real.rpow_def_of_pos two_pos, Real.exp_lt_exp]
    linarith [Real.log_two_gt_d9]
  have key : θr * Real.exp c < (2 ^ (1 / 64 : ℝ) * θr) ^ p := by
    calc θr * Real.exp c < θr * 2 ^ (130 / 16383 : ℝ) := mul_lt_mul_of_pos_left hlow hθ0
      _ = 2 ^ (1 / 64 * p + -(126 : ℝ) * (1 / 16383)) * θr := by
          rw [show 1 / 64 * p + -(126 : ℝ) * (1 / 16383) = 130 / 16383 by rw [hp']; norm_num]
          ring
      _ = 2 ^ (1 / 64 * p) * (2 ^ (-(126 : ℝ))) ^ (1 / 16383 : ℝ) * θr := by
          rw [← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
      _ ≤ 2 ^ (1 / 64 * p) * θr ^ (1 / 16383 : ℝ) * θr := by gcongr
      _ = (2 ^ (1 / 64 : ℝ) * θr) ^ p := by
          rw [Real.mul_rpow (by positivity) hθ0.le, ← Real.rpow_mul two_pos.le,
            show θr ^ p = θr ^ (1 / 16383 : ℝ) * θr by
              rw [hp', Real.rpow_add hθ0, Real.rpow_one]]
          ring
  have hp0 : 0 ≤ p := by rw [hp']; norm_num
  have hb : 0 < 2 ^ (1 / 64 : ℝ) * θr := mul_pos (by positivity) hθ0
  have hE : θ * ENNReal.ofReal (Real.exp c) < x ^ p := by
    calc θ * ENNReal.ofReal (Real.exp c) = ENNReal.ofReal (θr * Real.exp c) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hθt]
      _ < ENNReal.ofReal ((2 ^ (1 / 64 : ℝ) * θr) ^ p) :=
          (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hb _)).2 key
      _ = ((2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * θ) ^ p := by
          rw [← ENNReal.ofReal_rpow_of_nonneg hb.le hp0,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hθt, h2]
      _ ≤ x ^ p := ENNReal.rpow_le_rpow hx.le hp0
  exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2 hE).trans_le hxy

/-- **The executable signer with the executable SamplerZ against exact Falcon at Falcon-512.**
For admissible choices without range checks, `1/q` at 77 bits and every SamplerZ choice `C.samp`;
every experiment `oe` on `SampKey`s with at most `K ≤ 2³⁹` signing queries along every execution;
`ub` uniform bits: success `> 2^(1/64)·(T·2⁻¹²⁶ + 2⁻¹⁴⁰)` (plus `2⁻⁶¹` when shifts saturate) with
the executable signer running `samplerZ falcon512S C.samp ub` gives success `> T·2⁻¹³¹ - 2⁻¹⁴¹` with
exact Falcon signing on the true tree. With saturated shifts (the spec's own SamplerZ) the additive
`2⁻⁶¹` makes the statement empty for success `≤ 2⁻⁶¹` and is most of the threshold for `T ≤ 2⁶⁴`.
Hypotheses on ideal worlds only: those of `falcon512_exec_vs_true` for an ideal sampler `sampI`
(`hE`, `hM`, `hF`, `hsamp`), and `hI`. Not proved: what `falcon512_exec_vs_true`
does not prove; the PRNG (`ub` is ideal); the unbounded loop (`fuel = 128`); SamplerZ's
floating/fixed-point arithmetic (`x`, `ccs`, `r` exact in `ℚ`); NIST's 79-bit table (`tab79` is
ours). -/
theorem falcon512_exec_sampler_vs_true [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specKS C.x C.xn aux δq) α) (hq : PathSum (wKS C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 61) <
      𝒟[simulateQ (execImplS C δq implA (samplerZ falcon512S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT _ (embed C.x C.xn δq (embedS C.x C.xn δq oe)))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  set S' : SampChoices := { C.samp with shiftRej := true }
  have hN := pathSum_execZ C δq hq
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  have hw : ∀ t, 0 ≤ (Sum.elim (fun _ => (0 : ℝ)) fun _ => 1 : ιA ⊕ SQ → ℝ) t :=
    fun t => by rcases t with _ | _ <;> simp
  have hεs : (0 : ℝ) ≤ if C.samp.shiftRej then 0 else 1 / 2 ^ 110 := by split_ifs <;> norm_num
  have htv := (etvDist_simulateQ_le_path (implZ implA (samplerZ falcon512S C.samp ub))
    (implZ implA (samplerZ falcon512S S' ub)) hεs _ hw (fun x => by
      cases x with
      | inl x =>
        exact (@Measure.etvDist_self _ ⊤ _).le.trans bot_le
      | inr p =>
        refine (samplerZ_tv C.samp ub hub p.1.1 p.1.2 p.2).trans
          (ENNReal.ofReal_le_ofReal (le_of_eq (by simp))))
    hN).2
  have hle : 𝒟[simulateQ (implZ implA (samplerZ falcon512S C.samp ub))
      (simulateQ (execZ C δq) oe)] s ≤
      𝒟[simulateQ (implZ implA (samplerZ falcon512S S' ub)) (simulateQ (execZ C δq) oe)] s +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 61) := by
    refine (le_add_etvDist _ _ hs).trans (add_le_add le_rfl (htv.trans
      (ENNReal.ofReal_le_ofReal ?_)))
    split_ifs
    · simp
    · calc (1 : ℝ) / 2 ^ 110 * (1024 * K) ≤ 1 / 2 ^ 110 * (1024 * 2 ^ 39) := by gcongr
        _ = 1 / 2 ^ 61 := by norm_num
  rw [exec_factor] at hwin
  have hR' : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) <
      𝒟[simulateQ (implZ implA (samplerZ falcon512S S' ub)) (simulateQ (execZ C δq) oe)] s :=
    (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).1 (hwin.trans_le hle)
  have hhop := sampler_hop (a := 2 ^ 14) (by norm_num) S' rfl implA ub hub sampI hI _ hN hs
  have hθ := thresh_sampler T hT K hK _ _ hhop hR'
  rw [← exec_factor, embedS_exec] at hθ
  exact falcon512_exec_vs_true C hC hR hq77 δq K hK hδ T hT implA implE implM implF hAE hAM hAF
    hE hM hF sampI hsamp (embedS C.x C.xn δq oe) (pathSum_embedS C.x C.xn δq hq) hs hθ

end Hop

open FalconPrecision.FalconWitness in
/-- Auxiliary oracles, a perfect discrete Gaussian sampler and uniform bits on `[0, 2ᵏ)`. -/
@[reducible] def wspecU (aux : OracleSpec.{0, 0} ιA) : OracleSpec ((ιA ⊕ GQuery) ⊕ ℕ) :=
  Sum.elim (wspec aux) fun _ => ℕ

open FalconPrecision.FalconWitness in
noncomputable instance [OracleSpec.AnswerMeasure aux] : OracleSpec.AnswerMeasure (wspecU aux) :=
  @PFunctor.AnswerMeasure.mk (wspecU aux).toPFunctor (fun _ => ⊤)
    (fun | .inl t => OracleSpec.AnswerMeasure.toMeasure (spec := wspec aux) t
         | .inr k => (Measure.uniformOfFinset (Finset.range (2 ^ k)) : Measure ℕ))
    (fun | .inl t => OracleSpec.AnswerMeasure.isProbabilityMeasure_toMeasure (spec := wspec aux) t
         | .inr k => ⟨by
            change (Measure.uniformOfFinset (Finset.range (2 ^ k)) : Measure ℕ) Set.univ = 1
            rw [Measure.uniformOfFinset_apply]
            convert ENNReal.div_self (a := ((Finset.range (2 ^ k)).card : ℝ≥0∞)) (by simp)
              (by simp) using 2
            all_goals simp⟩)

open FalconPrecision.FalconWitness in
/-- A perfect sampler query `D_{σ,c}` of `wspecU` (`σ > 0`). -/
def gaussU (σ c : ℝ) (h : 0 < σ) : OracleComp (wspecU aux) ℤ :=
  liftM (OracleSpec.query (spec := wspecU aux) (.inl (.inr ⟨(σ, c), h⟩)))

theorem gaussU_congr {σ σ' c c' : ℝ} (h : 0 < σ) (h' : 0 < σ') (hσ : σ = σ') (hc : c = c') :
    gaussU (aux := aux) σ c h = gaussU σ' c' h' := by
  subst hσ hc
  rfl

open FalconPrecision.FalconWitness in
theorem evalDist_gaussU [OracleSpec.AnswerMeasure aux] (σ c : ℝ) (h : 0 < σ) :
    𝒟[gaussU (aux := aux) σ c h] = discreteGaussianMeasure σ c :=
  (@evalDist_liftM_query _ (wspecU aux) _ (.inl (.inr ⟨(σ, c), h⟩)) ⊤).trans
    (@MeasureTheory.trim_eq_self _ ⊤ _)

/-- A world of `wspecU`: auxiliary queries forwarded, SamplerZ at `D_{w q, c q}`. -/
def worldU (w c : Falcon.CallP → ℝ) (hw : ∀ q, 0 < w q) :
    QueryImpl (FalconGame.spec aux Falcon.CallP) (OracleComp (wspecU aux))
  | .inl t => liftM (OracleSpec.query (spec := wspecU aux) (.inl (.inl t)))
  | .inr q => gaussU (w q) (c q) (hw q)

/-- The ideal sampler of `wspecU`: `D_{σ̄,t̄}` for `σ̄ > 0`. -/
noncomputable def sampU (σ t : Fx 64) : OracleComp (wspecU aux) ℤ :=
  if h : 0 < σ.toReal then gaussU σ.toReal t.toReal h else pure 0

/-- **Node** (non-vacuity). In `OracleComp (wspecU aux)` the ideal-world hypotheses of
`falcon512_exec_sampler_vs_true` and `UnifBits` hold together. -/
theorem exec_sampler_worlds_exist [OracleSpec.AnswerMeasure aux] :
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
      (∀ σ t, inRangeB falcon512S σ = true →
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
  · rw [sampU, dite_eq_left_of_eq_true (eq_true (falcon512S_σ_pos h))]
    exact evalDist_gaussU _ _ _
  · have e : 𝒟[(liftM (OracleSpec.query (spec := wspecU aux) (.inr k)) :
        OracleComp (wspecU aux) ℕ)] = Measure.uniformOfFinset (Finset.range (2 ^ k)) :=
      (@evalDist_liftM_query _ (wspecU aux) _ (.inr k) ⊤).trans (@MeasureTheory.trim_eq_self _ ⊤ _)
    rw [e, Measure.uniformOfFinset_apply_singleton]
    simp [Finset.mem_range]

end FalconPrecision.Exec
