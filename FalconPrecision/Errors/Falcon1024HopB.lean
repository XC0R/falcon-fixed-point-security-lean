/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.HopB
public import FalconPrecision.Errors.Falcon1024Abort

/-! # Hop B at Falcon-1024 (tree depth 10)

`HopB.hopBP` at Falcon-1024: keys `KeyB1024` (`Key1024` with the whole basis), true tree
`KeyBP.trueTree σ1024` (`σ = 168.388571447`, spec Table 3.3), node bounds `lam1024`, depth 10
(`2048` SamplerZ calls per signing call), clamp radius `41.5` (Falcon-512: `30.5`), so the clamp
costs `p 41·2048K ≤ 2⁻²⁸¹` in X and in Y (`eps281`, from `eps_le1024`). Theorem 2 at `λ = 131`
(`renyiP` with `certs131`, as at Falcon-512: `2⁴⁹` SamplerZ calls, so `K ≤ 2³⁸`).

Budgets: `s2B1024 y δ = s2BP lam1024 10 y δ`, bounded term by term (`s2B1024_le`) for a tree error
`δ ≤ 2⁻⁴⁰` below the root, from `gainA1024_le` (`1.1437^L`) and `devB1024_le`
(`1.414214·y·3.16102^L`). Certificates at `y = 41.5`: the uniform tree error `2⁻⁴³`
(`δ43_1024`) supports `2²⁹` signing calls within `2⁻¹⁰` (`s2B1024_43`); `δ127_1024` (`2⁻⁵⁸` at the
root, `2⁻⁶³` below) supports `2³⁸` (`s2B1024_127`). Values, not proved: `2⁻⁴²` uniform does not fit
`2²⁹` calls (about `2²⁸·⁴⁵` at `2⁻⁹`); `δ127_1024` fits about `2⁶⁰·⁸` at `2⁻¹⁰`.

`falcon1024_hopB`: X against Y. `falcon1024_fixed_vs_true`: composed with hop A at Falcon-1024
(`Falcon.falcon1024_exact64n'`, `K ≤ 2²⁹`), F′ against Y; instances at `δ43_1024` and
`δ127_1024`.

The `λ = 256` level (Theorem 2 on `Falcon.CallP` past `λ = 256` by `Falcon.CallP.hleaf1023`;
`Nc = 2⁶⁴`, `S₂ = 2⁻¹⁰`, certificates `certs256`, `certs259`): `falcon1024_exact256'` (hop A at
`λ = 256`, `K ≤ 2²⁹`), `falcon1024_hopB259` (hop B at `λ′ = 259`, `K ≤ 2⁵³`, `K·s2B1024 41.5 δ ≤
2⁻¹⁰`), `falcon1024_fixed_vs_true256` (`K ≤ 2²⁹`: `T·2⁻²⁵⁴ + 2⁻²⁸⁰` in F′ to `T·2⁻²⁵⁹ - 2⁻²⁸¹` in
Y; `thresh256`) with instances at `δ43_1024` and `δ127_1024`. At `S₂ = 2⁻⁹` the exponent of `h36`
is above `1/4` at both levels (`0.3048`, `0.3084`, values), so `h36` fails for every `N`.

Assumed, as at Falcon-512: `KeyBP.Good σ1024 δ` on every signing key (`Close δ` and the stored tree
real), SamplerZ perfect in every world. Not proved: that key expansion gives `Close δ` for any
Falcon-1024 key (`Exec.check1024_sound` gives it for every key passing `Exec.check1024`; that a key
passes is `#eval` evidence only), NTRUSolve, the true leaves' range, signing-query bounds above
`2²⁹` in the composed theorems (Falcon's `2⁶⁴`), and what hop A at Falcon-1024 does not prove. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Errors.HopB

/-- Falcon-1024's `σ = 168.388571447` (spec Table 3.3). -/
noncomputable def σ1024 : ℝ := 168388571447 / 10 ^ 9

/-- A Falcon-1024 signing key with the whole basis `B = [[g, -f], [G, -F]]`. -/
abbrev KeyB1024 : Type := KeyBP 10 256 7365 (1298280334 / 10 ^ 9) σmin1024_ok lam1024

/-- Falcon-1024 keys passing `KeyBP.Good σ1024 δ`. -/
abbrev GoodKey1024 (δ : ℕ → ℝ) : Type :=
  GoodKeyP 10 256 7365 (1298280334 / 10 ^ 9) σmin1024_ok lam1024 σ1024 δ

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} {δ : ℕ → ℝ} {εq : ℝ}

/-- Experiment oracles at Falcon-1024: auxiliary oracles and a signing oracle on (key, hash). -/
abbrev specS1024 (aux : OracleSpec.{0, 0} ιA) (δ : ℕ → ℝ) :
    OracleSpec (ιA ⊕ (GoodKey1024 δ × (Fin (2 ^ 10) → ℤ))) :=
  specSP 10 256 7365 (1298280334 / 10 ^ 9) σmin1024_ok lam1024 σ1024 aux δ

/-- One per signing query at Falcon-1024. -/
noncomputable abbrev wK1024 (δ : ℕ → ℝ) : ιA ⊕ (GoodKey1024 δ × (Fin (2 ^ 10) → ℤ)) → ℝ :=
  wKP 10 256 7365 (1298280334 / 10 ^ 9) σmin1024_ok lam1024 σ1024 δ

/-- Type 1 signing at Falcon-1024 with the model's range checks (`sign164R R64_1024`). -/
noncomputable abbrev runA1024 (ρ : Arith64 εq) {α : Type} (oe : OracleComp (specS1024 aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  runKP (sign164R R64_1024 ρ) oe

/-- Abort-free signing on the stored tree at Falcon-1024: F′ under `implF`, X under `implE`. -/
noncomputable abbrev runX1024 (ρ : Arith64 εq) {α : Type} (oe : OracleComp (specS1024 aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  runKP (sign164G ρ fun _ _ _ => True) oe

/-- Signing on both trees at Falcon-1024: X under `implF`, Y under `implE`. -/
noncomputable abbrev runB1024 (δ : ℕ → ℝ) {α : Type} (oe : OracleComp (specS1024 aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  runBP δ oe

/-- Exact Falcon signing on the true tree at Falcon-1024: Y under `implE`. -/
noncomputable abbrev runT1024 (δ : ℕ → ℝ) {α : Type} (oe : OracleComp (specS1024 aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  runTP δ oe

/-- Per-call bound on the squared centre differences at Falcon-1024 (depth 10, `lam1024`). -/
noncomputable abbrev s2B1024 (y : ℝ) (δ : ℕ → ℝ) : ℝ := s2BP lam1024 10 y δ

/-! ## Certificates at depth 10 -/

theorem gainA1024_le : ∀ L, L ≤ 9 → gainAP lam1024 L ≤ (11437 / 10000) ^ L
  | 0, _ => le_of_eq (pow_zero _).symm
  | L + 1, hL => by
    have ih := gainA1024_le L (by omega)
    have hl : lam1024 L = 9990 / 10000 := by simp [lam1024]; omega
    have hr : √(lam1024 L ^ 2 + 4) ≤ 2235621 / 1000000 := by
      rw [Real.sqrt_le_left (by norm_num), hl]; norm_num
    have ht : 1414213 / 1000000 ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [gainAP, pow_succ, div_le_iff₀ (by positivity)]
    calc gainAP lam1024 L * (lam1024 L + √(lam1024 L ^ 2 + 4))
        ≤ (11437 / 10000) ^ L * (9990 / 10000 + 2235621 / 1000000) :=
          mul_le_mul ih (by linarith) (by positivity) (by positivity)
      _ ≤ (11437 / 10000) ^ L * (11437 / 10000) * (2 * (1414213 / 1000000)) := by
          rw [mul_assoc]; gcongr; norm_num
      _ ≤ (11437 / 10000) ^ L * (11437 / 10000) * (2 * √2) := by gcongr

theorem devB1024_le {δ : ℕ → ℝ} (y : ℝ) (hy : 0 ≤ y)
    (hδ : ∀ j < 9, 0 ≤ δ j ∧ δ j ≤ 1 / 2 ^ 40) :
    ∀ L, L ≤ 9 → devBP lam1024 y δ L ≤ 1414214 / 1000000 * y * (316102 / 100000) ^ L
  | 0, _ => by
    rw [devBP, pow_zero, mul_one]
    have : √2 ≤ 1414214 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_le_mul_of_nonneg_right this hy
  | L + 1, hL => by
    have ih := devB1024_le y hy hδ L (by omega)
    have hl : lam1024 L = 9990 / 10000 := by simp [lam1024]; omega
    obtain ⟨h0, h1⟩ := hδ L (by omega)
    have hr : √(2 * ((1 + lam1024 L + δ L) ^ 2 + 1)) ≤ 316102 / 100000 := by
      rw [Real.sqrt_le_left (by norm_num), hl]
      have : (1 + 9990 / 10000 + δ L) ^ 2 ≤ (1 + 9990 / 10000 + 1 / 2 ^ 40) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      linarith
    rw [devBP, pow_succ]
    calc √(2 * ((1 + lam1024 L + δ L) ^ 2 + 1)) * devBP lam1024 y δ L
        ≤ 316102 / 100000 * (1414214 / 1000000 * y * (316102 / 100000) ^ L) :=
          mul_le_mul hr ih (devBP_nonneg hy _ δ L) (by norm_num)
      _ = _ := by ring

/-- `s2B1024` for a tree error `δ ≤ 2⁻⁴⁰` below the root: the sum bounded term by term. -/
theorem s2B1024_le {δ : ℕ → ℝ} (y : ℝ) (hy : 0 ≤ y) (hδ : ∀ j < 9, 0 ≤ δ j ∧ δ j ≤ 1 / 2 ^ 40)
    (h9 : 0 ≤ δ 9) :
    s2B1024 y δ ≤ (∑ L ∈ Finset.range 10, (11437 / 10000) ^ L * δ L * sq512 (9 - L) *
      (1414214 / 1000000 * y * (316102 / 100000) ^ L)) ^ 2 := by
  have hδ0 : ∀ L ∈ Finset.range 10, 0 ≤ δ L := fun L hL => by
    rcases Nat.lt_or_ge L 9 with h | h
    · exact (hδ L h).1
    · rw [show L = 9 by simp at hL; omega]; exact h9
  refine pow_le_pow_left₀ (Finset.sum_nonneg fun L hL => mul_nonneg (mul_nonneg (mul_nonneg
    (gainAP_nonneg tb1024.lam_nonneg L) (hδ0 L hL)) (Real.sqrt_nonneg _))
      (devBP_nonneg hy _ δ L)) (Finset.sum_le_sum fun L hL => ?_) 2
  have hL9 : L ≤ 9 := by simp at hL; omega
  exact mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_right (gainA1024_le L hL9) (hδ0 L hL)) (sqrt_pow_le _)
    (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (hδ0 L hL))) (devB1024_le y hy hδ L hL9)
    (devBP_nonneg hy _ δ L) (mul_nonneg (mul_nonneg (by positivity) (hδ0 L hL))
      ((Real.sqrt_nonneg _).trans (sqrt_pow_le _)))

/-- Uniform tree error `2⁻⁴³` at every node (a candidate for `Close`; not derived here). -/
noncomputable def δ43_1024 : ℕ → ℝ := fun _ => 1 / 2 ^ 43

/-- Tree error of `δ127`'s shape at depth 10: `2⁻⁵⁸` at the root (level 9), `2⁻⁶³` below (a
candidate for `Close`; not derived here). -/
noncomputable def δ127_1024 (L : ℕ) : ℝ := if L = 9 then 1 / 2 ^ 58 else 1 / 2 ^ 63

/-- The uniform tree error `2⁻⁴³` supports `2²⁹` signing-oracle calls at `y = 41.5` within
`2⁻¹⁰`. -/
theorem s2B1024_43 : (2 : ℝ) ^ 29 * s2B1024 (83 / 2) δ43_1024 ≤ 1 / 2 ^ 10 := by
  have h := s2B1024_le (δ := δ43_1024) (83 / 2) (by norm_num)
    (fun j _ => by norm_num [δ43_1024]) (by norm_num [δ43_1024])
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, δ43_1024, sq512]
  norm_num

/-- `δ127_1024` supports `2³⁸` signing-oracle calls at `y = 41.5` within `2⁻¹⁰`. -/
theorem s2B1024_127 : (2 : ℝ) ^ 38 * s2B1024 (83 / 2) δ127_1024 ≤ 1 / 2 ^ 10 := by
  have h := s2B1024_le (δ := δ127_1024) (83 / 2) (by norm_num) (fun j hj => by
    simp only [δ127_1024, show j ≠ 9 by omega, ↓reduceIte]; norm_num) (by norm_num [δ127_1024])
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, δ127_1024, sq512]
  norm_num

/-- `pclamp 41·2048K ≤ 2⁻²⁸¹` for `K ≤ 2⁶⁴` (from `AbortExact.eps_le1024`). -/
theorem eps281 (K : ℕ) (hK : K ≤ 2 ^ 64) :
    ENNReal.ofReal (pclamp 41 * (K * 2048)) ≤ (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hK
  have hp : pclamp 41 ≤ 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 121) ^ 3 := by
    unfold pclamp
    exact mul_le_mul_of_nonneg_left exp_41 (by norm_num)
  have hc : 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 121) ^ 3 * (2 ^ 64 * 2048) ≤
      (1 / 2 ^ 140 : ℝ) ^ 2 / 2 := by norm_num
  have hx : pclamp 41 * (K * 2048) ≤ 1 / 2 ^ 281 :=
    calc pclamp 41 * (K * 2048)
        ≤ 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 121) ^ 3 * (2 ^ 64 * 2048) :=
          mul_le_mul hp (mul_le_mul_of_nonneg_right hK' (by norm_num)) (by positivity)
            (by positivity)
      _ ≤ (1 / 2 ^ 140) ^ 2 / 2 := hc
      _ = 1 / 2 ^ 281 := by rw [one_div_two_pow_280, div_div, ← pow_succ]
  rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos (by norm_num),
    Real.rpow_neg (by norm_num), show (281 : ℝ) = ((281 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact ENNReal.ofReal_le_ofReal (hx.trans_eq (one_div _))

/-- `T·2⁻¹²⁹ + 2⁻²⁸¹ + 2⁻²⁸⁰ ≤ T·2⁻¹²⁸` for `T ≥ 1` (arithmetic). -/
theorem thresh1024 (T : ℝ≥0∞) (hT : 1 ≤ T) :
    T * (2 : ℝ≥0∞) ^ (-(129 : ℝ)) + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) ≤
      T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) := by
  have h1 : (2 : ℝ≥0∞) ^ (-(281 : ℝ)) ≤ 2 ^ (-(130 : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ (-(280 : ℝ)) ≤ 2 ^ (-(130 : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have e1 := two_rpow_split 129
  have e0 := two_rpow_split 128
  norm_num at e1 e0
  rw [e0, mul_add, add_assoc]
  refine add_le_add le_rfl ?_
  calc (2 : ℝ≥0∞) ^ (-(281 : ℝ)) + 2 ^ (-(280 : ℝ)) ≤ 2 ^ (-(130 : ℝ)) + 2 ^ (-(130 : ℝ)) :=
      add_le_add h1 h2
    _ = 2 ^ (-(129 : ℝ)) := e1.symm
    _ ≤ T * 2 ^ (-(129 : ℝ)) := le_mul_of_one_le_left' hT

/-! ## Hop B and the composition with hop A at Falcon-1024 -/

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/--
**Hop B at Falcon-1024**: exact signing on the stored tree (X) against exact Falcon on the true tree
(Y, `KeyBP.trueTree σ1024`). For every experiment `oe` with at most `K ≤ 2³⁸` signing-oracle calls
(one ffSampling call each, restarts included) along every execution, on keys passing
`KeyBP.Good σ1024 δ` (stored tree real and `Close δ` to the true tree; hypotheses) with
`K·s2B1024 41.5 δ ≤ 2⁻⁹`: success `> T·2⁻¹²⁹ + 2⁻²⁸¹` in X gives success `> T·2⁻¹³¹ - 2⁻²⁸¹` in Y.
SamplerZ is perfect in every world (`hE`, `hM`, `hF`). Proof: `hopBP` at depth 10 with the clamp
radius `41.5` (`eps281`) and Theorem 2 at `λ = 131` (`certs131`; `2048K ≤ 2⁴⁹` SamplerZ calls). Not
proved: `Close δ` from a model of key expansion, NTRUSolve, the true leaves' range. -/
theorem falcon1024_hopB [∀ t, Countable (aux t)] (K : ℕ) (hK : K ≤ 2 ^ 38)
    (hδ : (K : ℝ) * s2B1024 (83 / 2) δ ≤ 1 / 2 ^ 9) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS1024 aux δ) α) (hq : PathSum (wK1024 δ) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(129 : ℝ)) + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) <
        𝒟[simulateQ implF (runB1024 δ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by exact_mod_cast hK
  have e1 : (2 : ℝ≥0∞) ^ (-(((131 : ℕ) : ℝ) - 2)) = 2 ^ (-(129 : ℝ)) := by congr 1; norm_num
  have e2 : (2 : ℝ≥0∞) ^ (-((131 : ℕ) : ℝ)) = 2 ^ (-(131 : ℝ)) := by norm_num
  have h := hopBP tb1024.lam_nonneg (83 / 2) (by norm_num) K 131 (2 ^ 51) (by norm_num)
    (by norm_num) (2 ^ 49) (1 / 2 ^ 9) (by norm_num; linarith) hδ (by norm_num) certs131.1
    certs131.2 (2 ^ (-(281 : ℝ))) (by
      rw [show (83 / 2 : ℝ) - 1 / 2 = 41 by norm_num, show (2 : ℝ) ^ (10 + 1) = 2048 by norm_num]
      exact eps281 K (hK.trans (by norm_num)))
    T hT implA implE implM implF hAE hAM hAF hE hM hF oe hq hs (by rw [e1]; exact hwin)
  rwa [e2] at h

/-- **Fixed-point signing against exact Falcon at Falcon-1024** (hop A then hop B). For every Type 1
arithmetic `ρ` with `1/q` within `2⁻⁷⁸` and every experiment `oe` with at most `K ≤ 2²⁹`
signing-oracle calls (one ffSampling call each, restarts included) along every execution, on keys
passing `KeyBP.Good σ1024 δ` with `K·s2B1024 41.5 δ ≤ 2⁻⁹`: success `> T·2⁻¹²⁶ + 2⁻²⁸⁰` with
check-free Type 1 signing on the stored tree (F′, `runX1024` under `implF`) gives success
`> T·2⁻¹³¹ - 2⁻²⁸¹` with exact Falcon signing on the true tree (Y, `runT1024` under `implE`).
Hypotheses and what is not proved: those of `falcon1024_hopB` and of
`Falcon.falcon1024_exact64n'`. -/
theorem falcon1024_fixed_vs_true [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29)
    (hδ : (K : ℝ) * s2B1024 (83 / 2) δ ≤ 1 / 2 ^ 9) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS1024 aux δ) α) (hq : PathSum (wK1024 δ) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hA := Falcon.falcon1024_exact64n' ρ K hK T hT implA implE implM implF hAE hAM hAF hE hM hF
    (runA1024 ρ oe) (runX1024 ρ oe) (swap_runAP _ _ K oe hq) hs hwin
  rw [relabel_XP ρ implA implE implF hAE hAF hE hF oe] at hA
  refine falcon1024_hopB K (hK.trans (by norm_num)) hδ T hT implA implE implM implF hAE hAM hAF hE
    hM hF oe hq hs ?_
  exact (ENNReal.add_lt_add_iff_right (rpow_ne_top _)).1 ((thresh1024 T hT).trans_lt hA)

/-- **Instance**: the uniform tree error `2⁻⁴³` (`δ43_1024`), `K ≤ 2²⁹` (`s2B1024_43`). `Close
δ43_1024` is a hypothesis on each key (`KeyBP.Good`); `Exec.falcon1024_fixed_vs_true43_checked`
replaces it by `Exec.check1024`. Other hypotheses, and what is not proved: those of
`falcon1024_fixed_vs_true`. -/
theorem falcon1024_fixed_vs_true43 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specS1024 aux δ43_1024) α) (hq : PathSum (wK1024 δ43_1024) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ43_1024 oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
  have h0 : 0 ≤ s2B1024 (83 / 2) δ43_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true ρ K hK ?_ T hT implA implE implM implF hAE hAM hAF hE hM hF oe
    hq hs hwin
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_43]

/-- **Instance**: the tree error `δ127_1024` (`2⁻⁵⁸` at the root, `2⁻⁶³` below), `K ≤ 2²⁹`
(`s2B1024_127`). `Close δ127_1024` is a hypothesis on each key (`KeyBP.Good`);
`Exec.falcon1024_fixed_vs_true127_checked` replaces it by `Exec.check1024`. Other hypotheses, and
what is not proved: those of `falcon1024_fixed_vs_true`. -/
theorem falcon1024_fixed_vs_true127 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specS1024 aux δ127_1024) α) (hq : PathSum (wK1024 δ127_1024) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ127_1024 oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by
    have : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
    linarith
  have h0 : 0 ≤ s2B1024 (83 / 2) δ127_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true ρ K hK ?_ T hT implA implE implM implF hAE hAM hAF hE hM hF oe
    hq hs hwin
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_127]

/-! ## The λ = 256 level at Falcon-1024 -/

/-- The Rényi certificates of `renyiP` at `λ = 256`, `N = 2⁵¹`, `2⁶⁴` SamplerZ calls and
`S₂ = 2⁻¹⁰` (exponents `0.0217`, `0.1524` against `ln(5/4) = 0.2231`, values). At `S₂ = 2⁻⁹` the
second exponent is `0.3048` (a value), above `1/4 > N·ln(1 + 1/(4N))`, so `h36` fails there for
every `N`. -/
theorem certs256 :
    Real.exp ((2 * ((256 : ℕ) : ℝ) - 1) * (2 * ((256 : ℕ) : ℝ)) * ((1 / 2 ^ 40) ^ 2 * 2 ^ 64) *
        ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2) / (2 * (2 * ((256 : ℕ) : ℝ) - 2))) ≤
      (1 + 1 / (4 * ((2 ^ 51 : ℕ) : ℝ))) ^ (2 ^ 51 : ℕ) ∧
    Real.exp ((2 * ((256 : ℕ) : ℝ) - 3) * (1 / 2 ^ 10) / (2 * (1277 / 1000) ^ 2) +
      (2 * ((256 : ℕ) : ℝ) - 3) * (2 * ((256 : ℕ) : ℝ) - 2) * (1 / 2 ^ 10) * (1 / 2 ^ 30) /
        (2 * (2 * ((256 : ℕ) : ℝ) - 4))) ≤
      (1 + 1 / (4 * ((2 ^ 51 : ℕ) : ℝ))) ^ (2 ^ 51 : ℕ) := by
  constructor
  · refine le_trans ?_ (Falcon.five_quarters_le _ (by positivity))
    push_cast
    refine (Falcon.exp_le_one_add_two_mul _ (by positivity) (by norm_num)).trans ?_
    norm_num
  · refine le_trans ?_ (Falcon.five_quarters_le _ (by positivity))
    push_cast
    refine (Falcon.exp_le_inv_one_sub _ (by norm_num)).trans ?_
    norm_num

/-- The Rényi certificates of `renyiP` at `λ = 259`, `N = 2⁵¹`, `2⁶⁴` SamplerZ calls and
`S₂ = 2⁻¹⁰` (exponents `0.0220`, `0.1542` against `ln(5/4) = 0.2231`, values). At `S₂ = 2⁻⁹` the
second exponent is `0.3084` (a value), above `1/4 > N·ln(1 + 1/(4N))`, so `h36` fails there for
every `N`. -/
theorem certs259 :
    Real.exp ((2 * ((259 : ℕ) : ℝ) - 1) * (2 * ((259 : ℕ) : ℝ)) * ((1 / 2 ^ 40) ^ 2 * 2 ^ 64) *
        ((1 / 2 + 1 / 2 ^ 19) / (3 / 10) ^ 2) / (2 * (2 * ((259 : ℕ) : ℝ) - 2))) ≤
      (1 + 1 / (4 * ((2 ^ 51 : ℕ) : ℝ))) ^ (2 ^ 51 : ℕ) ∧
    Real.exp ((2 * ((259 : ℕ) : ℝ) - 3) * (1 / 2 ^ 10) / (2 * (1277 / 1000) ^ 2) +
      (2 * ((259 : ℕ) : ℝ) - 3) * (2 * ((259 : ℕ) : ℝ) - 2) * (1 / 2 ^ 10) * (1 / 2 ^ 30) /
        (2 * (2 * ((259 : ℕ) : ℝ) - 4))) ≤
      (1 + 1 / (4 * ((2 ^ 51 : ℕ) : ℝ))) ^ (2 ^ 51 : ℕ) := by
  constructor
  · refine le_trans ?_ (Falcon.five_quarters_le _ (by positivity))
    push_cast
    refine (Falcon.exp_le_one_add_two_mul _ (by positivity) (by norm_num)).trans ?_
    norm_num
  · refine le_trans ?_ (Falcon.five_quarters_le _ (by positivity))
    push_cast
    refine (Falcon.exp_le_inv_one_sub _ (by norm_num)).trans ?_
    norm_num

/-- `T·2⁻²⁵⁷ + 2⁻²⁸¹ + 2⁻²⁸⁰ ≤ T·2⁻²⁵⁶` for `T ≥ 1` (arithmetic). -/
theorem thresh256 (T : ℝ≥0∞) (hT : 1 ≤ T) :
    T * (2 : ℝ≥0∞) ^ (-(257 : ℝ)) + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) ≤
      T * (2 : ℝ≥0∞) ^ (-(256 : ℝ)) := by
  have h1 : (2 : ℝ≥0∞) ^ (-(281 : ℝ)) ≤ 2 ^ (-(258 : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ (-(280 : ℝ)) ≤ 2 ^ (-(258 : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have e1 := two_rpow_split 257
  have e0 := two_rpow_split 256
  norm_num at e1 e0
  rw [e0, mul_add, add_assoc]
  refine add_le_add le_rfl ?_
  calc (2 : ℝ≥0∞) ^ (-(281 : ℝ)) + 2 ^ (-(280 : ℝ)) ≤ 2 ^ (-(258 : ℝ)) + 2 ^ (-(258 : ℝ)) :=
      add_le_add h1 h2
    _ = 2 ^ (-(257 : ℝ)) := e1.symm
    _ ≤ T * 2 ^ (-(257 : ℝ)) := le_mul_of_one_le_left' hT

/--
**Hop A at Falcon-1024 at `λ = 256`** (normalized `1/q`, `K ≤ 2²⁹`): `Falcon.falcon1024_exact64n'`
with Theorem 2 at `λ = 256` (`renyiP`, `certs256`: `2048K ≤ 2⁶⁴` SamplerZ calls, centre budget
`K·(76·4.4·2⁻³² + 1084900·2⁻⁴⁰)² ≤ 2⁻¹⁰`, `centers_budget1024n`) in place of `λ = 128`: success
`> T·2⁻²⁵⁴ + 2⁻²⁸⁰` in F′ gives success `> T·2⁻²⁵⁶ - 2⁻²⁸⁰` in X. Hypotheses and what is not
proved: those of `Falcon.falcon1024_exact64n'`. -/
theorem falcon1024_exact256' [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α) (hswap : Swap1024 ρ K oa ox)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) < 𝒟[simulateQ implF ox] s) :
    T * (2 : ℝ≥0∞) ^ (-(256 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
  have hK64 : K ≤ 2 ^ 64 := hK.trans (by norm_num)
  have hc : (K : ℝ) * (76 * (44 / 10 / 2 ^ 32) + 1084900 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 10 := by
    have := mul_le_mul_of_nonneg_right hK'
        (sq_nonneg (76 * (44 / 10 / 2 ^ 32) + 1084900 / 2 ^ 40 : ℝ))
    linarith [centers_budget1024n]
  have he1 : 76 * (44 / 10 / 2 ^ 32) + 1084900 / 2 ^ 40 ≤ (1 / 2 ^ 10 : ℝ) := by norm_num
  have hd := etvDist_F_F'1024 ρ (by norm_num) _ inp64_1024_norm he1 (409 / 10) (by norm_num) le_rfl
    implF hF K (by linarith) hswap
  have h1 : 𝒟[simulateQ implF ox] s ≤ 𝒟[simulateQ implF oa] s + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) := by
    refine (le_add_etvDist _ _ hs).trans (add_le_add le_rfl ?_)
    rw [Measure.etvDist_comm]
    exact hd.trans (eps_leF1024 K hK64)
  have hwin' : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) < 𝒟[simulateQ implF oa] s :=
    (ENNReal.add_lt_add_iff_right (rpow_ne_top _)).1 (hwin.trans_le h1)
  have e1 : (2 : ℝ≥0∞) ^ (-(((256 : ℕ) : ℝ) - 2)) = 2 ^ (-(254 : ℝ)) := by congr 1; norm_num
  have e2 : (2 : ℝ≥0∞) ^ (-((256 : ℕ) : ℝ)) = 2 ^ (-(256 : ℝ)) := by norm_num
  have h := renyiP 256 (2 ^ 51) (by norm_num) (by norm_num) (2 ^ 64) (1 / 2 ^ 10) certs256.1
    certs256.2 T hT implA implE implM implF hAE hAM hAF hE hM hF oa
    ((Uses1024.pathN hswap.usesG_left).weaken (by linarith))
    ((Uses1024.pathS (by norm_num) _ inp64_1024_norm he1 hswap.usesG_left).weaken hc)
    hs (by rw [e1]; exact hwin')
  rw [e2] at h
  have hd' := etvDist_E_X1024 ρ (by norm_num) _ inp64_1024_norm he1 41 (by norm_num) le_rfl implE
    hE K hswap
  exact h.trans_le ((le_add_etvDist _ _ hs).trans
    (add_le_add le_rfl (hd'.trans (eps_le1024 K hK64))))

/--
**Hop B at Falcon-1024 at `λ′ = 259`**: `falcon1024_hopB` with Theorem 2 at `λ = 259` (`renyiP`,
`certs259`: `2048K ≤ 2⁶⁴` SamplerZ calls, so `K ≤ 2⁵³`, and `S₂ = 2⁻¹⁰`). On keys passing
`KeyBP.Good σ1024 δ` with `K·s2B1024 41.5 δ ≤ 2⁻¹⁰`: success `> T·2⁻²⁵⁷ + 2⁻²⁸¹` in X gives success
`> T·2⁻²⁵⁹ - 2⁻²⁸¹` in Y. Hypotheses and what is not proved: those of `falcon1024_hopB`. -/
theorem falcon1024_hopB259 [∀ t, Countable (aux t)] (K : ℕ) (hK : K ≤ 2 ^ 53)
    (hδ : (K : ℝ) * s2B1024 (83 / 2) δ ≤ 1 / 2 ^ 10) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS1024 aux δ) α) (hq : PathSum (wK1024 δ) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(257 : ℝ)) + (2 : ℝ≥0∞) ^ (-(281 : ℝ)) <
        𝒟[simulateQ implF (runB1024 δ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 53 := by exact_mod_cast hK
  have e1 : (2 : ℝ≥0∞) ^ (-(((259 : ℕ) : ℝ) - 2)) = 2 ^ (-(257 : ℝ)) := by congr 1; norm_num
  have e2 : (2 : ℝ≥0∞) ^ (-((259 : ℕ) : ℝ)) = 2 ^ (-(259 : ℝ)) := by norm_num
  have h := hopBP tb1024.lam_nonneg (83 / 2) (by norm_num) K 259 (2 ^ 51) (by norm_num)
    (by norm_num) (2 ^ 64) (1 / 2 ^ 10) (by norm_num; linarith) hδ (by norm_num) certs259.1
    certs259.2 (2 ^ (-(281 : ℝ))) (by
      rw [show (83 / 2 : ℝ) - 1 / 2 = 41 by norm_num, show (2 : ℝ) ^ (10 + 1) = 2048 by norm_num]
      exact eps281 K (hK.trans (by norm_num)))
    T hT implA implE implM implF hAE hAM hAF hE hM hF oe hq hs (by rw [e1]; exact hwin)
  rwa [e2] at h

/-- **Fixed-point signing against exact Falcon at Falcon-1024 at the `λ = 256` level** (hop A at
`λ = 256`, hop B at `λ′ = 259`). For every Type 1 arithmetic `ρ` with `1/q` within `2⁻⁷⁸` and every
experiment `oe` with at most `K ≤ 2²⁹` signing-oracle calls (one ffSampling call each, restarts
included) along every execution, on keys passing `KeyBP.Good σ1024 δ` with
`K·s2B1024 41.5 δ ≤ 2⁻¹⁰`: success `> T·2⁻²⁵⁴ + 2⁻²⁸⁰` with check-free Type 1 signing on the
stored tree (F′, `runX1024` under `implF`) gives success `> T·2⁻²⁵⁹ - 2⁻²⁸¹` with exact Falcon
signing on the true tree (Y, `runT1024` under `implE`). Hypotheses and what is not proved: those of
`falcon1024_hopB259` and of `falcon1024_exact256'`. -/
theorem falcon1024_fixed_vs_true256 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29)
    (hδ : (K : ℝ) * s2B1024 (83 / 2) δ ≤ 1 / 2 ^ 10) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS1024 aux δ) α) (hq : PathSum (wK1024 δ) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hA := falcon1024_exact256' ρ K hK T hT implA implE implM implF hAE hAM hAF hE hM hF
    (runA1024 ρ oe) (runX1024 ρ oe) (swap_runAP _ _ K oe hq) hs hwin
  rw [relabel_XP ρ implA implE implF hAE hAF hE hF oe] at hA
  refine falcon1024_hopB259 K (hK.trans (by norm_num)) hδ T hT implA implE implM implF hAE hAM hAF
    hE hM hF oe hq hs ?_
  exact (ENNReal.add_lt_add_iff_right (rpow_ne_top _)).1 ((thresh256 T hT).trans_lt hA)

/-- **Instance**: the uniform tree error `2⁻⁴³` (`δ43_1024`), `K ≤ 2²⁹` (`s2B1024_43`). `Close
δ43_1024` is a hypothesis on each key (`KeyBP.Good`); `Exec.falcon1024_fixed_vs_true256_43_checked`
replaces it by `Exec.check1024`. Other hypotheses, and what is not proved: those of
`falcon1024_fixed_vs_true256`. -/
theorem falcon1024_fixed_vs_true256_43 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specS1024 aux δ43_1024) α) (hq : PathSum (wK1024 δ43_1024) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ43_1024 oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
  have h0 : 0 ≤ s2B1024 (83 / 2) δ43_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true256 ρ K hK ?_ T hT implA implE implM implF hAE hAM hAF hE hM hF
    oe hq hs hwin
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_43]

/-- **Instance**: the tree error `δ127_1024` (`2⁻⁵⁸` at the root, `2⁻⁶³` below), `K ≤ 2²⁹`
(`s2B1024_127`). `Close δ127_1024` is a hypothesis on each key (`KeyBP.Good`);
`Exec.falcon1024_fixed_vs_true256_127_checked` replaces it by `Exec.check1024`. Other hypotheses,
and what is not proved: those of `falcon1024_fixed_vs_true256`. -/
theorem falcon1024_fixed_vs_true256_127 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (oe : OracleComp (specS1024 aux δ127_1024) α) (hq : PathSum (wK1024 δ127_1024) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ implF (runX1024 ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) < 𝒟[simulateQ implE (runT1024 δ127_1024 oe)] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by
    have : (K : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hK
    linarith
  have h0 : 0 ≤ s2B1024 (83 / 2) δ127_1024 := s2BP_nonneg _ _ _ _
  refine falcon1024_fixed_vs_true256 ρ K hK ?_ T hT implA implE implM implF hAE hAM hAF hE hM hF
    oe hq hs hwin
  linarith [mul_le_mul_of_nonneg_right hK' h0, s2B1024_127]

end FalconPrecision.Errors.HopB
