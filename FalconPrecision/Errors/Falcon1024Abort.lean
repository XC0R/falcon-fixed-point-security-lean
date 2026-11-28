/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.AbortExact
public import FalconPrecision.Errors.Falcon1024Model

/-! # Abort bounds of Type 1 signing at Falcon-1024 (tree depth 10)

The route B′ argument of `AbortExact` at Falcon-1024, with SamplerZ answers clamped to within
`41` of the centre (Falcon-512: `30`). Tables `eT1024`, `gT1024` for depth 10 (`tables1024`): the
deterministic part of the input is in `‖·‖∞ ≤ 7541760 = 1024·7365` (`‖ĉ/q‖∞ ≤ 1024`,
`‖F̂‖∞ ≤ 7365`), and every checked exact value is in `‖·‖ ≤ 2²⁷ - 2`, so with clamped answers no
range check of `sign164R R64_1024` fires (`sign1024_clamp`).

For an input bound `inp64_1024 εq ≤ e` with `76 e + 1084900·2⁻⁴⁰ ≤ 2⁻¹⁰`: `etvDist_E_X1024`,
exact signing and abort-free exact signing are within `2·p y·2048K` in total variation for every
clamp radius `1/2 ≤ y ≤ 41` and every number `K` of signing calls;
`etvDist_F_F'1024`: Type 1 signing and check-free Type 1 signing within `2·p_F y·2048K` for
`1/2 ≤ y ≤ 40.9` and `K·(76 e + 1084900·2⁻⁴⁰)² ≤ 2⁻⁸`. At `y = 41`, `40.9` the constants
`2·p 41·2048K` and `2·p_F 40.9·2048K` are `≤ 2⁻²⁸⁰` for every `K ≤ 2⁶⁴` (`eps_le1024`,
`eps_leF1024`); the F-side bound itself needs `K·(76 e + 1084900·2⁻⁴⁰)² ≤ 2⁻⁸` (`K ≤ 2³¹` at
either input bound, a value). The radii grow from Falcon-512's `30`, `29.9` because at `y = 30`
the E-side constant `2·p 30·2048K` is about `2⁻¹⁵³` at `K = 2²⁹` (a value, not proved), above
`2⁻²⁵⁶`.

`Falcon.falcon1024_exact64n'`: hop A at Falcon-1024 (F′ against X, Theorem 2 at `λ = 128`,
`K ≤ 2²⁹`, additive `2⁻²⁸⁰`).

Not proved here: hop A at `λ = 256` and hop B (both proved in `Falcon1024HopB`), and that
`FTreeP.Real` holds for a stored tree (a hypothesis, as at Falcon-512). -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFTReal
  FalconPrecision.Errors.AbortTV ComplexConjugate

namespace FalconPrecision.Errors.AbortExact

open FalconPrecision.Errors.FFSamp MeasureTheory LatticeCrypto
open scoped ENNReal

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- ℓ2 bounds of the deviation of a call at depth `L`, Falcon-1024 (`y ≤ 41`). -/
noncomputable def eT1024 (L : ℕ) : ℝ :=
  (match L with
    | 0 => 581 | 1 => 1837 | 2 => 5807 | 3 => 18357 | 4 => 58027 | 5 => 183425 | 6 => 579809
    | 7 => 1832784 | 8 => 5793454 | 9 => 18313183 | _ => 855053713) / 10

/-- ℓ2 bounds of the random part of the input of a call at depth `L`, Falcon-1024. -/
noncomputable def gT1024 (L : ℕ) : ℝ :=
  (match L with
    | 0 => 26557107 | 1 => 37556239 | 2 => 53109437 | 3 => 75099161 | 4 => 106179297
    | 5 => 150076776 | 6 => 211979417 | 7 => 298962087 | 8 => 420202669 | 9 => 586065126
    | _ => 0) / 10

theorem tables1024 (L : ℕ) (hL : L < 10) :
    2 * ((1 + lam1024 L) ^ 2 + 1) * eT1024 L ^ 2 ≤ eT1024 (L + 1) ^ 2 ∧
      gT1024 (L + 1) + lam1024 L * (14143 / 10000) * eT1024 L ≤ 14142 / 10000 * gT1024 L ∧
      7541760 + gT1024 (L + 1) + lam1024 L * (14143 / 10000) * eT1024 L ≤ 2 ^ 27 - 2 ∧
      7541760 + gT1024 L + eT1024 L ≤ 2 ^ 27 - 2 ∧ 0 ≤ eT1024 L ∧ 0 ≤ gT1024 L ∧
      0 ≤ gT1024 (L + 1) := by
  interval_cases L <;> norm_num [eT1024, gT1024, lam1024]

theorem eT1024_nonneg (L : ℕ) : 0 ≤ eT1024 L := by unfold eT1024; split <;> norm_num

theorem eT1024_zero : 2 * 41 ^ 2 ≤ eT1024 0 ^ 2 := by norm_num [eT1024]

theorem gT1024_ten : gT1024 10 = 0 := by norm_num [gT1024]

theorem norm_t0E_le1024 (k : Key1024) (c : Fin (2 ^ 10) → ℤ) (hc : ∀ i, |c i| < 12289)
    (o : Out 10) : ‖t0E k c o‖ ≤ 7541760 := by
  rw [t0E, norm_neg, norm_mul]
  have := mul_le_mul (norm_fftE_cdqP c hc o) (k.hF o) (norm_nonneg _) (by norm_num)
  linarith

theorem norm_t1E_le1024 (k : Key1024) (c : Fin (2 ^ 10) → ℤ) (hc : ∀ i, |c i| < 12289)
    (o : Out 10) : ‖t1E k c o‖ ≤ 7541760 := by
  rw [t1E, norm_mul]
  have := mul_le_mul (norm_fftE_cdqP c hc o) (k.hf o) (norm_nonneg _) (by norm_num)
  linarith

theorem l2_zero_le1024 {L : ℕ} : l2 (0 : Out L → ℂ) ≤ gT1024 10 := by
  rw [gT1024_ten]; unfold l2; simp

variable {εq : ℝ}

/--
**No check of Type 1 signing at Falcon-1024 fires in T**: with answers within `41` of the centre, a
check passing on exact values in `‖·‖ ≤ 2²⁷ - 2` leaves the call equal to abort-free signing. -/
theorem sign1024G_clamp (ρ : Arith64 εq)
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hso : ∀ q : Falcon.CallP, AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 41)
        (so (.inr q) : OracleComp _ ℤ))
    (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop)
    (hchk : ∀ L vh v, (∀ o, ‖v o‖ ≤ 2 ^ 27 - 2) → chk L vh v) (k : Key1024) (hk : k.tree.Real)
    (c : Fin (2 ^ 10) → ℤ) :
    simulateQ so (sign164G (aux := aux) ρ chk k c) =
      simulateQ so (sign164G (aux := aux) ρ (fun _ _ _ => True) k c) := by
  unfold sign164G
  split_ifs with hc
  · rw [simulateQ_map, simulateQ_map, (ffsG_clampP tb1024.lam_nonneg 41 7541760 (2 ^ 27 - 2)
      eT1024 gT1024 10 tables1024 eT1024_zero eT1024_nonneg ρ.toArith (1 / 2 ^ 64) so hso chk
      hchk k.tree hk le_rfl (t0E k c) (t1E k c) (t0C64 ρ k c) (t1C64 ρ k c) (t0E k c)
      (t1E k c) 0 0 (add_zero _).symm (add_zero _).symm (norm_t0E_le1024 k c hc)
      (norm_t1E_le1024 k c hc) l2_zero_le1024 l2_zero_le1024 (isReal_t0EP k c)
      (isReal_t1EP k c)).1]
  · rfl

/-- `sign164R R64_1024` in T is abort-free Type 1 signing in T, for an input bound
`inp64_1024 εq ≤ e`. -/
theorem sign1024_clamp (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64_1024 εq ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10)
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hso : ∀ q : Falcon.CallP, AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 41)
        (so (.inr q) : OracleComp _ ℤ)) (k : Key1024)
    (hk : k.tree.Real) (c : Fin (2 ^ 10) → ℤ) :
    simulateQ so (sign164R (aux := aux) R64_1024 ρ k c) =
      simulateQ so (sign164G (aux := aux) ρ (fun _ _ _ => True) k c) := by
  rw [sign1024_eq_margin ρ hεq e he he1 k c]
  exact sign1024G_clamp ρ so hso _
      (fun L vh v h => InBR.chkM fun o => by unfold R64_1024; exact h o) k hk c

theorem sign1024G_pathN (ρ : Arith64 εq) (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop)
    (k : Key1024) (c : Fin (2 ^ 10) → ℤ) :
    PathSum w1 (sign164G (aux := aux) ρ chk k c) 2048 := by
  unfold sign164G
  split_ifs
  · rw [map_eq_bind_pure_comp]
    exact (PathSum.bind ((ffs_pathNGP ρ.toArith _ chk k.tree _ _ _ _).weaken (by norm_num))
      (T := 0) fun _ => .pure _ le_rfl).weaken (le_of_eq (add_zero _))
  · exact .pure _ (by norm_num)

/-- `ox` is `oa` with every call of Type 1 signing at Falcon-1024 replaced by abort-free exact
signing (at most `K` calls, keys with a real stored tree); every other query is auxiliary. -/
abbrev Swap1024 (ρ : Arith64 εq) : ℕ → {α : Type} →
    OracleComp (FalconGame.spec aux Falcon.CallP) α →
      OracleComp (FalconGame.spec aux Falcon.CallP) α → Prop :=
  SwapP 10 256 7365 (1298280334 / 10 ^ 9) σmin1024_ok lam1024 (sign164R R64_1024 ρ)
    (sign164G ρ fun _ _ _ => True)

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- **Exact signing against abort-free exact signing at Falcon-1024**: within `2·p y·2048K` in total
variation, for every `K` and every clamp radius `1/2 ≤ y ≤ 41`. -/
theorem etvDist_E_X1024 (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64_1024 εq ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10) (y : ℝ) (hy : 1 / 2 ≤ y) (hy41 : y ≤ 41)
    (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (K : ℕ) {α : Type} [MeasurableSpace α] {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap1024 ρ K oa ox) :
    (𝒟[simulateQ implE oa]).etvDist 𝒟[simulateQ implE ox] ≤
      2 * ENNReal.ofReal (pclamp y * (K * 2048)) :=
  etvDist_E_XP _ _ 2048 (by norm_num) (sign1024_pathN ρ) (sign1024G_pathN ρ _) 41 y hy hy41
    (fun so hso key c hk => sign1024_clamp ρ hεq e he he1 so hso key hk c) implE hE K h

/-- **Type 1 signing against abort-free Type 1 signing at Falcon-1024**, both answered by `implF`:
within `2·p_F y·2048K`, for every clamp radius `1/2 ≤ y ≤ 40.9` and `K` with
`K·(76 e + 1084900·2⁻⁴⁰)² ≤ 2⁻⁸`. -/
theorem etvDist_F_F'1024 (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64_1024 εq ≤ e)
    (he1 : 76 * e + 1084900 / 2 ^ 40 ≤ 1 / 2 ^ 10) (y : ℝ) (hy : 1 / 2 ≤ y) (hy' : y ≤ 409 / 10)
    [hA : ∀ t, Nonempty (aux t)] (implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (K : ℕ) (hKe : (K : ℝ) * (76 * e + 1084900 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 8) {α : Type}
    [MeasurableSpace α] {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap1024 ρ K oa ox) :
    (𝒟[simulateQ implF oa]).etvDist 𝒟[simulateQ implF ox] ≤
      2 * ENNReal.ofReal (pclampF y * (K * 2048)) :=
  etvDist_F_F'P _ _ 2048 _ (by norm_num) (sq_nonneg _) (sign1024_pathN ρ)
    (sign1024_pathS ρ hεq e he he1) 41 y hy (by linarith)
    (fun so hso key c hk => sign1024_clamp ρ hεq e he he1 so hso key hk c) implF hF K hKe h

/-- `exp(-41²/(2·1.825²)) ≤ 2⁻³⁶³ = (2⁻¹²¹)³`. -/
theorem exp_41 : Real.exp (-(41 ^ 2 / (2 * (1825 / 1000) ^ 2))) ≤ (1 / 2 ^ 121) ^ 3 := by
  have h2 : ((2 : ℝ) ^ 121) ^ 3 ≤ Real.exp 252 := by
    have := Real.exp_one_gt_d9
    calc ((2 : ℝ) ^ 121) ^ 3 ≤ (2.718 ^ 84) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by norm_num) 3
      _ ≤ (Real.exp 1 ^ 84) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by linarith) 84) 3
      _ = Real.exp 252 := by rw [← pow_mul, ← Real.exp_nat_mul]; norm_num
  calc Real.exp (-(41 ^ 2 / (2 * (1825 / 1000) ^ 2))) ≤ Real.exp (-252) :=
        Real.exp_le_exp.2 (by norm_num)
    _ = (Real.exp 252)⁻¹ := Real.exp_neg _
    _ ≤ (((2 : ℝ) ^ 121) ^ 3)⁻¹ := inv_anti₀ (by positivity) h2
    _ = (1 / 2 ^ 121) ^ 3 := by rw [one_div, inv_pow]

theorem one_div_two_pow_280 : (1 / 2 ^ 140 : ℝ) ^ 2 = 1 / 2 ^ 280 := by
  rw [div_pow, one_pow, ← pow_mul]

theorem two_rpow_neg280 : ENNReal.ofReal (1 / 2 ^ 280) = (2 : ℝ≥0∞) ^ (-(280 : ℝ)) := by
  rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos (by norm_num),
    Real.rpow_neg (by norm_num), show (280 : ℝ) = ((280 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    one_div]

/-- **The constant at Falcon-1024**: `2·p 41·2048K ≤ 2⁻²⁸⁰` for `K ≤ 2⁶⁴`. -/
theorem eps_le1024 (K : ℕ) (hK : K ≤ 2 ^ 64) :
    2 * ENNReal.ofReal (pclamp 41 * (K * 2048)) ≤ (2 : ℝ≥0∞) ^ (-(280 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hK
  have hp : pclamp 41 ≤ 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 121) ^ 3 := by
    unfold pclamp
    exact mul_le_mul_of_nonneg_left exp_41 (by norm_num)
  have hc : 2 * (2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 121) ^ 3 * (2 ^ 64 * 2048)) ≤
      (1 / 2 ^ 140 : ℝ) ^ 2 := by norm_num
  have hx : 2 * (pclamp 41 * (K * 2048)) ≤ 1 / 2 ^ 280 :=
    calc 2 * (pclamp 41 * (K * 2048))
        ≤ 2 * (2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 121) ^ 3 * (2 ^ 64 * 2048)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hp
            (mul_le_mul_of_nonneg_right hK' (by norm_num)) (by positivity) (by positivity))
            (by norm_num)
      _ ≤ (1 / 2 ^ 140) ^ 2 := hc
      _ = 1 / 2 ^ 280 := one_div_two_pow_280
  rw [← two_rpow_neg280, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hx

/-- `exp(-40.9²/(2·1.826²)) ≤ 2⁻³⁶⁰ = (2⁻⁷²)⁵`. -/
theorem exp_409 : Real.exp (-((409 / 10) ^ 2 / (2 * (1826 / 1000) ^ 2))) ≤ (1 / 2 ^ 72) ^ 5 := by
  have h2 : ((2 : ℝ) ^ 72) ^ 5 ≤ Real.exp 250 := by
    have := Real.exp_one_gt_d9
    calc ((2 : ℝ) ^ 72) ^ 5 ≤ (2.718 ^ 50) ^ 5 :=
          pow_le_pow_left₀ (by positivity) (by norm_num) 5
      _ ≤ (Real.exp 1 ^ 50) ^ 5 :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by linarith) 50) 5
      _ = Real.exp 250 := by rw [← pow_mul, ← Real.exp_nat_mul]; norm_num
  calc Real.exp (-((409 / 10) ^ 2 / (2 * (1826 / 1000) ^ 2))) ≤ Real.exp (-250) :=
        Real.exp_le_exp.2 (by norm_num)
    _ = (Real.exp 250)⁻¹ := Real.exp_neg _
    _ ≤ (((2 : ℝ) ^ 72) ^ 5)⁻¹ := inv_anti₀ (by positivity) h2
    _ = (1 / 2 ^ 72) ^ 5 := by rw [one_div, inv_pow]

/-- **The constant of the F side at Falcon-1024**: `2·p_F 40.9·2048K ≤ 2⁻²⁸⁰` for `K ≤ 2⁶⁴`. -/
theorem eps_leF1024 (K : ℕ) (hK : K ≤ 2 ^ 64) :
    2 * ENNReal.ofReal (pclampF (409 / 10) * (K * 2048)) ≤ (2 : ℝ≥0∞) ^ (-(280 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hK
  have hp : pclampF (409 / 10) ≤ 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 72) ^ 5 := by
    unfold pclampF
    exact mul_le_mul_of_nonneg_left exp_409 (by norm_num)
  have hc : 2 * (2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 72) ^ 5 * (2 ^ 64 * 2048)) ≤
      (1 / 2 ^ 140 : ℝ) ^ 2 := by norm_num
  have hx : 2 * (pclampF (409 / 10) * (K * 2048)) ≤ 1 / 2 ^ 280 :=
    calc 2 * (pclampF (409 / 10) * (K * 2048))
        ≤ 2 * (2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 72) ^ 5 * (2 ^ 64 * 2048)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hp
            (mul_le_mul_of_nonneg_right hK' (by norm_num)) (by positivity) (by positivity))
            (by norm_num)
      _ ≤ (1 / 2 ^ 140) ^ 2 := hc
      _ = 1 / 2 ^ 280 := one_div_two_pow_280
  rw [← two_rpow_neg280, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hx

end FalconPrecision.Errors.AbortExact

namespace FalconPrecision.Falcon

open MeasureTheory LatticeCrypto FalconPrecision.Errors.FFSamp FalconPrecision.Errors.AbortExact
open scoped ENNReal

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/--
**Hop A at Falcon-1024** (`λ = 128`, normalized `1/q`, `K ≤ 2²⁹`): check-free Type 1 signing F′
(`sign164G ρ (fun _ _ _ => True)`, `ox` answered by `implF`) against abort-free exact signing X on
the stored tree (the same `ox` answered by `implE`), where `oa` is `ox` with every call replaced by
`sign164R R64_1024 ρ` (`Swap1024`): success `> T·2⁻¹²⁶ + 2⁻²⁸⁰` in F′ gives success
`> T·2⁻¹²⁸ - 2⁻²⁸⁰` in X. Proof as `falcon512_exact64n'`: F′ to F by `etvDist_F_F'1024` at
`y = 40.9` (`eps_leF1024`); F to E by Theorem 2 at `λ = 128` (`falcon512_proved_n64`, a statement
on SamplerZ calls only, with `≤ 2048K ≤ 2⁶⁴` calls, `Uses1024.pathN`, and the centre budget
`K·(76·4.4·2⁻³² + 1084900·2⁻⁴⁰)² ≤ 2⁻¹⁰`, `Uses1024.pathS`, `centers_budget1024n`); E to X by
`etvDist_E_X1024` at `y = 41` (`eps_le1024`). Hypotheses and what is not proved: those of
`falcon512_exact64n'` with `Key1024`, `FTree1024` and `sign164R R64_1024` in place of `Key`,
`FTree` and `sign164`. At `λ = 256`: `Errors.HopB.falcon1024_exact256'`. -/
theorem falcon1024_exact64n' (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 29) (T : ℝ≥0∞)
    (hT : 1 ≤ T) [hA : ∀ t, Nonempty (aux t)]
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa ox : OracleComp (FalconGame.spec aux CallP) α) (hswap : Swap1024 ρ K oa ox)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) < 𝒟[simulateQ implF ox] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) := by
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
  have hwin' : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s :=
    (ENNReal.add_lt_add_iff_right (ENNReal.rpow_ne_top_of_nonneg' (by norm_num) (by norm_num))).1
      (hwin.trans_le h1)
  have h := falcon512_proved_n64 T hT implA implE implM implF hAE hAM hAF hE hM hF oa
    ((Uses1024.pathN hswap.usesG_left).weaken (by linarith))
    ((Uses1024.pathS (by norm_num) _ inp64_1024_norm he1 hswap.usesG_left).weaken (by linarith))
    hs hwin'
  have hd' := etvDist_E_X1024 ρ (by norm_num) _ inp64_1024_norm he1 41 (by norm_num) le_rfl implE
    hE K hswap
  exact h.trans_le ((le_add_etvDist _ _ hs).trans
    (add_le_add le_rfl (hd'.trans (eps_le1024 K hK64))))

end FalconPrecision.Falcon
