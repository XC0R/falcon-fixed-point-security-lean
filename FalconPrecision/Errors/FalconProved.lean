/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Instances

/-! # Theorem 2 at Falcon-512 with per-call budgets (TASK-009 S7f)

`falcon512_proved` is Theorem 2 at `λ = 128` for SamplerZ calls `CallP` whose leaf error `|σ̄/σ - 1|
≤ 2⁻⁴²` (`CallP.hΔσ`) is assumed per call. The worlds answer a call by `D_{σ,t}` (E), `D_{σ̄,t}` (M)
and `D_{σ̄,t̄}` (F).

Reference world. `falcon512_leaf` measures `σ̄` against the true-tree leaves `σ` (exact ffLDL⋆ from
`f, g, F, G`); `falcon512_centers` measures `t̄` against exact ffSampling run on the stored tree
`ℓ̂`. Fed together into `CallP`, E samples `D_{σ, t(ℓ̂)}`, which is neither exact Falcon nor exact
signing with the stored tree. The consistent instantiation is hop A (`CallP.stored`): `σ = σ̄` the
stored leaves and `t` the exact centres with the stored `ℓ̂`; then `hΔσ` is trivial,
`falcon512_leaf` is not needed for it, and E is exact signing with the stored tree. The stored
leaves must still lie in `[1.2778, 1.825]` (`CallP.hσ`): from a leaf check at key expansion (FIPS
206 draft: `σ̄ ∈ [σmin, σmax]`, else `⊥`; `FFSampModel.FTree`), or from `falcon512_leaf` together
with the true leaves in `[σmin, σmax]` (not formalised). Hop B, from the stored tree to the true
tree (centre shift `(t1 - z1)(ℓ̂ - ℓ)`, leaves `σ̄ → σ`), hence any statement relative to exact
Falcon, is not proved.

`hN` and `hS₂` are hypotheses here. `centers_budget` is the arithmetic that discharges `hS₂` for at
most `2³⁸` ffSampling calls (restarts included), each with centre errors of ℓ2 norm at most
`49·3.65·2⁻³² + 135700·2⁻⁴²`; `SignModel.falcon512_model` proves `hN` and `hS₂` for an `OracleComp`
model of fixed-point signing. `hS₂` ranges over every history of a full-support SamplerZ, while the
tag-21 range `|t̂|, |ẑ| < 2²¹` behind the per-call budget holds only with high probability (Lemma
12): `oa` must clamp or abort out-of-range values as the same function of the history in all three
worlds. `hN` (`2⁵¹` SamplerZ calls, i.e. `2⁴¹` ffSampling calls) is looser than the `2³⁸` ffSampling
calls (`2⁴⁸` SamplerZ calls) that `centers_budget` fits; the latter is the effective bound. -/

@[expose] public section

open MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Falcon

/-- Relative leaf error `2⁻⁴²` gives `|1/σ̄² - 1/σ²| ≤ 2⁻⁴⁰` on `σ ≥ 1`. -/
theorem inv_sq_sub_le42 (s sb : ℝ) (hs : 1 ≤ s) (hsb : 0 < sb) (h : |sb / s - 1| ≤ 1 / 2 ^ 42) :
    |1 / sb ^ 2 - 1 / s ^ 2| ≤ 1 / 2 ^ 40 := by
  have hs0 : 0 < s := by linarith
  set r := sb / s with hr
  have hsb' : sb = r * s := by rw [hr]; field_simp
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrlo : 1 - 1 / 2 ^ 42 ≤ r := by linarith
  have hid : 1 / sb ^ 2 - 1 / s ^ 2 = (1 - r) * (1 + r) / (r ^ 2 * s ^ 2) := by
    rw [hsb']; field_simp; ring
  rw [hid, abs_div, abs_mul, abs_of_pos (by positivity : 0 < r ^ 2 * s ^ 2),
      abs_of_pos (by linarith : 0 < 1 + r)]
  rw [div_le_iff₀ (by positivity)]
  have hrs : (1 - 1 / 2 ^ 42) ^ 2 ≤ r ^ 2 * s ^ 2 := by
    have : (1 - 1 / 2 ^ 42 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hrlo 2
    nlinarith [one_le_pow₀ (n := 2) hs]
  have hab : |1 - r| ≤ 1 / 2 ^ 42 := by rw [abs_sub_comm]; exact h
  calc |1 - r| * (1 + r) ≤ 1 / 2 ^ 42 * (2 + 1 / 2 ^ 42) :=
        mul_le_mul hab (by linarith) (by linarith) (by norm_num)
    _ ≤ 1 / 2 ^ 40 * (1 - 1 / 2 ^ 42) ^ 2 := by norm_num
    _ ≤ 1 / 2 ^ 40 * (r ^ 2 * s ^ 2) := by gcongr

/--
A SamplerZ call: reference and computed leaf and centre, with the leaf error bound `hΔσ` assumed per
call. `σ ≤ 1.825` (Lemma 5 at `τlo = 0.3` needs `σ ≤ √(10/3)`) admits stored leaves rounded above
`σmax = 1.8205`. -/
structure CallP where
  σ : ℝ
  σbar : ℝ
  t : ℝ
  tbar : ℝ
  hσ : 12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000
  hσbar : 0 < σbar
  hΔσ : |σbar / σ - 1| ≤ 1 / 2 ^ 42

/-- Hop A: the reference leaf is the stored leaf. -/
def CallP.stored (σ t tbar : ℝ) (hσ : 12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000) : CallP :=
  ⟨σ, σ, t, tbar, hσ, by linarith [hσ.1], by
    rw [div_self (by linarith [hσ.1]), sub_self, abs_zero]; positivity⟩

theorem CallP.hτ (c : CallP) : |1 / c.σbar ^ 2 - 1 / c.σ ^ 2| ≤ 1 / 2 ^ 40 :=
  inv_sq_sub_le42 _ _ (by linarith [c.hσ.1]) c.hσbar c.hΔσ

theorem CallP.hleaf (c : CallP) (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 511) :
    3 / 10 ≤ 1 / c.σ ^ 2 ∧ 1 / c.σ ^ 2 ≤ (1000 / 1277) ^ 2 ∧
      3 / 10 ≤ 1 / c.σ ^ 2 + a * (1 / c.σbar ^ 2 - 1 / c.σ ^ 2) ∧
      1 / c.σ ^ 2 + a * (1 / c.σbar ^ 2 - 1 / c.σ ^ 2) ≤ (1000 / 1277) ^ 2 := by
  obtain ⟨h1, h2⟩ := c.hσ
  have hp : 0 < c.σ := by linarith
  have hlo : 3002 / 10000 ≤ 1 / c.σ ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have hhi : 1 / c.σ ^ 2 ≤ 6125 / 10000 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨h3, h4⟩ := abs_le.1 c.hτ
  refine ⟨by linarith, hhi.trans (by norm_num), ?_, ?_⟩ <;> nlinarith

theorem CallP.hσbar_ge (c : CallP) : 1277 / 1000 ≤ c.σbar := by
  obtain ⟨h1, -⟩ := c.hσ
  have := abs_le.1 c.hΔσ
  have hp : 0 < c.σ := by linarith
  have : c.σbar = c.σ * (c.σbar / c.σ) := by field_simp
  nlinarith

/--
`2³⁸` ffSampling calls, each with center errors of ℓ2 norm `≤ 49·3.65·2⁻³² + 135700·2⁻⁴²`, sum to `≤
2⁻⁹`. -/
theorem centers_budget : (2 : ℝ) ^ 38 * (49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42) ^ 2 ≤ 1 /
    2 ^ 9 := by
  norm_num

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Theorem 2 at Falcon-512** (`λ = 128`) for calls with leaf error `≤ 2⁻⁴²`, under the
execution-level hypotheses `hN` (call count) and `hS₂` (centre-error path sum), relative to the
world E given by `CallP.σ`, `CallP.t` (exact signing with the stored tree under `CallP.stored`; hop
B to exact Falcon is not proved). -/
theorem falcon512_proved (T : ℝ≥0∞) (hT : 1 ≤ T) (implA : QueryImpl aux m)
    (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
        (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux CallP) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa (2 ^ 51))
    (hS₂ : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun q : CallP => (q.tbar - q.t) ^ 2) oa
        (1 / 2 ^ 9))
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have h :=
      FalconGame.theorem2 128 (2 ^ 51)
          (by norm_num) T hT CallP.σ CallP.σbar CallP.t CallP.tbar (3 / 10)
    (1277 / 1000) ((1 / 2 ^ 40) ^ 2 * 2 ^ 51)
        (1 / 2 ^ 9) implA implE implM implF hAE hAM hAF hE hM hF
    (fun q => by linarith [q.hσ.1]) (by norm_num)
    (fun q => by have := q.hleaf (2 * 128 - 1) (by norm_num) (by norm_num); push_cast; exact this)
    le_rfl (fun q => q.hσbar_ge) oa
    (hN.mono (sq_nonneg _) fun x => by
      cases x with
      | inl _ => simp
      | inr q => simpa using sq_le_sq' (abs_le.1 q.hτ).1 (abs_le.1 q.hτ).2) hS₂
    (by
      refine le_trans ?_ (five_quarters_le _ (by positivity))
      push_cast
      refine (exp_le_one_add_two_mul _ (by positivity) (by norm_num)).trans ?_
      norm_num)
    (by
      refine le_trans ?_ (five_quarters_le _ (by positivity))
      push_cast
      refine (exp_le_inv_one_sub _ (by norm_num)).trans ?_
      norm_num)
    hs (by convert hwin using 4; norm_num)
  convert h using 4

end FalconPrecision.Falcon
