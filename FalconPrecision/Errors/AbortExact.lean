/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.SignModel64
public import FalconPrecision.Errors.AbortTV
public import FalconPrecision.Errors.FFTReal
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Abort probability of exact Type 1 signing; Theorem 2 against abort-free signing

World T answers every SamplerZ query of E by `clamp y`: the sample if it lies within `y` of the
centre, else the rounded centre (`clampQ`, `simulateQ_clampQ`; `AbortTV.etvDist_implT_le`: T is
within `p y` of E per query).

Route B′ (ℓ2 amplification). Along every history of T (`AllOut`), with the stored tree real
(`FTree.Real`: every `ℓ̂` the FFT of a real polynomial, so the leaf centres are real, `FFTReal`) and
`y ≤ 30`, the deviation `(t̂0 - ẑ0, t̂1 - ẑ1)` of a call at depth `L` has ℓ2 norm `≤ eT L` (`2·30² ≤
eT 0²`, `eT (L+1)² ≥ 2((1 + Λ_L)² + 1)·eT L²`: merges are `√2` times unitary, line 10 adds `ℓ̂⊙δ1`),
its input is a deterministic part in `‖·‖∞ ≤ 1792000 = 512·3500` (splits of the root target) plus a
part of ℓ2 norm `≤ gT L`, and every checked exact value (the split inputs `t̂1`, `t̂0'` and the odd
merge inputs `ẑ1` of both children) is in `‖·‖ ≤ R64 - 2` (`ffsG_clamp`). Then every check `chk`
that passes on exact values in that range (`chkM R64`, `InBR.chkM`) leaves the clamped computation
unchanged against no checks at all.

X is abort-free exact signing: `sign164G ρ (fun _ _ _ => True)`, answered by E (for `c` with `|c i|
< q`, as HashToPoint outputs; otherwise `⊥` in every world); in E the answers depend only on the
stored leaf and the exact centre (`hE`), not on the computed centre carried by the query. `Swap ρ K
oa ox`: `ox` is `oa` with every call of `sign164` replaced by that abort-free call (at most `K`
calls, otherwise auxiliary queries). `etvDist_E_X`: `𝒟_E[oa]` and `𝒟_E[ox]` are within `2·p
y·1024K`. `falcon512_exact64n`: with `falcon512_model64n`, success `> T·2⁻¹²⁶` in F gives success `>
T·2⁻¹²⁸ - 2⁻¹⁴⁰` in X for `K ≤ 2³⁹` (`y = 30`; `2·p 30·2⁴⁹ ≤ 2⁻¹⁴⁰` is proved, `eps_le`; its value,
about `2⁻¹⁴³·⁹`, is not).

F runs the model's range checks, which deployed signers do not run. F′ is Type 1 signing with no
checks (`sign164G ρ (fun _ _ _ => True)` answered by F's sampler). World T_F keeps F's answer when
it lies within `29.9` of `t̄` and `(t̄ - t)² ≤ 2⁻⁸`, else replaces it by the rounded exact centre
(`clampQF`); the answers then lie within `30` of the exact centres, so no check fires (`ffsG_clamp`
for any such rewriting). The path sum of `(t̄ - t)²` is `≤ 2⁻⁹` along every execution of `oa`
(`Uses64.pathS`), so no query with `(t̄ - t)² > 2⁻⁸` occurs (`PathSum.indicator`); the budget is
taken along the clamped run, which is the same for `oa` and `ox` (`etvDist_simulateQ_rewrite`).
`etvDist_F_F'`: `𝒟_F[oa]` and `𝒟_F′[ox]` are within `2·p_F 29.9·1024K ≤ 2⁻¹⁴⁰` (`eps_leF`).
`falcon512_exact64n'`: success `> T·2⁻¹²⁶ + 2⁻¹⁴⁰` in F′ gives success `> T·2⁻¹²⁸ - 2⁻¹⁴⁰` in X. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFTReal
  FalconPrecision.Errors.AbortTV ComplexConjugate

namespace FalconPrecision.Errors.FFSamp

/--
Every stored `ℓ̂` is the FFT of a real polynomial (`IsReal`). A hypothesis on the stored tree, not a
check: it holds by construction when only half the spectrum is stored (conjugates implied) or the
rounding is sign-symmetric; full-spectrum storage rounded ties-up can violate it at ties. -/
def FTree.Real : {L : ℕ} → FTree L → Prop
  | _, .leaf _ _ => True
  | _, .node ℓ _ T0 T1 => IsReal ℓ ∧ T0.Real ∧ T1.Real

end FalconPrecision.Errors.FFSamp

namespace FalconPrecision.Errors.AbortExact

open FalconPrecision.Errors.FFSamp MeasureTheory LatticeCrypto
open scoped ENNReal

section AllOut

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Every result of `oa`, for every answer of every query, satisfies `P`. -/
inductive AllOut {α : Type} (P : α → Prop) : OracleComp spec α → Prop
  | pure (x : α) (h : P x) : AllOut P (pure x)
  | query_bind (t : ι) (k : spec.Range t → OracleComp spec α) (h : ∀ u, AllOut P (k u)) :
      AllOut P (liftM (OracleSpec.query t) >>= k)

theorem AllOut.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {oa : OracleComp spec α}
    {f : α → OracleComp spec β} (h : AllOut P oa) (hf : ∀ x, P x → AllOut Q (f x)) :
    AllOut Q (oa >>= f) := by
  induction h with
  | pure x hx => rw [pure_bind]; exact hf x hx
  | query_bind t k _ ih => rw [bind_assoc]; exact .query_bind t _ fun u => ih u

theorem AllOut.bind_congr {α β : Type} {P : α → Prop} {oa : OracleComp spec α}
    {f g : α → OracleComp spec β} (h : AllOut P oa) (hfg : ∀ x, P x → f x = g x) :
    oa >>= f = oa >>= g := by
  induction h with
  | pure x hx => rw [pure_bind, pure_bind, hfg x hx]
  | query_bind t k _ ih =>
    rw [bind_assoc, bind_assoc]
    exact congrArg _ (funext fun u => ih u)

end AllOut

theorem abs_clamp_sub_le {y t : ℝ} (hy : 1 / 2 ≤ y) (z : ℤ) : |(clamp y t z : ℝ) - t| ≤ y := by
  unfold clamp
  split_ifs with h
  · exact h.le
  · rw [abs_sub_comm]
    exact (abs_sub_round t).trans hy

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- World T as a rewriting of the computation: SamplerZ answers clamped by `clamp y`. -/
noncomputable def clampQ (y : ℝ) :
    QueryImpl (FalconGame.spec aux Falcon.CallP) (OracleComp (FalconGame.spec aux Falcon.CallP))
  | .inl x => liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl x))
  | .inr q => (clamp y q.t <$>
      (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) : OracleComp _
          ℤ) :
        OracleComp _ ℤ)

theorem simulateQ_clampQ {m : Type → Type*} [Monad m] [LawfulMonad m] (y : ℝ)
    (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m) {α : Type}
    (oa : OracleComp (FalconGame.spec aux Falcon.CallP) α) :
    simulateQ implE (simulateQ (clampQ y) oa) = simulateQ (implT y implE) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (so' := implE) (so := clampQ y)
    (impl := implT y implE) (fun t => ?_) oa
  rcases t with x | q
  · change simulateQ implE (liftM _) = implE (.inl x)
    exact simulateQ_spec_query (impl := implE) (Sum.inl x)
  · change simulateQ implE (clamp y q.t <$> _) = clamp y q.t <$> implE (.inr q)
    rw [simulateQ_map]
    exact congrArg _ (simulateQ_spec_query (impl := implE) (Sum.inr q))

theorem allOut_clampQ {y : ℝ} (hy : 1 / 2 ≤ y) (q : Falcon.CallP) :
    AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ y) (clampQ (aux := aux) y (.inr q) : OracleComp _ ℤ) :=
        by
  change AllOut _ (clamp y q.t <$> _)
  rw [map_eq_bind_pure_comp]
  exact .query_bind _ _ fun u => .pure _ (abs_clamp_sub_le hy u)


end FalconPrecision.Errors.AbortExact

namespace FalconPrecision.RenyiPath

section PathFacts

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Inversion of `PathSum` at a query. -/
theorem PathSum.inv_query {w : ι → ℝ} {α : Type} {t : ι} {k : spec.Range t → OracleComp spec α}
    {S : ℝ}
    (h : PathSum w (liftM (OracleSpec.query t) >>= k) S) (u : spec.Range t) :
    PathSum w (k u) (S - w t) := by
  generalize hx : (liftM (OracleSpec.query t) >>= k : OracleComp spec α) = x at h
  cases h with
  | pure y _ =>
    have e : (PFunctor.FreeM.liftBind t k : PFunctor.FreeM spec.toPFunctor α) =
        PFunctor.FreeM.pure y := hx
    cases e
  | query_bind t' k' h' =>
    have e : (PFunctor.FreeM.liftBind t k : PFunctor.FreeM spec.toPFunctor α) =
      PFunctor.FreeM.liftBind t' k' := hx
    injection e with e1 e2
    subst e1
    cases e2
    exact h' u

theorem PathSum.inv_pure {w : ι → ℝ} {α : Type} {x : α} {S : ℝ}
    (h : PathSum w (Pure.pure x : OracleComp spec α) S) : 0 ≤ S := by
  generalize hx : (Pure.pure x : OracleComp spec α) = y at h
  cases h with
  | pure y hS => exact hS
  | query_bind t k _ =>
    have e : (PFunctor.FreeM.pure x : PFunctor.FreeM spec.toPFunctor α) =
        PFunctor.FreeM.liftBind t k := hx
    cases e

/-- Path budgets of two weights add. -/
theorem PathSum.add {w w' : ι → ℝ} {α : Type} {oa : OracleComp spec α} {S S' : ℝ}
    (h : PathSum w oa S)
    (h' : PathSum w' oa S') : PathSum (fun t => w t + w' t) oa (S + S') := by
  induction h generalizing S' with
  | pure x hS => exact .pure x (add_nonneg hS h'.inv_pure)
  | @query_bind t k S _ ih =>
    refine .query_bind t k fun u => ?_
    have := ih u (h'.inv_query u)
    rwa [show S - w t + (S' - w' t) = S + S' - (w t + w' t) by ring] at this

/-- With every answer type inhabited and nonnegative weights, a path budget is nonnegative. -/
theorem PathSum.nonneg [∀ t, Nonempty (spec.Range t)] {w : ι → ℝ} (hw : ∀ t, 0 ≤ w t) {α : Type}
    {oa : OracleComp spec α} {S : ℝ} (h : PathSum w oa S) : 0 ≤ S := by
  induction h with
  | pure x hS => exact hS
  | query_bind t k _ ih => linarith [ih (Classical.arbitrary _), hw t]

/-- A negative budget leaves no execution: any weights and budget hold. -/
theorem PathSum.of_neg {w : ι → ℝ} (hw : ∀ t, 0 ≤ w t) {α : Type} {oa : OracleComp spec α} {S : ℝ}
    (h : PathSum w oa S) (hS : S < 0) (w' : ι → ℝ) (S' : ℝ) : PathSum w' oa S' := by
  induction h generalizing S' with
  | pure x h0 => exact absurd h0 (not_le.2 hS)
  | query_bind t k _ ih => exact .query_bind t k fun u => ih u (by linarith [hw t]) _

/-- A budget `S ≤ θ` admits no query of weight `> θ` along any execution. -/
theorem PathSum.indicator {w : ι → ℝ} (hw : ∀ t, 0 ≤ w t) {θ : ℝ} {α : Type}
    {oa : OracleComp spec α}
    {S : ℝ} (h : PathSum w oa S) (hS : S ≤ θ) : PathSum (fun t => if θ < w t then 1 else 0) oa 0 :=
        by
  induction h with
  | pure x _ => exact .pure x le_rfl
  | @query_bind t k S h ih =>
    refine .query_bind t k fun u => ?_
    by_cases hn : S - w t < 0
    · exact (h u).of_neg hw hn _ _
    · have hle : ¬θ < w t := by linarith
      simp only [hle, ↓reduceIte, sub_zero]
      exact ih u (by linarith [hw t])

/-- Post-processing every answer keeps path budgets. -/
theorem PathSum.simulateQ_map {w : ι → ℝ} {so : QueryImpl spec (OracleComp spec)}
    (f : (t : ι) → spec.Range t → spec.Range t)
        (hso : ∀ t, so t = f t <$> liftM (OracleSpec.query t))
    {α : Type} {oa : OracleComp spec α} {S : ℝ}
        (h : PathSum w oa S) : PathSum w (simulateQ so oa) S := by
  induction h with
  | pure x hS => rw [simulateQ_pure]; exact .pure x hS
  | query_bind t k _ ih =>
    rw [simulateQ_bind, show simulateQ so (liftM (OracleSpec.query t)) = so t from
      simulateQ_spec_query (impl := so) t, hso, map_eq_bind_pure_comp, bind_assoc]
    exact .query_bind t _ fun u => by simpa using ih (f t u)

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

theorem bind_map_eq {β γ : Type} [MeasurableSpace β] [DiscreteMeasurableSpace β] [MeasurableSpace γ]
    (μ : MeasureTheory.Measure β) (f : β → β) (κ : β → MeasureTheory.Measure γ) :
    (μ.map f).bind κ = μ.bind fun u => κ (f u) := by
  ext s hs
  rw [MeasureTheory.Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    MeasureTheory.Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete]

/-- **Total variation against a post-processed run**, the budget taken along the post-processed run.
-/
theorem etvDist_simulateQ_rewrite [∀ t, Nonempty (spec.Range t)] (impl : QueryImpl spec m)
    {so : QueryImpl spec (OracleComp spec)} (f : (t : ι) → spec.Range t → spec.Range t)
    (hso : ∀ t, so t = f t <$> liftM (OracleSpec.query t)) {c : ℝ} (hc : 0 ≤ c) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t)
    (hB : ∀ t, @MeasureTheory.Measure.etvDist _ ⊤ (@evalDist m _ (spec.Range t) ⊤ (impl t))
      (@MeasureTheory.Measure.map _ _ ⊤ ⊤ (f t) (@evalDist m _ (spec.Range t) ⊤ (impl t))) ≤
        ENNReal.ofReal (c * w t))
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) :
    ∀ S, PathSum w (simulateQ so oa) S →
      (𝒟[simulateQ impl oa]).etvDist 𝒟[simulateQ impl (simulateQ so oa)] ≤
          ENNReal.ofReal (c * S) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro S _
    simp only [simulateQ_pure, MeasureTheory.Measure.etvDist_self]
    exact bot_le
  | query_bind t k ih =>
    intro S h
    let : MeasurableSpace (spec.Range t) := ⊤
    have : DiscreteMeasurableSpace (spec.Range t) := ⟨fun _ => trivial⟩
    have e1 : simulateQ so (liftM (OracleSpec.query t) >>= k) =
        liftM (OracleSpec.query t) >>= fun u => simulateQ so (k (f t u)) := by
      rw [simulateQ_bind, show simulateQ so (liftM (OracleSpec.query t)) = so t from
        simulateQ_spec_query (impl := so) t, hso, map_eq_bind_pure_comp, bind_assoc]
      simp
    change PathSum w (simulateQ so (liftM (OracleSpec.query t) >>= k)) S at h
    change (𝒟[simulateQ impl (liftM (OracleSpec.query t) >>= k)]).etvDist
      𝒟[simulateQ impl (simulateQ so (liftM (OracleSpec.query t) >>= k))] ≤ _
    rw [e1] at h ⊢
    have hk := h.inv_query
    have hS : 0 ≤ S - w t := (hk (Classical.arbitrary _)).nonneg hw
    simp only [simulateQ_bind, show simulateQ impl (liftM (OracleSpec.query t)) = impl t from
      simulateQ_spec_query (impl := impl) t]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    have hmid := bind_map_eq 𝒟[impl t] (f t) fun a => 𝒟[simulateQ impl (k a)]
    calc ((𝒟[impl t]).bind (fun u => 𝒟[simulateQ impl (k u)])).etvDist
          ((𝒟[impl t]).bind fun u => 𝒟[simulateQ impl (simulateQ so (k (f t u)))])
        ≤ ((𝒟[impl t]).bind (fun u => 𝒟[simulateQ impl (k u)])).etvDist
            ((𝒟[impl t].map (f t)).bind fun a => 𝒟[simulateQ impl (k a)]) +
          ((𝒟[impl t].map (f t)).bind (fun a => 𝒟[simulateQ impl (k a)])).etvDist
            ((𝒟[impl t]).bind fun u => 𝒟[simulateQ impl (simulateQ so (k (f t u)))]) :=
          MeasureTheory.Measure.etvDist_triangle _ _ _
      _ ≤ ENNReal.ofReal (c * w t) + ENNReal.ofReal (c * (S - w t)) := by
          refine add_le_add
              ((MeasureTheory.Measure.etvDist_bind_le _ _ _ Measurable.of_discrete).trans
            (hB t)) ?_
          rw [hmid]
          refine (MeasureTheory.Measure.etvDist_bind_bind_le_lintegral _ _ _
            Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable
            (fun _ => ENNReal.ofReal (c * (S - w t))) (MeasureTheory.ae_of_all _ fun u =>
              ih (f t u) _ (hk u))).trans ?_
          rw [MeasureTheory.lintegral_const]
          exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
      _ = ENNReal.ofReal (c * S) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hc (hw t)) (mul_nonneg hc hS)]
          congr 1
          ring

end PathFacts

end FalconPrecision.RenyiPath

namespace FalconPrecision.Errors.AbortExact

open FalconPrecision.Errors.FFSamp MeasureTheory LatticeCrypto
open scoped ENNReal

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

theorem AllOut.mono {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} {P Q : α → Prop}
    {oa : OracleComp spec α} (h : AllOut P oa) (hPQ : ∀ x, P x → Q x) : AllOut Q oa := by
  induction h with
  | pure x hx => exact .pure x (hPQ x hx)
  | query_bind t k _ ih => exact .query_bind t k ih

theorem allOut_sim
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hso : ∀ q : Falcon.CallP, AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 30)
        (so (.inr q) : OracleComp _ ℤ)) (q : Falcon.CallP) :
    AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 30)
      (simulateQ so (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q))) :
        OracleComp _ ℤ) :=
  (congrArg (AllOut _) (simulateQ_spec_query (impl := so) (Sum.inr q))).mpr (hso q)

/-- ℓ2 bounds of the deviation of a call at depth `L` (route B′, `y = 30`). -/
noncomputable def eT (L : ℕ) : ℝ :=
  (match L with
    | 0 => 426 | 1 => 1344 | 2 => 4239 | 3 => 13365 | 4 => 42135 | 5 => 132834 | 6 => 418766
    | 7 => 1320179 | 8 => 4161921 | _ => 147264388) / 10

/-- ℓ2 bounds of the random part of the input of a call at depth `L`. -/
noncomputable def gT (L : ℕ) : ℝ :=
  (match L with
    | 0 => 6453504 | 1 => 9125946 | 2 => 12904024 | 3 => 18242920 | 4 => 25780379 | 5 => 36399477
    | 6 => 51289718 | 7 => 71946217 | 8 => 99893585 | _ => 0) / 10

theorem tables (L : ℕ) (hL : L ≤ 8) :
    2 * ((1 + lam512 L) ^ 2 + 1) * eT L ^ 2 ≤ eT (L + 1) ^ 2 ∧
      gT (L + 1) + lam512 L * (14143 / 10000) * eT L ≤ 14142 / 10000 * gT L ∧
      1792000 + gT (L + 1) + lam512 L * (14143 / 10000) * eT L ≤ 2 ^ 24 - 2 ∧
      1792000 + gT L + eT L ≤ 2 ^ 24 - 2 ∧ 0 ≤ eT L ∧ 0 ≤ gT L ∧ 0 ≤ gT (L + 1) := by
  interval_cases L <;> norm_num [eT, gT, lam512]

theorem eT_nonneg (L : ℕ) : 0 ≤ eT L := by unfold eT; split <;> norm_num

theorem eT_zero : 2 * 30 ^ 2 ≤ eT 0 ^ 2 := by norm_num [eT]

theorem gT_nine : gT 9 = 0 := by norm_num [gT]

theorem zeta_mul_conj (L : ℕ) (o : Out L) : zeta L o * conj (zeta L o) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_zeta]
  norm_num

/-- A merge undoes a split. -/
theorem mergeL_splitE {L : ℕ} (t : Out (L + 1) → ℂ) :
    mergeL (splitE t).1 (fun o => zeta L o * (splitE t).2 o) = t := by
  funext x
  obtain ⟨o, b⟩ := x
  have h := zeta_mul_conj L o
  cases b
  · change (t (o, false) + t (o, true)) / 2 +
      zeta L o * (conj (zeta L o) / 2 * (t (o, false) - t (o, true))) = t (o, false)
    linear_combination (t (o, false) - t (o, true)) / 2 * h
  · change (t (o, false) + t (o, true)) / 2 -
      zeta L o * (conj (zeta L o) / 2 * (t (o, false) - t (o, true))) = t (o, true)
    linear_combination -(t (o, false) - t (o, true)) / 2 * h

theorem splitE_add {L : ℕ} (a r : Out (L + 1) → ℂ) :
    (splitE (a + r)).1 = (splitE a).1 + (splitE r).1 ∧ (splitE (a + r)).2 = (splitE a).2 +
        (splitE r).2 := by
  constructor <;> funext o
  · change (a (o, false) + r (o, false) + (a (o, true) + r (o, true))) / 2 =
      (a (o, false) + a (o, true)) / 2 + (r (o, false) + r (o, true)) / 2
    ring
  · change conj (zeta L o) / 2 * (a (o, false) + r (o, false) - (a (o, true) + r (o, true))) =
      conj (zeta L o) / 2 * (a (o, false) - a (o, true)) + conj (zeta L o) / 2 *
          (r (o, false) - r (o, true))
    ring

theorem splitE_norm_le {L : ℕ} {a : Out (L + 1) → ℂ} {B : ℝ} (h : ∀ x, ‖a x‖ ≤ B) (o : Out L) :
    ‖(splitE a).1 o‖ ≤ B ∧ ‖(splitE a).2 o‖ ≤ B := by
  have h1 := norm_add_le (a (o, false)) (a (o, true))
  have h2 := norm_sub_le (a (o, false)) (a (o, true))
  have hf := h (o, false)
  have ht := h (o, true)
  constructor
  · change ‖(a (o, false) + a (o, true)) / 2‖ ≤ B
    rw [norm_div, Complex.norm_two]
    linarith
  · change ‖conj (zeta L o) / 2 * (a (o, false) - a (o, true))‖ ≤ B
    rw [norm_mul, norm_div, Complex.norm_two, Complex.norm_conj, norm_zeta]
    linarith

/-- A split is `1/√2` times unitary. -/
theorem l2_splitE_sq {L : ℕ} (r : Out (L + 1) → ℂ) :
    l2 (splitE r).1 ^ 2 + l2 (splitE r).2 ^ 2 = l2 r ^ 2 / 2 := by
  rw [l2_sq, l2_sq, l2_sq, sum_out_succ, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun o _ => ?_
  have := parallelogram_law_with_norm ℝ (r (o, false)) (r (o, true))
  change ‖(r (o, false) + r (o, true)) / 2‖ ^ 2 +
    ‖conj (zeta L o) / 2 * (r (o, false) - r (o, true))‖ ^ 2 = _
  rw [norm_mul, norm_div, norm_div, Complex.norm_two, Complex.norm_conj, norm_zeta]
  linarith

theorem l2_splitE_le {L : ℕ} {r : Out (L + 1) → ℂ} {g X : ℝ} (hr : l2 r ≤ X)
    (hX : X ≤ 14142 / 10000 * g) (hg : 0 ≤ g) : l2 (splitE r).1 ≤ g ∧ l2 (splitE r).2 ≤ g := by
  have h := l2_splitE_sq r
  have h0 := l2_nonneg r
  have hr2 : l2 r ^ 2 ≤ (14142 / 10000 * g) ^ 2 := pow_le_pow_left₀ h0 (hr.trans hX) 2
  have h1 := sq_nonneg (l2 (splitE r).1)
  have h2 := sq_nonneg (l2 (splitE r).2)
  constructor <;> refine (pow_le_pow_iff_left₀ (l2_nonneg _) hg two_ne_zero).1 ?_ <;> nlinarith

/-- The deviation `t - ẑ` of a node in terms of the deviation of the child that sampled `ẑ`. -/
theorem l2_sub_mergeE_sq {L : ℕ} (t : Out (L + 1) → ℂ) (s : Samp L) :
    l2 (t - mergeE s) ^ 2 = 2 * l2 (pairF ((splitE t).1 - s.e0) ((splitE t).2 - s.e1)) ^ 2 := by
  conv_lhs => rw [← mergeL_splitE t]
  rw [mergeE, mergeL_sub, l2_mergeL_sq, l2_pairF_sq]
  congr 3
  unfold l2
  congr 1
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Pi.sub_apply, ← mul_sub, norm_mul, norm_zeta, one_mul, Pi.sub_apply]

theorem norm_sub_le_of_pairF {L : ℕ} {t0 t1 : Out L → ℂ} {s : Samp L} {E : ℝ}
    (h : l2 (pairF (t0 - s.e0) (t1 - s.e1)) ≤ E) (o : Out L) : ‖t1 o - s.e1 o‖ ≤ E :=
  (norm_le_l2 (t1 - s.e1) o).trans ((l2_le_pairF _ _).2.trans h)

/-- Leaves: the FFT of a constant is the constant. -/
theorem isFFT_leaf (z0 z1 : ℤ) : IsFFT (Samp.leaf z0 z1) :=
  fun _ => ⟨by simp [Samp.leaf, evalAt], by simp [Samp.leaf, evalAt]⟩

/-- Every history of a clamped `ffsG` call: some output, `IsFFT`, deviation `≤ eT L` in ℓ2. -/
def Good {L : ℕ} (t0 t1 : Out L → ℂ) (r : Option (Samp L)) : Prop :=
  ∃ s, r = some s ∧ IsFFT s ∧ l2 (pairF (t0 - s.e0) (t1 - s.e1)) ≤ eT L

theorem norm_le_of_split {L : ℕ} {a r : Out L → ℂ} {B g : ℝ} (ha : ∀ o, ‖a o‖ ≤ B) (hr : l2 r ≤ g)
    (o : Out L) : ‖(a + r) o‖ ≤ B + g :=
  (norm_add_le _ _).trans (add_le_add (ha o) ((norm_le_l2 r o).trans hr))

/--
**Route B′ along the histories of T.** Inputs: real, a deterministic part in `‖·‖∞ ≤ 1792000` plus a
part of ℓ2 norm `≤ gT L`. Then every checked exact value is in `‖·‖ ≤ R64 - 2`, so a check `chk`
passing there leaves the clamped computation equal to the one without checks, and every history of
the latter is `Good`. -/
theorem ffsG_clamp (ρ : Arith) (u : ℝ)
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hso : ∀ q : Falcon.CallP, AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 30)
        (so (.inr q) : OracleComp _ ℤ))
    (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop)
    (hchk : ∀ L vh v, (∀ o, ‖v o‖ ≤ 2 ^ 24 - 2) → chk L vh v) {L : ℕ} (T : FTree L) (hT : T.Real) :
    L ≤ 9 → ∀ (t0 t1 t0h t1h a0 a1 r0 r1 : Out L → ℂ), t0 = a0 + r0 → t1 = a1 + r1 →
      (∀ o, ‖a0 o‖ ≤ 1792000) → (∀ o, ‖a1 o‖ ≤ 1792000) → l2 r0 ≤ gT L → l2 r1 ≤ gT L →
      IsReal t0 → IsReal t1 →
      simulateQ so (ffsG (aux := aux) ρ u chk T t0 t1 t0h t1h) =
        simulateQ so (ffsG (aux := aux) ρ u (fun _ _ _ => True) T t0 t1 t0h t1h) ∧
      AllOut (Good t0 t1)
        (simulateQ so (ffsG (aux := aux) ρ u (fun _ _ _ => True) T t0 t1 t0h t1h)) := by
  induction T with
  | leaf σ h =>
    intro _ t0 t1 t0h t1h _ _ _ _ _ _ _ _ _ _ h0 h1
    refine ⟨rfl, ?_⟩
    simp only [ffsG, simulateQ_bind, simulateQ_pure]
    refine (allOut_sim so hso _).bind fun z0 hz0 => (allOut_sim so hso _).bind fun z1 hz1 =>
      .pure _ ⟨_, rfl, isFFT_leaf _ _, ?_⟩
    have e0 : t0 () = ((t0 ()).re : ℂ) := Complex.ext (by simp) (by simpa using im_eq_zero h0 ())
    have e1 : t1 () = ((t1 ()).re : ℂ) := Complex.ext (by simp) (by simpa using im_eq_zero h1 ())
    change |(z0 : ℝ) - (t0 ()).re| ≤ 30 at hz0
    change |(z1 : ℝ) - (t1 ()).re| ≤ 30 at hz1
    have d0 : ‖(t0 - (Samp.leaf z0 z1).e0) ()‖ ≤ 30 := by
      change ‖t0 () - (z0 : ℂ)‖ ≤ 30
      rw [e0, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm]
      linarith [hz0]
    have d1 : ‖(t1 - (Samp.leaf z0 z1).e1) ()‖ ≤ 30 := by
      change ‖t1 () - (z1 : ℂ)‖ ≤ 30
      rw [e1, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm]
      linarith [hz1]
    refine (pow_le_pow_iff_left₀ (l2_nonneg _) (by norm_num [eT]) two_ne_zero).1 ?_
    rw [l2_pairF_sq, l2_out0, l2_out0]
    have := eT_zero
    nlinarith
        [norm_nonneg ((t0 - (Samp.leaf z0 z1).e0) ()), norm_nonneg ((t1 - (Samp.leaf z0 z1).e1) ())]
  | @node L ℓ hℓ T0 T1 ih0 ih1 =>
    intro hL t0 t1 t0h t1h a0 a1 r0 r1 ht0 ht1 ha0 ha1 hr0 hr1 h0 h1
    obtain ⟨hE, hG, hC3, hC2, hE0, hG0, hG1⟩ := tables L (by omega)
    have hlam := lam512_nonneg L
    have hpos : 0 ≤ lam512 L * (14143 / 10000) * eT L :=
        mul_nonneg (mul_nonneg hlam (by norm_num)) hE0
    obtain ⟨hTℓ, hT0, hT1⟩ := hT
    -- child 1
    have hs1 := splitE_add a1 r1
    have hn1 := splitE_norm_le ha1
    have hl1 := l2_splitE_le (r := r1) hr1 (by linarith) hG0
    have hR1 := isReal_splitE h1
    have IH1 :=
        ih1 hT1 (by omega) (splitE t1).1 (splitE t1).2 (splitCU ρ u t1h).1 (splitCU ρ u t1h).2
      (splitE a1).1 (splitE a1).2 (splitE r1).1 (splitE r1).2 (by rw [ht1, hs1.1])
          (by rw [ht1, hs1.2])
      (fun o => (hn1 o).1) (fun o => (hn1 o).2) hl1.1 hl1.2 hR1.1 hR1.2
    -- the checks and the child-0 data, for a good child-1 output
    have key : ∀ s1 : Samp L, IsFFT s1 →
        l2 (pairF ((splitE t1).1 - s1.e0) ((splitE t1).2 - s1.e1)) ≤ eT L →
        (∀ o, ‖s1.e1 o‖ ≤ 2 ^ 24 - 2) ∧ (∀ o, ‖upd t0 t1 (mergeE s1) ℓ o‖ ≤ 2 ^ 24 - 2) ∧
        l2 (t1 - mergeE s1) ^ 2 ≤ 2 * eT L ^ 2 ∧
        (∀ s0 : Samp L, l2 (pairF ((splitE (upd t0 t1 (mergeE s1) ℓ)).1 - s0.e0)
          ((splitE (upd t0 t1 (mergeE s1) ℓ)).2 - s0.e1)) ≤ eT L → ∀ o, ‖s0.e1 o‖ ≤ 2 ^ 24 - 2) ∧
        (simulateQ so (ffsG (aux := aux) ρ u chk T0 (splitE (upd t0 t1 (mergeE s1) ℓ)).1
            (splitE (upd t0 t1 (mergeE s1) ℓ)).2
                (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).1
            (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).2) =
          simulateQ so (ffsG (aux := aux) ρ u (fun _ _ _ => True) T0
            (splitE (upd t0 t1 (mergeE s1) ℓ)).1 (splitE (upd t0 t1 (mergeE s1) ℓ)).2
            (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).1
            (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).2) ∧
        AllOut (Good (splitE (upd t0 t1 (mergeE s1) ℓ)).1 (splitE (upd t0 t1 (mergeE s1) ℓ)).2)
          (simulateQ so (ffsG (aux := aux) ρ u (fun _ _ _ => True) T0
            (splitE (upd t0 t1 (mergeE s1) ℓ)).1 (splitE (upd t0 t1 (mergeE s1) ℓ)).2
            (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).1
            (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).2))) := by
      intro s1 hf1 hd1
      have hδ1sq : l2 (t1 - mergeE s1) ^ 2 ≤ 2 * eT L ^ 2 := by
        rw [l2_sub_mergeE_sq t1 s1]
        nlinarith [pow_le_pow_left₀ (l2_nonneg _) hd1 2]
      have hδ1 : l2 (t1 - mergeE s1) ≤ 14143 / 10000 * eT L := by
        refine (pow_le_pow_iff_left₀ (l2_nonneg _) (by positivity) two_ne_zero).1 ?_
        nlinarith
      have hrr : l2 (r0 + fun o => (t1 - mergeE s1) o * ℓ o) ≤ gT (L + 1) + lam512 L *
          (14143 / 10000 * eT L) :=
        (l2_add_le _ _).trans (add_le_add hr0 (by
          rw [show (fun o => (t1 - mergeE s1) o * ℓ o) = fun o => ℓ o * (t1 - mergeE s1) o from
            funext fun o => mul_comm _ _]
          exact (l2_mul_le _ _ _ hlam hℓ).trans (mul_le_mul_of_nonneg_left hδ1 hlam)))
      have hup : upd t0 t1 (mergeE s1) ℓ = a0 + (r0 + fun o => (t1 - mergeE s1) o * ℓ o) := by
        funext o; rw [ht0]; simp only [upd, Pi.add_apply, Pi.sub_apply]; ring
      have hs0 := splitE_add a0 (r0 + fun o => (t1 - mergeE s1) o * ℓ o)
      have hn0 := splitE_norm_le ha0
      have hl0 := l2_splitE_le hrr (by linarith) hG0
      have hR0 := isReal_splitE (isReal_upd h0 h1 (isReal_mergeE hf1) hTℓ)
      refine ⟨fun o => ?_, fun o => ?_, hδ1sq, fun s0 hd0 o => ?_,
          ih0 hT0 (by omega) _ _ _ _ (splitE a0).1 (splitE a0).2 _ _
        (by rw [hup, hs0.1]) (by rw [hup, hs0.2]) (fun o => (hn0 o).1)
            (fun o => (hn0 o).2) hl0.1 hl0.2
        hR0.1 hR0.2⟩
      · have hb := norm_le_of_split (fun o => (hn1 o).2) hl1.2 o
        rw [← hs1.2, ← ht1] at hb
        have hd := norm_sub_le_of_pairF hd1 o
        have := norm_sub_norm_le (s1.e1 o) ((splitE t1).2 o)
        rw [norm_sub_rev] at hd
        linarith
      · rw [hup]
        have := norm_le_of_split ha0 hrr o
        linarith
      · have hb := norm_le_of_split (fun o => (hn0 o).2) hl0.2 o
        rw [← hs0.2, ← hup] at hb
        have hd := norm_sub_le_of_pairF hd0 o
        have := norm_sub_norm_le (s0.e1 o) ((splitE (upd t0 t1 (mergeE s1) ℓ)).2 o)
        rw [norm_sub_rev] at hd
        linarith
    refine ⟨?_, ?_⟩
    · have hc1 : chk _ t1h t1 := hchk _ _ _ fun o => by
        have := norm_le_of_split ha1 hr1 o
        rw [← ht1] at this
        linarith
      simp only [ffsG, hc1, ↓reduceIte, simulateQ_bind]
      rw [IH1.1]
      refine IH1.2.bind_congr fun r1 ⟨s1, hr, hf1, hd1⟩ => ?_
      subst hr
      obtain ⟨hc2, hc3, -, hc4, IH0eq, IH0all⟩ := key s1 hf1 hd1
      simp only [Option.elim, hchk _ _ _ hc2, hchk _ _ _ hc3, and_self, ↓reduceIte, simulateQ_bind]
      rw [IH0eq]
      refine IH0all.bind_congr fun r0 ⟨s0, hr0, hf0, hd0⟩ => ?_
      subst hr0
      simp only [hchk _ _ _ (hc4 s0 hd0), ↓reduceIte]
    · simp only [ffsG, ↓reduceIte, simulateQ_bind]
      refine IH1.2.bind fun r1 ⟨s1, hr, hf1, hd1⟩ => ?_
      subst hr
      obtain ⟨-, -, hδ1, -, -, IH0all⟩ := key s1 hf1 hd1
      simp only [Option.elim, and_self, ↓reduceIte, simulateQ_bind]
      refine IH0all.bind fun r0 ⟨s0, hr0, hf0, hd0⟩ => ?_
      subst hr0
      simp only [simulateQ_pure]
      refine .pure _ ⟨_, rfl, join_fftU ρ u hf0 hf1, ?_⟩
      change l2 (pairF (t0 - mergeE s0) (t1 - mergeE s1)) ≤ eT (L + 1)
      set t0' := upd t0 t1 (mergeE s1) ℓ
      have hA : l2 (t0' - mergeE s0) ^ 2 ≤ 2 * eT L ^ 2 := by
        rw [l2_sub_mergeE_sq t0' s0]
        nlinarith [pow_le_pow_left₀ (l2_nonneg _) hd0 2]
      have he : t0 - mergeE s0 = (t0' - mergeE s0) + fun o => -((t1 - mergeE s1) o * ℓ o) := by
        funext o; simp only [t0', upd, Pi.add_apply, Pi.sub_apply]; ring
      have hd : l2 (t0 - mergeE s0) ≤ l2 (t0' - mergeE s0) + lam512 L * l2 (t1 - mergeE s1) := by
        rw [he]
        refine (l2_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [l2_neg, show (fun o => (t1 - mergeE s1) o * ℓ o) = fun o => ℓ o *
            (t1 - mergeE s1) o from
          funext fun o => mul_comm _ _]
        exact l2_mul_le _ _ _ hlam hℓ
      set A := l2 (t0' - mergeE s0)
      set Bv := l2 (t1 - mergeE s1)
      have hA0 : 0 ≤ A := l2_nonneg _
      have hB0 : 0 ≤ Bv := l2_nonneg _
      have hAB : A * Bv ≤ 2 * eT L ^ 2 := by nlinarith [sq_nonneg (A - Bv)]
      have hsum : (A + lam512 L * Bv) ^ 2 ≤ 2 * eT L ^ 2 * (1 + lam512 L) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hAB (by positivity : (0 : ℝ) ≤ 2 * lam512 L),
          mul_le_mul_of_nonneg_left hδ1 (sq_nonneg (lam512 L))]
      have hd2 : l2 (t0 - mergeE s0) ^ 2 ≤ (A + lam512 L * Bv) ^ 2 :=
        pow_le_pow_left₀ (l2_nonneg _) hd 2
      refine (pow_le_pow_iff_left₀ (l2_nonneg _) (eT_nonneg _) two_ne_zero).1 ?_
      rw [l2_pairF_sq]
      nlinarith

/-- The root targets are FFTs of real polynomials. -/
theorem isReal_t0E (k : Key) (c : Fin (2 ^ 9) → ℤ) : IsReal (t0E k c) := fun o => by
  have h1 := isReal_evalAt (cdq c) (fun i => Complex.conj_ofReal _) o
  have h2 := isReal_evalAt (fun i => (k.F i : ℂ)) (fun i => map_intCast _ _) o
  simp only [t0E, fftE] at h1 h2 ⊢
  rw [h1, h2, map_neg, map_mul]

theorem isReal_t1E (k : Key) (c : Fin (2 ^ 9) → ℤ) : IsReal (t1E k c) := fun o => by
  have h1 := isReal_evalAt (cdq c) (fun i => Complex.conj_ofReal _) o
  have h2 := isReal_evalAt (fun i => (k.f i : ℂ)) (fun i => map_intCast _ _) o
  simp only [t1E, fftE] at h1 h2 ⊢
  rw [h1, h2, map_mul]

theorem norm_fftE_cdq (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) (o : Out 9) :
    ‖fftE (cdq c) o‖ ≤ 512 := by
  have ha : ∀ i, ‖cdq c i‖ ≤ 1 := fun i => by
    have : |(c i : ℝ)| < 12289 := by exact_mod_cast hc i
    rw [cdq, Complex.norm_real, Real.norm_eq_abs, abs_div, div_le_one (by norm_num)]
    norm_num
    linarith
  exact (norm_evalAt_le _ _ (norm_pt 9 o) 1 ha).trans (by norm_num)

theorem norm_t0E_le (k : Key) (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) (o : Out 9) :
    ‖t0E k c o‖ ≤ 1792000 := by
  rw [t0E, norm_neg, norm_mul]
  have := mul_le_mul (norm_fftE_cdq c hc o) (k.hF o) (norm_nonneg _) (by norm_num)
  linarith

theorem norm_t1E_le (k : Key) (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) (o : Out 9) :
    ‖t1E k c o‖ ≤ 1792000 := by
  rw [t1E, norm_mul]
  have := mul_le_mul (norm_fftE_cdq c hc o) (k.hf o) (norm_nonneg _) (by norm_num)
  linarith

theorem l2_zero_le {L : ℕ} : l2 (0 : Out L → ℂ) ≤ gT 9 := by
  rw [gT_nine]; unfold l2; simp

variable {εq : ℝ}

/--
**No check of Type 1 signing fires in T** (route B′): a check passing on exact values in `‖·‖ ≤ R64
- 2` leaves the clamped call equal to abort-free signing. -/
theorem sign164G_clamp (ρ : Arith64 εq)
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hso : ∀ q : Falcon.CallP, AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 30)
        (so (.inr q) : OracleComp _ ℤ))
    (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop)
    (hchk : ∀ L vh v, (∀ o, ‖v o‖ ≤ 2 ^ 24 - 2) → chk L vh v) (k : Key) (hk : k.tree.Real)
    (c : Fin (2 ^ 9) → ℤ) :
    simulateQ so (sign164G (aux := aux) ρ chk k c) =
      simulateQ so (sign164G (aux := aux) ρ (fun _ _ _ => True) k c) := by
  unfold sign164G
  split_ifs with hc
  · rw [simulateQ_map, simulateQ_map, (ffsG_clamp ρ.toArith (1 / 2 ^ 64) so hso chk hchk k.tree hk
      le_rfl (t0E k c) (t1E k c) (t0C64 ρ k c) (t1C64 ρ k c) (t0E k c)
          (t1E k c) 0 0 (add_zero _).symm
      (add_zero _).symm (norm_t0E_le k c hc) (norm_t1E_le k c hc) l2_zero_le l2_zero_le
      (isReal_t0E k c) (isReal_t1E k c)).1]
  · rfl

/-- `sign164` in T is abort-free Type 1 signing in T, for an input bound `inp64 εq ≤ e`. -/
theorem sign164_clamp (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10)
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hso : ∀ q : Falcon.CallP, AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 30)
        (so (.inr q) : OracleComp _ ℤ)) (k : Key)
    (hk : k.tree.Real) (c : Fin (2 ^ 9) → ℤ) :
    simulateQ so (sign164 (aux := aux) ρ k c) =
      simulateQ so (sign164G (aux := aux) ρ (fun _ _ _ => True) k c) := by
  rw [sign164_eq_margin ρ hεq e he he1 k c]
  exact sign164G_clamp ρ so hso _
      (fun L vh v h => InBR.chkM fun o => by unfold R64; exact h o) k hk c

theorem sign164G_pathN (ρ : Arith64 εq) (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop) (k : Key)
    (c : Fin (2 ^ 9) → ℤ) : PathSum w1 (sign164G (aux := aux) ρ chk k c) 1024 := by
  unfold sign164G
  split_ifs
  · rw [map_eq_bind_pure_comp]
    exact (PathSum.bind ((ffs_pathNG ρ.toArith _ chk k.tree _ _ _ _).weaken (by norm_num))
      (T := 0) fun _ => .pure _ le_rfl).weaken (le_of_eq (add_zero _))
  · exact .pure _ (by norm_num)

/-- `ox` is `oa` with every call `sa key c` replaced by `sb key c` (at most `K` calls, each on a key
with a real stored tree); every other query is auxiliary. -/
inductive Swap (sa sb : Key → (Fin (2 ^ 9) → ℤ) →
    OracleComp (FalconGame.spec aux Falcon.CallP) (Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))))
        :
    ℕ → {α : Type} → OracleComp (FalconGame.spec aux Falcon.CallP) α →
      OracleComp (FalconGame.spec aux Falcon.CallP) α → Prop
  | pure (K : ℕ) {α : Type} (x : α) : Swap sa sb K (pure x) (pure x)
  | query (K : ℕ) {α : Type} (t : ιA)
      (k k' : (FalconGame.spec aux Falcon.CallP).Range (.inl t) →
        OracleComp (FalconGame.spec aux Falcon.CallP) α)
      (h : ∀ u, Swap sa sb K (k u) (k' u)) :
      Swap sa sb K
          (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl t)) >>= k)
        (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl t)) >>= k')
  | sign (K : ℕ) {α : Type} (key : Key) (hkey : key.tree.Real) (c : Fin (2 ^ 9) → ℤ)
      (k k' : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) →
        OracleComp (FalconGame.spec aux Falcon.CallP) α)
      (h : ∀ y, Swap sa sb K (k y) (k' y)) : Swap sa sb (K + 1) (sa key c >>= k) (sb key c >>= k')

section Swap

variable {sa sb : Key → (Fin (2 ^ 9) → ℤ) →
  OracleComp (FalconGame.spec aux Falcon.CallP) (Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)))}

theorem Swap.usesG_left {K : ℕ} {α : Type} {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap sa sb K oa ox) : UsesG sa K oa := by
  induction h with
  | pure K x => exact .pure K x
  | query K t k k' _ ih => exact .query K t k ih
  | sign K key _ c k k' _ ih => exact .sign K key c k ih

theorem Swap.usesG_right {K : ℕ} {α : Type}
    {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap sa sb K oa ox) : UsesG sb K ox := by
  induction h with
  | pure K x => exact .pure K x
  | query K t k k' _ ih => exact .query K t k' ih
  | sign K key _ c k k' _ ih => exact .sign K key c k' ih

theorem Swap.simulateQ_eq {K : ℕ} {α : Type}
    {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap sa sb K oa ox)
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hs : ∀ key c, key.tree.Real → simulateQ so (sa key c) = simulateQ so (sb key c)) :
    simulateQ so oa = simulateQ so ox := by
  induction h with
  | pure K x => rfl
  | query K t k k' _ ih => simp only [simulateQ_bind, ih]
  | sign K key hkey c k k' _ ih => simp only [simulateQ_bind, hs key c hkey, ih]

end Swap

/--
**A signing loop is a `Swap` instance**: spec Alg. 10 l. 4-11 with at most `n` calls, Type 1 signing
on one side and abort-free signing on the other. -/
theorem Swap.signLoopG {β : Type} (ρ : Arith64 εq) (k : Key) (hk : k.tree.Real)
    (c : Fin (2 ^ 9) → ℤ)
    (acc : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) → Option β) :
    ∀ n, Swap (aux := aux) (sign164 ρ)
        (sign164G ρ fun _ _ _ => True) n (signLoopG (sign164 ρ) k c acc n)
      (signLoopG (sign164G ρ fun _ _ _ => True) k c acc n)
  | 0 => Swap.pure 0 none
  | n + 1 => Swap.sign n k hk c _ _ fun y => by
    rcases acc y with _ | b
    exacts [Swap.signLoopG ρ k hk c acc n, Swap.pure n _]

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- **Exact signing against abort-free exact signing**: within `2·p y·1024K` in total variation. -/
theorem etvDist_E_X (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) (y : ℝ) (hy : 1 / 2 ≤ y) (hy30 : y ≤ 30)
    (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (K : ℕ) {α : Type} [MeasurableSpace α] {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) :
    (𝒟[simulateQ implE oa]).etvDist 𝒟[simulateQ implE ox] ≤
      2 * ENNReal.ofReal (pclamp y * (K * 1024)) := by
  have hw0 : ∀ t, 0 ≤ (w1 : ιA ⊕ Falcon.CallP → ℝ) t :=
      fun t => by rcases t with _ | _ <;> simp [w1]
  have hw1 : ∀ q, 1 ≤ (w1 : ιA ⊕ Falcon.CallP → ℝ) (.inr q) := fun q => by simp [w1]
  have h1 := etvDist_implT_le y (by linarith) implE hE w1 hw0 hw1 (Uses64.pathN h.usesG_left)
  have h2 := etvDist_implT_le y (by linarith) implE hE w1 hw0 hw1
    (UsesG.path h.usesG_right w1 (fun _ => rfl) 1024 (by norm_num) (sign164G_pathN ρ _))
  have heq : 𝒟[simulateQ (implT y implE) oa] = 𝒟[simulateQ (implT y implE) ox] := by
    rw [← simulateQ_clampQ, ← simulateQ_clampQ,
      h.simulateQ_eq _ fun key c hk => sign164_clamp ρ hεq e he he1 _
        (fun q => (allOut_clampQ hy q).mono fun _ h => h.trans hy30) key hk c]
  calc (𝒟[simulateQ implE oa]).etvDist 𝒟[simulateQ implE ox]
      ≤ (𝒟[simulateQ implE oa]).etvDist 𝒟[simulateQ (implT y implE) oa] +
          (𝒟[simulateQ (implT y implE) oa]).etvDist 𝒟[simulateQ implE ox] :=
        Measure.etvDist_triangle _ _ _
    _ ≤ ENNReal.ofReal (pclamp y * (K * 1024)) + ENNReal.ofReal (pclamp y * (K * 1024)) := by
        have h2' : (𝒟[simulateQ (implT y implE) oa]).etvDist 𝒟[simulateQ implE ox] ≤
            ENNReal.ofReal (pclamp y * (K * 1024)) := by
          rw [heq, Measure.etvDist_comm]
          exact h2
        exact add_le_add h1 h2'
    _ = 2 * ENNReal.ofReal (pclamp y * (K * 1024)) := (two_mul _).symm

/-- `exp(-30²/(2·1.825²)) ≤ 2⁻¹⁹⁴`. -/
theorem exp_thirty : Real.exp (-(30 ^ 2 / (2 * (1825 / 1000) ^ 2))) ≤ 1 / 2 ^ 194 := by
  have h2 : (2 : ℝ) ^ 194 ≤ Real.exp 135 := by
    have := Real.exp_one_gt_d9
    calc (2 : ℝ) ^ 194 ≤ 2.718 ^ 135 := by norm_num
      _ ≤ Real.exp 1 ^ 135 := pow_le_pow_left₀ (by norm_num) (by linarith) 135
      _ = Real.exp 135 := by rw [← Real.exp_nat_mul]; norm_num
  calc Real.exp (-(30 ^ 2 / (2 * (1825 / 1000) ^ 2))) ≤ Real.exp (-135) :=
        Real.exp_le_exp.2 (by norm_num)
    _ = (Real.exp 135)⁻¹ := Real.exp_neg _
    _ ≤ ((2 : ℝ) ^ 194)⁻¹ := inv_anti₀ (by positivity) h2
    _ = 1 / 2 ^ 194 := by norm_num

/-- **The constant**: `2·p 30·1024K ≤ 2⁻¹⁴⁰` for `K ≤ 2³⁹`. -/
theorem eps_le (K : ℕ) (hK : K ≤ 2 ^ 39) :
    2 * ENNReal.ofReal (pclamp 30 * (K * 1024)) ≤ (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  have hp : pclamp 30 ≤ 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 194) := by
    unfold pclamp
    exact mul_le_mul_of_nonneg_left exp_thirty (by norm_num)
  have hx : 2 * (pclamp 30 * (K * 1024)) ≤ 1 / 2 ^ 140 := by
    have := mul_le_mul hp (mul_le_mul_of_nonneg_right hK' (by norm_num : (0 : ℝ) ≤ 1024))
      (by positivity) (by norm_num)
    nlinarith [pclamp_nonneg 30]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_rpow_of_pos (by norm_num)]
  refine ENNReal.ofReal_le_ofReal (hx.trans_eq ?_)
  rw [Real.rpow_neg (by norm_num), show (140 : ℝ) = ((140 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `p_F y = 2(1 + 2⁻³⁶)·exp(-y²/(2·1.826²))`. -/
noncomputable def pclampF (y : ℝ) : ℝ :=
  2 * (1 + 1 / 2 ^ 36) * Real.exp (-(y ^ 2 / (2 * (1826 / 1000) ^ 2)))

theorem pclampF_nonneg (y : ℝ) : 0 ≤ pclampF y := by unfold pclampF; positivity

/-- A SamplerZ call's `σ̄` is at most `1.826`. -/
theorem σbar_le (q : Falcon.CallP) : q.σbar ≤ 1826 / 1000 := by
  obtain ⟨h1, h2⟩ := q.hσ
  have hp : 0 < q.σ := by linarith
  have h3 : q.σbar / q.σ ≤ 1 + 1 / 2 ^ 42 := by linarith [(abs_le.1 q.hΔσ).2]
  rw [div_le_iff₀ hp] at h3
  nlinarith

/--
F's SamplerZ answer clamped: kept when within `y` of the computed centre `t̄` and `(t̄ - t)² ≤ 2⁻⁸`,
else the rounded exact centre. -/
noncomputable def clampF (y : ℝ) (q : Falcon.CallP) (z : ℤ) : ℤ :=
  if |(z : ℝ) - q.tbar| < y ∧ (q.tbar - q.t) ^ 2 ≤ 1 / 2 ^ 8 then z else round q.t

theorem abs_clampF_sub_le {y : ℝ} (hy : 1 / 2 ≤ y) (q : Falcon.CallP) (z : ℤ) :
    |(clampF y q z : ℝ) - q.t| ≤ y + 1 / 16 := by
  unfold clampF
  split_ifs with h
  · have h2 : |q.tbar - q.t| ≤ 1 / 16 := abs_le.2 ⟨by nlinarith [h.2], by nlinarith [h.2]⟩
    calc |(z : ℝ) - q.t| = |((z : ℝ) - q.tbar) + (q.tbar - q.t)| := by congr 1; ring
      _ ≤ |(z : ℝ) - q.tbar| + |q.tbar - q.t| := abs_add_le _ _
      _ ≤ y + 1 / 16 := by linarith [h.1]
  · rw [abs_sub_comm]
    linarith [abs_sub_round q.t]

/-- The post-processing of world T_F. -/
noncomputable def fF (y : ℝ) : (t : ιA ⊕ Falcon.CallP) →
    (FalconGame.spec aux Falcon.CallP).Range t →
    (FalconGame.spec aux Falcon.CallP).Range t
  | .inl _ => id
  | .inr q => clampF y q

/-- World T_F as a rewriting: F's SamplerZ answers clamped by `clampF y`. -/
noncomputable def clampQF (y : ℝ) :
    QueryImpl (FalconGame.spec aux Falcon.CallP) (OracleComp (FalconGame.spec aux Falcon.CallP)) :=
  fun t => fF y t <$> liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) t)

theorem allOut_clampQF {y : ℝ} (hy : 1 / 2 ≤ y) (hy' : y ≤ 299 / 10) (q : Falcon.CallP) :
    AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 30)
        (clampQF (aux := aux) y (.inr q) : OracleComp _ ℤ) := by
  change AllOut _ ((clampF y q <$>
    (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) : OracleComp _
        ℤ)) :
      OracleComp _ ℤ)
  rw [map_eq_bind_pure_comp]
  have h30 : y + 1 / 16 ≤ 30 := by linarith
  exact .query_bind _ _ fun u => .pure _ ((abs_clampF_sub_le hy q u).trans h30)

omit [Monad m] [LawfulMonad m] in
theorem etvDist_map_clampF_le (mx : m ℤ) {q : Falcon.CallP}
    (hmx : 𝒟[mx] = discreteGaussianMeasure q.σbar q.tbar) {y : ℝ} (hy : 0 ≤ y) :
    𝒟[mx].etvDist (𝒟[mx].map (clampF y q)) ≤
      ENNReal.ofReal (pclampF y * 1 + if 1 / 2 ^ 8 < (q.tbar - q.t) ^ 2 then 1 else 0) := by
  by_cases hb : 1 / 2 ^ 8 < (q.tbar - q.t) ^ 2
  · simp only [hb, ↓reduceIte]
    refine (Measure.etvDist_le_one _ _ (evalDist_apply_univ_le_one _) ?_).trans ?_
    · rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ]
      exact evalDist_apply_univ_le_one _
    · rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [pclampF_nonneg y])
  · simp only [hb, ↓reduceIte, add_zero, mul_one]
    rw [hmx]
    have hsub : {z : ℤ | clampF y q z ≠ z} ⊆ {z : ℤ | y ≤ |(z : ℝ) - q.tbar|} :=
      fun z (hz : clampF y q z ≠ z) => by
        change y ≤ |(z : ℝ) - q.tbar|
        by_contra h
        have hb' : (q.tbar - q.t) ^ 2 ≤ 1 / 2 ^ 8 := not_lt.1 hb
        exact hz (by simp only [clampF, not_le.1 h, hb', and_self, ↓reduceIte])
    refine (etvDist_map_self_le _ _).trans ((measure_mono hsub).trans
      ((FalconPrecision.Errors.GaussTail.measure_abs_ge_falcon q.σbar q.tbar y q.hσbar_ge hy).trans
        (ENNReal.ofReal_le_ofReal ?_)))
    have h0 : 0 < q.σbar := by linarith [q.hσbar_ge]
    unfold pclampF
    gcongr
    exact σbar_le q

/-- **Type 1 signing against abort-free Type 1 signing**, both answered by `implF`: within `2·p_F
y·1024K`. -/
theorem etvDist_F_F' (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) (y : ℝ) (hy : 1 / 2 ≤ y) (hy' : y ≤ 299 / 10)
    [hA : ∀ t, Nonempty (aux t)] (implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (K : ℕ) (hKe : (K : ℝ) * (49 * e + 43700 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 8) {α : Type}
        [MeasurableSpace α]
    {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) :
    (𝒟[simulateQ implF oa]).etvDist 𝒟[simulateQ implF ox] ≤
      2 * ENNReal.ofReal (pclampF y * (K * 1024)) := by
  have hne : ∀ t, Nonempty ((FalconGame.spec aux Falcon.CallP).Range t) := fun t => by
    rcases t with x | q
    · exact hA x
    · exact ⟨(0 : ℤ)⟩
  let w : ιA ⊕ Falcon.CallP → ℝ := fun t => pclampF y * w1 t + if 1 / 2 ^ 8 < wS t then 1 else 0
  have hw1 : ∀ t, 0 ≤ (w1 : ιA ⊕ Falcon.CallP → ℝ) t :=
      fun t => by rcases t with _ | _ <;> simp [w1]
  have hwS : ∀ t, 0 ≤ (wS : ιA ⊕ Falcon.CallP → ℝ) t := fun t => by
    rcases t with _ | q
    · simp [wS]
    · exact sq_nonneg _
  have hw : ∀ t, 0 ≤ w t := fun t =>
    add_nonneg (mul_nonneg (pclampF_nonneg y) (hw1 t)) (by split_ifs <;> norm_num)
  have hB : ∀ t, @Measure.etvDist _ ⊤ (@evalDist m _ _ ⊤ (implF t))
      (@Measure.map _ _ ⊤ ⊤ (fF y t) (@evalDist m _ _ ⊤ (implF t))) ≤ ENNReal.ofReal (1 * w t) := by
    rintro (x | q)
    · change @Measure.etvDist _ ⊤
        (@evalDist m _ ((FalconGame.spec aux Falcon.CallP).Range (.inl x)) ⊤ (implF (.inl x)))
        (@Measure.map _ _ ⊤ ⊤ id
          (@evalDist m _ ((FalconGame.spec aux Falcon.CallP).Range (.inl x)) ⊤ (implF (.inl x)))) ≤
              _
      rw [@Measure.map_id _ ⊤]
      exact (@Measure.etvDist_self _ ⊤ _).trans_le bot_le
    · refine (etvDist_map_clampF_le (implF (.inr q)) (hF q) (by linarith)).trans (le_of_eq ?_)
      simp only [w, w1, wS, Sum.elim_inr, one_mul, mul_one]
      congr
  have hA : PathSum w oa (pclampF y * (K * 1024) + 0) :=
    (PathSum.mono (w' := fun t => pclampF y * w1 t) (pclampF_nonneg y) (fun _ => le_rfl)
      (Uses64.pathN h.usesG_left)).add ((Uses64.pathS hεq e he he1 h.usesG_left).indicator hwS hKe)
  have heqC : simulateQ (clampQF y) oa = simulateQ (clampQF y) ox :=
    h.simulateQ_eq _ fun key c hk => sign164_clamp ρ hεq e he he1 (clampQF y)
        (allOut_clampQF hy hy') key hk c
  have hA' := hA.simulateQ_map (fF y) fun _ => rfl
  have hX : PathSum w (simulateQ (clampQF y) ox) (pclampF y * (K * 1024) + 0) := heqC ▸ hA'
  have h1 := etvDist_simulateQ_rewrite implF (fF y) (fun _ => rfl) zero_le_one w hw hB oa _ hA'
  have h2 := etvDist_simulateQ_rewrite implF (fF y) (fun _ => rfl) zero_le_one w hw hB ox _ hX
  calc (𝒟[simulateQ implF oa]).etvDist 𝒟[simulateQ implF ox]
      ≤ (𝒟[simulateQ implF oa]).etvDist 𝒟[simulateQ implF (simulateQ (clampQF y) oa)] +
          (𝒟[simulateQ implF (simulateQ (clampQF y) oa)]).etvDist 𝒟[simulateQ implF ox] :=
        Measure.etvDist_triangle _ _ _
    _ ≤ ENNReal.ofReal (1 * (pclampF y * (K * 1024) + 0)) +
          ENNReal.ofReal (1 * (pclampF y * (K * 1024) + 0)) := by
        refine add_le_add h1 ?_
        rw [heqC, Measure.etvDist_comm]
        exact h2
    _ = 2 * ENNReal.ofReal (pclampF y * (K * 1024)) := by rw [one_mul, add_zero, two_mul]

/-- `exp(-29.9²/(2·1.826²)) ≤ 2⁻¹⁹³`. -/
theorem exp_299 : Real.exp (-((299 / 10) ^ 2 / (2 * (1826 / 1000) ^ 2))) ≤ 1 / 2 ^ 193 := by
  have h2 : (2 : ℝ) ^ 193 ≤ Real.exp 134 := by
    have := Real.exp_one_gt_d9
    calc (2 : ℝ) ^ 193 ≤ 2.718 ^ 134 := by norm_num
      _ ≤ Real.exp 1 ^ 134 := pow_le_pow_left₀ (by norm_num) (by linarith) 134
      _ = Real.exp 134 := by rw [← Real.exp_nat_mul]; norm_num
  calc Real.exp (-((299 / 10) ^ 2 / (2 * (1826 / 1000) ^ 2))) ≤ Real.exp (-134) :=
        Real.exp_le_exp.2 (by norm_num)
    _ = (Real.exp 134)⁻¹ := Real.exp_neg _
    _ ≤ ((2 : ℝ) ^ 193)⁻¹ := inv_anti₀ (by positivity) h2
    _ = 1 / 2 ^ 193 := by norm_num

/-- **The constant of the F side**: `2·p_F 29.9·1024K ≤ 2⁻¹⁴⁰` for `K ≤ 2³⁹`. -/
theorem eps_leF (K : ℕ) (hK : K ≤ 2 ^ 39) :
    2 * ENNReal.ofReal (pclampF (299 / 10) * (K * 1024)) ≤ (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  have hp : pclampF (299 / 10) ≤ 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 193) := by
    unfold pclampF
    exact mul_le_mul_of_nonneg_left exp_299 (by norm_num)
  have hx : 2 * (pclampF (299 / 10) * (K * 1024)) ≤ 1 / 2 ^ 140 := by
    have := mul_le_mul hp (mul_le_mul_of_nonneg_right hK' (by norm_num : (0 : ℝ) ≤ 1024))
      (by positivity) (by norm_num)
    nlinarith [pclampF_nonneg (299 / 10)]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_rpow_of_pos (by norm_num)]
  refine ENNReal.ofReal_le_ofReal (hx.trans_eq ?_)
  rw [Real.rpow_neg (by norm_num), show (140 : ℝ) = ((140 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

theorem two_rpow_neg140_ne_top : (2 : ℝ≥0∞) ^ (-(140 : ℝ)) ≠ ⊤ := by
  rw [Ne, ENNReal.rpow_eq_top_iff]
  norm_num

theorem le_add_etvDist {β : Type} [MeasurableSpace β] (μ ν : MeasureTheory.Measure β) {s : Set β}
    (hs : MeasurableSet s) : μ s ≤ ν s + μ.etvDist ν :=
  le_add_tsub.trans
      (add_le_add le_rfl (le_self_add.trans (Measure.absDiff_apply_le_etvDist μ ν hs)))

end FalconPrecision.Errors.AbortExact

namespace FalconPrecision.Falcon

open MeasureTheory InformationTheory LatticeCrypto FalconPrecision.Errors.FFSamp
    FalconPrecision.Errors.AbortExact
open scoped ENNReal

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Theorem 2 at Falcon-512 for Type 1 fixed-point signing against abort-free exact signing**
(normalized `1/q`, `K ≤ 2³⁹`; `λ = 128`, hop A). For every Type 1 arithmetic `ρ` with `1/q` within
`2⁻⁷⁸` and every pair of experiments `oa`, `ox` where `ox` is `oa` with each of its at most `K`
calls of Type 1 ffSampling (`sign164`, the non-split scale-first chain of 2026/2431 §3.1 with the
model's range checks `‖·‖ ≤ R64 - 1`, `R64 = 2²⁴`, which deployed signers do not run) replaced by
abort-free exact signing (`sign164G ρ (fun _ _ _ => True)`; `⊥` only for `c` with some `|c i| ≥ q`,
as in every world), each call on a key whose stored `ℓ̂` are FFTs of real polynomials
(`FTree.Real`), and otherwise only auxiliary queries (`Swap`): success `> T·2⁻¹²⁶` in F (Type 1
signing with `ρ` and those checks) gives success `> T·2⁻¹²⁸ - 2⁻¹⁴⁰` in X (abort-free exact signing
on the stored tree, answered by `implE`). The check-free Type 1 signer F′ is covered by
`falcon512_exact64n'`.

`2⁻¹⁴⁰` bounds `|Pr_E - Pr_X| ≤ 2·p 30·1024K` (`etvDist_E_X`, `eps_le`), `p 30 = 2(1 +
2⁻³⁶)exp(-30²/(2·1.825²))`: clamping every SamplerZ answer to within `30` of its centre costs `p 30`
per query (`GaussTail`, `AbortTV`), and with clamped answers no range check fires (`ffsG_clamp`,
route B′). Not proved: hop B (stored tree to the true tree of the key); the `ℓ̂` bounds of `FTree`
are checks added by this model, and `FTree.Real` is a hypothesis on the stored tree (it holds with
half-spectrum storage or sign-symmetric rounding); neither is in Falcon round 3 or the FIPS 206
draft, and nothing ties the tree to the key. No implementation (2026/2431's fxp32.64 signer, [DAB26]
64.64, c-fn-dsa) is shown to meet `sign164`'s operation sequence; the multiply-first order and the
split path are not modelled. SamplerZ is assumed perfect (`hE`, `hM`, `hF`). Keys: the paper's
modified NTRUGen (ePrint 2026/1531 Alg. 2), `Key`'s bounds up to keygen's rounding. X carries the
computed centres of `ρ` in its queries; `implE` ignores them (`hE`). No UF-CMA game is defined:
`oa`, `ox` are any experiments. Register overflow is not represented. Other hypotheses: those of
`falcon512_model64n`. -/
theorem falcon512_exact64n (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
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
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
  have h := falcon512_model64n ρ K hK T hT implA implE implM implF hAE hAM hAF hE hM hF oa
    hswap.usesG_left hs hwin
  have hd :=
      etvDist_E_X ρ (by norm_num) _ inp64_norm (by norm_num) 30
          (by norm_num) le_rfl implE hE K hswap
  exact h.trans_le ((le_add_etvDist _ _ hs).trans (add_le_add le_rfl (hd.trans (eps_le K hK))))

/--
**`falcon512_exact64n` for `1/q` at 64 fractional bits** (the baseline), `K ≤ 2³⁸`: same statement
and hypotheses with `falcon512_model64`. -/
theorem falcon512_exact64 (ρ : Arith64 (1 / 2 ^ 65)) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
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
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
  have h := falcon512_model64 ρ K hK T hT implA implE implM implF hAE hAM hAF hE hM hF oa
    hswap.usesG_left hs hwin
  have hd :=
      etvDist_E_X ρ (by norm_num) _ inp64_base (by norm_num) 30
          (by norm_num) le_rfl implE hE K hswap
  exact h.trans_le ((le_add_etvDist _ _ hs).trans (add_le_add le_rfl
    (hd.trans (eps_le K (hK.trans (by norm_num))))))

/-- **Theorem 2 at Falcon-512 between abort-free Type 1 signing and abort-free exact signing**
(normalized `1/q`, `K ≤ 2³⁹`; `λ = 128`, hop A). F′ is Type 1 fixed-point signing with no range
checks (`sign164G ρ (fun _ _ _ => True)` answered by `implF`), X is abort-free exact signing on the
stored tree (the same `ox` answered by `implE`): success `> T·2⁻¹²⁶ + 2⁻¹⁴⁰` in F′ gives success `>
T·2⁻¹²⁸ - 2⁻¹⁴⁰` in X. `oa` is `ox` with every abort-free call replaced by `sign164` (`Swap`), and
only fixes the hypotheses of `falcon512_exact64n`.

Proof: `|Pr_F[oa] - Pr_F′[ox]| ≤ 2·p_F 29.9·1024K ≤ 2⁻¹⁴⁰` (`etvDist_F_F'`, `eps_leF`): the clamp
that keeps F's answer when it lies within `29.9` of `t̄` and `(t̄ - t)² ≤ 2⁻⁸`, else replaces it by
the rounded exact centre, costs `p_F 29.9 = 2(1 + 2⁻³⁶)exp(-29.9²/(2·1.826²))` per query along every
execution of the clamped run (no query with `(t̄ - t)² > 2⁻⁸` occurs: the path sum of `(t̄ - t)²` is
`≤ 2⁻⁹`, `Uses64.pathS`); the clamped answers lie within `30` of the exact centres, so no range
check fires (`ffsG_clamp`); then `falcon512_exact64n`. Every auxiliary answer type is inhabited
(`hA`). Not proved, and other hypotheses: those of `falcon512_exact64n`. -/
theorem falcon512_exact64n' (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    [hA : ∀ t, Nonempty (aux t)]
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
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) < 𝒟[simulateQ implF ox] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  have hKe : (K : ℝ) * (49 * (54 / 100 / 2 ^ 32) + 43700 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 8 := by
    have := mul_le_mul_of_nonneg_right hK'
        (sq_nonneg (49 * (54 / 100 / 2 ^ 32) + 43700 / 2 ^ 40 : ℝ))
    linarith [centers_budget64n]
  have hd :=
      etvDist_F_F' ρ (by norm_num) _ inp64_norm (by norm_num) (299 / 10)
          (by norm_num) le_rfl implF hF
    K hKe hswap
  have h1 : 𝒟[simulateQ implF ox] s ≤ 𝒟[simulateQ implF oa] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
    refine (le_add_etvDist _ _ hs).trans (add_le_add le_rfl ?_)
    rw [Measure.etvDist_comm]
    exact hd.trans (eps_leF K hK)
  have hwin' : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s :=
    (ENNReal.add_lt_add_iff_right two_rpow_neg140_ne_top).1 (hwin.trans_le h1)
  exact falcon512_exact64n ρ K hK T hT implA implE implM implF hAE hAM hAF hE hM hF oa ox hswap hs
      hwin'

/--
**`falcon512_exact64n'` for `1/q` at 64 fractional bits** (the baseline), `K ≤ 2³⁸`: same statement
and hypotheses with `falcon512_exact64`. -/
theorem falcon512_exact64' (ρ : Arith64 (1 / 2 ^ 65)) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    [hA : ∀ t, Nonempty (aux t)]
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
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) < 𝒟[simulateQ implF ox] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by exact_mod_cast hK
  have hKe : (K : ℝ) * (49 * (33 / 10 / 2 ^ 32) + 43700 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 8 := by
    have := mul_le_mul_of_nonneg_right hK'
        (sq_nonneg (49 * (33 / 10 / 2 ^ 32) + 43700 / 2 ^ 40 : ℝ))
    linarith [centers_budget64]
  have hd :=
      etvDist_F_F' ρ (by norm_num) _ inp64_base (by norm_num) (299 / 10)
          (by norm_num) le_rfl implF hF
    K hKe hswap
  have h1 : 𝒟[simulateQ implF ox] s ≤ 𝒟[simulateQ implF oa] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) := by
    refine (le_add_etvDist _ _ hs).trans (add_le_add le_rfl ?_)
    rw [Measure.etvDist_comm]
    exact hd.trans (eps_leF K (hK.trans (by norm_num)))
  have hwin' : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s :=
    (ENNReal.add_lt_add_iff_right two_rpow_neg140_ne_top).1 (hwin.trans_le h1)
  exact falcon512_exact64 ρ K hK T hT implA implE implM implF hAE hAM hAF hE hM hF oa ox hswap hs
      hwin'

end FalconPrecision.Falcon
