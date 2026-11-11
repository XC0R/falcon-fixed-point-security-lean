/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.HopBCore

/-! # Hop B: exact signing with the stored tree against exact Falcon with the true tree

Hop A (`Falcon.falcon512_exact64n'`) compares Type 1 fixed-point signing F′ with X, exact signing on
the stored tree `Key.tree` (an `FTree`: leaves `σ̄`, factors `ℓ̂` from fixed-point key expansion,
not tied to the key). Hop B compares X with Y, exact Falcon: ffSampling (Alg. 8 of ePrint 2026/1531)
on the true tree `KeyB.trueTree`, the exact ffLDL⋆ (Alg. 5) of the Gram matrix `B·B⋆` of
`B = [[g, -f], [G, -F]]`, leaves `σ/√D` (Alg. 1 l. 6-7).

The stored tree's relation to the true tree is a hypothesis (`Close δ`): `‖ℓ̂ - ℓ‖∞ ≤ δ L` at every
node of depth `L + 1`, `|σ̄/σ - 1| ≤ 2⁻⁴²` and the true leaves in `[1.2778, 1.825]` at every leaf.
Its derivation from a model of key expansion is not part of this file.

Route. `ffsB` runs ffSampling on both trees with the same samples: a SamplerZ call carries the true
leaf and centre (`CallP.σ`, `CallP.t`) and the stored ones (`CallP.σbar`, `CallP.tbar`). Answered by
`D_{σ̄,t̄}` it is X (`relabel_X`); answered by `D_{σ,t}` it is Y (`relabel_Y`). Per call: Lemma 5
(leaves, `|1/σ̄² - 1/σ²| ≤ 2⁻⁴⁰`) and Lemma 4 (centres). The centre difference starts at line 10,
`t̄0' - t0' = (t̄0 - t0) + (t̄1 - t1)ℓ̂ + (t1 - ẑ1)(ℓ̂ - ℓ)`, so it needs a bound on the true
deviation `t1 - ẑ1`. This file clamps (`AbortExact.clampQ`, around the true centre, `y = 30.5`):
along every history of the clamped run the deviation of a call at depth `L` has ℓ2 norm
`≤ devB y δ L` (the true tree is real, `isReal_trueTree`, so the leaf centres are real;
`‖ℓ‖∞ ≤ lam512 L + δ L`), and the sum of squared centre differences of a call with input difference
`X` (ℓ2) is `≤ (gainA L·X + cB y δ L)²` (`ffsB_clamp`; at the root `X = 0` and
`cB y δ 9² = s2B y δ`). Clamping costs `p(y)` per SamplerZ call in Y and `p(y - 1/2)` in X
(`tv_clamp_F`: along the clamped run every squared centre difference `(t̄ - t)²` is
`≤ s2B y δ ≤ 1/4`). Theorem 2 (`FalconGame.theorem2`) at `λ = 131` then moves `T·2⁻¹²⁹` in X to
`T·2⁻¹³¹` in Y.

`falcon512_hopB`: X against Y. `falcon512_fixed_vs_true`: composed with hop A, F′ against Y;
instances at the tree errors `δ127` (`K ≤ 2³⁹`) and `δ63` (`K ≤ 2³⁰`). Experiments are `OracleComp`s
over auxiliary oracles and a signing oracle on keys passing `KeyB.Good δ` (`specS`); the four worlds
run them through `signImpl` with the respective signer.

Assumed (hypotheses of the theorems): on every signing key, `Close δ` and the stored tree real
(`KeyB.Good`; the leaf part of `Close` contains the true leaves' range `[1.2778, 1.825]`, paper §4.1
"Bounding the leaves" from `αGPV ≤ 1.17`); `K·s2B 30.5 δ ≤ 2⁻⁹` (proved for `δ127` at `K ≤ 2³⁹` and
`δ63` at `K ≤ 2³⁰`); SamplerZ perfect in every world (`hE`, `hM`, `hF`); `K ≤ 2³⁹` signing-oracle
calls (one ffSampling call each, restarts included) along every execution (hop A's cap; here it
bounds the clamp costs and the `2⁴⁹` SamplerZ calls of Theorem 2 at `λ = 131`); for the composition,
the hypotheses of `Falcon.falcon512_exact64n'`. The clamp is a proof device (no signer clamps): it
costs `≤ 2⁻¹⁴¹` in X and in Y (`eps141`). Proved here: the true tree is real (`isReal_trueTree`).
Not proved: a model of key expansion giving `Close δ` (at `p = 127` or `p = 63`), NTRUSolve (nothing
ties `g, G` to `f, F`; `fG - gF = q` is not assumed), the true leaves' range (§4.1, from
`αGPV ≤ 1.17`), and what hop A does not prove. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Errors.HopB

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} {δ : ℕ → ℝ} {εq : ℝ}

theorem l2_pairF_zero {L : ℕ} : l2 (pairF (0 : Out L → ℂ) 0) = 0 := by
  have h := l2_pairF_sq (0 : Out L → ℂ) 0
  have h0 : l2 (0 : Out L → ℂ) = 0 := by unfold l2; simp
  rw [h0] at h
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by linarith)

/-- **Centre differences of a clamped signing call** (`ffsB_clamp` at the root, `X = 0`). -/
theorem signB_clamp (y : ℝ) (hy : 1 / 2 ≤ y) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    Hist (PQ (s2B y δ)) (fun _ => True) (simulateQ (clampQ y) (signB (aux := aux) δ k c)) ∧
      PathSum wS (simulateQ (clampQ y) (signB (aux := aux) δ k c)) (s2B y δ) := by
  unfold signB
  split_ifs
  · rw [simulateQ_map, map_eq_bind_pure_comp]
    obtain ⟨H, P⟩ :=
        ffsB_clamp (aux := aux) y hy k.1.tree k.1.trueTree k.2.close (isReal_trueTree k.1)
      (t0E k.1.toKey c) (t1E k.1.toKey c) (t0E k.1.toKey c) (t1E k.1.toKey c) (isReal_t0E _ _)
      (isReal_t1E _ _) 0 (by rw [sub_self, sub_self, l2_pairF_zero])
    rw [mul_zero, zero_add, ← s2B_eq] at H P
    exact ⟨H.bind fun _ _ => .pure _ trivial,
        (P.bind fun _ => .pure _ le_rfl).weaken (le_of_eq (add_zero _))⟩
  · rw [simulateQ_pure]
    exact ⟨.pure _ trivial, .pure _ (s2B_nonneg y δ)⟩

theorem simulateQ_clampQ_signImpl (y : ℝ) {α : Type} (oe : OracleComp (specS aux δ) α) :
    simulateQ (clampQ y) (runB δ oe) =
      simulateQ (fun t => simulateQ (clampQ y) (signImpl (signB δ) t)) oe :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe

theorem clampQ_inl (y : ℝ) (x : ιA) :
    simulateQ (clampQ (aux := aux) y) (signImpl (signB δ) (.inl x)) =
      liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl x)) :=
  simulateQ_spec_query (impl := clampQ y) (Sum.inl x)

/-- Along the clamped run every SamplerZ query has `(t̄ - t)² ≤ s2B y δ` and `σ̄ ≤ 1.825`. -/
theorem hist_clamp (y : ℝ) (hy : 1 / 2 ≤ y) {α : Type} (oe : OracleComp (specS aux δ) α) :
    Hist (PQ (s2B y δ)) (fun _ => True) (simulateQ (clampQ y) (runB δ oe)) := by
  rw [simulateQ_clampQ_signImpl]
  refine Hist.simulateQ_impl _ (fun t => ?_) oe
  rcases t with x | kc
  · rw [clampQ_inl]
    exact Hist.query (P := PQ (s2B y δ)) (.inl x) trivial
  · exact (signB_clamp y hy kc.1 kc.2).1

/-- **Centre differences of the clamped run.** Along every history of the clamped run, the squared
centre differences of a signing query sum to `≤ s2B y δ`. Per node, line 10:
`e0' = e0 + e1·ℓ̂ + (t1 - ẑ1)(ℓ̂ - ℓ)` (`ℓ̂` from `FTree`, `‖ℓ̂ - ℓ‖∞ ≤ δ L` from `Close`); the true
deviation `t - ẑ` grows as in `AbortExact.ffsG_clamp` with `‖ℓ‖∞ ≤ lam512 L + δ L` (true tree real:
leaf centres real, `isReal_trueTree`). -/
theorem pathS_clamp (y : ℝ) (hy : 1 / 2 ≤ y) (K : ℕ) {α : Type} (oe : OracleComp (specS aux δ) α)
    (hq : PathSum (wK δ) oe K) :
    PathSum wS (simulateQ (clampQ y) (runB δ oe)) (K * s2B y δ) := by
  rw [simulateQ_clampQ_signImpl, mul_comm]
  refine pathSum_simulateQ_impl _ (s2B_nonneg y δ) (fun t => ?_) hq
  rcases t with x | kc
  · rw [clampQ_inl]
    exact pathSum_query _ (by simp [wS, wK])
  · exact (signB_clamp y hy kc.1 kc.2).2.weaken (by simp [wK])

theorem ffsB_pathN {L : ℕ} (T : FTree L) :
    ∀ (U : LTree L) (h : Close δ T U) (t0 t1 s0 s1 : Out L → ℂ),
      PathSum w1 (ffsB (aux := aux) δ T U h t0 t1 s0 s1) (2 ^ (L + 1)) := by
  induction T with
  | leaf σb hb =>
    intro U h t0 t1 s0 s1
    cases U with
    | leaf σ =>
    simp only [ffsB]
    exact .query_bind _ _ fun _ => .query_bind _ _ fun _ =>
      .pure _ (by change (0 : ℝ) ≤ 2 ^ (0 + 1) - 1 - 1; norm_num)
  | @node L ℓh hℓh T0 T1 ih0 ih1 =>
    intro U h t0 t1 s0 s1
    cases U with
    | node ℓ U0 U1 =>
    simp only [ffsB]
    refine (PathSum.bind (ih1 U1 h.2.2 _ _ _ _) (T := 2 ^ (L + 1) + 0) fun r1 =>
      PathSum.bind (ih0 U0 h.2.1 _ _ _ _) fun _ => .pure _ le_rfl).weaken (le_of_eq (by ring))

/-- At most `1024` SamplerZ calls per signing query (as `sign164_pathN`, `UsesG.path`). -/
theorem pathN_runB (K : ℕ) {α : Type} (oe : OracleComp (specS aux δ) α) (hq : PathSum (wK δ) oe K) :
    PathSum w1 (runB δ oe) (K * 1024) := by
  rw [mul_comm]
  refine pathSum_simulateQ_impl _ (by norm_num) (fun t => ?_) hq
  rcases t with x | kc
  · exact pathSum_query _ (by simp [w1, wK])
  · change PathSum w1 (signB δ kc.1 kc.2) _
    unfold signB
    split_ifs
    · rw [map_eq_bind_pure_comp]
      exact (PathSum.bind (ffsB_pathN _ _ _ _ _ _ _) (T := 0) fun _ => .pure _ le_rfl).weaken
        (by simp [wK]; norm_num)
    · exact .pure _ (by simp [wK])

/-! ## Relabelling: the stored and true worlds as ffSampling on one tree -/

/-- A SamplerZ query relabelled to `CallP.stored σ t t`: all that `implE` reads. -/
noncomputable def canonE :
    QueryImpl (FalconGame.spec aux Falcon.CallP) (OracleComp (FalconGame.spec aux Falcon.CallP))
  | .inl x => liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl x))
  | .inr q => (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
      (.inr (Falcon.CallP.stored q.σ q.t q.t q.hσ))) : OracleComp _ ℤ)

open Classical in
/--
A SamplerZ query with `σ̄ ∈ [1.2778, 1.825]` relabelled to `CallP.stored σ̄ t̄ t̄`: all that `implF`
reads. -/
noncomputable def canonF :
    QueryImpl (FalconGame.spec aux Falcon.CallP) (OracleComp (FalconGame.spec aux Falcon.CallP))
  | .inl x => liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl x))
  | .inr q => if h : 12778 / 10000 ≤ q.σbar ∧ q.σbar ≤ 1825 / 1000 then
      (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
        (.inr (Falcon.CallP.stored q.σbar q.tbar q.tbar h))) : OracleComp _ ℤ)
    else (liftM
        (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) : OracleComp _ ℤ)

theorem canonF_inr_of (q : Falcon.CallP) (hq : 12778 / 10000 ≤ q.σbar ∧ q.σbar ≤ 1825 / 1000) :
    (canonF (aux := aux) (.inr q) : OracleComp _ ℤ) =
      liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
        (.inr (Falcon.CallP.stored q.σbar q.tbar q.tbar hq))) := by
  simp only [canonF, hq, and_self, ↓reduceDIte]
  rfl

theorem canonF_inr_not (q : Falcon.CallP) (hq : ¬(12778 / 10000 ≤ q.σbar ∧ q.σbar ≤ 1825 / 1000)) :
    (canonF (aux := aux) (.inr q) : OracleComp _ ℤ) =
      liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) := by
  simp only [canonF, hq, ↓reduceDIte]
  rfl

/-- Results of ffSampling on the stored tree (`ffsG`) and on both trees (`ffsB`): same integers and
exact FFTs. -/
def RelX {L : ℕ} (r : Option (Samp L)) (s : Samp L) : Prop :=
  ∃ s', r = some s' ∧ s'.z0 = s.z0 ∧ s'.z1 = s.z1 ∧ s'.e0 = s.e0 ∧ s'.e1 = s.e1

/--
Abort-free ffSampling on the stored tree (`ffsG`, exact inputs `e`, computed `c`) and ffSampling on
both trees (`ffsB`, true inputs `r`, stored inputs `e`) make the same relabelled queries. -/
theorem sameQ_ffsG_ffsB (ρ : Arith) (u : ℝ) {L : ℕ} (T : FTree L) :
    ∀ (U : LTree L) (h : Close δ T U) (e0 e1 c0 c1 r0 r1 : Out L → ℂ),
      SameQ RelX (simulateQ canonE (ffsG (aux := aux) ρ u (fun _ _ _ => True) T e0 e1 c0 c1))
        (simulateQ canonF (ffsB (aux := aux) δ T U h r0 r1 e0 e1)) := by
  induction T with
  | leaf σb hb =>
    intro U h e0 e1 c0 c1 r0 r1
    cases U with
    | leaf σ =>
    simp only [ffsG, ffsB, simulateQ_inr, simulateQ_pure,
      canonF_inr_of (callB σ σb (r0 ()).re (e0 ()).re hb h) (leaf_range hb),
      canonF_inr_of (callB σ σb (r1 ()).re (e1 ()).re hb h) (leaf_range hb)]
    refine .query_bind _ _ _ fun z0 => .query_bind _ _ _ fun z1 => .pure _ _ ?_
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  | @node L ℓh hℓh T0 T1 ih0 ih1 =>
    intro U h e0 e1 c0 c1 r0 r1
    cases U with
    | node ℓ U0 U1 =>
    simp only [ffsG, ffsB, and_self, ↓reduceIte, simulateQ_bind, simulateQ_pure]
    refine (ih1 U1 h.2.2 _ _ _ _ _ _).bind fun r1 s1 hr => ?_
    obtain ⟨s1', rfl, hz0, hz1, he0, he1⟩ := hr
    have hm : mergeE s1' = mergeE s1 := by simp only [mergeE, he0, he1]
    simp only [Option.elim, simulateQ_bind, hm]
    refine (ih0 U0 h.2.1 _ _ _ _ _ _).bind fun r0 s0 hr0 => ?_
    obtain ⟨s0', rfl, hz0', hz1', he0', he1'⟩ := hr0
    simp only [simulateQ_pure]
    refine .pure _ _ ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp only [joinU, joinE, mergeE, hz0, hz1, he0, he1, hz0', hz1', he0', he1']

/-- ffSampling on both trees and on the true tree make the same relabelled queries. -/
theorem sameQ_ffsB_ffsT {L : ℕ} (T : FTree L) :
    ∀ (U : LTree L) (h : Close δ T U) (hU : U.InRange) (t0 t1 s0 s1 : Out L → ℂ),
      SameQ Eq (simulateQ canonE (ffsB (aux := aux) δ T U h t0 t1 s0 s1))
        (simulateQ canonE (ffsT (aux := aux) U hU t0 t1)) := by
  induction T with
  | leaf σb hb =>
    intro U h hU t0 t1 s0 s1
    cases U with
    | leaf σ =>
    simp only [ffsB, ffsT, simulateQ_inr, simulateQ_pure]
    exact .query_bind _ _ _ fun z0 => .query_bind _ _ _ fun z1 => .pure _ _ rfl
  | @node L ℓh hℓh T0 T1 ih0 ih1 =>
    intro U h hU t0 t1 s0 s1
    cases U with
    | node ℓ U0 U1 =>
    simp only [ffsB, ffsT, simulateQ_bind, simulateQ_pure]
    refine (ih1 U1 h.2.2 hU.2 _ _ _ _).bind fun r1 s1 hr => ?_
    subst hr
    exact (ih0 U0 h.2.1 hU.1 _ _ _ _).bind fun r0 s0 hr0 => hr0 ▸ .pure _ _ rfl

theorem canon_signX (ρ : Arith64 εq) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    simulateQ canonE (sign164G (aux := aux) ρ (fun _ _ _ => True) k.1.toKey c) =
      simulateQ canonF (signB (aux := aux) δ k c) := by
  unfold sign164G signB
  split_ifs
  · rw [simulateQ_map, simulateQ_map]
    refine (sameQ_ffsG_ffsB ρ.toArith _ k.1.tree k.1.trueTree k.2.close _ _ _ _ _ _).map_eq _ _ ?_
    rintro _ s ⟨s', rfl, hz0, hz1, -, -⟩
    simp only [Option.map, hz0, hz1]
  · rfl

theorem canon_signT (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    simulateQ canonE (signB (aux := aux) δ k c) = simulateQ canonE (signT (aux := aux) δ k c) := by
  unfold signB signT
  split_ifs
  · rw [simulateQ_map, simulateQ_map]
    exact (sameQ_ffsB_ffsT k.1.tree k.1.trueTree k.2.close _ _ _ _ _).map_eq _ _ fun _ _ h => h ▸
        rfl
  · rfl

theorem canon_runX (ρ : Arith64 εq) {α : Type} (oe : OracleComp (specS aux δ) α) :
    simulateQ canonE (runX ρ oe) = simulateQ canonF (runB δ oe) := by
  unfold runX runB
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe,
    QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe]
  congr 1
  funext t
  rcases t with x | kc
  · exact (simulateQ_spec_query (impl := canonE) (Sum.inl x)).trans
      (simulateQ_spec_query (impl := canonF) (Sum.inl x)).symm
  · exact canon_signX ρ kc.1 kc.2

theorem canon_runT {α : Type} (oe : OracleComp (specS aux δ) α) :
    simulateQ canonE (runB δ oe) = simulateQ canonE (runT δ oe) := by
  unfold runB runT
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe,
    QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe]
  refine congrArg (fun impl => simulateQ impl oe) (funext fun t => ?_)
  rcases t with x | kc
  · exact (simulateQ_spec_query (impl := canonE) (Sum.inl x)).trans
      (simulateQ_spec_query (impl := canonE) (Sum.inl x)).symm
  · exact canon_signT kc.1 kc.2

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

omit [LawfulEvalDistSemantics m] in
theorem dist_canonE (implE implG : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hA : ∀ x, implG (.inl x) = implE (.inl x))
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hG : ∀ q : Falcon.CallP, @evalDist m _ ℤ ⊤
      (implG (.inr (Falcon.CallP.stored q.σ q.t q.t q.hσ))) = discreteGaussianMeasure q.σ q.t)
    (t : ιA ⊕ Falcon.CallP) :
    @evalDist m _ ((FalconGame.spec aux _).Range t) ⊤ (implE t) =
      @evalDist m _ ((FalconGame.spec aux _).Range t) ⊤ (simulateQ implG (canonE t)) := by
  rcases t with x | q
  · rw [show simulateQ implG (canonE (.inl x)) = implG (.inl x) from
      simulateQ_spec_query (impl := implG) (Sum.inl x), hA]
  · rw [show simulateQ implG (canonE (.inr q)) =
      implG (.inr (Falcon.CallP.stored q.σ q.t q.t q.hσ)) from
      simulateQ_spec_query (impl := implG) (Sum.inr _)]
    exact (hE q).trans (hG q).symm

/--
X two ways: `runX` under `implE` and `runB` under `implF` both sample `D_{σ̄, t̄}` with the stored
tree's exact centres (`ffsG`'s exact component is `ffsB`'s stored component), and agree on auxiliary
queries. -/
theorem relabel_X (ρ : Arith64 εq) (implA : QueryImpl aux m)
    (implE implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] (oe : OracleComp (specS aux δ) α) :
    𝒟[simulateQ implE (runX ρ oe)] = 𝒟[simulateQ implF (runB δ oe)] := by
  have h1 : 𝒟[simulateQ implE (runX ρ oe)] = 𝒟[simulateQ implF (simulateQ canonE (runX ρ oe))] := by
    rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := fun t => simulateQ implF (canonE t))
      (fun _ => rfl)]
    exact distEq_simulateQ _ _ (dist_canonE implE implF (fun x => (hAF x).trans (hAE x).symm) hE
      fun q => hF _) _
  have h2 : 𝒟[simulateQ implF (simulateQ canonF (runB δ oe))] = 𝒟[simulateQ implF (runB δ oe)] := by
    rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := fun t => simulateQ implF (canonF t))
      (fun _ => rfl)]
    refine (distEq_simulateQ _ _ (fun t => ?_) _).symm
    rcases t with x | q
    · rw [show simulateQ implF (canonF (.inl x)) = implF (.inl x) from
        simulateQ_spec_query (impl := implF) (Sum.inl x)]
    · by_cases hq : 12778 / 10000 ≤ q.σbar ∧ q.σbar ≤ 1825 / 1000
      · rw [show simulateQ implF (canonF (.inr q)) =
            implF (.inr (Falcon.CallP.stored q.σbar q.tbar q.tbar hq)) by
          rw [canonF_inr_of q hq]; exact simulateQ_spec_query (impl := implF) (Sum.inr _)]
        exact (hF q).trans (hF (Falcon.CallP.stored q.σbar q.tbar q.tbar hq)).symm
      · rw [show simulateQ implF (canonF (.inr q)) = implF (.inr q) by
          rw [canonF_inr_not q hq]; exact simulateQ_spec_query (impl := implF) (Sum.inr _)]
  rw [h1, canon_runX, h2]

/-- Y two ways: `runB` and `runT` under `implE` both sample `D_{σ, t}` with the true tree's centres.
-/
theorem relabel_Y (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    {α : Type} [MeasurableSpace α] (oe : OracleComp (specS aux δ) α) :
    𝒟[simulateQ implE (runB δ oe)] = 𝒟[simulateQ implE (runT δ oe)] := by
  have h := dist_canonE implE implE (fun _ => rfl) hE fun q => hE _
  rw [distEq_simulateQ implE _ h, distEq_simulateQ implE _ h,
    ← QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := fun t => simulateQ implE (canonE t))
        (fun _ => rfl),
    ← QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := fun t => simulateQ implE (canonE t))
        (fun _ => rfl),
    canon_runT]

/-- `runA` and `runX` form hop A's `Swap`: every signing query is on a key with a real stored tree.
Induction on `oe` (`AbortExact.Swap`); every auxiliary answer type is inhabited (a budget of `K`
calls then bounds the calls along every execution). -/
theorem swap_runA [hA : ∀ t, Nonempty (aux t)] (ρ : Arith64 εq) (K : ℕ) {α : Type}
    (oe : OracleComp (specS aux δ) α) (hq : PathSum (wK δ) oe K) :
    Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K (runA ρ oe) (runX ρ oe) := by
  have hne : ∀ t, Nonempty ((specS aux δ).Range t) := fun t => by
    rcases t with x | _
    · exact hA x
    · exact ⟨none⟩
  have hw : ∀ t, 0 ≤ wK (ιA := ιA) δ t := fun t => by rcases t with _ | _ <;> simp [wK]
  induction oe using OracleComp.inductionOn generalizing K with
  | pure x => exact Swap.pure K x
  | query_bind t k ih =>
    unfold runA runX
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query]
    rcases t with x | kc
    · exact Swap.query K x _ _ fun u => ih u K (by simpa [wK] using hq.inv_query u)
    · have h1 : (0 : ℝ) ≤ K - 1 := by simpa [wK] using (hq.inv_query none).nonneg hw
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by
        have : (1 : ℝ) ≤ K := by linarith
        have : 1 ≤ K := by exact_mod_cast this
        omega⟩
      exact Swap.sign K' kc.1.1.toKey kc.1.2.real kc.2 _ _ fun u =>
        ih u K' (by simpa [wK] using hq.inv_query u)

omit [Monad m] [LawfulMonad m] [LawfulEvalDistSemantics m] in
/-- `p_F` of the X side: a SamplerZ answer of `D_{σ̄, t̄}` with `σ̄ ≤ 1.825` and `|t̄ - t| ≤ 1/2`,
clamped around `t` at `y`, moves at most `p(y - 1/2)`. -/
theorem etvDist_map_clamp_shift (mx : m ℤ) {q : Falcon.CallP}
    (hmx : 𝒟[mx] = discreteGaussianMeasure q.σbar q.tbar) {y : ℝ} (hy : 1 ≤ y)
    (hq : (q.tbar - q.t) ^ 2 ≤ 1 / 4) (hσ : q.σbar ≤ 1825 / 1000) :
    𝒟[mx].etvDist (𝒟[mx].map (clamp y q.t)) ≤ ENNReal.ofReal (pclamp (y - 1 / 2)) := by
  rw [hmx]
  have h2 : |q.tbar - q.t| ≤ 1 / 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hsub : {z : ℤ | clamp y q.t z ≠ z} ⊆ {z : ℤ | y - 1 / 2 ≤ |(z : ℝ) - q.tbar|} :=
    fun z (hz : clamp y q.t z ≠ z) => by
      change y - 1 / 2 ≤ |(z : ℝ) - q.tbar|
      by_contra hc
      have hlt : |(z : ℝ) - q.t| < y :=
        calc |(z : ℝ) - q.t| = |((z : ℝ) - q.tbar) + (q.tbar - q.t)| := by congr 1; ring
          _ ≤ |(z : ℝ) - q.tbar| + |q.tbar - q.t| := abs_add_le _ _
          _ < y := by linarith [not_le.1 hc]
      exact hz (by simp only [clamp, hlt, ↓reduceIte])
  refine (etvDist_map_self_le _ _).trans ((measure_mono hsub).trans
    ((FalconPrecision.Errors.GaussTail.measure_abs_ge_falcon q.σbar q.tbar (y - 1 / 2) q.hσbar_ge
        (by linarith)).trans
      (ENNReal.ofReal_le_ofReal ?_)))
  have h0 : 0 < q.σbar := by linarith [q.hσbar_ge]
  unfold pclamp
  gcongr

omit [Monad m] [LawfulMonad m] in
theorem etvDist_map_le_one (mx : m ℤ) (f : ℤ → ℤ) : 𝒟[mx].etvDist (𝒟[mx].map f) ≤ 1 := by
  refine Measure.etvDist_le_one _ _ (evalDist_apply_univ_le_one _) ?_
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ]
  exact evalDist_apply_univ_le_one _

/-- World T's post-processing: SamplerZ answers clamped by `clamp y`. -/
noncomputable def fT (y : ℝ) : (t : ιA ⊕ Falcon.CallP) →
    (FalconGame.spec aux Falcon.CallP).Range t →
    (FalconGame.spec aux Falcon.CallP).Range t
  | .inl _ => id
  | .inr q => clamp y q.t

theorem clampQ_eq (y : ℝ) (t : ιA ⊕ Falcon.CallP) :
    clampQ (aux := aux) y t =
        fT y t <$> liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) t) := by
  rcases t with x | q
  · exact (id_map _).symm
  · rfl

/-- Clamping around the true centre costs `p(y - 1/2)` per SamplerZ call in X: along the clamped run
`|t̄ - t| ≤ 1/2` (from the budget), and `P_{D_{σ̄,t̄}}[|z - t| ≥ y] ≤ P[|z - t̄| ≥ y - 1/2]`
(`GaussTail`, `etvDist_simulateQ_rewrite_hist`). -/
theorem tv_clamp_F (y : ℝ) (hy : 1 ≤ y) (implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (K : ℕ) (hS : (K : ℝ) * s2B y δ ≤ 1 / 2 ^ 9) {α : Type} [MeasurableSpace α]
    (oe : OracleComp (specS aux δ) α) (hq : PathSum (wK δ) oe K) :
    (𝒟[simulateQ implF (runB δ oe)]).etvDist 𝒟[simulateQ implF (simulateQ (clampQ y) (runB δ oe))] ≤
      ENNReal.ofReal (pclamp (y - 1 / 2) * (K * 1024)) := by
  have hw : ∀ t, 0 ≤ (w1 : ιA ⊕ Falcon.CallP → ℝ) t := fun t => by rcases t with _ | _ <;> simp [w1]
  have hN := pathN_runB K oe hq
  have hid : ∀ x, @Measure.etvDist _ ⊤
      (@evalDist m _ ((FalconGame.spec aux Falcon.CallP).Range (.inl x)) ⊤ (implF (.inl x)))
      (@Measure.map _ _ ⊤ ⊤ (fT y (.inl x))
        (@evalDist m _ ((FalconGame.spec aux Falcon.CallP).Range (.inl x)) ⊤ (implF (.inl x)))) =
            0 := by
    intro x
    change @Measure.etvDist _ ⊤ _ (@Measure.map _ _ ⊤ ⊤ id _) = 0
    rw [@Measure.map_id _ ⊤]
    exact @Measure.etvDist_self _ ⊤ _
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine
      (etvDist_simulateQ_rewrite_hist implF (fT y) (clampQ_eq y) zero_le_one w1 hw (fun _ => True)
      (fun t _ => ?_) (runB δ oe) _ hN (Hist.true _)).trans (by simp)
    rcases t with x | q
    · rw [hid]; exact bot_le
    · exact (etvDist_map_le_one (implF (.inr q)) _).trans (by simp [w1])
  · have hs : s2B y δ ≤ 1 / 4 := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith [mul_le_mul_of_nonneg_right this (s2B_nonneg y δ)]
    refine etvDist_simulateQ_rewrite_hist implF (fT y) (clampQ_eq y)
        (pclamp_nonneg _) w1 hw (PQ (s2B y δ))
      (fun t ht => ?_) (runB δ oe) _ hN (hist_clamp y (by linarith) oe)
    rcases t with x | q
    · rw [hid]; exact bot_le
    · refine (etvDist_map_clamp_shift (implF (.inr q)) (hF q) hy (ht.1.trans hs) ht.2).trans
        (le_of_eq ?_)
      simp [w1]

/-- Theorem 2 at `λ = 131` (`FalconGame.theorem2`, as `Falcon.falcon512_proved_n64`): at most `2⁴⁹`
SamplerZ calls (`|1/σ̄² - 1/σ²| ≤ 2⁻⁴⁰` each, `Falcon.CallP.hτ`) and squared centre differences
`≤ 2⁻⁹` along every execution. -/
theorem renyi131 [∀ t, Countable (aux t)] (T : ℝ≥0∞) (hT : 1 ≤ T) (implA : QueryImpl aux m)
    (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (o : OracleComp (FalconGame.spec aux Falcon.CallP) α) (hN : PathSum w1 o (2 ^ 49))
    (hS : PathSum wS o (1 / 2 ^ 9)) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(129 : ℝ)) < 𝒟[simulateQ implF o] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE o] s := by
  have h :=
      FalconGame.theorem2 131 (2 ^ 51)
          (by norm_num) T hT Falcon.CallP.σ Falcon.CallP.σbar Falcon.CallP.t
    Falcon.CallP.tbar (3 / 10) (1277 / 1000) ((1 / 2 ^ 40) ^ 2 * 2 ^ 49)
        (1 / 2 ^ 9) implA implE implM implF
    hAE hAM hAF hE hM hF (fun q => by linarith [q.hσ.1]) (by norm_num)
    (fun q => by have := q.hleaf (2 * 131 - 1) (by norm_num) (by norm_num); push_cast; exact this)
    le_rfl (fun q => q.hσbar_ge) o
    (hN.mono (sq_nonneg _) fun x => by
      cases x with
      | inl _ => simp [w1]
      | inr q => simpa [w1] using sq_le_sq' (abs_le.1 q.hτ).1 (abs_le.1 q.hτ).2) hS
    (by
      refine le_trans ?_ (Falcon.five_quarters_le _ (by positivity))
      push_cast
      refine (Falcon.exp_le_one_add_two_mul _ (by positivity) (by norm_num)).trans ?_
      norm_num)
    (by
      refine le_trans ?_ (Falcon.five_quarters_le _ (by positivity))
      push_cast
      refine (Falcon.exp_le_inv_one_sub _ (by norm_num)).trans ?_
      norm_num)
    hs (by convert hwin using 4; norm_num)
  convert h using 4

/-- `pclamp 30·1024K ≤ 2⁻¹⁴¹` for `K ≤ 2³⁹` (arithmetic, as `AbortExact.eps_le`). -/
theorem eps141 (K : ℕ) (hK : K ≤ 2 ^ 39) :
    ENNReal.ofReal (pclamp 30 * (K * 1024)) ≤ (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  have hp : pclamp 30 ≤ 2 * (1 + 1 / 2 ^ 36) * (1 / 2 ^ 194) := by
    unfold pclamp
    exact mul_le_mul_of_nonneg_left exp_thirty (by norm_num)
  have hx : pclamp 30 * (K * 1024) ≤ 1 / 2 ^ 141 := by
    have := mul_le_mul hp (mul_le_mul_of_nonneg_right hK' (by norm_num : (0 : ℝ) ≤ 1024))
      (by positivity) (by norm_num)
    linarith
  rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos (by norm_num)]
  refine ENNReal.ofReal_le_ofReal (hx.trans_eq ?_)
  rw [Real.rpow_neg (by norm_num), show (141 : ℝ) = ((141 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

theorem two_rpow_split (n : ℝ) : (2 : ℝ≥0∞) ^ (-n) = 2 ^ (-(n + 1)) + 2 ^ (-(n + 1)) := by
  rw [← two_mul, show -n = 1 + -(n + 1) by ring,
      ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.rpow_one]

/-- `T·2⁻¹²⁹ + 2⁻¹⁴¹ + 2⁻¹⁴⁰ ≤ T·2⁻¹²⁸` for `T ≥ 1` (arithmetic). -/
theorem thresh (T : ℝ≥0∞) (hT : 1 ≤ T) :
    T * (2 : ℝ≥0∞) ^ (-(129 : ℝ)) + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) ≤
      T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) := by
  have h1 : (2 : ℝ≥0∞) ^ (-(141 : ℝ)) ≤ 2 ^ (-(130 : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ (-(140 : ℝ)) ≤ 2 ^ (-(130 : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have e1 := two_rpow_split 129
  have e0 := two_rpow_split 128
  norm_num at e1 e0
  rw [e0, mul_add, add_assoc]
  refine add_le_add le_rfl ?_
  calc (2 : ℝ≥0∞) ^ (-(141 : ℝ)) + 2 ^ (-(140 : ℝ)) ≤ 2 ^ (-(130 : ℝ)) + 2 ^ (-(130 : ℝ)) :=
      add_le_add h1 h2
    _ = 2 ^ (-(129 : ℝ)) := e1.symm
    _ ≤ T * 2 ^ (-(129 : ℝ)) := le_mul_of_one_le_left' hT

theorem gainA_le : ∀ L, L ≤ 8 → gainA L ≤ (11402 / 10000) ^ L
  | 0, _ => le_of_eq (pow_zero _).symm
  | L + 1, hL => by
    have ih := gainA_le L (by omega)
    have hl : lam512 L = 9923 / 10000 := by simp [lam512]; omega
    have hr : √(lam512 L ^ 2 + 4) ≤ 223264 / 100000 := by
      rw [Real.sqrt_le_left (by norm_num), hl]; norm_num
    have ht : 1414213 / 1000000 ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [gainA, pow_succ, div_le_iff₀ (by positivity)]
    calc gainA L * (lam512 L + √(lam512 L ^ 2 + 4))
        ≤ (11402 / 10000) ^ L * (9923 / 10000 + 223264 / 100000) :=
          mul_le_mul ih (by linarith) (by positivity) (by positivity)
      _ ≤ (11402 / 10000) ^ L * (11402 / 10000) * (2 * (1414213 / 1000000)) := by
          rw [mul_assoc]; gcongr; norm_num
      _ ≤ (11402 / 10000) ^ L * (11402 / 10000) * (2 * √2) := by gcongr

theorem devB_le {δ : ℕ → ℝ} (hδ : ∀ j < 8, 0 ≤ δ j ∧ δ j ≤ 1 / 2 ^ 40) :
    ∀ L, L ≤ 8 → devB (61 / 2) δ L ≤ 431336 / 10000 * (315255 / 100000) ^ L
  | 0, _ => by
    rw [devB, pow_zero, mul_one]
    have : √2 ≤ 1414214 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  | L + 1, hL => by
    have ih := devB_le hδ L (by omega)
    have hl : lam512 L = 9923 / 10000 := by simp [lam512]; omega
    obtain ⟨h0, h1⟩ := hδ L (by omega)
    have hr : √(2 * ((1 + lam512 L + δ L) ^ 2 + 1)) ≤ 315255 / 100000 := by
      rw [Real.sqrt_le_left (by norm_num), hl]
      have : (1 + 9923 / 10000 + δ L) ^ 2 ≤ (1 + 9923 / 10000 + 1 / 2 ^ 40) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      linarith
    rw [devB, pow_succ]
    calc √(2 * ((1 + lam512 L + δ L) ^ 2 + 1)) * devB (61 / 2) δ L
        ≤ 315255 / 100000 * (431336 / 10000 * (315255 / 100000) ^ L) :=
          mul_le_mul hr ih (devB_nonneg (by norm_num) δ L) (by norm_num)
      _ = _ := by ring

/-- `s2B` at `y = 30.5` for a tree error `δ ≤ 2⁻⁴⁰` below the root: the sum bounded term by term. -/
theorem s2B_le {δ : ℕ → ℝ} (hδ : ∀ j < 8, 0 ≤ δ j ∧ δ j ≤ 1 / 2 ^ 40) (h8 : 0 ≤ δ 8) :
    s2B (61 / 2) δ ≤ (∑ L ∈ Finset.range 9, (11402 / 10000) ^ L * δ L * sq512 (8 - L) *
      (431336 / 10000 * (315255 / 100000) ^ L)) ^ 2 := by
  have hδ0 : ∀ L ∈ Finset.range 9, 0 ≤ δ L := fun L hL => by
    rcases Nat.lt_or_ge L 8 with h | h
    · exact (hδ L h).1
    · rw [show L = 8 by simp at hL; omega]; exact h8
  refine pow_le_pow_left₀ (Finset.sum_nonneg fun L hL => mul_nonneg (mul_nonneg (mul_nonneg
    (gainA_nonneg L) (hδ0 L hL)) (Real.sqrt_nonneg _)) (devB_nonneg (by norm_num) δ L))
    (Finset.sum_le_sum fun L hL => ?_) 2
  have hL8 : L ≤ 8 := by simp at hL; omega
  exact mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_right (gainA_le L hL8) (hδ0 L hL)) (sqrt_pow_le _)
    (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (hδ0 L hL))) (devB_le hδ L hL8)
    (devB_nonneg (by norm_num) δ L) (mul_nonneg (mul_nonneg (by positivity) (hδ0 L hL))
      ((Real.sqrt_nonneg _).trans (sqrt_pow_le _)))

/-- The `p = 127` tree supports `2³⁹` signing-oracle calls at `y = 30.5` (value
`2^39 · s2B 30.5 δ127 ≈ 2⁻³⁶·⁵`). -/
theorem s2B_falcon : (2 : ℝ) ^ 39 * s2B (61 / 2) δ127 ≤ 1 / 2 ^ 9 := by
  have h := s2B_le (δ := δ127) (fun j hj => by
    simp only [δ127, show j ≠ 8 by omega, ↓reduceIte]; norm_num) (by norm_num [δ127])
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, δ127, sq512]
  norm_num

/-- The `p = 63` tree supports `2³⁰` signing-oracle calls at `y = 30.5` (value
`2^30 · s2B 30.5 δ63 ≈ 2⁻⁹·⁴⁹`). -/
theorem s2B_falcon63 : (2 : ℝ) ^ 30 * s2B (61 / 2) δ63 ≤ 1 / 2 ^ 9 := by
  have h := s2B_le (δ := δ63) (fun j hj => by
    simp only [δ63, show j ≠ 8 by omega, ↓reduceIte]; norm_num) (by norm_num [δ63])
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, δ63, sq512]
  norm_num

/-! ## Hop B and the composition with hop A -/

theorem pclamp_anti {y y' : ℝ} (h0 : 0 ≤ y) (h : y ≤ y') : pclamp y' ≤ pclamp y := by
  unfold pclamp
  gcongr

theorem rpow_ne_top (x : ℝ) : (2 : ℝ≥0∞) ^ x ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg' (by norm_num) (by norm_num)

/--
**Hop B at Falcon-512**: exact signing on the stored tree (X) against exact Falcon on the true tree
(Y). For every experiment `oe` with at most `K ≤ 2³⁹` signing-oracle calls (one ffSampling call
each, restarts included) along every execution, on keys passing `KeyB.Good δ` (stored tree real and
`Close δ` to the true tree; hypotheses) with `K·s2B 30.5 δ ≤ 2⁻⁹`: success `> T·2⁻¹²⁹ + 2⁻¹⁴¹` in X
gives success `> T·2⁻¹³¹ - 2⁻¹⁴¹` in Y. SamplerZ is perfect in every world (`hE`, `hM`, `hF`).
Proof: clamp every SamplerZ answer to within `30.5` of its true centre, at cost `≤ 2⁻¹⁴¹` in X
(`tv_clamp_F`) and in Y (`etvDist_implT_le`, `eps141`); Theorem 2 at `λ = 131` on the clamped run
(`renyi131`, budgets `pathN_runB`, `pathS_clamp`). Not proved: `Close δ` from a model of key
expansion, NTRUSolve, the true leaves' range (§4.1, from `αGPV ≤ 1.17`). -/
theorem falcon512_hopB [∀ t, Countable (aux t)] (K : ℕ) (hK : K ≤ 2 ^ 39)
    (hδ : (K : ℝ) * s2B (61 / 2) δ ≤ 1 / 2 ^ 9) (T : ℝ≥0∞) (hT : 1 ≤ T) (implA : QueryImpl aux m)
    (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specS aux δ) α) (hq : PathSum (wK δ) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(129 : ℝ)) + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) <
        𝒟[simulateQ implF (runB δ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ oe)] s + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
        by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  have hw0 : ∀ t, 0 ≤ (w1 : ιA ⊕ Falcon.CallP → ℝ) t :=
      fun t => by rcases t with _ | _ <;> simp [w1]
  have hw1 : ∀ q, 1 ≤ (w1 : ιA ⊕ Falcon.CallP → ℝ) (.inr q) := fun q => by simp [w1]
  have hε : ENNReal.ofReal (pclamp 30 * (K * 1024)) ≤ (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := eps141 K hK
  have hX : 𝒟[simulateQ implF (runB δ oe)] s ≤
      𝒟[simulateQ implF (simulateQ (clampQ (61 / 2)) (runB δ oe))] s + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
          by
    refine (le_add_etvDist _ _ hs).trans (add_le_add le_rfl ?_)
    refine (tv_clamp_F (61 / 2) (by norm_num) implF hF K hδ oe hq).trans (le_trans ?_ hε)
    norm_num
  have hwc : T * (2 : ℝ≥0∞) ^ (-(129 : ℝ)) <
      𝒟[simulateQ implF (simulateQ (clampQ (61 / 2)) (runB δ oe))] s :=
    (ENNReal.add_lt_add_iff_right (rpow_ne_top _)).1 (hwin.trans_le hX)
  have hN : PathSum w1 (simulateQ (clampQ (61 / 2)) (runB δ oe)) (2 ^ 49) := by
    refine (PathSum.simulateQ_map (fT (61 / 2)) (clampQ_eq _) (pathN_runB K oe hq)).weaken ?_
    linarith [hK']
  have hS : PathSum wS (simulateQ (clampQ (61 / 2)) (runB δ oe)) (1 / 2 ^ 9) :=
    (pathS_clamp (61 / 2) (by norm_num) K oe hq).weaken hδ
  have hY := renyi131 T hT implA implE implM implF hAE hAM hAF hE hM hF _ hN hS hs hwc
  have hYc : 𝒟[simulateQ implE (simulateQ (clampQ (61 / 2)) (runB δ oe))] s ≤
      𝒟[simulateQ implE (runB δ oe)] s + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
    refine (le_add_etvDist _ _ hs).trans (add_le_add le_rfl ?_)
    rw [Measure.etvDist_comm, simulateQ_clampQ]
    refine (etvDist_implT_le (61 / 2) (by norm_num) implE hE w1 hw0 hw1 (pathN_runB K oe hq)).trans
      (le_trans (ENNReal.ofReal_le_ofReal ?_) hε)
    exact mul_le_mul_of_nonneg_right (pclamp_anti (by norm_num) (by norm_num)) (by positivity)
  rw [← relabel_Y implE hE oe]
  exact hY.trans_le hYc

/-- **Fixed-point signing against exact Falcon at Falcon-512** (hop A then hop B). For every Type 1
arithmetic `ρ` with `1/q` within `2⁻⁷⁸` and every experiment `oe` with at most `K ≤ 2³⁹`
signing-oracle calls (one ffSampling call each, restarts included) along every execution, on keys
passing `KeyB.Good δ` with `K·s2B 30.5 δ ≤ 2⁻⁹`: success `> T·2⁻¹²⁶ + 2⁻¹⁴⁰` with check-free Type 1
signing on the stored tree (F′, `runX` under `implF`) gives success `> T·2⁻¹³¹ - 2⁻¹⁴¹` with exact
Falcon signing on the true tree (Y, `runT` under `implE`). Hypotheses of hop A: those of
`Falcon.falcon512_exact64n'` (every auxiliary answer type inhabited, `K ≤ 2³⁹`). Hypotheses and what
is not proved: those of `falcon512_hopB` and of `Falcon.falcon512_exact64n'`. -/
theorem falcon512_fixed_vs_true [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78))
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) δ ≤ 1 / 2 ^ 9) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS aux δ) α) (hq : PathSum (wK δ) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ oe)] s + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
        by
  have hA := Falcon.falcon512_exact64n' ρ K hK T hT implA implE implM implF hAE hAM hAF hE hM hF
    (runA ρ oe) (runX ρ oe) (swap_runA ρ K oe hq) hs hwin
  rw [relabel_X ρ implA implE implF hAE hAF hE hF oe] at hA
  refine falcon512_hopB K hK hδ T hT implA implE implM implF hAE hAM hAF hE hM hF oe hq hs ?_
  exact (ENNReal.add_lt_add_iff_right (rpow_ne_top _)).1 ((thresh T hT).trans_lt hA)

/--
**Instance**: the `p = 127` tree (`δ127`), `K ≤ 2³⁹` (`s2B_falcon`). `Close δ127` is a hypothesis on
each key (`KeyB.Good`); no model of key expansion at `p = 127` is formalised. Other hypotheses, and
what is not proved: those of `falcon512_fixed_vs_true`. -/
theorem falcon512_fixed_vs_true127 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS aux δ127) α) (hq : PathSum (wK δ127) oe K) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ127 oe)] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  have h0 : 0 ≤ s2B (61 / 2) δ127 := s2B_nonneg _ _
  refine falcon512_fixed_vs_true ρ K hK ?_ T hT implA implE implM implF hAE hAM hAF hE hM hF oe hq
      hs hwin
  exact (mul_le_mul_of_nonneg_right hK' h0).trans s2B_falcon

/-- **Instance**: the `p = 63` tree (`δ63`: `‖ℓ̂ - ℓ‖∞ ≤ 0.8123·2⁻⁴⁰` at the root, `≤ 0.7072·2⁻⁴¹`
below), `K ≤ 2³⁰` (`s2B_falcon63`; `2³⁰·s2B 30.5 δ63 ≈ 2⁻⁹·⁴⁹`). `Close δ63` is a hypothesis on each
key (`KeyB.Good`). For this tree, existing lemmas cover parts of it, none composed here: the leaf
condition `|σ̄/σ - 1| ≤ 2⁻⁴²` has the form of `LDL.falcon512_leaf` (its `V` is not tied to
`KeyB.trueTree` in Lean), conditional on its `hroot` (root values in `[q/16, 16q]`, Lemma 8 (15)
with `αhybrid ≤ γhybrid = 4`, with relative error `≤ 2⁻⁴⁵`; the pieces `LDL.fft512_err`,
`LDL.root512`, `LDL.root11_512` are not composed into it), `hstep` (inner steps within `2⁻³⁵`;
`LDL.step512` at assumed per-operation budgets) and `hs` (the normalisation `σ/√D̂`). Not covered by
any lemma: the factor bounds `‖ℓ̂ - ℓ‖∞ ≤ δ63 L` (the diagonal relative errors of `LDL.tree_rel` do
not yield them in Lean; the constants are numerical estimates), the range `[1.2778, 1.825]` of the
true leaves (§4.1, from `αGPV ≤ 1.17`), and the stored tree's `‖ℓ̂‖∞ ≤ lam512 L` (`FTree`) and
realness (`FTree.Real`). Other hypotheses, and what is not proved: those of
`falcon512_fixed_vs_true`. -/
theorem falcon512_fixed_vs_true63 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 30) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS aux δ63) α) (hq : PathSum (wK δ63) oe K) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ63 oe)] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hK
  have h0 : 0 ≤ s2B (61 / 2) δ63 := s2B_nonneg _ _
  refine falcon512_fixed_vs_true ρ K
      (hK.trans (by norm_num)) ?_ T hT implA implE implM implF hAE hAM hAF hE hM
    hF oe hq hs hwin
  exact (mul_le_mul_of_nonneg_right hK' h0).trans s2B_falcon63

end FalconPrecision.Errors.HopB
