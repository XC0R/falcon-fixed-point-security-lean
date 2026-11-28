/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignRefine
public import FalconPrecision.Exec.KeyCheck1024

/-! # The executable signer refines S8's model at Falcon-1024

At every size `2^(L+1)` with the check thresholds of a `CheckParams` `S`, and the tables cut at
the depth (`AdmN (L + 1) C`, `arithXN (L + 1) C h`): `signX_refinesP` (`sign164G` on the key
`toKeyBP` of a raw key passing `check` at `S` is `signX` on the stored tree `storeC … S.σq`),
`execImplP`, `world_eqP` (`runKP (sign164G …)` on embedded experiments is the executable world).
Falcon-1024 (`params1024`, `L = 9`, cutoff `N = 10`): `signX_refines1024`, `execImpl1024`,
`world_eq1024`, and `falcon1024_exec_vs_true`, `falcon1024_exec_vs_true256` with their instances
at `δ43q_1024` and `δ127q_1024`: the `falcon1024_*_checked` statements of `Exec.KeyCheck1024`
with the fixed-point world replaced by the executable signer's world (`execImpl1024`), for
choices with `AdmN 10 C`, no range checks (`C.rchk = none`) and `1/q` at 77 bits.

Not proved here: a Lean term `AdmN 10 C` for a concrete `C` (its condition `twOkN C.x.rc 10`
holds only by `#eval` of `twOkFastN`, which is evidence, not a kernel proof); that a key passes
`check1024` (not proved for any key); hop B for range checks; that the whole signer `signMsgX` is
the hop-B experiment, and a query count of its restart loop at Falcon-1024 (`pathSum_signLoopX`
is at Falcon-512); words (stated for `C.word = none`; the ranges and words of `signX` are
`Exec.SignRange1024`, composed with the sampler in `Exec.SignWordHop1024`); multiply-first, the
split path, half-spectrum storage; the sampler (`hE`, `hM`, `hF`; the executable SamplerZ is
composed with these theorems in `Exec.SamplerHop1024`, `falcon1024_exec_sampler_vs_true(256)`). -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- **Refinement at every size**: in every world `impl` whose SamplerZ answer on `(σ̄, t̄)` is
`samp σ̄ t̄`, S8's `sign164G` with `arithXN (L + 1) C h` and the checks `chkOf C.rchk`, on the key
of a raw key of size `2^(L+1)` passing `check` at the thresholds of `S`, is the executable attempt
`signX` on the stored tree `storeC … S.σq`. -/
theorem signX_refinesP (C : Choices) (S : CheckParams) {L : ℕ} (h : AdmN (L + 1) C)
    (δq : ℕ → ℚ) (k : RawKey (L + 1)) (hk : check C.x C.xn δq k S.fB S.FB S.σlo S.Λq S.σq = true)
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t) (c : ZPoly (L + 1)) :
    simulateQ impl (sign164G (aux := aux) (arithXN (L + 1) C h) (chkOf C.rchk)
        (toKeyBP C.x C.xn S δq k hk).toKey c) = signX C samp (storeC C.x C.xn k S.σq) k c := by
  have hT : (storeC C.x C.xn k S.σq).Ok S.σlo S.Λq :=
    storeB_centreP C.x C.xn k S.σq ▸ CTree.ok_of_okB _ (check_ok C.x C.xn hk).ok
  unfold sign164G signX
  by_cases hc : ∀ i, |c i| < 12289
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc),
      simulateQ_map, (targetX_toCN (L + 1) C h le_rfl _ c).1,
      (targetX_toCN (L + 1) C h le_rfl _ c).2]
    exact ffsX_refinesN (L + 1) C h impl samp himpl S.hσl S.hΛ le_rfl (storeC C.x C.xn k S.σq) hT
      _ _ _ _
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc),
      simulateQ_pure]

/-- The executable signer's world at every size: auxiliary queries by `implA`, a signing query
`(k, c)` by `signX` on `storeC k S.σq`. -/
def execImplP (C : Choices) (S : CheckParams) (δq : ℕ → ℚ) (L : ℕ) {m : Type → Type*} [Monad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) :
    QueryImpl (specKP C.x C.xn aux S δq L) m
  | .inl x => implA x
  | .inr kc => signX C samp (storeC C.x C.xn kc.1.1 S.σq) kc.1.1 kc.2

theorem world_eqP (C : Choices) (S : CheckParams) {L : ℕ} (h : AdmN (L + 1) C) (δq : ℕ → ℚ)
    {m : Type → Type*} [Monad m] [LawfulMonad m] (hR : C.rchk = none) (implA : QueryImpl aux m)
    (implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (hAF : ∀ x, implF (.inl x) = implA x)
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} (oe : OracleComp (specKP C.x C.xn aux S δq L) α) :
    simulateQ implF (runKP (sign164G (arithXN (L + 1) C h) fun _ _ _ => True)
        (embedP C.x C.xn S δq L oe)) =
      simulateQ (execImplP C S δq L implA samp) oe := by
  unfold runKP embedP
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe,
    QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe]
  refine congrArg (fun impl => simulateQ impl oe) (funext fun t => ?_)
  rcases t with x | kc
  · exact ((congrArg (simulateQ implF) (simulateQ_spec_query (impl := signImplP
      (σ := S.σ) (δ := fun j => (δq j : ℝ))
      fun k c => sign164G (arithXN (L + 1) C h) (fun _ _ _ => True) k.1.toKey c)
      (Sum.inl x))).trans (simulateQ_spec_query (impl := implF) (Sum.inl x))).trans (hAF x)
  · refine (congrArg (simulateQ implF) (simulateQ_spec_query (impl := signImplP
      (σ := S.σ) (δ := fun j => (δq j : ℝ))
      fun k c => sign164G (arithXN (L + 1) C h) (fun _ _ _ => True) k.1.toKey c)
      (Sum.inr (kc.1.toGood, kc.2)))).trans ?_
    have e := signX_refinesP C S h δq kc.1.1 kc.1.2 implF samp hsamp kc.2
    rw [show chkOf C.rchk = fun _ _ _ => True by rw [hR]; rfl] at e
    exact e

/-! ## Falcon-1024 -/

/-- **Refinement at Falcon-1024** (tables cut at `N = 10`): in every world `impl` whose SamplerZ
answer on `(σ̄, t̄)` is `samp σ̄ t̄`, S8's `sign164G` with `arithXN 10 C h` and the checks
`chkOf C.rchk`, on the key `toKeyB1024` of a raw key passing `check1024`, is the executable
attempt `signX` on the stored tree `storeC … σ1024q`. -/
theorem signX_refines1024 (C : Choices) (h : AdmN 10 C) (δq : ℕ → ℚ) (k : RawKey 10)
    (hk : check1024 C.x C.xn δq k = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t) (c : ZPoly 10) :
    simulateQ impl (sign164G (aux := aux) (arithXN 10 C h) (chkOf C.rchk)
        (toKeyB1024 C.x C.xn δq k hk).toKey c) = signX C samp (storeC C.x C.xn k σ1024q) k c :=
  signX_refinesP C params1024 h δq k hk impl samp himpl c

/-- The executable signer's world at Falcon-1024: auxiliary queries by `implA`, a signing query
`(k, c)` by `signX` on `storeC k σ1024q`. -/
def execImpl1024 (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    (implA : QueryImpl aux m) (samp : Fx 64 → Fx 64 → m ℤ) :
    QueryImpl (specK1024 C.x C.xn aux δq) m
  | .inl x => implA x
  | .inr kc => signX C samp (storeC C.x C.xn kc.1.1 σ1024q) kc.1.1 kc.2

theorem world_eq1024 (C : Choices) (h : AdmN 10 C) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    [LawfulMonad m] (hR : C.rchk = none) (implA : QueryImpl aux m)
    (implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (hAF : ∀ x, implF (.inl x) = implA x)
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} (oe : OracleComp (specK1024 C.x C.xn aux δq) α) :
    simulateQ implF (runX1024 (arithXN 10 C h) (embed1024 C.x C.xn δq oe)) =
      simulateQ (execImpl1024 C δq implA samp) oe := by
  have e : execImpl1024 C δq implA samp = execImplP C params1024 δq 9 implA samp := by
    funext t; rcases t with x | kc <;> rfl
  rw [e]
  exact world_eqP C params1024 h δq hR implA implF hAF samp hsamp oe

section HopB

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- **The executable signer against exact Falcon at Falcon-1024 on checked keys**: for choices
with `AdmN 10 C` (tables cut at `N = 10`), no range checks (`C.rchk = none`, the check of
`runX1024`) and `1/q` at 77 bits, every experiment `oe` on raw keys passing `check1024` with at
most `K ≤ 2²⁹` signing queries along every execution, `K·s2B1024 41.5 δ ≤ 2⁻⁹`, a sampler `samp`
that is `D_{σ̄,t̄}` (`hF` on a world `implF` agreeing with it on grid values): success
`> T·2⁻¹²⁶ + 2⁻²⁸⁰` with the executable signer (`execImpl1024`) gives success
`> T·2⁻¹³¹ - 2⁻²⁸¹` with exact signing on the true tree. `AdmN 10 C` is a hypothesis (its table
condition `twOkN C.x.rc 10` holds only by `#eval`, not a kernel proof). Other hypotheses and what
is not proved: those of `falcon1024_fixed_vs_true_checked`. -/
theorem falcon1024_exec_vs_true [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK1024 C.x C.xn aux δq) α) (hq : PathSum (wKC1024 C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ (execImpl1024 C δq implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  obtain rfl : qi = QInv.w77 := hq77
  refine falcon1024_fixed_vs_true_checked x xn δq (arithXN 10 _ hC) K hK hδ T hT implA implE
    implM implF hAE hAM hAF hE hM hF oe hq hs ?_
  have e : simulateQ implF (runX1024 (εq := 1 / 2 ^ 78) (arithXN 10 _ hC)
      (embed1024 x xn δq oe)) = simulateQ (execImpl1024 _ δq implA samp) oe :=
    world_eq1024 _ hC δq hR implA implF hAF samp hsamp oe
  rw [e]
  exact hwin

/-- **Instance** of `falcon1024_exec_vs_true` at the uniform tree error `2⁻⁴³` (`δ43q_1024`),
`K ≤ 2²⁹`, by `falcon1024_fixed_vs_true43_checked`. That a key passes
`check1024 C.x C.xn δ43q_1024` is a hypothesis on every signing key (`specK1024`), not proved for
any key; `AdmN 10 C` is a hypothesis (`#eval` evidence only). Other hypotheses, and what is not
proved: those of `falcon1024_exec_vs_true`. -/
theorem falcon1024_exec_vs_true43 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK1024 C.x C.xn aux δ43q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ43q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ (execImpl1024 C δ43q_1024 implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ43q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  obtain rfl : qi = QInv.w77 := hq77
  refine falcon1024_fixed_vs_true43_checked x xn (arithXN 10 _ hC) K hK T hT implA implE implM
    implF hAE hAM hAF hE hM hF oe hq hs ?_
  have e : simulateQ implF (runX1024 (εq := 1 / 2 ^ 78) (arithXN 10 _ hC)
      (embed1024 x xn δ43q_1024 oe)) = simulateQ (execImpl1024 _ δ43q_1024 implA samp) oe :=
    world_eq1024 _ hC δ43q_1024 hR implA implF hAF samp hsamp oe
  rw [e]
  exact hwin

/-- **Instance** of `falcon1024_exec_vs_true` at the tree error `δ127q_1024` (`2⁻⁵⁸` at the root,
`2⁻⁶³` below), `K ≤ 2²⁹`, by `falcon1024_fixed_vs_true127_checked`. That a key passes
`check1024 C.x C.xn δ127q_1024` is a hypothesis on every signing key (`specK1024`), not proved for
any key; `AdmN 10 C` is a hypothesis (`#eval` evidence only). Other hypotheses, and what is not
proved: those of `falcon1024_exec_vs_true`. -/
theorem falcon1024_exec_vs_true127 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK1024 C.x C.xn aux δ127q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ (execImpl1024 C δ127q_1024 implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ127q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  obtain rfl : qi = QInv.w77 := hq77
  refine falcon1024_fixed_vs_true127_checked x xn (arithXN 10 _ hC) K hK T hT implA implE implM
    implF hAE hAM hAF hE hM hF oe hq hs ?_
  have e : simulateQ implF (runX1024 (εq := 1 / 2 ^ 78) (arithXN 10 _ hC)
      (embed1024 x xn δ127q_1024 oe)) = simulateQ (execImpl1024 _ δ127q_1024 implA samp) oe :=
    world_eq1024 _ hC δ127q_1024 hR implA implF hAF samp hsamp oe
  rw [e]
  exact hwin

/-- **The executable signer against exact Falcon at Falcon-1024 on checked keys, `λ = 256`
level**: `falcon1024_fixed_vs_true256_checked` with the fixed-point world replaced by the
executable signer's world (`execImpl1024`), for choices with `AdmN 10 C`, `C.rchk = none` and
`1/q` at 77 bits; `K ≤ 2²⁹`, `K·s2B1024 41.5 δ ≤ 2⁻¹⁰`: success `> T·2⁻²⁵⁴ + 2⁻²⁸⁰` with the
executable signer gives success `> T·2⁻²⁵⁹ - 2⁻²⁸¹` with exact signing on the true tree.
`AdmN 10 C` is a hypothesis (`#eval` evidence only). Other hypotheses and what is not proved:
those of `falcon1024_fixed_vs_true256_checked`. -/
theorem falcon1024_exec_vs_true256 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK1024 C.x C.xn aux δq) α) (hq : PathSum (wKC1024 C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ (execImpl1024 C δq implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) < 𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  obtain rfl : qi = QInv.w77 := hq77
  refine falcon1024_fixed_vs_true256_checked x xn δq (arithXN 10 _ hC) K hK hδ T hT implA implE
    implM implF hAE hAM hAF hE hM hF oe hq hs ?_
  have e : simulateQ implF (runX1024 (εq := 1 / 2 ^ 78) (arithXN 10 _ hC)
      (embed1024 x xn δq oe)) = simulateQ (execImpl1024 _ δq implA samp) oe :=
    world_eq1024 _ hC δq hR implA implF hAF samp hsamp oe
  rw [e]
  exact hwin

/-- **Instance** of `falcon1024_exec_vs_true256` at the uniform tree error `2⁻⁴³` (`δ43q_1024`),
`K ≤ 2²⁹`, by `falcon1024_fixed_vs_true256_43_checked`. That a key passes
`check1024 C.x C.xn δ43q_1024` is a hypothesis on every signing key (`specK1024`), not proved for
any key; `AdmN 10 C` is a hypothesis (`#eval` evidence only). Other hypotheses, and what is not
proved: those of `falcon1024_exec_vs_true256`. -/
theorem falcon1024_exec_vs_true256_43 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK1024 C.x C.xn aux δ43q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ43q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ (execImpl1024 C δ43q_1024 implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ43q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  obtain rfl : qi = QInv.w77 := hq77
  refine falcon1024_fixed_vs_true256_43_checked x xn (arithXN 10 _ hC) K hK T hT implA implE
    implM implF hAE hAM hAF hE hM hF oe hq hs ?_
  have e : simulateQ implF (runX1024 (εq := 1 / 2 ^ 78) (arithXN 10 _ hC)
      (embed1024 x xn δ43q_1024 oe)) = simulateQ (execImpl1024 _ δ43q_1024 implA samp) oe :=
    world_eq1024 _ hC δ43q_1024 hR implA implF hAF samp hsamp oe
  rw [e]
  exact hwin

/-- **Instance** of `falcon1024_exec_vs_true256` at the tree error `δ127q_1024` (`2⁻⁵⁸` at the
root, `2⁻⁶³` below), `K ≤ 2²⁹`, by `falcon1024_fixed_vs_true256_127_checked`. That a key passes
`check1024 C.x C.xn δ127q_1024` is a hypothesis on every signing key (`specK1024`), not proved for
any key; `AdmN 10 C` is a hypothesis (`#eval` evidence only). Other hypotheses, and what is not
proved: those of `falcon1024_exec_vs_true256`. -/
theorem falcon1024_exec_vs_true256_127 [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
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
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK1024 C.x C.xn aux δ127q_1024) α)
    (hq : PathSum (wKC1024 C.x C.xn δ127q_1024) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(254 : ℝ)) + (2 : ℝ≥0∞) ^ (-(280 : ℝ)) <
        𝒟[simulateQ (execImpl1024 C δ127q_1024 implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(259 : ℝ)) <
        𝒟[simulateQ implE (runT1024 _ (embed1024 C.x C.xn δ127q_1024 oe))] s +
        (2 : ℝ≥0∞) ^ (-(281 : ℝ)) := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  obtain rfl : qi = QInv.w77 := hq77
  refine falcon1024_fixed_vs_true256_127_checked x xn (arithXN 10 _ hC) K hK T hT implA implE
    implM implF hAE hAM hAF hE hM hF oe hq hs ?_
  have e : simulateQ implF (runX1024 (εq := 1 / 2 ^ 78) (arithXN 10 _ hC)
      (embed1024 x xn δ127q_1024 oe)) = simulateQ (execImpl1024 _ δ127q_1024 implA samp) oe :=
    world_eq1024 _ hC δ127q_1024 hR implA implF hAF samp hsamp oe
  rw [e]
  exact hwin

end HopB

end FalconPrecision.Exec
