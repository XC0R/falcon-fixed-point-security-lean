/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.AbortExact

/-! # Hop B, core: the true tree, ffSampling on both trees, centre differences of a clamped run

`KeyB.trueTree` is exact ffLDL⋆ (ePrint 2026/1531 Alg. 5) of `B·B⋆`; it is real (`isReal_trueTree`).
`Close δ` relates the stored tree (`FTree`, hop A) to it. `ffsB` runs ffSampling (Alg. 8) on both
trees with the same samples; the experiments `runA`, `runX`, `runB`, `runT` (signers `sign164`,
`sign164G`, `signB`, `signT`) are the four worlds of `HopB`. `Hist` and `SameQ` describe the queries
along every execution; `etvDist_simulateQ_rewrite_hist` is `RenyiPath.etvDist_simulateQ_rewrite`
with the per-query bound needed only on the queries of the post-processed run satisfying `P`, the
budget on the original run, and no answer type required to be inhabited. `ffsB_clamp`: along every
history of a call with SamplerZ answers clamped to within `y` of the true centre, the squared centre
differences sum to `≤ (gainA L·X + cB y δ L)²` for input difference `X`. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Errors.HopB

/-! ## The true tree -/

/-- A Falcon tree without range data: factors `ℓ` at the nodes, leaf standard deviations. -/
inductive LTree : ℕ → Type
  | leaf (σ : ℝ) : LTree 0
  | node {L : ℕ} (ℓ : Out (L + 1) → ℂ) (T0 T1 : LTree L) : LTree (L + 1)

/-- Every leaf in `[1.2778, 1.825]`. -/
def LTree.InRange : {L : ℕ} → LTree L → Prop
  | _, .leaf σ => 12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000
  | _, .node _ U0 U1 => U0.InRange ∧ U1.InRange

/-- Every factor `ℓ` is the FFT of a real polynomial (`IsReal`). -/
def LTree.Real : {L : ℕ} → LTree L → Prop
  | _, .leaf _ => True
  | _, .node ℓ U0 U1 => IsReal ℓ ∧ U0.Real ∧ U1.Real

/-- **ffLDL⋆, exact** (ePrint 2026/1531 Alg. 5; spec Alg. 9) of the self-adjoint Gram matrix
`[[g00, g10⋆], [g10, g11]]` over `Out L`: `ℓ = g10/g00`, `D00 = g00`, `D11 = g11 - |g10|²/g00`;
child `i` is ffLDL⋆ of the split of `Dii`, `[[a, b], [b⋆, a]]` with `(a, b) = splitfft Dii`; a leaf
is normalised to `σ/√D` (Alg. 1 l. 6-7). -/
noncomputable def ffldl (σ : ℝ) : (L : ℕ) → (g00 g10 g11 : Out L → ℂ) → LTree L
  | 0, g00, _, _ => .leaf (σ / √(g00 ()).re)
  | L + 1, g00, g10, g11 =>
    .node (fun o => g10 o / g00 o)
      (ffldl σ L (splitE g00).1 (fun o => conj ((splitE g00).2 o)) (splitE g00).1)
      (ffldl σ L (splitE fun o => g11 o - g10 o * conj (g10 o) / g00 o).1
        (fun o => conj ((splitE fun o => g11 o - g10 o * conj (g10 o) / g00 o).2 o))
        (splitE fun o => g11 o - g10 o * conj (g10 o) / g00 o).1)

/-- Falcon-512's `σ = 165.736617183` (spec Table 3.3). -/
noncomputable def σ512 : ℝ := 165736617183 / 10 ^ 9

/-- Exact FFT of an integer polynomial of size `2⁹`. -/
noncomputable def fftZ (a : Fin (2 ^ 9) → ℤ) : Out 9 → ℂ := fftE fun i => (a i : ℂ)

/-- A signing key with the whole basis `B = [[g, -f], [G, -F]]`. -/
structure KeyB extends Key where
  g : Fin (2 ^ 9) → ℤ
  G : Fin (2 ^ 9) → ℤ

/-- `(B·B⋆)₀₀ = gg⋆ + ff⋆`. -/
noncomputable def KeyB.gram00 (k : KeyB) (o : Out 9) : ℂ :=
  fftZ k.g o * conj (fftZ k.g o) + fftZ k.f o * conj (fftZ k.f o)

/-- `(B·B⋆)₁₀ = Gg⋆ + Ff⋆`. -/
noncomputable def KeyB.gram10 (k : KeyB) (o : Out 9) : ℂ :=
  fftZ k.G o * conj (fftZ k.g o) + fftZ k.F o * conj (fftZ k.f o)

/-- `(B·B⋆)₁₁ = GG⋆ + FF⋆`. -/
noncomputable def KeyB.gram11 (k : KeyB) (o : Out 9) : ℂ :=
  fftZ k.G o * conj (fftZ k.G o) + fftZ k.F o * conj (fftZ k.F o)

/-- **The true tree**: exact ffLDL⋆ of `B·B⋆` at Falcon-512. -/
noncomputable def KeyB.trueTree (k : KeyB) : LTree 9 := ffldl σ512 9 k.gram00 k.gram10 k.gram11

theorem isReal_conj {L : ℕ} {v : Out L → ℂ} (h : IsReal v) : IsReal fun o => conj (v o) :=
    fun o => by
  simp only [h o]

theorem isReal_ffldl (σ : ℝ) : ∀ (L : ℕ)
    (g00 g10 g11 : Out L → ℂ), IsReal g00 → IsReal g10 → IsReal g11 →
    (ffldl σ L g00 g10 g11).Real
  | 0, _, _, _, _, _, _ => trivial
  | L + 1, g00, g10, g11, h00, h10, h11 => by
    have hd : IsReal fun o => g11 o - g10 o * conj (g10 o) / g00 o := fun o => by
      simp only [h00 o, h10 o, h11 o, map_sub, map_mul, map_div₀, Complex.conj_conj]
    have s0 := isReal_splitE h00
    have s1 := isReal_splitE hd
    exact ⟨fun o => by simp only [h00 o, h10 o, map_div₀],
      isReal_ffldl σ L _ _ _ s0.1 (isReal_conj s0.2) s0.1,
          isReal_ffldl σ L _ _ _ s1.1 (isReal_conj s1.2) s1.1⟩

theorem isReal_fftZ (a : Fin (2 ^ 9) → ℤ) : IsReal (fftZ a) :=
  isReal_evalAt (L := 9) (fun i => (a i : ℂ)) fun _ => map_intCast _ _

/-- **The true tree is real**: every `ℓ` of exact ffLDL⋆ of `B·B⋆` is the FFT of a real polynomial.
-/
theorem isReal_trueTree (k : KeyB) : k.trueTree.Real := by
  have hg := isReal_fftZ k.g
  have hf := isReal_fftZ k.f
  have hG := isReal_fftZ k.G
  have hF := isReal_fftZ k.F
  refine isReal_ffldl σ512 9 _ _ _ (fun o => ?_) (fun o => ?_) (fun o => ?_) <;>
    simp only [KeyB.gram00, KeyB.gram10, KeyB.gram11, hg o, hf o, hG o, hF o, map_add, map_mul,
      Complex.conj_conj]

/--
**Stored tree against true tree**: `‖ℓ̂ - ℓ‖∞ ≤ δ L` at every node of depth `L + 1`; at every leaf
the true `σ` in `[1.2778, 1.825]` and `|σ̄/σ - 1| ≤ 2⁻⁴²` (`Falcon.CallP.hΔσ`). -/
def Close (δ : ℕ → ℝ) : {L : ℕ} → FTree L → LTree L → Prop
  | _, .leaf σb _, .leaf σ => (12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000) ∧ |σb / σ - 1| ≤ 1 / 2 ^ 42
  | _, @FTree.node L ℓh _ T0 T1, .node ℓ U0 U1 => (∀ o, ‖ℓh o - ℓ o‖ ≤ δ L) ∧ Close δ T0 U0 ∧
      Close δ T1 U1

theorem Close.inRange {δ : ℕ → ℝ} : {L : ℕ} → {T : FTree L} → {U : LTree L} → Close δ T U →
    U.InRange
  | _, .leaf _ _, .leaf _, h => h.1
  | _, .node _ _ _ _, .node _ _ _, h => ⟨Close.inRange h.2.1, Close.inRange h.2.2⟩

/-- A position at every level. -/
def outPt : (L : ℕ) → Out L
  | 0 => ()
  | L + 1 => (outPt L, false)

theorem Close.delta_nonneg {δ : ℕ → ℝ} : {L : ℕ} → {T : FTree L} → {U : LTree L} → Close δ T U →
    ∀ j < L, 0 ≤ δ j
  | _, .leaf _ _, .leaf _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | _, .node _ _ _ _, .node _ _ _, h, j, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact Close.delta_nonneg h.2.1 j hj
    · exact (norm_nonneg _).trans (h.1 (outPt _))

/--
Conditions of hop B on a signing key: the stored tree is real (hop A, `FTree.Real`) and `Close δ` to
the true tree. -/
structure KeyB.Good (δ : ℕ → ℝ) (k : KeyB) : Prop where
  real : k.tree.Real
  close : Close δ k.tree k.trueTree

/-- Keys passing `KeyB.Good δ`. -/
def GoodKey (δ : ℕ → ℝ) : Type := {k : KeyB // k.Good δ}

/-! ## Signers -/

/-- A SamplerZ call with the true leaf and centre (`σ`, `t`) and the stored ones (`σbar`, `tbar`).
-/
def callB (σ σb t tb : ℝ) (hb : 1277833697 / 10 ^ 9 ≤ σb ∧ σb ≤ 18205 / 10000)
    (h : (12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000) ∧ |σb / σ - 1| ≤ 1 / 2 ^ 42) : Falcon.CallP :=
  ⟨σ, σb, t, tb, h.1, by linarith [hb.1], h.2⟩

/-- Line 14 on exact values. -/
noncomputable def joinE {L : ℕ} (s0 s1 : Samp L) : Samp (L + 1) :=
  ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1, mergeE s0, mergeE s1, mergeE s0, mergeE s1⟩

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- **ffSampling on both trees with the same samples**: true-tree centres `t0, t1` (factors `ℓ`),
stored-tree centres `s0, s1` (factors `ℓ̂`), both exact. -/
noncomputable def ffsB (δ : ℕ → ℝ) : {L : ℕ} → (T : FTree L) → (U : LTree L) → Close δ T U →
    (t0 t1 s0 s1 : Out L → ℂ) → OracleComp (FalconGame.spec aux Falcon.CallP) (Samp L)
  | _, .leaf σb hb, .leaf σ, h, t0, t1, s0, s1 =>
    (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
      (.inr (callB σ σb (t0 ()).re (s0 ()).re hb h))) : OracleComp _ ℤ) >>= fun z0 =>
    (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
      (.inr (callB σ σb (t1 ()).re (s1 ()).re hb h))) : OracleComp _ ℤ) >>= fun z1 =>
    pure (Samp.leaf z0 z1)
  | _, .node ℓh _ T0 T1, .node ℓ U0 U1, h, t0, t1, s0, s1 =>
    ffsB δ T1 U1 h.2.2 (splitE t1).1 (splitE t1).2 (splitE s1).1 (splitE s1).2 >>= fun r1 =>
    ffsB δ T0 U0 h.2.1 (splitE (upd t0 t1 (mergeE r1) ℓ)).1 (splitE (upd t0 t1 (mergeE r1) ℓ)).2
      (splitE (upd s0 s1 (mergeE r1) ℓh)).1 (splitE (upd s0 s1 (mergeE r1) ℓh)).2 >>= fun r0 =>
    pure (joinE r0 r1)

/-- **ffSampling on the true tree** (exact Falcon): SamplerZ calls `CallP.stored σ t t`. -/
noncomputable def ffsT : {L : ℕ} → (U : LTree L) → U.InRange → (t0 t1 : Out L → ℂ) →
    OracleComp (FalconGame.spec aux Falcon.CallP) (Samp L)
  | _, .leaf σ, h, t0, t1 =>
    (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
      (.inr (Falcon.CallP.stored σ (t0 ()).re (t0 ()).re h))) : OracleComp _ ℤ) >>= fun z0 =>
    (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
      (.inr (Falcon.CallP.stored σ (t1 ()).re (t1 ()).re h))) : OracleComp _ ℤ) >>= fun z1 =>
    pure (Samp.leaf z0 z1)
  | _, .node ℓ U0 U1, h, t0, t1 =>
    ffsT U1 h.2 (splitE t1).1 (splitE t1).2 >>= fun r1 =>
    ffsT U0 h.1 (splitE (upd t0 t1 (mergeE r1) ℓ)).1
        (splitE (upd t0 t1 (mergeE r1) ℓ)).2 >>= fun r0 =>
    pure (joinE r0 r1)

/-- A signature's integer part `z = (z0, z1)`, or `⊥`. -/
abbrev Sig : Type := Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))

open Classical in
/-- One ffSampling call of signing (spec Alg. 10 l. 3, 6) on both trees. -/
noncomputable def signB (δ : ℕ → ℝ) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    OracleComp (FalconGame.spec aux Falcon.CallP) Sig :=
  if ∀ i, |c i| < 12289 then
    (fun s => some (s.z0, s.z1)) <$> ffsB δ k.1.tree k.1.trueTree k.2.close
      (t0E k.1.toKey c) (t1E k.1.toKey c) (t0E k.1.toKey c) (t1E k.1.toKey c)
  else pure none

open Classical in
/-- One ffSampling call of exact Falcon signing (spec Alg. 10 l. 3, 6) on the true tree. -/
noncomputable def signT (δ : ℕ → ℝ) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    OracleComp (FalconGame.spec aux Falcon.CallP) Sig :=
  if ∀ i, |c i| < 12289 then
    (fun s => some (s.z0, s.z1)) <$> ffsT k.1.trueTree k.2.close.inRange (t0E k.1.toKey c)
        (t1E k.1.toKey c)
  else pure none

/-! ## Experiments -/

/-- Experiment oracles: auxiliary oracles and a signing oracle on (key, hash). -/
@[reducible] def specS (aux : OracleSpec.{0, 0} ιA) (δ : ℕ → ℝ) :
    OracleSpec (ιA ⊕ (GoodKey δ × (Fin (2 ^ 9) → ℤ))) :=
  Sum.elim aux fun _ => Sig

/-- One per signing query. -/
def wK (δ : ℕ → ℝ) : ιA ⊕ (GoodKey δ × (Fin (2 ^ 9) → ℤ)) → ℝ := Sum.elim (fun _ => 0) fun _ => 1

/-- Answer signing queries by `sg`, auxiliary queries by themselves. -/
noncomputable def signImpl {δ : ℕ → ℝ}
    (sg : GoodKey δ → (Fin (2 ^ 9) → ℤ) → OracleComp (FalconGame.spec aux Falcon.CallP) Sig) :
    QueryImpl (specS aux δ) (OracleComp (FalconGame.spec aux Falcon.CallP))
  | .inl x => liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl x))
  | .inr kc => sg kc.1 kc.2

variable {δ : ℕ → ℝ} {εq : ℝ}

/-- Type 1 signing with the model's range checks (`sign164`). -/
noncomputable def runA (ρ : Arith64 εq) {α : Type} (oe : OracleComp (specS aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  simulateQ (signImpl fun k c => sign164 ρ k.1.toKey c) oe

/-- Abort-free signing on the stored tree: F′ under `implF`, X under `implE`. -/
noncomputable def runX (ρ : Arith64 εq) {α : Type} (oe : OracleComp (specS aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  simulateQ (signImpl fun k c => sign164G ρ (fun _ _ _ => True) k.1.toKey c) oe

/-- Signing on both trees: X under `implF`, Y under `implE`. -/
noncomputable def runB (δ : ℕ → ℝ) {α : Type} (oe : OracleComp (specS aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  simulateQ (signImpl (signB δ)) oe

/-- Exact Falcon signing on the true tree: Y under `implE`. -/
noncomputable def runT (δ : ℕ → ℝ) {α : Type} (oe : OracleComp (specS aux δ) α) :
    OracleComp (FalconGame.spec aux Falcon.CallP) α :=
  simulateQ (signImpl (signT δ)) oe

/-! ## Budgets -/

/-- ℓ2 gain from the input error of a stored-tree call at depth `L` to its leaf errors: `A₀ = 1`,
`A_{L+1} = A_L·(Λ + √(Λ² + 4))/(2√2)`, `Λ = lam512 L` (largest singular value of `[[1, Λ], [0, 1]]`,
split `1/√2`). -/
noncomputable def gainA : ℕ → ℝ
  | 0 => 1
  | L + 1 => gainA L * (lam512 L + √(lam512 L ^ 2 + 4)) / (2 * √2)

/--
ℓ2 bound on the true deviation `t - z` of a call at depth `L` when every leaf answer lies within `y`
of its centre: `D₀ = √2·y`, `D_{L+1} = √(2((1 + lam512 L + δ L)² + 1))·D_L`. -/
noncomputable def devB (y : ℝ) (δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => √2 * y
  | L + 1 => √(2 * ((1 + lam512 L + δ L) ^ 2 + 1)) * devB y δ L

/--
Per-call bound on the sum of squared centre differences `(t̄ - t)²`: the `(t1 - ẑ1)(ℓ̂ - ℓ)` terms
of the `2^(8-L)` nodes of depth `L + 1` (ℓ2 `≤ δ L·√(2^(8-L))·√2·devB y δ L`), each through
`gainA L` after the split. -/
noncomputable def s2B (y : ℝ) (δ : ℕ → ℝ) : ℝ :=
  (∑ L ∈ Finset.range 9, gainA L * δ L * √(2 ^ (8 - L)) * devB y δ L) ^ 2

/-- Centre-difference budget injected below a call at depth `L`: `C₀ = 0`,
`C_{L+1} = √2·C_L + gainA L·δ L·devB y δ L`. -/
noncomputable def cB (y : ℝ) (δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | L + 1 => √2 * cB y δ L + gainA L * δ L * devB y δ L

/--
Assumed tree error (`Close δ127`) of a key expansion at `p = 127` stored in 64-bit words: `2⁻⁵⁸` at
the root (`‖ℓ̂‖∞ ≤ 24`), `2⁻⁶³` below; target values, not derived here. -/
noncomputable def δ127 (L : ℕ) : ℝ := if L = 8 then 1 / 2 ^ 58 else 1 / 2 ^ 63

/-- Assumed tree error (`Close δ63`) of key expansion at `p = 63`, numerical estimates (not proved):
`0.8123·2⁻⁴⁰ ≥ 2⁻⁴⁰·³` at the root, `0.7072·2⁻⁴¹ ≥ 2⁻⁴¹·⁵` below. -/
noncomputable def δ63 (L : ℕ) : ℝ := if L = 8 then 8123 / 10000 / 2 ^ 40 else 7072 / 10000 / 2 ^ 41

theorem gainA_nonneg : ∀ L, 0 ≤ gainA L
  | 0 => zero_le_one
  | L + 1 => by
    rw [gainA]
    exact div_nonneg
        (mul_nonneg (gainA_nonneg L) (add_nonneg (lam512_nonneg L) (Real.sqrt_nonneg _)))
      (by positivity)

theorem devB_nonneg {y : ℝ} (hy : 0 ≤ y) (δ : ℕ → ℝ) : ∀ L, 0 ≤ devB y δ L
  | 0 => mul_nonneg (Real.sqrt_nonneg _) hy
  | L + 1 => mul_nonneg (Real.sqrt_nonneg _) (devB_nonneg hy δ L)

theorem cB_nonneg {y : ℝ} (hy : 0 ≤ y) {δ : ℕ → ℝ} : ∀ L, (∀ j < L, 0 ≤ δ j) → 0 ≤ cB y δ L
  | 0, _ => le_rfl
  | L + 1, h => by
    rw [cB]
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (cB_nonneg hy L fun j hj => h j (by omega)))
      (mul_nonneg (mul_nonneg (gainA_nonneg L) (h L (by omega))) (devB_nonneg hy δ L))

theorem cB_eq (y : ℝ) (δ : ℕ → ℝ) :
    ∀ n, cB y δ n = ∑ L ∈ Finset.range n, gainA L * δ L * √(2 ^ (n - 1 - L)) * devB y δ L
  | 0 => by simp [cB]
  | n + 1 => by
    rw [cB, cB_eq y δ n, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun L hL => ?_
      have hL' := Finset.mem_range.1 hL
      rw [show n + 1 - 1 - L = n - 1 - L + 1 by omega, pow_succ, Real.sqrt_mul (by positivity)]
      ring
    · simp

theorem s2B_eq (y : ℝ) (δ : ℕ → ℝ) : s2B y δ = cB y δ 9 ^ 2 := by
  rw [cB_eq]
  rfl

theorem s2B_nonneg (y : ℝ) (δ : ℕ → ℝ) : 0 ≤ s2B y δ := sq_nonneg _

/-! ## Executions -/

section Hist

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Every query along every execution of `oa` satisfies `P`, every result satisfies `Q`. -/
inductive Hist (P : ι → Prop) {α : Type} (Q : α → Prop) : OracleComp spec α → Prop
  | pure (x : α) (h : Q x) : Hist P Q (pure x)
  | query_bind (t : ι) (k : spec.Range t → OracleComp spec α) (ht : P t) (h : ∀ u, Hist P Q (k u)) :
      Hist P Q (liftM (OracleSpec.query t) >>= k)

theorem Hist.bind {P : ι → Prop} {α β : Type} {Q : α → Prop} {R : β → Prop} {oa : OracleComp spec α}
    {f : α → OracleComp spec β} (h : Hist P Q oa) (hf : ∀ x, Q x → Hist P R (f x)) :
    Hist P R (oa >>= f) := by
  induction h with
  | pure x hx => rw [pure_bind]; exact hf x hx
  | query_bind t k ht _ ih => rw [bind_assoc]; exact .query_bind t _ ht fun u => ih u

theorem Hist.mono {P P' : ι → Prop} {α : Type} {Q Q' : α → Prop} {oa : OracleComp spec α}
    (h : Hist P Q oa) (hP : ∀ t, P t → P' t) (hQ : ∀ x, Q x → Q' x) : Hist P' Q' oa := by
  induction h with
  | pure x hx => exact .pure x (hQ x hx)
  | query_bind t k ht _ ih => exact .query_bind t k (hP t ht) ih

theorem Hist.query {P : ι → Prop} (t : ι) (ht : P t) :
    Hist P (fun _ => True) (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)) := by
  rw [← bind_pure (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))]
  exact .query_bind t _ ht fun u => .pure u trivial

theorem Hist.true {α : Type} (oa : OracleComp spec α) : Hist (fun _ : ι => True)
    (fun _ => True) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact .pure x trivial
  | query_bind t k ih => exact .query_bind t k trivial ih

theorem Hist.inv_query {P : ι → Prop} {α : Type} {Q : α → Prop} {t : ι}
    {k : spec.Range t → OracleComp spec α}
    (h : Hist P Q (liftM (OracleSpec.query t) >>= k)) : P t ∧ ∀ u, Hist P Q (k u) := by
  generalize hx : (liftM (OracleSpec.query t) >>= k : OracleComp spec α) = x at h
  cases h with
  | pure y _ =>
    have e : (PFunctor.FreeM.liftBind t k : PFunctor.FreeM spec.toPFunctor α) =
        PFunctor.FreeM.pure y := hx
    cases e
  | query_bind t' k' ht h' =>
    have e : (PFunctor.FreeM.liftBind t k : PFunctor.FreeM spec.toPFunctor α) =
      PFunctor.FreeM.liftBind t' k' := hx
    injection e with e1 e2
    subst e1
    cases e2
    exact ⟨ht, h'⟩

/-- Path budgets add along `>>=` when the continuation's budget holds on the results of `oa`. -/
theorem pathSum_bind_hist {w : ι → ℝ} {P : ι → Prop} {α β : Type} {Q : α → Prop}
    {oa : OracleComp spec α}
    {f : α → OracleComp spec β} {S T : ℝ} (h : PathSum w oa S) (hh : Hist P Q oa)
    (hf : ∀ x, Q x → PathSum w (f x) T) : PathSum w (oa >>= f) (S + T) := by
  induction hh generalizing S with
  | pure x hx => rw [pure_bind]; exact (hf x hx).weaken (by linarith [h.inv_pure])
  | query_bind t k _ _ ih =>
    rw [bind_assoc]
    exact .query_bind t _ fun u => by
      have := ih u (h.inv_query u)
      rwa [show S - w t + T = S + T - w t by ring] at this

theorem pathSum_query {w : ι → ℝ} (t : ι) {S : ℝ} (h : 0 ≤ S - w t) :
    PathSum w (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)) S := by
  rw [← bind_pure (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))]
  exact .query_bind t _ fun u => .pure u h

/-- Budgets through an implementation: per-query budgets `c·w' t` of the implementation give `c·K`.
-/
theorem pathSum_simulateQ_impl {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} {w : ι → ℝ} {w' : ι' → ℝ}
    (impl : QueryImpl spec' (OracleComp spec)) {c : ℝ} (hc : 0 ≤ c)
        (h : ∀ t, PathSum w (impl t) (c * w' t))
    {α : Type} {oe : OracleComp spec' α} {K : ℝ} (hK : PathSum w' oe K) :
    PathSum w (simulateQ impl oe) (c * K) := by
  induction hK with
  | pure x hS => rw [simulateQ_pure]; exact .pure x (mul_nonneg hc hS)
  | @query_bind t k S _ ih =>
    rw [simulateQ_bind, show simulateQ impl (liftM (OracleSpec.query t)) = impl t from
      simulateQ_spec_query (impl := impl) t]
    have := (h t).bind fun u => ih u
    rwa [show c * w' t + c * (S - w' t) = c * S by ring] at this

theorem Hist.simulateQ_impl {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} {P : ι → Prop}
    (impl : QueryImpl spec' (OracleComp spec)) (h : ∀ t, Hist P (fun _ => True) (impl t)) {α : Type}
    (oe : OracleComp spec' α) : Hist P (fun _ => True) (simulateQ impl oe) := by
  induction oe using OracleComp.inductionOn with
  | pure x => rw [simulateQ_pure]; exact .pure x trivial
  | query_bind t k ih =>
    rw [simulateQ_bind, show simulateQ impl (liftM (OracleSpec.query t)) = impl t from
      simulateQ_spec_query (impl := impl) t]
    exact (h t).bind fun u _ => ih u

/-- Two computations with the same queries along every execution, results related by `R`. -/
inductive SameQ {α β : Type} (R : α → β → Prop) : OracleComp spec α → OracleComp spec β → Prop
  | pure (x : α) (y : β) (h : R x y) : SameQ R (pure x) (pure y)
  | query_bind (t : ι) (k : spec.Range t → OracleComp spec α)
      (k' : spec.Range t → OracleComp spec β)
      (h : ∀ u, SameQ R (k u) (k' u)) :
      SameQ R (liftM (OracleSpec.query t) >>= k) (liftM (OracleSpec.query t) >>= k')

theorem SameQ.bind {α β γ δ' : Type} {R : α → β → Prop} {S : γ → δ' → Prop} {oa : OracleComp spec α}
    {ob : OracleComp spec β} {f : α → OracleComp spec γ} {g : β → OracleComp spec δ'}
        (h : SameQ R oa ob)
    (hf : ∀ x y, R x y → SameQ S (f x) (g y)) : SameQ S (oa >>= f) (ob >>= g) := by
  induction h with
  | pure x y hxy => rw [pure_bind, pure_bind]; exact hf x y hxy
  | query_bind t k k' _ ih => rw [bind_assoc, bind_assoc]; exact .query_bind t _ _ fun u => ih u

theorem SameQ.map_eq {α β γ : Type} {R : α → β → Prop} {oa : OracleComp spec α}
    {ob : OracleComp spec β}
    (h : SameQ R oa ob) (F : α → γ) (G : β → γ)
        (hFG : ∀ x y, R x y → F x = G y) : F <$> oa = G <$> ob := by
  induction h with
  | pure x y hxy => rw [map_pure, map_pure, hFG x y hxy]
  | query_bind t k k' _ ih => rw [map_bind, map_bind]; exact congrArg _ (funext ih)

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- Implementations with equal answer distributions give equal output distributions. -/
theorem distEq_simulateQ (impl₁ impl₂ : QueryImpl spec m)
    (h : ∀ t, @evalDist m _ (spec.Range t) ⊤ (impl₁ t) = @evalDist m _ (spec.Range t) ⊤ (impl₂ t))
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) :
    𝒟[simulateQ impl₁ oa] = 𝒟[simulateQ impl₂ oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure]
  | query_bind t k ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    have : DiscreteMeasurableSpace (spec.Range t) := ⟨fun _ => trivial⟩
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, h t]
    simp_rw [ih]

/--
**Total variation against a post-processed run**, the budget taken along the original run and the
queries of the post-processed run satisfying `P` (no answer type needs to be inhabited). -/
theorem etvDist_simulateQ_rewrite_hist (impl : QueryImpl spec m)
    {so : QueryImpl spec (OracleComp spec)} (f : (t : ι) → spec.Range t → spec.Range t)
    (hso : ∀ t, so t = f t <$> liftM (OracleSpec.query t)) {c : ℝ} (hc : 0 ≤ c) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t) (P : ι → Prop)
    (hB : ∀ t, P t → @MeasureTheory.Measure.etvDist _ ⊤ (@evalDist m _ (spec.Range t) ⊤ (impl t))
      (@MeasureTheory.Measure.map _ _ ⊤ ⊤ (f t) (@evalDist m _ (spec.Range t) ⊤ (impl t))) ≤
        ENNReal.ofReal (c * w t))
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) :
    ∀ S, PathSum w oa S → Hist P (fun _ => True) (simulateQ so oa) →
      (𝒟[simulateQ impl oa]).etvDist 𝒟[simulateQ impl (simulateQ so oa)] ≤
          ENNReal.ofReal (c * S) := by
  have hz : ∀ (ob : OracleComp spec α) (S : ℝ), PathSum w ob S → S < 0 → 𝒟[simulateQ impl ob] = 0 :=
    fun ob S h hS => ((etvDist_simulateQ_le_path impl impl hc w hw
      (fun _ => (@Measure.etvDist_self _ ⊤ _).trans_le bot_le) h).1 hS).1
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro S _ _
    simp only [simulateQ_pure, MeasureTheory.Measure.etvDist_self]
    exact bot_le
  | query_bind t k ih =>
    intro S h hH
    let : MeasurableSpace (spec.Range t) := ⊤
    have : DiscreteMeasurableSpace (spec.Range t) := ⟨fun _ => trivial⟩
    have e1 : simulateQ so (liftM (OracleSpec.query t) >>= k) =
        liftM (OracleSpec.query t) >>= fun u => simulateQ so (k (f t u)) := by
      rw [simulateQ_bind, show simulateQ so (liftM (OracleSpec.query t)) = so t from
        simulateQ_spec_query (impl := so) t, hso, map_eq_bind_pure_comp, bind_assoc]
      simp
    change PathSum w (liftM (OracleSpec.query t) >>= k) S at h
    change Hist P (fun _ => True) (simulateQ so (liftM (OracleSpec.query t) >>= k)) at hH
    change (𝒟[simulateQ impl (liftM (OracleSpec.query t) >>= k)]).etvDist
      𝒟[simulateQ impl (simulateQ so (liftM (OracleSpec.query t) >>= k))] ≤ _
    rw [e1] at hH ⊢
    obtain ⟨hPt, hHk⟩ := hH.inv_query
    have hk := h.inv_query
    simp only [simulateQ_bind, show simulateQ impl (liftM (OracleSpec.query t)) = impl t from
      simulateQ_spec_query (impl := impl) t]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    by_cases hS : S - w t < 0
    · have z1 : (fun u => 𝒟[simulateQ impl (k u)]) = 0 := funext fun u => hz _ _ (hk u) hS
      have z2 : (fun u => 𝒟[simulateQ impl (simulateQ so (k (f t u)))]) = 0 :=
        funext fun u => by
          have := (etvDist_simulateQ_le_path impl impl hc w hw
            (fun _ => (@Measure.etvDist_self _ ⊤ _).trans_le bot_le)
            ((hk (f t u)).simulateQ_map f hso)).1 hS
          exact this.1
      rw [z1, z2, Measure.etvDist_self]
      exact bot_le
    · have hS' : 0 ≤ S - w t := not_lt.1 hS
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
              (hB t hPt)) ?_
            rw [hmid]
            refine (MeasureTheory.Measure.etvDist_bind_bind_le_lintegral _ _ _
              Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable
              (fun _ => ENNReal.ofReal (c * (S - w t))) (MeasureTheory.ae_of_all _ fun u =>
                ih (f t u) _ (hk (f t u)) (hHk u))).trans ?_
            rw [MeasureTheory.lintegral_const]
            exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
        _ = ENNReal.ofReal (c * S) := by
            rw [← ENNReal.ofReal_add (mul_nonneg hc (hw t)) (mul_nonneg hc hS')]
            congr 1
            ring

end Hist

/-! ## Clamped runs: the centre differences (the mathematics of hop B) -/

/-- SamplerZ queries with centre difference `(t̄ - t)² ≤ B` and `σ̄ ≤ 1.825`. -/
def PQ (B : ℝ) : ιA ⊕ Falcon.CallP → Prop :=
  Sum.elim (fun _ => True) fun q => (q.tbar - q.t) ^ 2 ≤ B ∧ q.σbar ≤ 1825 / 1000

theorem PQ_mono {B B' : ℝ} (hB : B ≤ B') (t : ιA ⊕ Falcon.CallP) (h : PQ B t) : PQ B' t := by
  rcases t with _ | q
  · trivial
  · exact ⟨h.1.trans hB, h.2⟩

/-- An output of a clamped `ffsB` call: `IsFFT`, deviation `t - ẑ` within `devB y δ L` in ℓ2. -/
def GoodB (y : ℝ) (δ : ℕ → ℝ) {L : ℕ} (t0 t1 : Out L → ℂ) (s : Samp L) : Prop :=
  IsFFT s ∧ l2 (pairF (t0 - s.e0) (t1 - s.e1)) ≤ devB y δ L

theorem isFFT_joinE {L : ℕ} {s0 s1 : Samp L} (h0 : IsFFT s0)
    (h1 : IsFFT s1) : IsFFT (joinE s0 s1) :=
  fun x => ⟨congrFun (mergeE_eq h0) x, congrFun (mergeE_eq h1) x⟩

theorem splitE_sub {L : ℕ} (a b : Out (L + 1) → ℂ) :
    (splitE a).1 - (splitE b).1 = (splitE (a - b)).1 ∧ (splitE a).2 - (splitE b).2 =
        (splitE (a - b)).2 := by
  constructor <;> funext o
  · change (a (o, false) + a (o, true)) / 2 - (b (o, false) + b (o, true)) / 2 =
      (a (o, false) - b (o, false) + (a (o, true) - b (o, true))) / 2
    ring
  · change conj (zeta L o) / 2 * (a (o, false) - a (o, true)) - conj (zeta L o) / 2 *
      (b (o, false) - b (o, true)) =
      conj (zeta L o) / 2 * (a (o, false) - b (o, false) - (a (o, true) - b (o, true)))
    ring

/-- Line 10 with `‖ℓ‖ ≤ Λ` is at most `(Λ + √(Λ² + 4))/2` in ℓ2 (largest singular value of
`[[1, ℓ], [0, 1]]`). -/
theorem norm_update_sq_le (a b ℓ : ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hℓ : ‖ℓ‖ ≤ Λ) :
    ‖a + b * ℓ‖ ^ 2 + ‖b‖ ^ 2 ≤ ((Λ + √(Λ ^ 2 + 4)) / 2) ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  set r := √(Λ ^ 2 + 4)
  have hr : r ^ 2 = Λ ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hu := norm_nonneg a
  have hv := norm_nonneg b
  have h1 : ‖a + b * ℓ‖ ≤ ‖a‖ + Λ * ‖b‖ := (norm_add_le _ _).trans (by
    rw [norm_mul]; linarith [mul_le_mul_of_nonneg_left hℓ hv])
  have hQ : 0 ≤ (Λ + r) * ‖a‖ ^ 2 - 4 * ‖a‖ * ‖b‖ + (r - Λ) * ‖b‖ ^ 2 := by
    have e : (Λ + r) * ((Λ + r) * ‖a‖ ^ 2 - 4 * ‖a‖ * ‖b‖ + (r - Λ) * ‖b‖ ^ 2) =
        ((Λ + r) * ‖a‖ - 2 * ‖b‖) ^ 2 := by linear_combination ‖b‖ ^ 2 * hr
    have hpos : 0 < Λ + r := by nlinarith
    exact (mul_nonneg_iff_of_pos_left hpos).1 (e ▸ sq_nonneg _)
  have e2 : ((Λ + r) / 2) ^ 2 = (Λ ^ 2 + 2 + Λ * r) / 2 := by linear_combination hr / 4
  rw [e2]
  have h2 : ‖a + b * ℓ‖ ^ 2 ≤ (‖a‖ + Λ * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [mul_nonneg hΛ hQ]

theorem l2_update_sq_le {L : ℕ} (d0 d1 ℓ : Out L → ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hℓ : ∀ o, ‖ℓ o‖ ≤ Λ) :
    l2 (fun o => d0 o + d1 o * ℓ o) ^ 2 + l2 d1 ^ 2 ≤ ((Λ + √(Λ ^ 2 + 4)) / 2) ^ 2 *
        l2 (pairF d0 d1) ^ 2 := by
  rw [l2_pairF_sq, l2_sq, l2_sq, l2_sq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
  exact Finset.sum_le_sum fun o _ => norm_update_sq_le _ _ _ hΛ (hℓ o)

/-- **One node of the centre-difference budget.** Child 1 with input difference `x1` (`2x1² = Q²`),
child 0 with `(P + e·√2·D)/√2`, where `P² + Q² ≤ s²X²` (line 10 on the differences, `s` the singular
value) and `e·√2·D` bounds the injected `(t1 - ẑ1)(ℓ̂ - ℓ)`: the two budgets sum to at most the
parent's. -/
theorem budget_step {A C Λ X P Q D e x1 : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hX : 0 ≤ X)
    (hD : 0 ≤ D) (he : 0 ≤ e) (hP : 0 ≤ P)
    (hPQ : P ^ 2 + Q ^ 2 ≤ ((Λ + √(Λ ^ 2 + 4)) / 2) ^ 2 * X ^ 2) (hx1 : 2 * x1 ^ 2 = Q ^ 2)
        (hx1' : 0 ≤ x1) :
    (A * x1 + C) ^ 2 + (A * ((P + e * (√2 * D)) / √2) + C) ^ 2 ≤
      (A * (Λ + √(Λ ^ 2 + 4)) / (2 * √2) * X + (√2 * C + A * e * D)) ^ 2 := by
  set r := √(Λ ^ 2 + 4)
  set t := √2
  have ht2 : t ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 < t := Real.sqrt_pos.2 (by norm_num)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set s := (Λ + r) / 2 with hs
  have hs0 : 0 ≤ s := by positivity
  set X0 := (P + e * (t * D)) / t
  set M := s * X / t + e * D
  have hX0t : X0 * t = P + e * (t * D) := div_mul_cancel₀ _ ht0.ne'
  have hMt : M * t = s * X + e * (t * D) := by
    simp only [M]
    field_simp
  have hPs : P ≤ s * X := by
    have : P ^ 2 ≤ (s * X) ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg Q]
    exact (pow_le_pow_iff_left₀ hP (by positivity) two_ne_zero).1 this
  have hX00 : 0 ≤ X0 := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hsq : x1 ^ 2 + X0 ^ 2 ≤ M ^ 2 := by
    have h1 : Q ^ 2 + (X0 * t) ^ 2 ≤ (M * t) ^ 2 := by
      rw [hX0t, hMt]
      nlinarith [mul_le_mul_of_nonneg_left hPs (by positivity : (0 : ℝ) ≤ 2 * (e * (t * D)))]
    have e1 : (X0 * t) ^ 2 = 2 * X0 ^ 2 := by rw [mul_pow, ht2]; ring
    have e2 : (M * t) ^ 2 = 2 * M ^ 2 := by rw [mul_pow, ht2]; ring
    linarith
  have hsum : x1 + X0 ≤ t * M := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, ht2]
    nlinarith [sq_nonneg (x1 - X0)]
  have e1 : A * (Λ + r) / (2 * t) * X + (t * C + A * e * D) = A * M + t * C := by
    simp only [M, s]
    field_simp
    ring
  rw [e1]
  have e2 : (A * M + t * C) ^ 2 = A ^ 2 * M ^ 2 + 2 * (A * C) * (t * M) + 2 * C ^ 2 := by
    linear_combination C ^ 2 * ht2
  rw [e2]
  nlinarith
      [mul_le_mul_of_nonneg_left hsum (mul_nonneg hA hC),
          mul_le_mul_of_nonneg_left hsq (sq_nonneg A)]

/-- One node of the true deviation (as `ffsG_clamp`, with `‖ℓ‖ ≤ Λ + e`). -/
theorem dev_step {A B D Λ e a : ℝ} (hΛ : 0 ≤ Λ + e) (hA : A ^ 2 ≤ 2 * D ^ 2)
    (hB : B ^ 2 ≤ 2 * D ^ 2) (ha : 0 ≤ a) (h : a ≤ A + (Λ + e) * B) :
    a ^ 2 + B ^ 2 ≤ (√(2 * ((1 + Λ + e) ^ 2 + 1)) * D) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hAB : A * B ≤ 2 * D ^ 2 := by nlinarith [sq_nonneg (A - B)]
  have h2 : a ^ 2 ≤ (A + (Λ + e) * B) ^ 2 := pow_le_pow_left₀ ha h 2
  nlinarith [mul_le_mul_of_nonneg_left hAB (by positivity : (0 : ℝ) ≤ 2 * (Λ + e)),
    mul_le_mul_of_nonneg_left hB (sq_nonneg (Λ + e))]

theorem simulateQ_inr {β : Type}
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (q : Falcon.CallP) (k : ℤ → OracleComp (FalconGame.spec aux Falcon.CallP) β) :
    simulateQ so ((liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) :
      OracleComp _ ℤ) >>= k) = (so (.inr q) : OracleComp _ ℤ) >>= fun z => simulateQ so (k z) := by
  rw [simulateQ_bind]
  exact congrArg (· >>= fun z => simulateQ so (k z)) (simulateQ_spec_query (impl := so) (Sum.inr q))

theorem simulateQ_clampQ_inr {β : Type} (y : ℝ) (q : Falcon.CallP)
    (k : ℤ → OracleComp (FalconGame.spec aux Falcon.CallP) β) :
    simulateQ (clampQ y)
        ((liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) :
      OracleComp _ ℤ) >>= k) =
      (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) : OracleComp _
          ℤ) >>=
        fun z => simulateQ (clampQ y) (k (clamp y q.t z)) := by
  rw [simulateQ_inr]
  exact bind_map_left _ _ _

/--
**Centre differences of a clamped `ffsB` call.** Inputs: true centres real, stored minus true of ℓ2
norm `≤ X`. Along every history of the call with SamplerZ answers clamped to within `y` of the true
centre: the output is `GoodB`, every query has `(t̄ - t)² ≤ (gainA L·X + cB y δ L)²`, and so does
the sum over the call. -/
theorem ffsB_clamp (y : ℝ) (hy : 1 / 2 ≤ y) {L : ℕ} (T : FTree L) :
    ∀ (U : LTree L) (h : Close δ T U), U.Real → ∀ (t0 t1 s0 s1 : Out L → ℂ), IsReal t0 → IsReal t1 →
      ∀ X, l2 (pairF (s0 - t0) (s1 - t1)) ≤ X →
      Hist (PQ ((gainA L * X + cB y δ L) ^ 2)) (GoodB y δ t0 t1)
          (simulateQ (clampQ y) (ffsB (aux := aux) δ T U h t0 t1 s0 s1)) ∧
        PathSum wS (simulateQ (clampQ y) (ffsB (aux := aux) δ T U h t0 t1 s0 s1))
          ((gainA L * X + cB y δ L) ^ 2) := by
  have hy0 : 0 ≤ y := by linarith
  have hre : ∀ a b : ℂ, (a.re - b.re) ^ 2 ≤ ‖a - b‖ ^ 2 := fun a b => by
    rw [← Complex.sub_re]
    exact sq_le_sq' (abs_le.1 (Complex.abs_re_le_norm _)).1 (abs_le.1 (Complex.abs_re_le_norm _)).2
  induction T with
  | leaf σb hb =>
    intro U h _ t0 t1 s0 s1 h0 h1 X hX
    cases U with
    | leaf σ =>
    simp only [ffsB, simulateQ_clampQ_inr, simulateQ_pure]
    have hX0 : 0 ≤ X := (l2_nonneg _).trans hX
    have hl : ‖s0 () - t0 ()‖ ^ 2 + ‖s1 () - t1 ()‖ ^ 2 ≤ X ^ 2 := by
      have h2 := pow_le_pow_left₀ (l2_nonneg _) hX 2
      rw [l2_pairF_sq, l2_out0, l2_out0] at h2
      exact h2
    have q0 := hre (s0 ()) (t0 ())
    have q1 := hre (s1 ()) (t1 ())
    have hn0 := sq_nonneg ((s0 ()).re - (t0 ()).re)
    have hn1 := sq_nonneg ((s1 ()).re - (t1 ()).re)
    have hσ : σb ≤ 1825 / 1000 := by linarith [hb.2]
    have e : (gainA 0 * X + cB y δ 0) ^ 2 = X ^ 2 := by simp [gainA, cB]
    rw [e]
    refine ⟨.query_bind _ _
        ⟨by change ((s0 ()).re - (t0 ()).re) ^ 2 ≤ X ^ 2; linarith, hσ⟩ fun z0 =>
      .query_bind _ _ ⟨by change ((s1 ()).re - (t1 ()).re) ^ 2 ≤ X ^ 2; linarith, hσ⟩ fun z1 =>
        .pure _ ⟨isFFT_leaf _ _, ?_⟩,
      .query_bind _ _ fun z0 => .query_bind _ _ fun z1 => .pure _ ?_⟩
    · have e0 : t0 () = ((t0 ()).re : ℂ) := Complex.ext (by simp) (by simpa using im_eq_zero h0 ())
      have e1 : t1 () = ((t1 ()).re : ℂ) := Complex.ext (by simp) (by simpa using im_eq_zero h1 ())
      have hz0 := abs_clamp_sub_le (t := (t0 ()).re) hy z0
      have hz1 := abs_clamp_sub_le (t := (t1 ()).re) hy z1
      have d0 : ‖t0 () - (clamp y (t0 ()).re z0 : ℂ)‖ ≤ y := by
        rw [e0, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_sub_comm]
        simpa using hz0
      have d1 : ‖t1 () - (clamp y (t1 ()).re z1 : ℂ)‖ ≤ y := by
        rw [e1, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_sub_comm]
        simpa using hz1
      refine (pow_le_pow_iff_left₀ (l2_nonneg _) (devB_nonneg hy0 δ 0) two_ne_zero).1 ?_
      rw [l2_pairF_sq, l2_out0, l2_out0]
      change ‖t0 () - (clamp y (t0 ()).re z0 : ℂ)‖ ^ 2 + ‖t1 () - (clamp y (t1 ()).re z1 : ℂ)‖ ^ 2 ≤
        (√2 * y) ^ 2
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      nlinarith [norm_nonneg (t0 () - (clamp y (t0 ()).re z0 : ℂ)),
        norm_nonneg (t1 () - (clamp y (t1 ()).re z1 : ℂ))]
    · change 0 ≤ X ^ 2 - ((s0 ()).re - (t0 ()).re) ^ 2 - ((s1 ()).re - (t1 ()).re) ^ 2
      linarith
  | @node L ℓh hℓh T0 T1 ih0 ih1 =>
    intro U h hU t0 t1 s0 s1 h0 h1 X hX
    cases U with
    | node ℓ U0 U1 =>
    obtain ⟨hℓR, hU0, hU1⟩ := hU
    simp only [ffsB, simulateQ_bind, simulateQ_pure]
    have hδL : 0 ≤ δ L := (norm_nonneg _).trans (h.1 (outPt _))
    have hA := gainA_nonneg L
    have hC := cB_nonneg hy0 L (Close.delta_nonneg h.2.1)
    have hD := devB_nonneg hy0 δ L
    have hlam := lam512_nonneg L
    have hX0 : 0 ≤ X := (l2_nonneg _).trans hX
    have hℓ' : ∀ o, ‖ℓ o‖ ≤ lam512 L + δ L := fun o =>
      calc ‖ℓ o‖ = ‖ℓh o - (ℓh o - ℓ o)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖ℓh o‖ + ‖ℓh o - ℓ o‖ := norm_sub_le _ _
        _ ≤ lam512 L + δ L := add_le_add (hℓh o) (h.1 o)
    have hs1 := splitE_sub s1 t1
    have hR1 := isReal_splitE h1
    obtain ⟨H1, P1⟩ :=
        ih1 U1 h.2.2 hU1 (splitE t1).1 (splitE t1).2 (splitE s1).1 (splitE s1).2 hR1.1 hR1.2
      _ le_rfl
    set x1 := l2 (pairF ((splitE s1).1 - (splitE t1).1) ((splitE s1).2 - (splitE t1).2)) with hx1d
    have hx1 : 2 * x1 ^ 2 = l2 (s1 - t1) ^ 2 := by
      rw [hx1d, hs1.1, hs1.2, l2_pairF_sq]
      linarith [l2_splitE_sq (s1 - t1)]
    set P := l2 (fun o => (s0 - t0) o + (s1 - t1) o * ℓh o)
    set X0 := (P + δ L * (√2 * devB y δ L)) / √2 with hX0d
    have hX00 : 0 ≤ X0 := div_nonneg (add_nonneg (l2_nonneg _) (mul_nonneg hδL
      (mul_nonneg (Real.sqrt_nonneg _) hD))) (Real.sqrt_nonneg _)
    have key : ∀ r1 : Samp L, GoodB y δ (splitE t1).1 (splitE t1).2 r1 →
        IsReal (upd t0 t1 (mergeE r1) ℓ) ∧ l2 (t1 - mergeE r1) ^ 2 ≤ 2 * devB y δ L ^ 2 ∧
        l2 (pairF ((splitE (upd s0 s1 (mergeE r1) ℓh)).1 - (splitE (upd t0 t1 (mergeE r1) ℓ)).1)
          ((splitE (upd s0 s1 (mergeE r1) ℓh)).2 - (splitE (upd t0 t1 (mergeE r1) ℓ)).2)) ≤ X0 := by
      intro r1 ⟨hf1, hd1⟩
      have hz : l2 (t1 - mergeE r1) ^ 2 ≤ 2 * devB y δ L ^ 2 := by
        rw [l2_sub_mergeE_sq t1 r1]
        linarith [pow_le_pow_left₀ (l2_nonneg _) hd1 2]
      refine ⟨isReal_upd h0 h1 (isReal_mergeE hf1) hℓR, hz, ?_⟩
      have hv := splitE_sub (upd s0 s1 (mergeE r1) ℓh) (upd t0 t1 (mergeE r1) ℓ)
      rw [hv.1, hv.2]
      have hve : upd s0 s1 (mergeE r1) ℓh - upd t0 t1 (mergeE r1) ℓ =
          (fun o => (s0 - t0) o + (s1 - t1) o * ℓh o) + fun o => (ℓh o - ℓ o) *
              (t1 - mergeE r1) o := by
        funext o
        simp only [upd, Pi.add_apply, Pi.sub_apply]
        ring
      have hz' : l2 (t1 - mergeE r1) ≤ √2 * devB y δ L := by
        refine (pow_le_pow_iff_left₀ (l2_nonneg _) (by positivity) two_ne_zero).1 ?_
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        exact hz
      have hvl : l2 (upd s0 s1 (mergeE r1) ℓh - upd t0 t1 (mergeE r1) ℓ) ≤ P + δ L *
          (√2 * devB y δ L) := by
        rw [hve]
        refine (l2_add_le _ _).trans (add_le_add le_rfl ?_)
        exact (l2_mul_le (fun o => ℓh o - ℓ o) _ _ hδL h.1).trans
            (mul_le_mul_of_nonneg_left hz' hδL)
      refine (pow_le_pow_iff_left₀ (l2_nonneg _) hX00 two_ne_zero).1 ?_
      rw [l2_pairF_sq, l2_splitE_sq, hX0d, div_pow, Real.sq_sqrt (by norm_num)]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (l2_nonneg _) hvl 2) (by norm_num)
    have hbud : (gainA L * x1 + cB y δ L) ^ 2 + (gainA L * X0 + cB y δ L) ^ 2 ≤
        (gainA (L + 1) * X + cB y δ (L + 1)) ^ 2 := by
      have hPQ : P ^ 2 + l2 (s1 - t1) ^ 2 ≤ ((lam512 L + √(lam512 L ^ 2 + 4)) / 2) ^ 2 * X ^ 2 :=
        (l2_update_sq_le (s0 - t0) (s1 - t1) ℓh hlam hℓh).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (l2_nonneg _) hX 2) (sq_nonneg _))
      have := budget_step hA hC hlam hX0 hD hδL (l2_nonneg _) hPQ hx1 (l2_nonneg _)
      rw [gainA, cB]
      exact this
    have hb1 : (gainA L * x1 + cB y δ L) ^ 2 ≤ (gainA (L + 1) * X + cB y δ (L + 1)) ^ 2 := by
      linarith [hbud, sq_nonneg (gainA L * X0 + cB y δ L)]
    have hb0 : (gainA L * X0 + cB y δ L) ^ 2 ≤ (gainA (L + 1) * X + cB y δ (L + 1)) ^ 2 := by
      linarith [hbud, sq_nonneg (gainA L * x1 + cB y δ L)]
    refine ⟨(H1.mono (PQ_mono hb1) fun _ h => h).bind fun r1 hr1 => ?_,
      ((pathSum_bind_hist (T := (gainA L * X0 + cB y δ L) ^ 2 + 0) P1 H1 fun r1 hr1 => ?_).weaken
          ?_ :
      PathSum wS _ _)⟩
    · obtain ⟨hR0, hz, hx0⟩ := key r1 hr1
      obtain ⟨H0, -⟩ := ih0 U0 h.2.1 hU0 _ _ _ _ (isReal_splitE hR0).1 (isReal_splitE hR0).2 X0 hx0
      refine (H0.mono (PQ_mono hb0) fun _ h => h).bind fun r0 hr0 => .pure _ ?_
      obtain ⟨hf1, -⟩ := hr1
      obtain ⟨hf0, hd0⟩ := hr0
      refine ⟨isFFT_joinE hf0 hf1, ?_⟩
      change l2 (pairF (t0 - mergeE r0) (t1 - mergeE r1)) ≤ devB y δ (L + 1)
      set t0' := upd t0 t1 (mergeE r1) ℓ
      have hA' : l2 (t0' - mergeE r0) ^ 2 ≤ 2 * devB y δ L ^ 2 := by
        rw [l2_sub_mergeE_sq t0' r0]
        linarith [pow_le_pow_left₀ (l2_nonneg _) hd0 2]
      have he : t0 - mergeE r0 = (t0' - mergeE r0) + fun o => -((t1 - mergeE r1) o * ℓ o) := by
        funext o
        simp only [t0', upd, Pi.add_apply, Pi.sub_apply]
        ring
      have hd : l2 (t0 - mergeE r0) ≤ l2 (t0' - mergeE r0) + (lam512 L + δ L) *
          l2 (t1 - mergeE r1) := by
        rw [he]
        refine (l2_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [l2_neg, show (fun o => (t1 - mergeE r1) o * ℓ o) = fun o => ℓ o *
            (t1 - mergeE r1) o from
          funext fun o => mul_comm _ _]
        exact l2_mul_le _ _ _ (by positivity) hℓ'
      refine (pow_le_pow_iff_left₀ (l2_nonneg _) (devB_nonneg hy0 δ _) two_ne_zero).1 ?_
      rw [l2_pairF_sq, devB]
      exact dev_step (by positivity) hA' hz (l2_nonneg _) hd
    · obtain ⟨hR0, -, hx0⟩ := key r1 hr1
      obtain ⟨-, P0⟩ := ih0 U0 h.2.1 hU0 _ _ _ _ (isReal_splitE hR0).1 (isReal_splitE hR0).2 X0 hx0
      exact P0.bind fun _ => .pure _ le_rfl
    · linarith

end FalconPrecision.Errors.HopB
