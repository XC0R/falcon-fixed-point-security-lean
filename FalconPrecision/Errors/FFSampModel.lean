/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FxModel
public import FalconPrecision.Errors.FalconProved
public import FalconPrecision.Errors.PathCompose

/-! # An execution model of ffSampling at Falcon-512 and its path budgets

`ffs ρ T t0 t1 t0h t1h` is ffSampling (ePrint 2026/1531 Alg. 8, spec Alg. 11) as an `OracleComp`
over `FalconGame.spec aux CallP`, run on the stored tree `T` in two arithmetics at once: exact (`t0,
t1`, the reference of hop A: exact arithmetic with the stored `ℓ̂`) and fixed point at tag 21 (`t0h,
t1h`, arithmetic `ρ : Arith`). A node splits `t1` (`splitfft`: `halve`, odd half by `mul` with the
split table), recurses on `T1`, merges `ẑ1` (`mergefft`: `mul` with the merge table), computes line
10 `t0' = t0 + (t1 - ẑ1)·ℓ̂` (product by `mul`), splits `t0'`, recurses on `T0` and merges. A leaf
issues two SamplerZ queries `CallP.stored σ̄ t t̄` (Re of the exact and the computed centre) and
returns the sampled integers.

Range checks (`InC`): a node aborts (`none`, `⊥`) unless the computed split inputs `t̄1`, `t̄0'` and
the computed odd merge inputs `ẑ1` of both children satisfy `‖·‖ ≤ 2²¹ - 1`. A fixed-point signer
can run them, and they are functions of the history, identical in the three worlds of Theorem 2. The
proofs need the exact values in `‖·‖ ≤ 2²¹` (`InB`, the range of Lemma 12). They follow from the
checks because the proved errors of the checked values are below the margin `1`: input errors `≤
2⁻¹⁰` (from the budget hypothesis of `ffs_pathS`), line 10 `≤ 25.0001·2⁻¹⁰ + 2⁻²⁰ ≤ 1` (`upd_err`
states the bound `≤ 1`), merge errors `≤ ezU ≤ 1` (`ezU512_le`).

The stored tree is an `FTree`: a tree with every leaf `σ̄ ∈ [σmin, σmax]` (FIPS 206 draft), which
supplies `CallP.stored`'s range, and `‖ℓ̂‖∞ ≤ 24.0001` at the root, `≤ 0.9923` below (`lam512`). The
`ℓ̂` check is added here; it is not in Falcon round 3 or the FIPS 206 draft. Up to the rounding of
the stored tree (not formalised), the root bound is the paper's `γroot = 24` (Alg. 2 l. 14-15, Lemma
7 (12)); the inner bound follows from `γhybrid = 4` (l. 8, §8.5) through Lemma 8 (16), which is
pen-and-paper only (not formalised). Nothing ties the tree to the key `f, F` of `SignModel.Key`.

`ffs` returns the integers `z` (`ilv`) together with `ẑ`. Recovering `z` from the computed FFT form
(invFFT and rounding, which needs merge errors `< 1/2`) is not modelled.

`ffs_pathS`: on every history the per-node relations of `ETree.Hyp` (the premises of `node_l2`)
follow from the model; since they hold for every history and the child budgets depend only on
bounded quantities, the recursion of `run_l2` holds along executions, with path sums of `(t̄ - t)²`.
`ffs_pathN`: at most `2^(L+1)` SamplerZ queries.

`ffsU ρ u R` is the same algorithm with every fixed-point operation at output ulp `u` and range
checks `‖·‖ ≤ R - 1` (`InCR`), exact values in `‖·‖ ≤ R` (`InBR`); `ffs = ffsU ρ 2⁻⁴² 2²¹`. A
`Budget` collects the per-node constants (twiddle error `δ`, split error `r'`, merge constant `c`,
line-10 budgets `W`) with the inequalities the proofs use; `ffs_pathSU` and `ffs_pathNU` are
`ffs_pathS`, `ffs_pathN` for every budget, and `b512` is the tag-21 budget of `ffs`. `ffsU = ffsG ρ
u (‖·‖ ≤ R - 1)` is the instance of `ffsG`, which takes any check on (computed, exact) pairs;
`ffsU_eq_margin`: while the checks pass, every checked computed value is within `1` of its exact
value. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath

namespace FalconPrecision.Errors.FFSamp

/-- A stored Falcon tree of depth `L`: leaves in `[σmin, σmax] = [1.277833697, 1.8205]` (Falcon-512,
spec Table 3.3), `‖ℓ̂‖∞ ≤ lam512 L` at every node (a check added by this model, not part of key
expansion). -/
inductive FTree : ℕ → Type
  | leaf (σ : ℝ) (h : 1277833697 / 10 ^ 9 ≤ σ ∧ σ ≤ 18205 / 10000) : FTree 0
  | node {L : ℕ} (ℓ : Out (L + 1) → ℂ) (h : ∀ o, ‖ℓ o‖ ≤ lam512 L) (T0 T1 : FTree L) : FTree (L + 1)

/-- Output of an ffSampling call of size `2^L`: integer polynomials `z0, z1`, their FFTs (`e0, e1`;
`IsFFT`, proved for every result in `ffs_pathS`) and the computed FFTs (`c0, c1`). -/
structure Samp (L : ℕ) where
  z0 : Fin (2 ^ L) → ℤ
  z1 : Fin (2 ^ L) → ℤ
  e0 : Out L → ℂ
  e1 : Out L → ℂ
  c0 : Out L → ℂ
  c1 : Out L → ℂ

/-- Coefficients of `mergefft(a, b)`: `a` at the even, `b` at the odd indices. -/
def ilv {L : ℕ} (a b : Fin (2 ^ L) → ℤ) : Fin (2 ^ (L + 1)) → ℤ := fun i =>
  if i.1 % 2 = 0 then a ⟨i.1 / 2, by have := i.2; have := pow_succ 2 L; omega⟩
  else b ⟨i.1 / 2, by have := i.2; have := pow_succ 2 L; omega⟩

/-- A leaf's output. -/
def Samp.leaf (z0 z1 : ℤ) : Samp 0 :=
  ⟨fun _ => z0, fun _ => z1, fun _ => z0, fun _ => z1, fun _ => z0, fun _ => z1⟩

/-- The range `R` of exact values. -/
def InBR (R : ℝ) {L : ℕ} (v : Out L → ℂ) : Prop := ∀ o, ‖v o‖ ≤ R

/-- The range check `‖·‖ ≤ R - 1` on computed values. -/
def InCR (R : ℝ) {L : ℕ} (v : Out L → ℂ) : Prop := ∀ o, ‖v o‖ ≤ R - 1

/-- Lemma 12's range at tag 21. -/
def InB {L : ℕ} (v : Out L → ℂ) : Prop := InBR (2 ^ 21) v

/-- The range check on computed values at tag 21. -/
def InC {L : ℕ} (v : Out L → ℂ) : Prop := InCR (2 ^ 21) v

theorem InCR.inBR {R : ℝ} {L : ℕ} {v vh : Out L → ℂ} (h : InCR R vh) (hd : ∀ o, ‖vh o - v o‖ ≤ 1) :
    InBR R v := fun o => by
  have := norm_sub_norm_le (v o) (vh o)
  rw [norm_sub_rev] at this
  linarith [h o, hd o]

theorem InC.inB {L : ℕ} {v vh : Out L → ℂ} (h : InC vh) (hd : ∀ o, ‖vh o - v o‖ ≤ 1) : InB v :=
  InCR.inBR h hd

theorem norm_le_l2 {ι : Type} [Fintype ι] (f : ι → ℂ) (i : ι) : ‖f i‖ ≤ l2 f :=
  Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖f j‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i))

theorem l2_pairF_sq {L : ℕ} (a b : Out L → ℂ) : l2 (pairF a b) ^ 2 = l2 a ^ 2 + l2 b ^ 2 := by
  rw [l2_sq, l2_sq, l2_sq, sum_pairF, ← Finset.sum_add_distrib]; rfl

theorem l2_le_pairF {L : ℕ} (a b : Out L → ℂ) : l2 a ≤ l2 (pairF a b) ∧ l2 b ≤ l2 (pairF a b) := by
  have h := l2_pairF_sq a b
  constructor <;> refine (pow_le_pow_iff_left₀ (l2_nonneg _) (l2_nonneg _) two_ne_zero).1 ?_ <;>
    nlinarith [sq_nonneg (l2 a), sq_nonneg (l2 b)]

/-- `splitfft`, exact. -/
noncomputable def splitE {L : ℕ} (t : Out (L + 1) → ℂ) : (Out L → ℂ) × (Out L → ℂ) :=
  (fun o => (t (o, false) + t (o, true)) / 2,
    fun o => starRingEnd ℂ (zeta L o) / 2 * (t (o, false) - t (o, true)))

/-- `splitfft` at output ulp `u`. -/
noncomputable def splitCU (ρ : Arith) (u : ℝ) {L : ℕ}
    (t : Out (L + 1) → ℂ) : (Out L → ℂ) × (Out L → ℂ) :=
  (fun o => ρ.halve u (t (o, false) + t (o, true)),
    fun o => ρ.mul u (ρ.tws L o) (t (o, false) - t (o, true)))

/-- `splitfft` at tag 21. -/
noncomputable def splitC (ρ : Arith) {L : ℕ} (t : Out (L + 1) → ℂ) : (Out L → ℂ) × (Out L → ℂ) :=
  splitCU ρ (1 / 2 ^ 42) t

/-- `mergefft` of `ẑ`, exact. -/
noncomputable def mergeE {L : ℕ} (s : Samp L) : Out (L + 1) → ℂ :=
    mergeL s.e0 fun o => zeta L o * s.e1 o

/-- `mergefft` of `ẑ` at output ulp `u`. -/
noncomputable def mergeCU (ρ : Arith) (u : ℝ) {L : ℕ} (s : Samp L) : Out (L + 1) → ℂ :=
  mergeL s.c0 fun o => ρ.mul u (ρ.tw L o) (s.c1 o)

/-- `mergefft` of `ẑ` at tag 21. -/
noncomputable def mergeC (ρ : Arith) {L : ℕ} (s : Samp L) : Out (L + 1) → ℂ :=
    mergeCU ρ (1 / 2 ^ 42) s

/-- Line 10, exact: `t0 + (t1 - z)·ℓ̂`. -/
noncomputable def upd {L : ℕ} (t0 t1 z ℓ : Out L → ℂ) : Out L → ℂ :=
    fun o => t0 o + (t1 o - z o) * ℓ o

/-- Line 10 at output ulp `u`. -/
noncomputable def updCU (ρ : Arith) (u : ℝ) {L : ℕ} (t0 t1 z ℓ : Out L → ℂ) : Out L → ℂ :=
  fun o => t0 o + ρ.mul u (t1 o - z o) (ℓ o)

/-- Line 10 at tag 21. -/
noncomputable def updC (ρ : Arith) {L : ℕ} (t0 t1 z ℓ : Out L → ℂ) : Out L → ℂ :=
    updCU ρ (1 / 2 ^ 42) t0 t1 z ℓ

/-- Line 14 at output ulp `u`: `(ẑ0, ẑ1)` from the two children. -/
noncomputable def joinU (ρ : Arith) (u : ℝ) {L : ℕ} (s0 s1 : Samp L) : Samp (L + 1) :=
  ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1, mergeE s0, mergeE s1, mergeCU ρ u s0, mergeCU ρ u s1⟩

/-- Line 14: `(ẑ0, ẑ1)` from the two children. -/
noncomputable def join (ρ : Arith) {L : ℕ} (s0 s1 : Samp L) : Samp (L + 1) :=
    joinU ρ (1 / 2 ^ 42) s0 s1

theorem leaf_range {σ : ℝ} (h : 1277833697 / 10 ^ 9 ≤ σ ∧ σ ≤ 18205 / 10000) :
    12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000 :=
  ⟨by linarith [h.1], by linarith [h.2]⟩

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

open Classical in
/--
**ffSampling** (Alg. 8) in exact and fixed-point arithmetic at output ulp `u`, with a check `chk L
vh v` on every checked pair (computed `vh`, exact `v`): the split inputs `t̄1`, `t̄0'` and the odd
merge inputs `ẑ1` of both children; `none` (`⊥`) when a check fails. -/
noncomputable def ffsG (ρ : Arith) (u : ℝ) (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop) :
    {L : ℕ} → FTree L → (t0 t1 t0h t1h : Out L → ℂ) →
    OracleComp (FalconGame.spec aux Falcon.CallP) (Option (Samp L))
  | _, .leaf σ h, t0, t1, t0h, t1h =>
    (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
      (.inr (Falcon.CallP.stored σ (t0 ()).re (t0h ()).re (leaf_range h)))) : OracleComp _ ℤ) >>=
          fun z0 =>
    (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP)
      (.inr (Falcon.CallP.stored σ (t1 ()).re (t1h ()).re (leaf_range h)))) : OracleComp _ ℤ) >>=
          fun z1 =>
    pure (some (Samp.leaf z0 z1))
  | _, .node ℓ _ T0 T1, t0, t1, t0h, t1h =>
    if chk _ t1h t1 then
      ffsG ρ u chk T1 (splitE t1).1 (splitE t1).2 (splitCU ρ u t1h).1
          (splitCU ρ u t1h).2 >>= fun r1 =>
        r1.elim (pure none) fun s1 =>
          if chk _ s1.c1 s1.e1 ∧ chk _ (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)
              (upd t0 t1 (mergeE s1) ℓ) then
            ffsG ρ u chk T0 (splitE (upd t0 t1 (mergeE s1) ℓ)).1
                (splitE (upd t0 t1 (mergeE s1) ℓ)).2
              (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).1
              (splitCU ρ u (updCU ρ u t0h t1h (mergeCU ρ u s1) ℓ)).2 >>=
              fun r0 => r0.elim (pure none) fun s0 =>
                if chk _ s0.c1 s0.e1 then pure (some (joinU ρ u s0 s1)) else pure none
          else pure none
    else pure none

/-- **ffSampling** (Alg. 8) in exact and fixed-point arithmetic at output ulp `u`, with range checks
`‖·‖ ≤ R - 1` on computed values. -/
noncomputable def ffsU (ρ : Arith) (u R : ℝ) {L : ℕ} (T : FTree L) (t0 t1 t0h t1h : Out L → ℂ) :
    OracleComp (FalconGame.spec aux Falcon.CallP) (Option (Samp L)) :=
  ffsG ρ u (fun _ vh _ => InCR R vh) T t0 t1 t0h t1h

/--
**ffSampling** (Alg. 8) in exact and fixed-point arithmetic at tag 21, with range checks on computed
values. -/
noncomputable def ffs (ρ : Arith) {L : ℕ} (T : FTree L) (t0 t1 t0h t1h : Out L → ℂ) :
    OracleComp (FalconGame.spec aux Falcon.CallP) (Option (Samp L)) :=
  ffsU ρ (1 / 2 ^ 42) (2 ^ 21) T t0 t1 t0h t1h

/-- Squared centre error of a SamplerZ call; auxiliary queries weigh `0`. -/
noncomputable def wS : ιA ⊕ Falcon.CallP → ℝ := Sum.elim (fun _ => 0) fun q => (q.tbar - q.t) ^ 2

/-- One per SamplerZ call. -/
def w1 : ιA ⊕ Falcon.CallP → ℝ := Sum.elim (fun _ => 0) fun _ => 1

/-- The exact values of an output are the FFTs of its integer polynomials. -/
def IsFFT {L : ℕ} (s : Samp L) : Prop :=
  ∀ o, s.e0 o = evalAt (fun i => (s.z0 i : ℂ)) (pt L o) ∧ s.e1 o = evalAt (fun i => (s.z1 i : ℂ))
      (pt L o)

/-- Merge errors of an output within `ezU c`, and `IsFFT`. -/
def InvU (c : ℝ) (L : ℕ) : Option (Samp L) → Prop
  | none => True
  | some s => (l2 (s.c0 - s.e0) ≤ ezU c L ∧ l2 (s.c1 - s.e1) ≤ ezU c L) ∧ IsFFT s

/-- Merge errors of an output within `ezU` at `c = 2.122·2⁻⁴²`, and `IsFFT`. -/
def Inv (L : ℕ) : Option (Samp L) → Prop := InvU (2122 / 1000 / 2 ^ 42) L

theorem ilv_evens {L : ℕ} (a b : Fin (2 ^ L) → ℤ) :
    evens (castC fun i => (ilv a b i : ℂ)) = fun i => (a i : ℂ) := by
  funext i
  simp only [evens, castC, ilv]
  split_ifs with h
  · congr 2; ext; simp
  · simp at h

theorem ilv_odds {L : ℕ} (a b : Fin (2 ^ L) → ℤ) :
    odds (castC fun i => (ilv a b i : ℂ)) = fun i => (b i : ℂ) := by
  funext i
  simp only [odds, castC, ilv]
  split_ifs with h
  · simp at h
  · congr 2; ext; simp; omega

/-- `mergefft` of FFTs is the FFT of the interleaved coefficients. -/
theorem mergeL_ilv {L : ℕ} (a b : Fin (2 ^ L) → ℤ) :
    mergeL (fun o => evalAt (fun i => (a i : ℂ)) (pt L o))
        (fun o => zeta L o * evalAt (fun i => (b i : ℂ))
      (pt L o)) = fun x => evalAt (fun i => (ilv a b i : ℂ)) (pt (L + 1) x) := by
  funext x
  obtain ⟨o, bb⟩ := x
  have h1 := evalAt_split (castC fun i => (ilv a b i : ℂ)) (zeta L o)
  have h2 := evalAt_split (castC fun i => (ilv a b i : ℂ)) (-zeta L o)
  rw [evalAt_castC, ilv_evens, ilv_odds, zeta_sq] at h1
  rw [evalAt_castC, ilv_evens, ilv_odds, neg_sq, zeta_sq] at h2
  cases bb
  · change _ + _ = _; rw [pt_succ]; simpa using h1.symm
  · change _ - _ = _; rw [pt_succ]; simp only [↓reduceIte, h2]; ring

theorem join_fftU (ρ : Arith) (u : ℝ) {L : ℕ} {s0 s1 : Samp L} (h0 : IsFFT s0) (h1 : IsFFT s1) :
    IsFFT (joinU ρ u s0 s1) := by
  have e : ∀ s : Samp L, IsFFT s → mergeE s = fun x => evalAt (fun i => (ilv s.z0 s.z1 i : ℂ))
      (pt (L + 1) x) :=
    fun s hs => by
      rw [← mergeL_ilv]; unfold mergeE; congr 1 <;> funext o
      · exact (hs o).1
      · rw [(hs o).2]
  exact fun x => ⟨congrFun (e s0 h0) x, congrFun (e s1 h1) x⟩

theorem join_fft (ρ : Arith) {L : ℕ} {s0 s1 : Samp L} (h0 : IsFFT s0)
    (h1 : IsFFT s1) : IsFFT (join ρ s0 s1) :=
  join_fftU ρ _ h0 h1

theorem lam512_nonneg (L : ℕ) : 0 ≤ lam512 L := by unfold lam512; split_ifs <;> norm_num

theorem sqrt_two_ulp21 : √2 * (1 / 2 ^ 42) ≤ (141422 / 100000 / 2 ^ 42 : ℝ) :=
  (mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num)

theorem ezU512_le (L : ℕ) (hL : L ≤ 8) : ezU (2122 / 1000 / 2 ^ 42) L ≤ 1 := by
  interval_cases L <;> simp only [ezU, sq512] <;> norm_num

theorem w512_le (L : ℕ) : w512 L ≤ 1 / 2 ^ 20 := by unfold w512; split <;> norm_num

/-- Per-node budgets of `ffsU` at output ulp `u` and range `R` (Falcon-512 tree constants `lam512`,
`nn512`): twiddle tables within `δ`, split errors within `r'` (`halve` and `2δR + √2u`), merge
constant `c ≥ δR + √2u`, line-10 budgets `W L ≥ lam512 L · ezU c (L + 1) + sq512 (L + 1) · √2u`, and
the margins of the range checks (`W L ≤ 2⁻²⁰`, `ezU c L ≤ 1`). -/
structure Budget where
  u : ℝ
  R : ℝ
  δ : ℝ
  r' : ℝ
  c : ℝ
  W : ℕ → ℝ
  hu : 0 < u
  hδ0 : 0 ≤ δ
  hδ : δ ≤ 1 / 2 ^ 63
  hR : 0 ≤ R
  hhalve : √2 * (u / 2) ≤ r'
  hsplit : 2 * δ * R + √2 * u ≤ r'
  hc : δ * R + √2 * u ≤ c
  hW0 : ∀ L, 0 ≤ W L
  hW1 : ∀ L, W L ≤ 1 / 2 ^ 20
  hW : ∀ L, L ≤ 8 → lam512 L * ezU c (L + 1) + sq512 (L + 1) * (√2 * u) ≤ W L
  hez : ∀ L, L ≤ 8 → ezU c L ≤ 1

theorem Budget.r'_nonneg (b : Budget) : 0 ≤ b.r' :=
  (mul_nonneg (Real.sqrt_nonneg _) (half_pos b.hu).le).trans b.hhalve

theorem Budget.ulp_nonneg (b : Budget) : 0 ≤ √2 * b.u := mul_nonneg (Real.sqrt_nonneg _) b.hu.le

/-- The tag-21 budget of `ffs` (ePrint 2026/1531 Table 4). -/
noncomputable def b512 : Budget where
  u := 1 / 2 ^ 42
  R := 2 ^ 21
  δ := 7072 / 10000 / 2 ^ 63
  r' := 29 / 10 / 2 ^ 42
  c := 2122 / 1000 / 2 ^ 42
  W := w512
  hu := by positivity
  hδ0 := by positivity
  hδ := by norm_num
  hR := by positivity
  hhalve := (mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num)
  hsplit := by linarith [sqrt_two_ulp21, split512]
  hc := by linarith [sqrt_two_ulp21]
  hW0 := w512_nonneg
  hW1 := w512_le
  hW L hL := by
    have h := ez512 L hL
    have hX : (0 : ℝ) ≤ 2 ^ 22 * ((if L = 8 then 2 ^ 5 else 1) * (7072 / 10000) / 2 ^ 63) := by
      split_ifs <;> positivity
    have hs := mul_le_mul_of_nonneg_left (by linarith [sqrt_two_ulp21] : √2 * (1 / 2 ^ 42) ≤
      2 ^ 22 * ((if L = 8 then 2 ^ 5 else 1) * (7072 / 10000) / 2 ^ 63) + 141422 / 100000 / 2 ^ 42)
      ((Real.sqrt_nonneg _).trans (sqrt_pow_le (L + 1)))
    linarith
  hez := ezU512_le

/-- Split relations of `ETree.Hyp` at one slot, for a budget `b`. -/
theorem split_relU (b : Budget) (ρ : Arith)
    (htws : ∀ L o, ‖ρ.tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ b.δ) {L : ℕ}
        (t th : Out (L + 1) → ℂ)
    (hB : InBR b.R t) (o : Out L) :
    ‖((splitCU ρ b.u th).1 - (splitE t).1) o -
      ((th (o, false) - t (o, false)) + (th (o, true) - t (o, true))) / 2‖ ≤ b.r' ∧
    ‖((splitCU ρ b.u th).2 - (splitE t).2) o -
      ρ.tws L o * ((th (o, false) - t (o, false)) - (th (o, true) - t (o, true)))‖ ≤ b.r' := by
  constructor
  · have e : ((splitCU ρ b.u th).1 - (splitE t).1) o -
        ((th (o, false) - t (o, false)) + (th (o, true) - t (o, true))) / 2 =
        ρ.halve b.u (th (o, false) + th (o, true)) - (th (o, false) + th (o, true)) / 2 := by
      simp only [splitCU, splitE, Pi.sub_apply]; ring
    rw [e]
    exact (ρ.halve_err b.hu _).trans b.hhalve
  · set c := ρ.tws L o
    have e : ((splitCU ρ b.u th).2 - (splitE t).2) o -
        c * ((th (o, false) - t (o, false)) - (th (o, true) - t (o, true))) =
        (c * (th (o, false) - th (o, true)) +
          (ρ.mul b.u c (th (o, false) - th (o, true)) - c * (th (o, false) - th (o, true))) -
          starRingEnd ℂ (zeta L o) / 2 * (t (o, false) - t (o, true))) -
        c * ((th (o, false) - t (o, false)) - (th (o, true) - t (o, true))) := by
      simp only [splitCU, splitE, Pi.sub_apply, c]; ring
    rw [e]
    exact (split_budget _ _ _ _ c (zeta L o) _ _ _ _ (hB _) (hB _) (htws L o)
      (ρ.mul_err b.hu _ _)).trans b.hsplit

/-- The line-10 term `w` of `ETree.Hyp` is within `b.W L`. -/
theorem w_boundU (b : Budget) (ρ : Arith) {L : ℕ} (hL : L ≤ 8) (ℓ : Out (L + 1) → ℂ)
    (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L) (t0 t1 t0h t1h z zh : Out (L + 1) → ℂ)
    (hz : l2 (zh - z) ≤ ezU b.c (L + 1)) :
    l2 (updCU ρ b.u t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)) ≤ b.W L := by
  have hw := w_l2 L (fun o => ρ.mul b.u (t1h o - zh o) (ℓ o) - (t1h o - zh o) * ℓ o) ℓ (zh - z) 0 0
    (lam512 L) _ 0 0 _ (lam512_nonneg L) le_rfl b.ulp_nonneg le_rfl
    (fun o => ρ.mul_err b.hu _ _) hℓ hz (fun _ => by simp) (fun _ => by simp)
  have e : updCU ρ b.u t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1) =
      fun o => ρ.mul b.u (t1h o - zh o) (ℓ o) - (t1h o - zh o) * ℓ o - ℓ o * (zh - z) o +
        (0 : Out (L + 1) → ℂ) o * (0 : Out (L + 1) → ℂ) o := by
    funext o; simp only [updCU, upd, Pi.sub_apply, Pi.mul_apply, Pi.zero_apply]; ring
  rw [e]
  simp only [mul_zero, zero_add] at hw
  linarith [b.hW L hL, mul_le_mul_of_nonneg_right (sqrt_pow_le (L + 1)) b.ulp_nonneg]

/-- Merge errors of `ẑ` propagate within `ezU b.c`. -/
theorem merge_invU (b : Budget) (ρ : Arith) (htw : ∀ L o, ‖ρ.tw L o - zeta L o‖ ≤ b.δ) {L : ℕ}
    (s : Samp L)
    (hs : InvU b.c L (some s))
        (hB : InBR b.R s.e1) : l2 (mergeCU ρ b.u s - mergeE s) ≤ ezU b.c (L + 1) := by
  have h :=
      merge_l2 L s.e0 s.e1 s.c0 s.c1 (zeta L) (ρ.tw L) (fun o => ρ.mul b.u (ρ.tw L o) (s.c1 o)) b.δ
    (√2 * b.u) b.R _ (norm_zeta L)
        (htw L) b.ulp_nonneg b.hR (fun o => ρ.mul_err b.hu _ _) hB hs.1.1 hs.1.2
  have hE0 : 0 ≤ ezU b.c L := (Real.sqrt_nonneg _).trans hs.1.1
  have h1 : 2 * (1 + b.δ) * ezU b.c L ≤ 2 * (1 + 1 / 2 ^ 63) * ezU b.c L :=
    mul_le_mul_of_nonneg_right (by linarith [b.hδ]) hE0
  have hd : 0 ≤ b.δ * b.R + √2 * b.u := add_nonneg (mul_nonneg b.hδ0 b.hR) b.ulp_nonneg
  have h2 : √2 * (√(2 ^ L) * (b.δ * b.R + √2 * b.u)) ≤ 141422 / 100000 * (sq512 L * b.c) :=
    mul_le_mul sqrt_two_le
        (mul_le_mul (sqrt_pow_le L) b.hc hd ((Real.sqrt_nonneg _).trans (sqrt_pow_le L)))
      (mul_nonneg (Real.sqrt_nonneg _) hd) (by norm_num)
  refine h.trans ?_
  rw [ezU]
  linarith

/-- `√2(1/2 + δ)` at `δ = 0.7072·2⁻⁶³`. -/
theorem K512_nonneg : 0 ≤ √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63 : ℝ) := by positivity

/-- **Node bound** for a budget `b`. Both children's input errors, from `node_l2`. -/
theorem node_quadU (b : Budget) (ρ : Arith)
    (htws : ∀ L o, ‖ρ.tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ b.δ) {L : ℕ} (ℓ : Out (L + 1) → ℂ)
    (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L) (t0 t1 t0h t1h t0' t0h' : Out (L + 1) → ℂ) (hB1 : InBR b.R t1)
    (hB0 : InBR b.R t0') (hw : l2 (t0h' - t0' - (t0h - t0) - ℓ * (t1h - t1)) ≤ b.W L) (e : ℝ)
    (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) :
    l2 (pairF ((splitCU ρ b.u t1h).1 - (splitE t1).1) ((splitCU ρ b.u t1h).2 - (splitE t1).2)) ^ 2 +
      l2 (pairF ((splitCU ρ b.u t0h').1 - (splitE t0').1)
          ((splitCU ρ b.u t0h').2 - (splitE t0').2)) ^ 2 ≤
      (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + b.W L) + 2 * √(2 ^ L) * b.r') ^ 2 := by
  obtain ⟨hN0, hN1, hN⟩ := hyp512 L
  set w := t0h' - t0' - (t0h - t0) - ℓ * (t1h - t1)
  have hy : ∀ p, (t0h - t0 + ℓ * (t1h - t1) + w) p = t0h' p - t0' p := fun p => by
    simp only [w, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring
  have h := node_l2 L (lam512 L) (nn512 L) (7072 / 10000 / 2 ^ 63) b.r' hN0 hN1 hN
    (by positivity) b.r'_nonneg (t0h - t0) (t1h - t1) ℓ w hℓ (ρ.tws L) (ρ.norm_tws L) _ _ _ _
    (fun o => (split_relU b ρ htws t1 t1h hB1 o).1) (fun o => (split_relU b ρ htws t1 t1h hB1 o).2)
    (fun o => by rw [hy (o, false), hy (o, true)]; exact (split_relU b ρ htws t0' t0h' hB0 o).1)
    (fun o => by rw [hy (o, false), hy (o, true)]; exact (split_relU b ρ htws t0' t0h' hB0 o).2)
  rw [← l2_quad_sq]
  refine pow_le_pow_left₀ (l2_nonneg _) (h.trans ?_) 2
  have := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he hN0) hw) K512_nonneg
  linarith

/-- The first child's input error alone (second child replaced by its exact relations), for a budget
`b`. -/
theorem node_a1U (b : Budget) (ρ : Arith)
    (htws : ∀ L o, ‖ρ.tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ b.δ) {L : ℕ} (ℓ : Out (L + 1) → ℂ)
    (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L) (t0 t1 t0h t1h : Out (L + 1) → ℂ) (hB1 : InBR b.R t1) (e : ℝ)
    (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) :
    l2 (pairF ((splitCU ρ b.u t1h).1 - (splitE t1).1) ((splitCU ρ b.u t1h).2 - (splitE t1).2)) ≤
      √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + b.W L) + 2 * √(2 ^ L) * b.r' := by
  obtain ⟨hN0, hN1, hN⟩ := hyp512 L
  set y := t0h - t0 + ℓ * (t1h - t1) + 0
  have h := node_l2 L (lam512 L) (nn512 L) (7072 / 10000 / 2 ^ 63) b.r' hN0 hN1 hN
    (by positivity) b.r'_nonneg (t0h - t0) (t1h - t1) ℓ 0 hℓ (ρ.tws L) (ρ.norm_tws L) _ _
    (fun o => (y (o, false) + y (o, true)) / 2) (fun o => ρ.tws L o * (y (o, false) - y (o, true)))
    (fun o => (split_relU b ρ htws t1 t1h hB1 o).1) (fun o => (split_relU b ρ htws t1 t1h hB1 o).2)
    (fun o => by rw [sub_self, norm_zero]; exact b.r'_nonneg)
    (fun o => by rw [sub_self, norm_zero]; exact b.r'_nonneg)
  have h0 : l2 (0 : Out (L + 1) → ℂ) ≤ b.W L := by
    simpa [l2] using b.hW0 L
  refine le_trans ?_ (h.trans ?_)
  · refine (pow_le_pow_iff_left₀ (l2_nonneg _) (l2_nonneg _) two_ne_zero).1 ?_
    rw [l2_quad_sq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he hN0) h0) K512_nonneg
    linarith

/-- Budget step: `(A a₁ + C)² + (A√(R² - a₁²) + C)² ≤ (AR + √2 C)²` (Minkowski). -/
theorem budget_step (A C a1 R : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (ha1 : 0 ≤ a1) (h : a1 ≤ R) :
    (A * a1 + C) ^ 2 + (A * √(R ^ 2 - a1 ^ 2) + C) ^ 2 ≤ (A * R + √2 * C) ^ 2 := by
  set s := √(R ^ 2 - a1 ^ 2)
  have hs : s ^ 2 = R ^ 2 - a1 ^ 2 := Real.sq_sqrt (by nlinarith)
  have hm := mink2 (A * a1) C (A * s) C
  have e1 : √((A * a1) ^ 2 + (A * s) ^ 2) = A * R := by
    rw [show (A * a1) ^ 2 + (A * s) ^ 2 =
        (A * R) ^ 2 by rw [mul_pow, mul_pow, mul_pow, ← mul_add, hs]; ring]
    exact Real.sqrt_sq (mul_nonneg hA (ha1.trans h))
  have e2 : √(C ^ 2 + C ^ 2) = √2 * C := by
    rw [show C ^ 2 + C ^ 2 = 2 * C ^ 2 by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq hC]
  rw [e1, e2] at hm
  rw [← Real.sq_sqrt (by positivity : 0 ≤ (A * a1 + C) ^ 2 + (A * s + C) ^ 2)]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hm 2

theorem coef_succU (W : ℕ → ℝ) (r' K e : ℝ) (L : ℕ) :
    coefA nn512 K (L + 1) * e + coefC nn512 W K r' (L + 1) =
      coefA nn512 K L * (K * (nn512 L * e + W L) + 2 * √(2 ^ L) * r') + √2 *
          coefC nn512 W K r' L := by
  simp only [coefA, coefC]; ring

theorem coef_succ (K e : ℝ) (L : ℕ) :
    coefA nn512 K (L + 1) * e + coefC nn512 w512 K (29 / 10 / 2 ^ 42) (L + 1) =
      coefA nn512 K L * (K * (nn512 L * e + w512 L) + 2 * √(2 ^ L) * (29 / 10 / 2 ^ 42)) +
        √2 * coefC nn512 w512 K (29 / 10 / 2 ^ 42) L :=
  coef_succU w512 _ K e L

theorem one_le_coefA512 : ∀ L, 1 ≤ coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L
  | 0 => by simp [coefA]
  | L + 1 => by
    have h2 : (14142 / 10000 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
    have hN : 16125 / 10000 ≤ nn512 L := by unfold nn512; split_ifs <;> norm_num
    have hK : 1 ≤ √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * nn512 L := by nlinarith
    rw [coefA, mul_assoc]
    nlinarith [one_le_coefA512 L]

/-- Nonnegative coefficients for a budget `b`. -/
theorem coef_nonnegU (b : Budget) (L : ℕ) :
    0 ≤ coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L ∧
      0 ≤ coefC nn512 b.W (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) b.r' L :=
  ⟨(coefA_mono nn512 (fun L => (hyp512 L).1) _ _ K512_nonneg le_rfl L).1,
    (coefC_le nn512 b.W (fun L => (hyp512 L).1) b.hW0 _ _ b.r' √2
        (fun L => √(2 ^ L)) K512_nonneg le_rfl
      b.r'_nonneg le_rfl (fun _ => le_rfl) L).1⟩

/-- The line-10 output `t̄0'` is within `1` of `t0'` in ℓ2, for a budget `b`. -/
theorem upd_errU (b : Budget) (ρ : Arith) {L : ℕ} (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h z zh : Out (L + 1) → ℂ) (e : ℝ) (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e)
    (he1 : e ≤ 1 / 2 ^ 10)
    (hw : l2 (updCU ρ b.u t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)) ≤ b.W L) :
    l2 (updCU ρ b.u t0h t1h zh ℓ - upd t0 t1 z ℓ) ≤ 1 := by
  set w := updCU ρ b.u t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)
  have e' : updCU ρ b.u t0h t1h zh ℓ - upd t0 t1 z ℓ = w + (t0h - t0) + fun o => ℓ o *
      (t1h - t1) o := by
    funext o; simp only [w, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring
  rw [e']
  have hd := l2_le_pairF (t0h - t0) (t1h - t1)
  have hm := (l2_mul_le ℓ (t1h - t1) _ (lam512_nonneg L) hℓ).trans
    (mul_le_mul_of_nonneg_left (hd.2.trans he) (lam512_nonneg L))
  have hl : lam512 L * e ≤ 240001 / 10000 * (1 / 2 ^ 10) :=
    mul_le_mul (by unfold lam512; split_ifs <;> norm_num) he1 ((l2_nonneg _).trans he) (by norm_num)
  linarith
      [l2_add_le (w + (t0h - t0)) (fun o => ℓ o * (t1h - t1) o), l2_add_le w (t0h - t0), b.hW1 L]

/--
**One node of `ffsU` along executions** for a budget `b`: children with budgets `(A e + C)²` give
`(A R + √2 C)²`. The budget bound `≤ 2⁻¹⁰` gives the margin of the range checks. -/
theorem node_stepU (b : Budget) (ρ : Arith) (htw : ∀ L o, ‖ρ.tw L o - zeta L o‖ ≤ b.δ)
    (htws : ∀ L o, ‖ρ.tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ b.δ) {L : ℕ} (hL : L ≤ 8)
    (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L) (T0 T1 : FTree L) (A C : ℝ) (hA : 0 ≤ A)
        (hC : 0 ≤ C)
    (ih0 : ∀ (t0 t1 t0h t1h : Out L → ℂ) (e : ℝ), l2 (pairF (t0h - t0) (t1h - t1)) ≤ e →
      A * e + C ≤ 1 / 2 ^ 10 →
      PathSumP wS (InvU b.c L) (ffsU (aux := aux) ρ b.u b.R T0 t0 t1 t0h t1h) ((A * e + C) ^ 2))
    (ih1 : ∀ (t0 t1 t0h t1h : Out L → ℂ) (e : ℝ), l2 (pairF (t0h - t0) (t1h - t1)) ≤ e →
      A * e + C ≤ 1 / 2 ^ 10 →
      PathSumP wS (InvU b.c L) (ffsU (aux := aux) ρ b.u b.R T1 t0 t1 t0h t1h) ((A * e + C) ^ 2))
    (t0 t1 t0h t1h : Out (L + 1) → ℂ) (e : ℝ) (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e)
    (he1 : e ≤ 1 / 2 ^ 10)
    (hΦ : A * (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + b.W L) + 2 * √(2 ^ L) * b.r') +
      √2 * C ≤ 1 / 2 ^ 10) :
    PathSumP wS (InvU b.c (L + 1)) (ffsU (aux := aux) ρ b.u b.R (.node ℓ hℓ T0 T1) t0 t1 t0h t1h)
      ((A * (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + b.W L) + 2 * √(2 ^ L) * b.r') +
        √2 * C) ^ 2) := by
  generalize hR : √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + b.W L) + 2 * √(2 ^ L) *
      b.r' = R
    at hΦ ⊢
  have hC2 : C ≤ √2 * C := le_mul_of_one_le_left hC (Real.le_sqrt_of_sq_le (by norm_num))
  have hz : ∀ s : Samp L, InvU b.c L (some s) → InCR b.R s.c1 → InBR b.R s.e1 := fun s hs hc =>
    InCR.inBR hc fun o => (norm_le_l2 (s.c1 - s.e1) o).trans (hs.1.2.trans (b.hez L hL))
  simp only [ffsU, ffsG]
  split_ifs with hc1
  swap
  · exact .pure _ (sq_nonneg _) trivial
  have hb1 : InBR b.R t1 := InCR.inBR hc1 fun o => (norm_le_l2 (t1h - t1) o).trans
    (((l2_le_pairF _ _).2.trans he).trans (he1.trans (by norm_num)))
  obtain ⟨a1, ha⟩ : ∃ a1, l2 (pairF ((splitCU ρ b.u t1h).1 - (splitE t1).1)
      ((splitCU ρ b.u t1h).2 - (splitE t1).2)) = a1 := ⟨_, rfl⟩
  have ha1 := (node_a1U b ρ htws ℓ hℓ t0 t1 t0h t1h hb1 e he).trans_eq hR
  rw [ha] at ha1
  have ha0 : 0 ≤ a1 := ha ▸ l2_nonneg _
  have hbud := budget_step A C a1 R hA hC ha0 ha1
  refine (PathSumP.bind (T := (A * √(R ^ 2 - a1 ^ 2) + C) ^ 2 + 0) (ih1 _ _ _ _ a1 ha.le
    (by linarith [mul_le_mul_of_nonneg_left ha1 hA])) fun r1 hr1 => ?_).weaken (by linarith [hbud])
  cases r1 with
  | none => exact .pure _ (add_nonneg (sq_nonneg _) le_rfl) trivial
  | some s1 =>
    simp only [Option.elim]
    split_ifs with hb
    swap
    · exact .pure _ (add_nonneg (sq_nonneg _) le_rfl) trivial
    have hw := w_boundU b ρ hL ℓ hℓ t0 t1 t0h t1h _ _ (merge_invU b ρ htw s1 hr1 (hz s1 hr1 hb.1))
    have hb0 := InCR.inBR hb.2 fun o => (norm_le_l2 _ o).trans
      (upd_errU b ρ ℓ hℓ t0 t1 t0h t1h _ _ e he he1 hw)
    have hq := node_quadU b ρ htws ℓ hℓ t0 t1 t0h t1h _ _ hb1 hb0 hw e he
    rw [ha, hR] at hq
    have hs := Real.sqrt_le_sqrt (by nlinarith : R ^ 2 - a1 ^ 2 ≤ R ^ 2)
    rw [Real.sqrt_sq (ha0.trans ha1)] at hs
    refine PathSumP.bind (ih0 _ _ _ _ _ (Real.le_sqrt_of_sq_le (by linarith [hq]))
      (by linarith [mul_le_mul_of_nonneg_left hs hA])) fun r0 hr0 => ?_
    cases r0 with
    | none => exact .pure _ le_rfl trivial
    | some s0 =>
      dsimp only
      split_ifs with hc0
      · exact .pure _ le_rfl ⟨⟨merge_invU b ρ htw s0 hr0 (hz s0 hr0 hc0),
          merge_invU b ρ htw s1 hr1 (hz s1 hr1 hb.1)⟩, join_fftU ρ b.u hr0.2 hr1.2⟩
      · exact .pure _ le_rfl trivial

/--
**Path budget of one `ffsU` call** for a budget `b` (hop A). Input errors of ℓ2 norm `≤ e` with `Ā_L
e + C̄_L ≤ 2⁻¹⁰` give, along every execution, `Σ (t̄ - t)² ≤ (Ā_L e + C̄_L)²` over the SamplerZ
queries; every returned `ẑ` has merge errors within `ezU b.c`. -/
theorem ffs_pathSU (b : Budget) (ρ : Arith) (htw : ∀ L o, ‖ρ.tw L o - zeta L o‖ ≤ b.δ)
    (htws : ∀ L o, ‖ρ.tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ b.δ) {L : ℕ} (T : FTree L) :
    L ≤ 9 → ∀ (t0 t1 t0h t1h : Out L → ℂ) (e : ℝ), l2 (pairF (t0h - t0) (t1h - t1)) ≤ e →
    coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L * e +
      coefC nn512 b.W (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) b.r' L ≤ 1 / 2 ^ 10 →
    PathSumP wS (InvU b.c L) (ffsU (aux := aux) ρ b.u b.R T t0 t1 t0h t1h)
      ((coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L * e +
        coefC nn512 b.W (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) b.r' L) ^ 2) := by
  induction T with
  | leaf σ h =>
    intro _ t0 t1 t0h t1h e he _
    have hx : l2 (pairF (t0h - t0) (t1h - t1)) ^ 2 = ‖t0h () - t0 ()‖ ^ 2 + ‖t1h () - t1 ()‖ ^ 2 :=
      l2_pairF_leaf _ _
    have hre : ∀ a b : ℂ, (a.re - b.re) ^ 2 ≤ ‖a - b‖ ^ 2 := fun a b => by
      rw [← Complex.sub_re]
      exact sq_le_sq' (abs_le.1 (Complex.abs_re_le_norm _)).1
          (abs_le.1 (Complex.abs_re_le_norm _)).2
    have h0 := l2_nonneg (pairF (t0h - t0) (t1h - t1))
    simp only [ffsU, ffsG, coefA, coefC]
    refine .query_bind _ _ fun z0 => .query_bind _ _ fun z1 => .pure _ ?_ ?_
    · change 0 ≤ (1 * e + 0) ^ 2 - ((t0h ()).re - (t0 ()).re) ^ 2 - ((t1h ()).re - (t1 ()).re) ^ 2
      nlinarith [hre (t0h ()) (t0 ()), hre (t1h ()) (t1 ()), mul_le_mul he he h0 (h0.trans he)]
    · exact ⟨⟨by simp [Samp.leaf, l2, ezU], by simp [Samp.leaf, l2, ezU]⟩,
        fun _ => ⟨by simp [Samp.leaf, evalAt], by simp [Samp.leaf, evalAt]⟩⟩
  | @node L ℓ hℓ T0 T1 ih0 ih1 =>
    intro hL t0 t1 t0h t1h e he hΦ
    have he1 : e ≤ 1 / 2 ^ 10 := by
      linarith [mul_le_mul_of_nonneg_right (one_le_coefA512 (L + 1)) ((l2_nonneg _).trans he),
        (coef_nonnegU b (L + 1)).2]
    rw [coef_succU] at hΦ ⊢
    exact node_stepU b ρ htw htws (by omega) ℓ hℓ T0 T1 _ _ (coef_nonnegU b L).1
        (coef_nonnegU b L).2
      (ih0 (by omega)) (ih1 (by omega)) t0 t1 t0h t1h e he he1 hΦ

/--
**SamplerZ queries of one `ffsG` call**: at most `2^(L+1)` along every execution, for every check.
-/
theorem ffs_pathNG (ρ : Arith) (u : ℝ) (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop) {L : ℕ}
    (T : FTree L) (t0 t1 t0h t1h : Out L → ℂ) :
    PathSum w1 (ffsG (aux := aux) ρ u chk T t0 t1 t0h t1h) (2 ^ (L + 1)) := by
  induction T with
  | leaf σ h =>
    simp only [ffsG]
    exact .query_bind _ _ fun _ => .query_bind _ _ fun _ =>
      .pure _ (by change (0 : ℝ) ≤ 2 ^ (0 + 1) - 1 - 1; norm_num)
  | @node L ℓ hℓ T0 T1 ih0 ih1 =>
    simp only [ffsG]
    split_ifs
    · refine (PathSum.bind (ih1 _ _ _ _) (T := 2 ^ (L + 1) + 0) fun r1 => ?_).weaken
        (le_of_eq (by ring))
      cases r1 with
      | none => exact .pure _ (by positivity)
      | some s1 =>
        simp only [Option.elim]
        split_ifs
        · refine PathSum.bind (ih0 _ _ _ _) fun r0 => ?_
          cases r0 with
          | none => exact .pure _ le_rfl
          | some s0 => dsimp only; split_ifs <;> exact .pure _ le_rfl
        · exact .pure _ (by positivity)
    · exact .pure _ (by positivity)

/-- **SamplerZ queries of one `ffsU` call**: at most `2^(L+1)` along every execution. -/
theorem ffs_pathNU (ρ : Arith) (u R : ℝ) {L : ℕ} (T : FTree L) (t0 t1 t0h t1h : Out L → ℂ) :
    PathSum w1 (ffsU (aux := aux) ρ u R T t0 t1 t0h t1h) (2 ^ (L + 1)) :=
  ffs_pathNG ρ u _ T t0 t1 t0h t1h

/-- The range check `‖vh‖ ≤ R - 1`, required when `vh` is within `1` of `v` slotwise. -/
def chkM (R : ℝ) (L : ℕ) (vh v : Out L → ℂ) : Prop := (∀ o, ‖vh o - v o‖ ≤ 1) → InCR R vh

/-- Exact values in `‖·‖ ≤ R - 2` pass `chkM R`. -/
theorem InBR.chkM {R : ℝ} {L : ℕ} {v vh : Out L → ℂ} (h : InBR (R - 2) v) : chkM R L vh v :=
    fun hd o => by
  linarith [h o, hd o, norm_sub_norm_le (vh o) (v o)]

/--
**Check margins of `ffsU`** for a budget `b`. While the earlier checks pass, every checked computed
value (`t̄1`, `t̄0'`, the odd merge inputs `ẑ1` of both children) is within `1` of its exact value
slotwise: replacing every range check `‖vh‖ ≤ R - 1` by `chkM R` (the same check, required only
within that margin) does not change the computation. With `InBR.chkM`, exact checked values in `‖·‖
≤ R - 2` pass every check of the right side. -/
theorem ffsU_eq_margin (b : Budget) (ρ : Arith) (htw : ∀ L o, ‖ρ.tw L o - zeta L o‖ ≤ b.δ)
    (htws : ∀ L o, ‖ρ.tws L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ b.δ) {L : ℕ} (T : FTree L) :
    L ≤ 9 → ∀ (t0 t1 t0h t1h : Out L → ℂ) (e : ℝ), l2 (pairF (t0h - t0) (t1h - t1)) ≤ e →
    coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L * e +
      coefC nn512 b.W (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) b.r' L ≤ 1 / 2 ^ 10 →
    ffsU (aux := aux) ρ b.u b.R T t0 t1 t0h t1h = ffsG ρ b.u (chkM b.R) T t0 t1 t0h t1h := by
  induction T with
  | leaf σ h => intros; rfl
  | @node L ℓ hℓ T0 T1 ih0 ih1 =>
    intro hL t0 t1 t0h t1h e he hΦ
    have he1 : e ≤ 1 / 2 ^ 10 := by
      linarith [mul_le_mul_of_nonneg_right (one_le_coefA512 (L + 1)) ((l2_nonneg _).trans he),
        (coef_nonnegU b (L + 1)).2]
    rw [coef_succU] at hΦ
    obtain ⟨hA, hC⟩ := coef_nonnegU b L
    set A := coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L
    set C := coefC nn512 b.W (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) b.r' L
    set R' :=
        √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + b.W L) + 2 * √(2 ^ L) * b.r' with hR'
    have hC2 : C ≤ √2 * C := le_mul_of_one_le_left hC (Real.le_sqrt_of_sq_le (by norm_num))
    have hbud : ∀ a, a ≤ R' → A * a + C ≤ 1 / 2 ^ 10 := fun a ha => by
      linarith [mul_le_mul_of_nonneg_left ha hA]
    have hz : ∀ s : Samp L, InvU b.c L (some s) → ∀ o, ‖s.c1 o - s.e1 o‖ ≤ 1 := fun s hs o =>
      (norm_le_l2 (s.c1 - s.e1) o).trans (hs.1.2.trans (b.hez L (by omega)))
    have hm1 : ∀ o, ‖t1h o - t1 o‖ ≤ 1 := fun o => (norm_le_l2 (t1h - t1) o).trans
      (((l2_le_pairF _ _).2.trans he).trans (he1.trans (by norm_num)))
    simp only [ffsU, ffsG]
    split_ifs with hc1 hc1' hc1''
    · have hb1 : InBR b.R t1 := InCR.inBR hc1 hm1
      have ha1 := node_a1U b ρ htws ℓ hℓ t0 t1 t0h t1h hb1 e he
      have h1 := ih1 (by omega) _ _ _ _ _ le_rfl (hbud _ ha1)
      have p1 := ffs_pathSU (aux := aux) b ρ htw htws T1 (by omega) _ _ _ _ _ le_rfl (hbud _ ha1)
      rw [← h1]
      refine p1.bind_congr fun r1 hr1 => ?_
      cases r1 with
      | none => rfl
      | some s1 =>
        simp only [Option.elim]
        have hs1 := hz s1 hr1
        have hmu : InCR b.R s1.c1 → ∀ o, ‖updCU ρ b.u t0h t1h (mergeCU ρ b.u s1) ℓ o -
            upd t0 t1 (mergeE s1) ℓ o‖ ≤ 1 := fun hc o => (norm_le_l2 _ o).trans
          (upd_errU b ρ ℓ hℓ t0 t1 t0h t1h _ _ e he he1
              (w_boundU b ρ (by omega) ℓ hℓ t0 t1 t0h t1h _ _
            (merge_invU b ρ htw s1 hr1 (InCR.inBR hc hs1))))
        split_ifs with hc hc' hc''
        · have hw := w_boundU b ρ (by omega) ℓ hℓ t0 t1 t0h t1h _ _
            (merge_invU b ρ htw s1 hr1 (InCR.inBR hc.1 hs1))
          have hb0 : InBR b.R (upd t0 t1 (mergeE s1) ℓ) := InCR.inBR hc.2 (hmu hc.1)
          have hq := node_quadU b ρ htws ℓ hℓ t0 t1 t0h t1h _ _ hb1 hb0 hw e he
          rw [← hR'] at hq
          have hR0 : 0 ≤ R' := (l2_nonneg _).trans ha1
          have ha0 : l2 (pairF ((splitCU ρ b.u (updCU ρ b.u t0h t1h (mergeCU ρ b.u s1) ℓ)).1 -
              (splitE (upd t0 t1 (mergeE s1) ℓ)).1)
                  ((splitCU ρ b.u (updCU ρ b.u t0h t1h (mergeCU ρ b.u s1) ℓ)).2 -
              (splitE (upd t0 t1 (mergeE s1) ℓ)).2)) ≤ R' :=
            (pow_le_pow_iff_left₀ (l2_nonneg _) hR0 two_ne_zero).1
              (by nlinarith [sq_nonneg (l2 (pairF ((splitCU ρ b.u t1h).1 - (splitE t1).1)
                ((splitCU ρ b.u t1h).2 - (splitE t1).2)))])
          have h0 := ih0 (by omega) _ _ _ _ _ le_rfl (hbud _ ha0)
          have p0 :=
              ffs_pathSU (aux := aux) b ρ htw htws T0 (by omega) _ _ _ _ _ le_rfl (hbud _ ha0)
          rw [← h0]
          refine p0.bind_congr fun r0 hr0 => ?_
          cases r0 with
          | none => rfl
          | some s0 =>
            dsimp only
            have hs0 := hz s0 hr0
            split_ifs with hd hd' hd''
            · rfl
            · exact absurd (fun _ => hd) hd'
            · exact absurd (hd'' hs0) hd
            · rfl
        · exact absurd ⟨fun _ => hc.1, fun _ => hc.2⟩ hc'
        · exact absurd ⟨hc''.1 hs1, hc''.2 (hmu (hc''.1 hs1))⟩ hc
        · rfl
    · exact absurd (fun _ => hc1) hc1'
    · exact absurd (hc1'' hm1) hc1
    · rfl

/-- Split relations of `ETree.Hyp` at one slot. -/
theorem split_rel (ρ : Arith) {L : ℕ} (t th : Out (L + 1) → ℂ) (hB : InB t) (o : Out L) :
    ‖((splitC ρ th).1 - (splitE t).1) o -
      ((th (o, false) - t (o, false)) + (th (o, true) - t (o, true))) / 2‖ ≤ 29 / 10 / 2 ^ 42 ∧
    ‖((splitC ρ th).2 - (splitE t).2) o -
      ρ.tws L o * ((th (o, false) - t (o, false)) - (th (o, true) - t (o, true)))‖ ≤ 29 / 10 /
          2 ^ 42 :=
  split_relU b512 ρ ρ.tws_err t th hB o

/-- The line-10 term `w` of `ETree.Hyp` is within `w512 L`. -/
theorem w_bound (ρ : Arith) {L : ℕ} (hL : L ≤ 8) (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h z zh : Out (L + 1) → ℂ) (hz : l2 (zh - z) ≤ ezU (2122 / 1000 / 2 ^ 42) (L + 1)) :
    l2 (updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)) ≤ w512 L :=
  w_boundU b512 ρ hL ℓ hℓ t0 t1 t0h t1h z zh hz

/-- Merge errors of `ẑ` propagate within `ezU`. -/
theorem merge_inv (ρ : Arith) {L : ℕ} (s : Samp L) (hs : Inv L (some s)) (hB : InB s.e1) :
    l2 (mergeC ρ s - mergeE s) ≤ ezU (2122 / 1000 / 2 ^ 42) (L + 1) :=
  merge_invU b512 ρ ρ.tw_err s hs hB

/-- **Node bound.** Both children's input errors, from `node_l2`. -/
theorem node_quad (ρ : Arith) {L : ℕ} (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h t0' t0h' : Out (L + 1) → ℂ) (hB1 : InB t1) (hB0 : InB t0')
    (hw : l2 (t0h' - t0' - (t0h - t0) - ℓ * (t1h - t1)) ≤ w512 L) (e : ℝ)
    (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) :
    l2 (pairF ((splitC ρ t1h).1 - (splitE t1).1) ((splitC ρ t1h).2 - (splitE t1).2)) ^ 2 +
      l2 (pairF ((splitC ρ t0h').1 - (splitE t0').1) ((splitC ρ t0h').2 - (splitE t0').2)) ^ 2 ≤
      (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + w512 L) + 2 * √(2 ^ L) *
          (29 / 10 / 2 ^ 42)) ^ 2 :=
  node_quadU b512 ρ ρ.tws_err ℓ hℓ t0 t1 t0h t1h t0' t0h' hB1 hB0 hw e he

/-- The first child's input error alone (second child replaced by its exact relations). -/
theorem node_a1 (ρ : Arith) {L : ℕ} (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h : Out (L + 1) → ℂ) (hB1 : InB t1) (e : ℝ)
        (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) :
    l2 (pairF ((splitC ρ t1h).1 - (splitE t1).1) ((splitC ρ t1h).2 - (splitE t1).2)) ≤
      √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + w512 L) + 2 * √(2 ^ L) *
          (29 / 10 / 2 ^ 42) :=
  node_a1U b512 ρ ρ.tws_err ℓ hℓ t0 t1 t0h t1h hB1 e he

/-- The line-10 output `t̄0'` is within `1` of `t0'` in ℓ2. -/
theorem upd_err (ρ : Arith) {L : ℕ} (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h z zh : Out (L + 1) → ℂ) (e : ℝ) (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e)
    (he1 : e ≤ 1 / 2 ^ 10)
    (hw : l2 (updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)) ≤ w512 L) :
    l2 (updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ) ≤ 1 :=
  upd_errU b512 ρ ℓ hℓ t0 t1 t0h t1h z zh e he he1 hw

/-- **One node of ffSampling along executions**: children with budgets `(A e + C)²` give `(A R + √2
C)²`. The budget bound `≤ 2⁻¹⁰` gives the margin of the range checks. -/
theorem node_step (ρ : Arith) {L : ℕ} (hL : L ≤ 8) (ℓ : Out (L + 1) → ℂ)
    (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (T0 T1 : FTree L) (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ih0 : ∀ (t0 t1 t0h t1h : Out L → ℂ)
        (e : ℝ), l2 (pairF (t0h - t0) (t1h - t1)) ≤ e → A * e + C ≤ 1 / 2 ^ 10 →
      PathSumP wS (Inv L) (ffs (aux := aux) ρ T0 t0 t1 t0h t1h) ((A * e + C) ^ 2))
    (ih1 : ∀ (t0 t1 t0h t1h : Out L → ℂ)
        (e : ℝ), l2 (pairF (t0h - t0) (t1h - t1)) ≤ e → A * e + C ≤ 1 / 2 ^ 10 →
      PathSumP wS (Inv L) (ffs (aux := aux) ρ T1 t0 t1 t0h t1h) ((A * e + C) ^ 2))
    (t0 t1 t0h t1h : Out (L + 1) → ℂ) (e : ℝ) (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e)
        (he1 : e ≤ 1 / 2 ^ 10)
    (hΦ : A *
        (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + w512 L) + 2 * √(2 ^ L) *
            (29 / 10 / 2 ^ 42)) + √2 * C ≤ 1 / 2 ^ 10) :
    PathSumP wS (Inv (L + 1)) (ffs (aux := aux) ρ (.node ℓ hℓ T0 T1) t0 t1 t0h t1h)
      ((A * (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + w512 L) + 2 * √(2 ^ L) *
          (29 / 10 / 2 ^ 42)) + √2 * C) ^ 2) :=
  node_stepU b512 ρ ρ.tw_err ρ.tws_err hL ℓ hℓ T0 T1 A C hA hC ih0 ih1 t0 t1 t0h t1h e he he1 hΦ

/--
**Path budget of one ffSampling call** (hop A). Input errors of ℓ2 norm `≤ e` with `Ā_L e + C̄_L ≤
2⁻¹⁰` give, along every execution, `Σ (t̄ - t)² ≤ (Ā_L e + C̄_L)²` over the SamplerZ queries; every
returned `ẑ` has merge errors within `ezU`. -/
theorem ffs_pathS (ρ : Arith) {L : ℕ} (T : FTree L) : L ≤ 9 → ∀ (t0 t1 t0h t1h : Out L → ℂ) (e : ℝ),
    l2 (pairF (t0h - t0) (t1h - t1)) ≤ e →
    coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L * e +
        coefC nn512 w512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) (29 / 10 / 2 ^ 42) L ≤ 1 / 2 ^ 10 →
    PathSumP wS (Inv L) (ffs (aux := aux) ρ T t0 t1 t0h t1h)
      ((coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L * e +
          coefC nn512 w512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) (29 / 10 / 2 ^ 42) L) ^ 2) :=
  ffs_pathSU b512 ρ ρ.tw_err ρ.tws_err T

/-- **SamplerZ queries of one ffSampling call**: at most `2^(L+1)` along every execution. -/
theorem ffs_pathN (ρ : Arith) {L : ℕ} (T : FTree L) (t0 t1 t0h t1h : Out L → ℂ) :
    PathSum w1 (ffs (aux := aux) ρ T t0 t1 t0h t1h) (2 ^ (L + 1)) :=
  ffs_pathNG ρ _ _ T t0 t1 t0h t1h

end FalconPrecision.Errors.FFSamp
