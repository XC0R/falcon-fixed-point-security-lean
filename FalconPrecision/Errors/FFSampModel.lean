/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FxModel
public import FalconPrecision.Errors.FalconProved
public import FalconPrecision.Errors.PathCompose

/-! # An execution model of ffSampling at Falcon-512 and its path budgets (TASK-009 S7g)

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
`ffs_pathN`: at most `2^(L+1)` SamplerZ queries. -/

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

/-- Lemma 12's range at tag 21. -/
def InB {L : ℕ} (v : Out L → ℂ) : Prop := ∀ o, ‖v o‖ ≤ 2 ^ 21

/-- The range check on computed values at tag 21. -/
def InC {L : ℕ} (v : Out L → ℂ) : Prop := ∀ o, ‖v o‖ ≤ 2 ^ 21 - 1

theorem InC.inB {L : ℕ} {v vh : Out L → ℂ} (h : InC vh) (hd : ∀ o, ‖vh o - v o‖ ≤ 1) : InB v :=
    fun o => by
  have := norm_sub_norm_le (v o) (vh o)
  rw [norm_sub_rev] at this
  linarith [h o, hd o]

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

/-- `splitfft` at tag 21. -/
noncomputable def splitC (ρ : Arith) {L : ℕ} (t : Out (L + 1) → ℂ) : (Out L → ℂ) × (Out L → ℂ) :=
  (fun o => ρ.halve (1 / 2 ^ 42) (t (o, false) + t (o, true)),
    fun o => ρ.mul (1 / 2 ^ 42) (ρ.tws L o) (t (o, false) - t (o, true)))

/-- `mergefft` of `ẑ`, exact. -/
noncomputable def mergeE {L : ℕ} (s : Samp L) : Out (L + 1) → ℂ :=
    mergeL s.e0 fun o => zeta L o * s.e1 o

/-- `mergefft` of `ẑ` at tag 21. -/
noncomputable def mergeC (ρ : Arith) {L : ℕ} (s : Samp L) : Out (L + 1) → ℂ :=
  mergeL s.c0 fun o => ρ.mul (1 / 2 ^ 42) (ρ.tw L o) (s.c1 o)

/-- Line 10, exact: `t0 + (t1 - z)·ℓ̂`. -/
noncomputable def upd {L : ℕ} (t0 t1 z ℓ : Out L → ℂ) : Out L → ℂ :=
    fun o => t0 o + (t1 o - z o) * ℓ o

/-- Line 10 at tag 21. -/
noncomputable def updC (ρ : Arith) {L : ℕ} (t0 t1 z ℓ : Out L → ℂ) : Out L → ℂ :=
  fun o => t0 o + ρ.mul (1 / 2 ^ 42) (t1 o - z o) (ℓ o)

/-- Line 14: `(ẑ0, ẑ1)` from the two children. -/
noncomputable def join (ρ : Arith) {L : ℕ} (s0 s1 : Samp L) : Samp (L + 1) :=
  ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1, mergeE s0, mergeE s1, mergeC ρ s0, mergeC ρ s1⟩

theorem leaf_range {σ : ℝ} (h : 1277833697 / 10 ^ 9 ≤ σ ∧ σ ≤ 18205 / 10000) :
    12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000 :=
  ⟨by linarith [h.1], by linarith [h.2]⟩

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

open Classical in
/--
**ffSampling** (Alg. 8) in exact and fixed-point arithmetic, with range checks on computed values.
-/
noncomputable def ffs (ρ : Arith) : {L : ℕ} → FTree L → (t0 t1 t0h t1h : Out L → ℂ) →
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
    if InC t1h then
      ffs ρ T1 (splitE t1).1 (splitE t1).2 (splitC ρ t1h).1 (splitC ρ t1h).2 >>= fun r1 =>
        r1.elim (pure none) fun s1 =>
          if InC s1.c1 ∧ InC (updC ρ t0h t1h (mergeC ρ s1) ℓ) then
            ffs ρ T0 (splitE (upd t0 t1 (mergeE s1) ℓ)).1 (splitE (upd t0 t1 (mergeE s1) ℓ)).2
              (splitC ρ (updC ρ t0h t1h (mergeC ρ s1) ℓ)).1
                  (splitC ρ (updC ρ t0h t1h (mergeC ρ s1) ℓ)).2 >>=
              fun r0 => r0.elim (pure none) fun s0 =>
                if InC s0.c1 then pure (some (join ρ s0 s1)) else pure none
          else pure none
    else pure none

/-- Squared centre error of a SamplerZ call; auxiliary queries weigh `0`. -/
noncomputable def wS : ιA ⊕ Falcon.CallP → ℝ := Sum.elim (fun _ => 0) fun q => (q.tbar - q.t) ^ 2

/-- One per SamplerZ call. -/
def w1 : ιA ⊕ Falcon.CallP → ℝ := Sum.elim (fun _ => 0) fun _ => 1

/-- The exact values of an output are the FFTs of its integer polynomials. -/
def IsFFT {L : ℕ} (s : Samp L) : Prop :=
  ∀ o, s.e0 o = evalAt (fun i => (s.z0 i : ℂ)) (pt L o) ∧ s.e1 o = evalAt (fun i => (s.z1 i : ℂ))
      (pt L o)

/-- Merge errors of an output within `ezU` at `c = 2.122·2⁻⁴²`, and `IsFFT`. -/
def Inv (L : ℕ) : Option (Samp L) → Prop
  | none => True
  | some s => (l2 (s.c0 - s.e0) ≤ ezU (2122 / 1000 / 2 ^ 42) L ∧
      l2 (s.c1 - s.e1) ≤ ezU (2122 / 1000 / 2 ^ 42) L) ∧ IsFFT s

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

theorem join_fft (ρ : Arith) {L : ℕ} {s0 s1 : Samp L} (h0 : IsFFT s0)
    (h1 : IsFFT s1) : IsFFT (join ρ s0 s1) := by
  have e : ∀ s : Samp L, IsFFT s → mergeE s = fun x => evalAt (fun i => (ilv s.z0 s.z1 i : ℂ))
      (pt (L + 1) x) :=
    fun s hs => by
      rw [← mergeL_ilv]; unfold mergeE; congr 1 <;> funext o
      · exact (hs o).1
      · rw [(hs o).2]
  exact fun x => ⟨congrFun (e s0 h0) x, congrFun (e s1 h1) x⟩

theorem lam512_nonneg (L : ℕ) : 0 ≤ lam512 L := by unfold lam512; split_ifs <;> norm_num

theorem sqrt_two_ulp21 : √2 * (1 / 2 ^ 42) ≤ (141422 / 100000 / 2 ^ 42 : ℝ) :=
  (mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num)

/-- Split relations of `ETree.Hyp` at one slot. -/
theorem split_rel (ρ : Arith) {L : ℕ} (t th : Out (L + 1) → ℂ) (hB : InB t) (o : Out L) :
    ‖((splitC ρ th).1 - (splitE t).1) o -
      ((th (o, false) - t (o, false)) + (th (o, true) - t (o, true))) / 2‖ ≤ 29 / 10 / 2 ^ 42 ∧
    ‖((splitC ρ th).2 - (splitE t).2) o -
      ρ.tws L o * ((th (o, false) - t (o, false)) - (th (o, true) - t (o, true)))‖ ≤ 29 / 10 /
          2 ^ 42 := by
  have hu : (0 : ℝ) < 1 / 2 ^ 42 := by positivity
  constructor
  · have e : ((splitC ρ th).1 - (splitE t).1) o -
        ((th (o, false) - t (o, false)) + (th (o, true) - t (o, true))) / 2 =
        ρ.halve (1 / 2 ^ 42) (th (o, false) + th (o, true)) - (th (o, false) + th (o, true)) / 2 :=
            by
      simp only [splitC, splitE, Pi.sub_apply]; ring
    rw [e]
    refine (ρ.halve_err hu _).trans ?_
    nlinarith [sqrt_two_ulp21]
  · set c := ρ.tws L o
    have e : ((splitC ρ th).2 - (splitE t).2) o -
        c * ((th (o, false) - t (o, false)) - (th (o, true) - t (o, true))) =
        (c * (th (o, false) - th (o, true)) +
          (ρ.mul (1 / 2 ^ 42) c (th (o, false) - th (o, true)) - c *
              (th (o, false) - th (o, true))) -
          starRingEnd ℂ (zeta L o) / 2 * (t (o, false) - t (o, true))) -
        c * ((th (o, false) - t (o, false)) - (th (o, true) - t (o, true))) := by
      simp only [splitC, splitE, Pi.sub_apply, c]; ring
    rw [e]
    exact (split_budget _ _ _ _ c (zeta L o) _ _ _ _ (hB _) (hB _) (ρ.tws_err L o)
      ((ρ.mul_err hu _ _).trans sqrt_two_ulp21)).trans split512

/-- The line-10 term `w` of `ETree.Hyp` is within `w512 L`. -/
theorem w_bound (ρ : Arith) {L : ℕ} (hL : L ≤ 8) (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h z zh : Out (L + 1) → ℂ) (hz : l2 (zh - z) ≤ ezU (2122 / 1000 / 2 ^ 42) (L + 1)) :
    l2 (updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)) ≤ w512 L := by
  have hw :=
      w_l2 L (fun o => ρ.mul (1 / 2 ^ 42) (t1h o - zh o) (ℓ o) - (t1h o - zh o) * ℓ o) ℓ
          (zh - z) 0 0
    (lam512 L) _ 0 0 _ (lam512_nonneg L) le_rfl (by positivity) le_rfl
    (fun o => (ρ.mul_err (by positivity) _ _).trans sqrt_two_ulp21) hℓ hz (fun _ => by simp)
        (fun _ => by simp)
  have e : updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1) =
      fun o => ρ.mul (1 / 2 ^ 42) (t1h o - zh o) (ℓ o) - (t1h o - zh o) * ℓ o - ℓ o * (zh - z) o +
        (0 : Out (L + 1) → ℂ) o * (0 : Out (L + 1) → ℂ) o := by
    funext o; simp only [updC, upd, Pi.sub_apply, Pi.mul_apply, Pi.zero_apply]; ring
  rw [e]
  have h := ez512 L hL
  have hs := sqrt_pow_le (L + 1)
  have hX : (0 : ℝ) ≤ 2 ^ 22 * ((if L = 8 then 2 ^ 5 else 1) * (7072 / 10000) / 2 ^ 63) := by
    split_ifs <;> positivity
  nlinarith [mul_le_mul hs (le_add_of_nonneg_left hX : (0 : ℝ) * 0 + 141422 / 100000 / 2 ^ 42 ≤ _)
    (by positivity) ((Real.sqrt_nonneg _).trans hs)]

/-- Merge errors of `ẑ` propagate within `ezU`. -/
theorem merge_inv (ρ : Arith) {L : ℕ} (s : Samp L) (hs : Inv L (some s)) (hB : InB s.e1) :
    l2 (mergeC ρ s - mergeE s) ≤ ezU (2122 / 1000 / 2 ^ 42) (L + 1) := by
  have h := merge_l2 L s.e0 s.e1 s.c0 s.c1 (zeta L) (ρ.tw L)
    (fun o => ρ.mul (1 / 2 ^ 42) (ρ.tw L o) (s.c1 o)) (7072 / 10000 / 2 ^ 63)
        (141422 / 100000 / 2 ^ 42)
    (2 ^ 21) _ (norm_zeta L) (ρ.tw_err L) (by positivity) (by positivity)
    (fun o => (ρ.mul_err (by positivity) _ _).trans sqrt_two_ulp21) hB hs.1.1 hs.1.2
  have hE0 : 0 ≤ ezU (2122 / 1000 / 2 ^ 42) L := (Real.sqrt_nonneg _).trans hs.1.1
  have h1 : 2 * (1 + 7072 / 10000 / 2 ^ 63) * ezU (2122 / 1000 / 2 ^ 42) L ≤
      2 * (1 + 1 / 2 ^ 63) * ezU (2122 / 1000 / 2 ^ 42) L :=
    mul_le_mul_of_nonneg_right (by norm_num) hE0
  have h2 : √2 * (√(2 ^ L) * (7072 / 10000 / 2 ^ 63 * 2 ^ 21 + 141422 / 100000 / 2 ^ 42)) ≤
      141422 / 100000 * (sq512 L * (2122 / 1000 / 2 ^ 42)) :=
    mul_le_mul sqrt_two_le (mul_le_mul (sqrt_pow_le L) (by norm_num) (by positivity)
      ((Real.sqrt_nonneg _).trans (sqrt_pow_le L))) (by positivity) (by norm_num)
  refine h.trans ?_
  rw [ezU]
  linarith

/-- `√2(1/2 + δ)` at `δ = 0.7072·2⁻⁶³`. -/
theorem K512_nonneg : 0 ≤ √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63 : ℝ) := by positivity

/-- **Node bound.** Both children's input errors, from `node_l2`. -/
theorem node_quad (ρ : Arith) {L : ℕ} (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h t0' t0h' : Out (L + 1) → ℂ) (hB1 : InB t1) (hB0 : InB t0')
    (hw : l2 (t0h' - t0' - (t0h - t0) - ℓ * (t1h - t1)) ≤ w512 L) (e : ℝ)
    (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) :
    l2 (pairF ((splitC ρ t1h).1 - (splitE t1).1) ((splitC ρ t1h).2 - (splitE t1).2)) ^ 2 +
      l2 (pairF ((splitC ρ t0h').1 - (splitE t0').1) ((splitC ρ t0h').2 - (splitE t0').2)) ^ 2 ≤
      (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + w512 L) + 2 * √(2 ^ L) *
          (29 / 10 / 2 ^ 42)) ^ 2 := by
  obtain ⟨hN0, hN1, hN⟩ := hyp512 L
  set w := t0h' - t0' - (t0h - t0) - ℓ * (t1h - t1)
  have hy : ∀ p, (t0h - t0 + ℓ * (t1h - t1) + w) p = t0h' p - t0' p := fun p => by
    simp only [w, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring
  have h := node_l2 L (lam512 L) (nn512 L) (7072 / 10000 / 2 ^ 63) (29 / 10 / 2 ^ 42) hN0 hN1 hN
    (by positivity) (by positivity) (t0h - t0) (t1h - t1) ℓ w hℓ (ρ.tws L) (ρ.norm_tws L) _ _ _ _
    (fun o => (split_rel ρ t1 t1h hB1 o).1) (fun o => (split_rel ρ t1 t1h hB1 o).2)
    (fun o => by rw [hy (o, false), hy (o, true)]; exact (split_rel ρ t0' t0h' hB0 o).1)
    (fun o => by rw [hy (o, false), hy (o, true)]; exact (split_rel ρ t0' t0h' hB0 o).2)
  rw [← l2_quad_sq]
  refine pow_le_pow_left₀ (l2_nonneg _) (h.trans ?_) 2
  have := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he hN0) hw) K512_nonneg
  linarith

/-- The first child's input error alone (second child replaced by its exact relations). -/
theorem node_a1 (ρ : Arith) {L : ℕ} (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h : Out (L + 1) → ℂ) (hB1 : InB t1) (e : ℝ)
        (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e) :
    l2 (pairF ((splitC ρ t1h).1 - (splitE t1).1) ((splitC ρ t1h).2 - (splitE t1).2)) ≤
      √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + w512 L) + 2 * √(2 ^ L) *
          (29 / 10 / 2 ^ 42) := by
  obtain ⟨hN0, hN1, hN⟩ := hyp512 L
  set y := t0h - t0 + ℓ * (t1h - t1) + 0
  have h := node_l2 L (lam512 L) (nn512 L) (7072 / 10000 / 2 ^ 63) (29 / 10 / 2 ^ 42) hN0 hN1 hN
    (by positivity) (by positivity) (t0h - t0) (t1h - t1) ℓ 0 hℓ (ρ.tws L) (ρ.norm_tws L) _ _
    (fun o => (y (o, false) + y (o, true)) / 2) (fun o => ρ.tws L o * (y (o, false) - y (o, true)))
    (fun o => (split_rel ρ t1 t1h hB1 o).1) (fun o => (split_rel ρ t1 t1h hB1 o).2)
    (fun o => by rw [sub_self, norm_zero]; positivity)
        (fun o => by rw [sub_self, norm_zero]; positivity)
  have h0 : l2 (0 : Out (L + 1) → ℂ) ≤ w512 L := by
    simpa [l2] using w512_nonneg L
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

theorem coef_succ (K e : ℝ) (L : ℕ) :
    coefA nn512 K (L + 1) * e + coefC nn512 w512 K (29 / 10 / 2 ^ 42) (L + 1) =
      coefA nn512 K L * (K * (nn512 L * e + w512 L) + 2 * √(2 ^ L) * (29 / 10 / 2 ^ 42)) +
        √2 * coefC nn512 w512 K (29 / 10 / 2 ^ 42) L := by
  simp only [coefA, coefC]; ring

theorem one_le_coefA512 : ∀ L, 1 ≤ coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L
  | 0 => by simp [coefA]
  | L + 1 => by
    have h2 : (14142 / 10000 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
    have hN : 16125 / 10000 ≤ nn512 L := by unfold nn512; split_ifs <;> norm_num
    have hK : 1 ≤ √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * nn512 L := by nlinarith
    rw [coefA, mul_assoc]
    nlinarith [one_le_coefA512 L]

theorem ezU512_le (L : ℕ) (hL : L ≤ 8) : ezU (2122 / 1000 / 2 ^ 42) L ≤ 1 := by
  interval_cases L <;> simp only [ezU, sq512] <;> norm_num

theorem w512_le (L : ℕ) : w512 L ≤ 1 / 2 ^ 20 := by unfold w512; split <;> norm_num

/-- The line-10 output `t̄0'` is within `1` of `t0'` in ℓ2. -/
theorem upd_err (ρ : Arith) {L : ℕ} (ℓ : Out (L + 1) → ℂ) (hℓ : ∀ o, ‖ℓ o‖ ≤ lam512 L)
    (t0 t1 t0h t1h z zh : Out (L + 1) → ℂ) (e : ℝ) (he : l2 (pairF (t0h - t0) (t1h - t1)) ≤ e)
    (he1 : e ≤ 1 / 2 ^ 10)
    (hw : l2 (updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)) ≤ w512 L) :
    l2 (updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ) ≤ 1 := by
  set w := updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ - (t0h - t0) - ℓ * (t1h - t1)
  have e' : updC ρ t0h t1h zh ℓ - upd t0 t1 z ℓ = w + (t0h - t0) + fun o => ℓ o * (t1h - t1) o := by
    funext o; simp only [w, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring
  rw [e']
  have hd := l2_le_pairF (t0h - t0) (t1h - t1)
  have hm := (l2_mul_le ℓ (t1h - t1) _ (lam512_nonneg L) hℓ).trans
    (mul_le_mul_of_nonneg_left (hd.2.trans he) (lam512_nonneg L))
  have hl : lam512 L * e ≤ 240001 / 10000 * (1 / 2 ^ 10) :=
    mul_le_mul (by unfold lam512; split_ifs <;> norm_num) he1 ((l2_nonneg _).trans he) (by norm_num)
  linarith
      [l2_add_le (w + (t0h - t0)) (fun o => ℓ o * (t1h - t1) o), l2_add_le w (t0h - t0), w512_le L]

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
          (29 / 10 / 2 ^ 42)) + √2 * C) ^ 2) := by
  generalize hR : √2 * (1 / 2 + 7072 / 10000 / 2 ^ 63) * (nn512 L * e + w512 L) + 2 * √(2 ^ L) *
      (29 / 10 / 2 ^ 42) = R at hΦ ⊢
  have hC2 : C ≤ √2 * C := le_mul_of_one_le_left hC (Real.le_sqrt_of_sq_le (by norm_num))
  have hz : ∀ s : Samp L, Inv L (some s) → InC s.c1 → InB s.e1 := fun s hs hc =>
    hc.inB fun o => (norm_le_l2 (s.c1 - s.e1) o).trans (hs.1.2.trans (ezU512_le L hL))
  simp only [ffs]
  split_ifs with hc1
  swap
  · exact .pure _ (sq_nonneg _) trivial
  have hb1 : InB t1 := hc1.inB fun o => (norm_le_l2 (t1h - t1) o).trans
    (((l2_le_pairF _ _).2.trans he).trans (he1.trans (by norm_num)))
  obtain ⟨a1, ha⟩ : ∃ a1,
      l2 (pairF ((splitC ρ t1h).1 - (splitE t1).1) ((splitC ρ t1h).2 - (splitE t1).2)) = a1 :=
    ⟨_, rfl⟩
  have ha1 := (node_a1 ρ ℓ hℓ t0 t1 t0h t1h hb1 e he).trans_eq hR
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
    have hw := w_bound ρ hL ℓ hℓ t0 t1 t0h t1h _ _ (merge_inv ρ s1 hr1 (hz s1 hr1 hb.1))
    have hb0 :=
        hb.2.inB fun o => (norm_le_l2 _ o).trans (upd_err ρ ℓ hℓ t0 t1 t0h t1h _ _ e he he1 hw)
    have hq := node_quad ρ ℓ hℓ t0 t1 t0h t1h _ _ hb1 hb0 hw e he
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
      · exact .pure _ le_rfl
          ⟨⟨merge_inv ρ s0 hr0 (hz s0 hr0 hc0), merge_inv ρ s1 hr1 (hz s1 hr1 hb.1)⟩,
              join_fft ρ hr0.2 hr1.2⟩
      · exact .pure _ le_rfl trivial

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
          coefC nn512 w512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) (29 / 10 / 2 ^ 42) L) ^ 2) := by
  obtain ⟨hc, -, -⟩ := coef512 (7072 / 10000 / 2 ^ 63) (by positivity) le_rfl
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
    simp only [ffs, coefA, coefC]
    refine .query_bind _ _ fun z0 => .query_bind _ _ fun z1 => .pure _ ?_ ?_
    · change 0 ≤ (1 * e + 0) ^ 2 - ((t0h ()).re - (t0 ()).re) ^ 2 - ((t1h ()).re - (t1 ()).re) ^ 2
      nlinarith [hre (t0h ()) (t0 ()), hre (t1h ()) (t1 ()), mul_le_mul he he h0 (h0.trans he)]
    · exact ⟨⟨by simp [Samp.leaf, l2, ezU], by simp [Samp.leaf, l2, ezU]⟩,
        fun _ => ⟨by simp [Samp.leaf, evalAt], by simp [Samp.leaf, evalAt]⟩⟩
  | @node L ℓ hℓ T0 T1 ih0 ih1 =>
    intro hL t0 t1 t0h t1h e he hΦ
    have he1 : e ≤ 1 / 2 ^ 10 := by
      linarith
          [mul_le_mul_of_nonneg_right (one_le_coefA512 (L + 1))
              ((l2_nonneg _).trans he), (hc (L + 1)).2]
    rw [coef_succ] at hΦ ⊢
    exact node_step ρ (by omega) ℓ hℓ T0 T1 _ _ (hc L).1 (hc L).2 (ih0 (by omega)) (ih1 (by omega))
      t0 t1 t0h t1h e he he1 hΦ

/-- **SamplerZ queries of one ffSampling call**: at most `2^(L+1)` along every execution. -/
theorem ffs_pathN (ρ : Arith) {L : ℕ} (T : FTree L) (t0 t1 t0h t1h : Out L → ℂ) :
    PathSum w1 (ffs (aux := aux) ρ T t0 t1 t0h t1h) (2 ^ (L + 1)) := by
  induction T with
  | leaf σ h =>
    simp only [ffs]
    exact .query_bind _ _ fun _ => .query_bind _ _ fun _ =>
      .pure _ (by change (0 : ℝ) ≤ 2 ^ (0 + 1) - 1 - 1; norm_num)
  | @node L ℓ hℓ T0 T1 ih0 ih1 =>
    simp only [ffs]
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

end FalconPrecision.Errors.FFSamp
