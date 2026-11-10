/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFSampL2

/-! # Center errors of a whole ffSampling run (TASK-009 S7e)

`ETree L` records, for an ffSampling call of size `2^L` (Alg. 8), the errors of the inputs `(δt0,
δt1)` at every node; the leaves (`k = 1`) hold the errors of the centers passed to SamplerZ. `Hyp`
asks at each node the per-slot relations of `node_l2` (line 10 with `|ℓ̂| ≤ Λ`, the extra term `w`
with `‖w‖₂ ≤ W`, both splits within `r'`). Then the ℓ2 norm of all center errors is at most
`A_L·‖(δt0, δt1)‖₂ + C_L`, `A_{L+1} = A_L·K·N_L`, `C_{L+1} = A_L(K·W_L + 2√(2^L)r') + √2·C_L`, `K =
√2(1/2 + δ)`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFSamp

open FalconPrecision.Errors.FFTRec

/-- Input errors at every node of an ffSampling call of size `2^L`. -/
inductive ETree : ℕ → Type
  | leaf : ℂ → ℂ → ETree 0
  | node {L : ℕ} : (Out (L + 1) → ℂ) → (Out (L + 1) → ℂ) → ETree L → ETree L → ETree (L + 1)

namespace ETree

/-- Input errors `(δt0, δt1)` of the root call. -/
def x0 : {L : ℕ} → ETree L → Out L → ℂ
  | _, leaf a _ => fun _ => a
  | _, node x0 _ _ _ => x0

def x1 : {L : ℕ} → ETree L → Out L → ℂ
  | _, leaf _ b => fun _ => b
  | _, node _ x1 _ _ => x1

/-- Sum of squared center errors over all leaves (SamplerZ calls). -/
noncomputable def leafSq : {L : ℕ} → ETree L → ℝ
  | _, leaf a b => ‖a‖ ^ 2 + ‖b‖ ^ 2
  | _, node _ _ c1 c0 => leafSq c1 + leafSq c0

/-- The per-node error relations of ffSampling (child `c1` from `t̂1`, child `c0` from `t̂0'`). -/
def Hyp (Λ N W : ℕ → ℝ) (δ r' : ℝ) : {L : ℕ} → ETree L → Prop
  | _, leaf _ _ => True
  | _, @node L x0 x1 c1 c0 => ∃ (ℓh w : Out (L + 1) → ℂ) (c : Out L → ℂ),
      (∀ o, ‖ℓh o‖ ≤ Λ L) ∧ (∀ o, ‖c o‖ ≤ 1 / 2 + δ) ∧ l2 w ≤ W L ∧
      (∀ o, ‖c1.x0 o - (x1 (o, false) + x1 (o, true)) / 2‖ ≤ r') ∧
      (∀ o, ‖c1.x1 o - c o * (x1 (o, false) - x1 (o, true))‖ ≤ r') ∧
      (∀ o, ‖c0.x0 o - ((x0 + ℓh * x1 + w) (o, false) + (x0 + ℓh * x1 + w) (o, true)) / 2‖ ≤ r') ∧
      (∀ o, ‖c0.x1 o - c o * ((x0 + ℓh * x1 + w) (o, false) - (x0 + ℓh * x1 + w) (o, true))‖ ≤ r') ∧
      Hyp Λ N W δ r' c1 ∧ Hyp Λ N W δ r' c0

end ETree

/-- Affine bound coefficients. -/
noncomputable def coefA (N : ℕ → ℝ) (K : ℝ) : ℕ → ℝ
  | 0 => 1
  | L + 1 => coefA N K L * K * N L

noncomputable def coefC (N W : ℕ → ℝ) (K r' : ℝ) : ℕ → ℝ
  | 0 => 0
  | L + 1 => coefA N K L * (K * W L + 2 * √(2 ^ L) * r') + √2 * coefC N W K r' L

theorem l2_nonneg {ι : Type} [Fintype ι] (f : ι → ℂ) : 0 ≤ l2 f := Real.sqrt_nonneg _

theorem l2_quad_sq {L : ℕ} (e1 o1 e0 o0 : Out L → ℂ) :
    l2 (quad e1 o1 e0 o0) ^ 2 = l2 (pairF e1 o1) ^ 2 + l2 (pairF e0 o0) ^ 2 := by
  rw [l2_sq, l2_sq, l2_sq, sum_quad, sum_pairF, sum_pairF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [quad, pairF]; ring

theorem l2_pairF_leaf (a b : ℂ) : l2 (pairF (fun _ : Out 0 => a) fun _ => b) ^ 2 = ‖a‖ ^ 2 +
    ‖b‖ ^ 2 := by
  rw [l2_sq, sum_pairF]
  change ∑ _o : Unit, _ = _
  simp [pairF]

theorem leafSq_nonneg : ∀ {L : ℕ} (T : ETree L), 0 ≤ T.leafSq
  | _, .leaf a b => by simp only [ETree.leafSq]; positivity
  | _, .node _ _ c1 c0 => by
    simp only [ETree.leafSq]; exact add_nonneg (leafSq_nonneg c1) (leafSq_nonneg c0)

/-- Minkowski in `ℝ²`. -/
theorem mink2 (p q u v : ℝ) :
    √((p + q) ^ 2 + (u + v) ^ 2) ≤ √(p ^ 2 + u ^ 2) + √(q ^ 2 + v ^ 2) := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ p ^ 2 + u ^ 2)
  have h2 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ q ^ 2 + v ^ 2)
  have hcs : p * q + u * v ≤ √(p ^ 2 + u ^ 2) * √(q ^ 2 + v ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (p * v - u * q)]
  nlinarith

/-- **ℓ2 center error of an ffSampling run.** -/
theorem run_l2 (Λ N W : ℕ → ℝ) (δ r' : ℝ) (hδ : 0 ≤ δ) (hr' : 0 ≤ r') (hN0 : ∀ L, 0 ≤ N L)
    (hN1 : ∀ L, 1 + Λ L ^ 2 ≤ N L ^ 2) (hN : ∀ L, Λ L ^ 2 ≤ (N L ^ 2 - 1) * (N L ^ 2 - 1 - Λ L ^ 2))
    (hW : ∀ L, 0 ≤ W L) :
    ∀ L (T : ETree L), T.Hyp Λ N W δ r' →
      √T.leafSq ≤ coefA N (√2 * (1 / 2 + δ)) L * l2 (pairF T.x0 T.x1) +
          coefC N W (√2 * (1 / 2 + δ)) r' L := by
  set K := √2 * (1 / 2 + δ)
  have hK : 0 ≤ K := by positivity
  have hA : ∀ L, 0 ≤ coefA N K L := by
    intro L; induction L with
    | zero => simp [coefA]
    | succ L ih => simp only [coefA]; have := hN0 L; positivity
  have hC : ∀ L, 0 ≤ coefC N W K r' L := by
    intro L; induction L with
    | zero => simp [coefC]
    | succ L ih => simp only [coefC]; have := hA L; have := hW L; positivity
  intro L T
  induction T with
  | leaf a b =>
    intro _
    simp only [ETree.leafSq, coefA, coefC, one_mul, add_zero, ETree.x0, ETree.x1]
    rw [← l2_pairF_leaf, Real.sqrt_sq (l2_nonneg _)]
  | @node L x0 x1 c1 c0 ih1 ih0 =>
    intro hT
    obtain ⟨ℓh, w, c, hℓ, hc, hw, he1, ho1, he0, ho0, h1, h0⟩ := hT
    have hnode := node_l2 L (Λ L) (N L) δ r' (hN0 L) (hN1 L) (hN L) hδ hr' x0 x1 ℓh w hℓ c hc
      c1.x0 c1.x1 c0.x0 c0.x1 he1 ho1 he0 ho0
    have b1 := ih1 h1
    have b0 := ih0 h0
    set a1 := l2 (pairF c1.x0 c1.x1)
    set a0 := l2 (pairF c0.x0 c0.x1)
    have ha1 : 0 ≤ a1 := Real.sqrt_nonneg _
    have ha0 : 0 ≤ a0 := Real.sqrt_nonneg _
    have hq : √(a1 ^ 2 + a0 ^ 2) ≤ K * (N L * l2 (pairF x0 x1) + W L) + 2 * √(2 ^ L) * r' := by
      rw [← l2_quad_sq, Real.sqrt_sq (l2_nonneg _)]
      exact hnode.trans (by gcongr)
    simp only [ETree.leafSq, ETree.x0, ETree.x1, coefA, coefC]
    set A := coefA N K L
    set C := coefC N W K r' L
    have hs1 : c1.leafSq ≤ (A * a1 + C) ^ 2 := by
      have := Real.sq_sqrt (leafSq_nonneg c1)
      nlinarith
          [Real.sqrt_nonneg c1.leafSq, mul_le_mul b1 b1 (Real.sqrt_nonneg _)
              (by linarith [Real.sqrt_nonneg c1.leafSq])]
    have hs0 : c0.leafSq ≤ (A * a0 + C) ^ 2 := by
      have := Real.sq_sqrt (leafSq_nonneg c0)
      nlinarith
          [Real.sqrt_nonneg c0.leafSq, mul_le_mul b0 b0 (Real.sqrt_nonneg _)
              (by linarith [Real.sqrt_nonneg c0.leafSq])]
    have hm := mink2 (A * a1) C (A * a0) C
    have hAa : √((A * a1) ^ 2 + (A * a0) ^ 2) = A * √(a1 ^ 2 + a0 ^ 2) := by
      rw [show (A * a1) ^ 2 + (A * a0) ^ 2 = A ^ 2 * (a1 ^ 2 + a0 ^ 2) by ring,
          Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (hA L)]
    have hCC : √(C ^ 2 + C ^ 2) = √2 * C := by
      rw [show C ^ 2 + C ^ 2 = 2 * C ^ 2 by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (hC L)]
    calc √(c1.leafSq + c0.leafSq) ≤ √((A * a1 + C) ^ 2 + (A * a0 + C) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
      _ ≤ A * √(a1 ^ 2 + a0 ^ 2) + √2 * C := by rw [← hAa, ← hCC]; exact hm
      _ ≤ A * (K * (N L * l2 (pairF x0 x1) + W L) + 2 * √(2 ^ L) * r') + √2 * C :=
          by gcongr; exact hA L
      _ = A * K * N L * l2 (pairF x0 x1) + (A * (K * W L + 2 * √(2 ^ L) * r') + √2 * C) := by ring

end FalconPrecision.Errors.FFSamp
