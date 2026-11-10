/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.LDLSigma
public import FalconPrecision.Errors.LDLFx

/-! # Falcon-512 leaf-error instance (TASK-009 S7d)

ffLDL⋆ at Falcon-512 (`q = 12289`, `γhybrid = 4`, keygen-enforced, Alg. 2 l. 8, §8.5: diagonal
values in `[q/16, 16q]` by Lemma 8), 8 inner levels, Type 2 budgets at Table 4 tags (`D̂` at tag 18,
`L̂10` at tag 0, `p = 63`). `falcon512_leaf` is conditional on: the root values in the Lemma 8 range
with relative error `≤ 2⁻⁴⁵` (`hroot`), every inner step within `ε = 2⁻³⁵` (`hstep`), and the
normalisation `σ/√D̂` within relative `2⁻⁵⁰` (`hs`). Then every leaf has `|σ̄_i/σ_i - 1| ≤ 2⁻⁴²`,
measured against the true-tree leaves `σ_i = σ/√V` (exact ffLDL⋆ from `f, g, F, G`).

Not proved: `hstep` from the per-operation budgets (`step512` is arithmetic on the bound of
`hm_fx_err`, whose side conditions are not discharged, with `e₀ ≤ 2⁻⁴⁵`, `e₁ ≤ 2⁻⁴³`, `eL ≤ 2⁻⁵⁴`,
`eD ≤ 2⁻⁴⁴` assumed); `hroot` from `fft512_err`, `root512`, `root11_512` (not composed); the
reciprocal (`eL`) and rsqrt (`hs`) in fixed point; the Lemma 8 range. -/

@[expose] public section

namespace FalconPrecision.Errors.LDL

/--
The inner-step budget (arithmetic): the bound of `hm_fx_err` at the assumed per-operation budgets is
within `ε = 2⁻³⁵`. -/
theorem step512 (a e₀ e₁ eL eD : ℝ) (ha : a ≤ 196700) (h₀ : e₀ ≤ 1 / 2 ^ 45) (h₁ : e₁ ≤ 1 / 2 ^ 43)
    (hL : eL ≤ 1 / 2 ^ 54) (hD : eD ≤ 1 / 2 ^ 44) (heL : 0 ≤ eL) :
    201 / 100 * (e₀ + e₁ + a * eL) + eD ≤ 1 / 2 ^ 35 := by
  have : a * eL ≤ 196700 * (1 / 2 ^ 54) := mul_le_mul ha hL heL (by norm_num)
  nlinarith

/-- **Falcon-512 leaves**, conditional on `hroot`, `hstep`, `hs`. -/
theorem falcon512_leaf (σ : ℝ) (hσ : 0 < σ) (Idx : ℕ → Type) (V Vh : (ℓ : ℕ) → Idx ℓ → ℝ)
    (hroot : ∀ i, (12289 / 16 ≤ V 0 i ∧ V 0 i ≤ 16 * 12289) ∧ RelClose (1 / 2 ^ 45) (V 0 i)
        (Vh 0 i))
    (hstep : ∀ ℓ j, ∃ i₁ i₂,
      (V (ℓ + 1) j = am (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - am (Vh ℓ i₁) (Vh ℓ i₂)| ≤ 1 / 2 ^ 35) ∨
      (V (ℓ + 1) j = hm (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - hm (Vh ℓ i₁) (Vh ℓ i₂)| ≤ 1 / 2 ^ 35))
    (σh : Idx 8 → ℝ) (hs : ∀ j, |σh j - σ / √(Vh 8 j)| ≤ 1 / 2 ^ 50 * (σ / √(Vh 8 j))) (j : Idx 8) :
    |σh j / (σ / √(V 8 j)) - 1| ≤ 1 / 2 ^ 42 := by
  have h :=
      (leaf_sigma_err (12289 / 16) (16 * 12289) (1 / 2 ^ 45) (1 / 2 ^ 35)
          (1 / 2 ^ 50) σ (by norm_num)
    (by norm_num) hσ Idx V Vh hroot hstep (by norm_num) 8 (by norm_num) σh hs j).2
  refine h.trans ?_
  norm_num

end FalconPrecision.Errors.LDL
