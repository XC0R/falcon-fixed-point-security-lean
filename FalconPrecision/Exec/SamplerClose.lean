/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerCloseP

/-! # The Rényi distance of SamplerZ to `D_{σ̄,t̄}`

`samplerZ_mgf`: for a sampler that rejects saturated shifts, at every `σ̄ ∈ [σmin, σmax]` and
every `t̄`, the Rényi MGF of order `a ≥ 2` against `D_{σ̄,t̄}` is at most `exp((a - 1)·εZ a)`, from
a `χ²` bound `chi2B = 2⁻⁷⁶` and a ratio bound `uB = 1 + 2⁻⁴⁰` (`lawZ_close`) through
`renyiMGF_le_chi2` (`t^a ≤ 1 + a(t - 1) + a(a-1)/2·u^(a-2)(t - 1)²` for `t ∈ [0, u]`,
`rpow_le_chi2`).

`lawZ_close` compares each of the `38` candidates `(z0 ≤ 18, b)` with its ideal weight
`pdt[0]/2^(w+1)·ccs·exp(-(z - r)²/(2σ̄²))` (`cand_bounds`: the table against
`exp(-i²/(2σmax²))`, `tab_ok`; BerExp's acceptance against `ccs·exp(-x)`, `accW_mem`), so the
acceptance of a round is within `2⁻⁴²` of `A* = pdt[0]/2^(w+1)·ccs·Θ` (`accZ_bounds`); the
`χ²` sum is at most `21·2⁻⁸¹` on the candidates (`chi_fin`) plus `11·2⁻⁸¹`, the mass of
`D_{σ̄,t̄}` at distance `≥ 19` from `t̄` (`tail19_le`, the Chernoff bound of `GaussTail`).

`samplerZ_tv`: saturating instead of rejecting moves at most `2⁻¹¹⁰` in total variation per call
(ePrint 2026/2902 p. 4: a saturated shift multiplies the acceptance by `2^(s-63)`, so no useful
Rényi bound of high order holds for it); a shift `≥ 64` needs `z0 ≥ 15`, whose `pdt` mass is at
most `2⁻⁵⁰` (`wZ_sat`, `pdt_tail15`).

The proofs are those of `Exec.SamplerCloseP` (every `σmin ∈ [1.277833697, 1.3]`) at Falcon-512's
`σmin = 1.277833697`; `lawZ_close1024`, `samplerZ_mgf1024`, `samplerZ_tv1024` are the same at
Falcon-1024 (`falcon1024S`, `σmin = 1.298280334`). -/

@[expose] public section

open MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- The ideal weight of the candidate `z`: `pdt[0]/2^(w+1)·ccs·exp(-(z - r)²/(2σ̄²))`. -/
noncomputable def wsZ (S : SampChoices) (σq r : ℚ) (z : ℤ) : ℝ :=
  (pdtZ (falcon512S.tab S.base) 0 : ℝ) / 2 ^ ((falcon512S.tab S.base).w + 1) *
    ((falcon512S.σmin / σq : ℚ) : ℝ) * Real.exp (-(((z : ℝ) - r) ^ 2 / (2 * (σq : ℝ) ^ 2)))

/-- `pdt[0]/2^(w+1)·ccs`. -/
noncomputable def K0Z (S : SampChoices) (σq : ℚ) : ℝ :=
  (pdtZ (falcon512S.tab S.base) 0 : ℝ) / 2 ^ ((falcon512S.tab S.base).w + 1) *
    ((falcon512S.σmin / σq : ℚ) : ℝ)

theorem wsZ_eq (S : SampChoices) (σq r : ℚ) (z : ℤ) :
    wsZ S σq r z = K0Z S σq * Real.exp (-(((z : ℝ) - r) ^ 2 / (2 * (σq : ℝ) ^ 2))) := rfl

/-- The ideal acceptance `A* = K0·Θ`. -/
noncomputable def AsZ (S : SampChoices) (σq : ℚ) (s : ℤ) (r : ℚ) : ℝ :=
  K0Z S σq * discreteGaussianSum σq ((s : ℝ) + r)

theorem falcon512S_σ_pos {σ : Fx 64} (hσ : inRangeB falcon512S σ = true) : 0 < σ.toReal :=
  sampS_σ_pos sminOk512 hσ

/-- **One candidate against its ideal weight** (`i ≤ 18`): above within `1 + 2⁻⁴³`, below within
`1 - epsT i - 2⁻⁴⁴` and `2⁻⁶²`, and the square of the difference. -/
theorem cand_bounds (S : SampChoices) (hS : S.shiftRej = true) {σq r : ℚ}
    (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) {i : ℕ}
    (hi : i ≤ 18) (b : Bool) :
    (wZ falcon512S S σq r i b : ℝ) ≤ wsZ S σq r (zOf i b) * (1 + 1 / 2 ^ 43) ∧
      wsZ S σq r (zOf i b) * (1 - epsT i - 1 / 2 ^ 44) - 1 / 2 ^ 62 ≤
        wZ falcon512S S σq r i b ∧
      ((wZ falcon512S S σq r i b : ℝ) - wsZ S σq r (zOf i b)) ^ 2 ≤
        wsZ S σq r (zOf i b) *
          ((8 * epsT i ^ 2 + 1 / 2 ^ 86) * wsZ S σq r (zOf i b) + 1 / 2 ^ 103) :=
  cand_boundsP sminOk512 S hS hσ1 hσ2 hr0 hr1 hi b

/-- `K0Z·Θ ∈ [1/2, 3/5]` and `Θ ∈ [16/5, 23/5]` on SamplerZ's range. -/
theorem K0Z_theta (S : SampChoices) {σq : ℚ} (c : ℝ) (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) :
    1 / 2 ≤ K0Z S σq * discreteGaussianSum σq c ∧ K0Z S σq * discreteGaussianSum σq c ≤ 3 / 5 ∧
      16 / 5 ≤ discreteGaussianSum σq c ∧ discreteGaussianSum σq c ≤ 23 / 5 :=
  K0ZP_theta sminOk512 S c hσ1 hσ2

theorem wZz_out (S : SampChoices) (σ r : ℚ) {z : ℤ} (hz : z < -18 ∨ 19 < z) :
    wZz falcon512S S σ r z = 0 :=
  wZz_outP falcon512S.σmin S σ r hz

theorem AsZ_mem (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) :
    1 / 2 ≤ AsZ S σq s r ∧ AsZ S σq s r ≤ 3 / 5 ∧ 0 < K0Z S σq ∧
      K0Z S σq ≤ AsZ S σq s r * (5 / 16) :=
  AsZP_mem sminOk512 S hσ1 hσ2 s r

theorem DZ_eq (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) (z : ℤ) :
    DZ σq s r (s + z) = wsZ S σq r z / AsZ S σq s r :=
  DZP_eq sminOk512 S hσ1 hσ2 s r z

theorem hws0' (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) (z : ℤ) : 0 < wsZ S σq r z :=
  hws0P sminOk512 S hσ1 hσ2 s r z

theorem sum_ws_candC (S : SampChoices) {σq : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (s : ℤ) (r : ℚ) :
    ∑ p ∈ candC, wsZ S σq r (zOf p.1 p.2) =
      AsZ S σq s r * ∑ p ∈ candC, DZ σq s r (s + zOf p.1 p.2) :=
  sum_ws_candCP sminOk512 S hσ1 hσ2 s r

theorem ws_le_E (S : SampChoices) {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℤ) (i : ℕ) (b : Bool) :
    wsZ S σq r (zOf i b) ≤ K0Z S σq * Real.exp (-((i ^ 2 : ℕ) * (kS : ℝ))) :=
  ws_le_EP sminOk512 S hσ1 hσ2 hr0 hr1 s i b

theorem eps_ws_candC (S : SampChoices) {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℤ) :
    ∑ p ∈ candC, (epsT p.1 : ℝ) * wsZ S σq r (zOf p.1 p.2) ≤ 2 * K0Z S σq * (1 / 2 ^ 43) ∧
      ∑ p ∈ candC, (epsT p.1 : ℝ) ^ 2 * wsZ S σq r (zOf p.1 p.2) ≤
        2 * K0Z S σq * (1 / 2 ^ 81) :=
  eps_ws_candCP sminOk512 S hσ1 hσ2 hr0 hr1 s

theorem accZ_candC (S : SampChoices) (σq r : ℚ) :
    (accZ falcon512S S σq r : ℝ) = ∑ p ∈ candC, (wZ falcon512S S σq r p.1 p.2 : ℝ) :=
  accZ_candCP falcon512S.σmin S σq r

/-- **The acceptance of a round** against `A*`. -/
theorem accZ_bounds (S : SampChoices) (hS : S.shiftRej = true) {σq r : ℚ}
    (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ℤ) :
    AsZ S σq s r * (1 - 1 / 2 ^ 42) ≤ accZ falcon512S S σq r ∧
      (accZ falcon512S S σq r : ℝ) ≤ AsZ S σq s r * (1 + 1 / 2 ^ 43) :=
  accZ_boundsP sminOk512 S hS hσ1 hσ2 hr0 hr1 s

/-- **The `χ²` sum over the candidates**, with `λ` within `2⁻⁴¹` of `1` and the exhaustion
mass `ρF ≤ 2⁻⁶⁴` at `⌊t̄⌋`. -/
theorem chi_fin (S : SampChoices) (hS : S.shiftRej = true) {σq r : ℚ}
    (hσ1 : falcon512S.σmin ≤ σq) (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ℤ) {lam ρF : ℝ} (hl1 : lam ≤ 1 + 1 / 2 ^ 41) (hl2 : 1 - 1 / 2 ^ 41 ≤ lam)
    (hρ0 : 0 ≤ ρF) (hρ1 : ρF ≤ 1 / 2 ^ 64) :
    ∑ p ∈ candC, ((lam * wZ falcon512S S σq r p.1 p.2 / AsZ S σq s r +
      (if s + zOf p.1 p.2 = s then ρF else 0)) - DZ σq s r (s + zOf p.1 p.2)) ^ 2 /
        DZ σq s r (s + zOf p.1 p.2) ≤ 21 / 2 ^ 81 :=
  chi_finP sminOk512 S hS hσ1 hσ2 hr0 hr1 s hl1 hl2 hρ0 hρ1

/-- **Node.** Closeness of `lawZ` at Falcon-512 with shift rejection, both tables: nonnegative,
within `uB` of `D_{σ̄,t̄}` pointwise, `χ² ≤ chi2B`, at every `σ̄ ∈ [σmin, σmax]` and `t̄`. -/
theorem lawZ_close (S : SampChoices) (hS : S.shiftRej = true) (σ t : Fx 64)
    (hσ : inRangeB falcon512S σ = true) :
    (∀ y, 0 ≤ lawZ falcon512S S σ t y) ∧
      (∀ y, (lawZ falcon512S S σ t y : ℝ) ≤
        uB * discreteGaussianPMF σ.toReal t.toReal y) ∧
      ∑' y, ENNReal.ofReal (((lawZ falcon512S S σ t y : ℝ) -
        discreteGaussianPMF σ.toReal t.toReal y) ^ 2 /
          discreteGaussianPMF σ.toReal t.toReal y) ≤ ENNReal.ofReal chi2B :=
  lawZ_closeP sminOk512 S hS σ t hσ

omit [LawfulMonad m] in
/-- **Per-call closeness**: the Rényi MGF of order `a ≥ 2` of SamplerZ with shift rejection
against `D_{σ̄,t̄}` is at most `exp((a - 1)·εZ a)`. -/
theorem samplerZ_mgf {a : ℝ} (ha : 2 ≤ a) (S : SampChoices) (hS : S.shiftRej = true)
    (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64) (hσ : inRangeB falcon512S σ = true) :
    renyiMGF a 𝒟[samplerZ falcon512S S ub σ t] (discreteGaussianMeasure σ.toReal t.toReal) ≤
      ENNReal.ofReal (Real.exp ((a - 1) * εZ a)) :=
  samplerZ_mgfP sminOk512 ha S hS ub hub σ t hσ

/-- **Per candidate**: saturating adds at most `pdt[i]/2ʷ·2⁻⁶⁴`, and nothing for `i ≤ 14`. -/
theorem wZ_sat (c : Centre) (b0 : BaseBits) {σq r : ℚ} (hσ1 : falcon512S.σmin ≤ σq)
    (hσ2 : σq ≤ falcon512S.σmax) (hr0 : 0 ≤ r) (hr1 : r < 1) (i : ℕ) (b : Bool) :
    (wZ falcon512S ⟨c, true, b0⟩ σq r i b : ℝ) ≤ wZ falcon512S ⟨c, false, b0⟩ σq r i b ∧
      (wZ falcon512S ⟨c, false, b0⟩ σq r i b : ℝ) - wZ falcon512S ⟨c, true, b0⟩ σq r i b ≤
        (if 15 ≤ i then (pdtZ (falcon512S.tab b0) i : ℝ) else 0) /
          2 ^ (falcon512S.tab b0).w / 2 ^ 64 :=
  wZ_satP sminOk512 c b0 hσ1 hσ2 hr0 hr1 i b

omit [LawfulMonad m] in
/-- **Node.** Saturating a shift `≥ 64` instead of rejecting moves at most `2⁻¹¹⁰` per call. -/
theorem samplerZ_tv (S : SampChoices) (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64)
    (hσ : inRangeB falcon512S σ = true) :
    (𝒟[samplerZ falcon512S S ub σ t]).etvDist
        𝒟[samplerZ falcon512S { S with shiftRej := true } ub σ t] ≤
      ENNReal.ofReal (if S.shiftRej then 0 else 1 / 2 ^ 110) :=
  samplerZ_tvP sminOk512 S ub hub σ t hσ

/-! ## Falcon-1024 -/

/-- **Node.** `lawZ_close` at Falcon-1024 (`falcon1024S`): nonnegative, within `uB` of
`D_{σ̄,t̄}` pointwise, `χ² ≤ chi2B`, at every `σ̄ ∈ [1.298280334, 1.8205]` and `t̄`. -/
theorem lawZ_close1024 (S : SampChoices) (hS : S.shiftRej = true) (σ t : Fx 64)
    (hσ : inRangeB falcon1024S σ = true) :
    (∀ y, 0 ≤ lawZ falcon1024S S σ t y) ∧
      (∀ y, (lawZ falcon1024S S σ t y : ℝ) ≤
        uB * discreteGaussianPMF σ.toReal t.toReal y) ∧
      ∑' y, ENNReal.ofReal (((lawZ falcon1024S S σ t y : ℝ) -
        discreteGaussianPMF σ.toReal t.toReal y) ^ 2 /
          discreteGaussianPMF σ.toReal t.toReal y) ≤ ENNReal.ofReal chi2B :=
  lawZ_closeP sminOk1024 S hS σ t hσ

omit [LawfulMonad m] in
/-- **Per-call closeness at Falcon-1024**: the Rényi MGF of order `a ≥ 2` of SamplerZ
(`falcon1024S`) with shift rejection against `D_{σ̄,t̄}` is at most `exp((a - 1)·εZ a)`. -/
theorem samplerZ_mgf1024 {a : ℝ} (ha : 2 ≤ a) (S : SampChoices) (hS : S.shiftRej = true)
    (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64) (hσ : inRangeB falcon1024S σ = true) :
    renyiMGF a 𝒟[samplerZ falcon1024S S ub σ t] (discreteGaussianMeasure σ.toReal t.toReal) ≤
      ENNReal.ofReal (Real.exp ((a - 1) * εZ a)) :=
  samplerZ_mgfP sminOk1024 ha S hS ub hub σ t hσ

omit [LawfulMonad m] in
/-- **Node.** At Falcon-1024 (`falcon1024S`), saturating a shift `≥ 64` instead of rejecting
moves at most `2⁻¹¹⁰` per call. -/
theorem samplerZ_tv1024 (S : SampChoices) (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64)
    (hσ : inRangeB falcon1024S σ = true) :
    (𝒟[samplerZ falcon1024S S ub σ t]).etvDist
        𝒟[samplerZ falcon1024S { S with shiftRej := true } ub σ t] ≤
      ENNReal.ofReal (if S.shiftRej then 0 else 1 / 2 ^ 110) :=
  samplerZ_tvP sminOk1024 S ub hub σ t hσ

end FalconPrecision.Exec
