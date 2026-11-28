/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignRange
public import FalconPrecision.Exec.KeyCheck1024

/-! # Integer ranges and words of the executable signer at Falcon-1024

`Exec.SignRange` at `n = 1024`: keys `k : RawKey 10` passing `check1024` (`‖f̂‖ ≤ 256`,
`‖F̂‖ ≤ 7365`, stored factors `‖ℓ̂‖ ≤ lam1024 L`, stored tree `storeC … σ1024q`) and the
integer-range check `checkRange C i W k σ1024q` (tables `twOkN C.x.rc 10`,
`bc = 2·(1024·12288) + 1`, `rangeT` on the stored tree), with the tree lemmas of `Exec.SignRangeN`
at the table cutoff `N = 10`.

Certificates: the target is within `7·2⁻²³` of the exact one (`targetX_ref1024`, both orders), and
`gBP lam1024 (2^(i-1)) 10 (7·2⁻²³) ≤ imE i` for `2^(i-1) ≥ 2²⁶` (`gB_ten`), so the theorems
assume `27 ≤ i` (the `bc` fit of `checkRange` gives only `i ≥ 26`). Theorems: `leafX_im1024`
(every leaf centre of the unbounded signer has `|Im t̄| ≤ imE i`), `signX_word1024` (the attempt
`signX` on `(i + 64)`-bit words is the unbounded one, `27 ≤ i ≤ 64`), `sign32_eq_sign64_1024`.

Not proved here: that any key passes `check1024` or `checkRange … σ1024q` (not proved for any key;
`#eval` runs of `checkRangeA` on round-3 KAT keys are evidence, not kernel proofs); the theorems
for `i < 27` or `i > 64`; sampler answers outside `⌊t̄⌋ ± W` (only `clampS W`); that a word
implementation of each operation computes `Fx.wrap` of the unbounded result; the whole signer
`signMsgX` on words here (only the attempt `signX`; the signer: `signMsgX_word1024`,
`Exec.SignEquiv1024`). -/

@[expose] public section

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.FFTReal FalconPrecision.Errors.Fixed ComplexConjugate

namespace FalconPrecision.Exec

/-! ## The target -/

theorem norm_evalAt_c1024 {c : ZPoly 10} (hc : ∀ j, |c j| < 12289) (o : Out 10) :
    ‖evalAt (fun j => (c j : ℂ)) (pt 10 o)‖ ≤ 12582912 := by
  have := norm_evalAt_le (fun j => (c j : ℂ)) (pt 10 o) (norm_pt 10 o) 12288 fun j => by
    rw [Complex.norm_intCast]
    have : |c j| ≤ 12288 := by linarith [hc j]
    exact_mod_cast this
  norm_num at this
  exact this

section Target

variable (C : Choices) (hw : C.word = none) (htw : twOkN C.x.rc 10 = true) (f F c : ZPoly 10)
  (hc : ∀ j, |c j| < 12289)
include hw htw hc

/-- **Target error at Falcon-1024**: with `‖f̂‖ ≤ 256`, `‖F̂‖ ≤ 7365` (`check1024`), the unbounded
target is within `7·2⁻²³` of the exact one, in both orders. -/
theorem targetX_ref1024 (hf : ∀ o, ‖evalAt (fun j => (f j : ℂ)) (pt 10 o)‖ ≤ 256)
    (hF : ∀ o, ‖evalAt (fun j => (F j : ℂ)) (pt 10 o)‖ ≤ 7365) (o : Out 10) :
    ‖((targetX C f F c).1 o).toC - (tRef f F c).1 o‖ ≤ 7 / 2 ^ 23 ∧
      ‖((targetX C f F c).2 o).toC - (tRef f F c).2 o‖ ≤ 7 / 2 ^ 23 := by
  have Ec := fftW_errN C hw htw _ 10 le_rfl c (norm_evalAt_c1024 hc) o
  have Ef := fftW_errN C hw htw _ 10 le_rfl f hf o
  have EF := fftW_errN C hw htw _ 10 le_rfl F hF o
  norm_num at Ec Ef EF
  have hcB := norm_evalAt_c1024 hc o
  have hfB := hf o
  have hFB := hF o
  set ce := evalAt (fun j => (c j : ℂ)) (pt 10 o)
  set fe := evalAt (fun j => (f j : ℂ)) (pt 10 o)
  set Fe := evalAt (fun j => (F j : ℂ)) (pt 10 o)
  have nc : ‖(fftW C 10 c o).toC‖ ≤ 12582913 := by
    linarith [norm_le_norm_add_norm_sub' (fftW C 10 c o).toC ce]
  cases ht : C.target
  · simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id, tRef]
    set qh := divqX C.x.rm C.qinv (fftW C 10 c o)
    have hq : ‖qh.toC - ce / 12289‖ ≤ 3 / 2 ^ 36 := by
      have h1 : ‖qh.toC - (fftW C 10 c o).toC / 12289‖ ≤
          2 / 2 ^ 64 + 2 * ‖(fftW C 10 c o).toC‖ / 2 ^ 64 := divqX_err C.x.rm C.qinv _
      rw [show qh.toC - ce / 12289 = (qh.toC - (fftW C 10 c o).toC / 12289) +
        ((fftW C 10 c o).toC - ce) / 12289 by ring]
      refine (norm_add_le _ _).trans ?_
      rw [norm_div, Complex.norm_ofNat]
      linarith
    have hqn : ‖qh.toC‖ ≤ 1024 := by
      have := norm_le_norm_add_norm_sub' qh.toC (ce / 12289)
      rw [norm_div, Complex.norm_ofNat] at this
      linarith
    constructor
    · have e := norm_prod_err (x := -(ce / 12289)) (y := Fe)
        (Cx.mul_err C.x.rm qh.neg (fftW C 10 F o))
      rw [Cx.toC_neg, norm_neg, neg_sub_neg, norm_sub_rev (ce / 12289)] at e
      rw [show -(ce * Fe) / 12289 = -(ce / 12289) * Fe by ring]
      have m1 := mul_le_mul hqn EF (norm_nonneg _) (by norm_num)
      have m2 := mul_le_mul hq hFB (norm_nonneg _) (by norm_num)
      linarith
    · have e := norm_prod_err (x := ce / 12289) (y := fe) (Cx.mul_err C.x.rm qh (fftW C 10 f o))
      rw [show ce * fe / 12289 = ce / 12289 * fe by ring]
      have m1 := mul_le_mul hqn Ef (norm_nonneg _) (by norm_num)
      have m2 := mul_le_mul hq hfB (norm_nonneg _) (by norm_num)
      linarith
  · simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id, tRef]
    have key : ∀ (g : ZPoly 10) (B : ℝ), ‖evalAt (fun j => (g j : ℂ)) (pt 10 o)‖ ≤ B →
        B ≤ 7365 → ‖(fftW C 10 g o).toC - evalAt (fun j => (g j : ℂ)) (pt 10 o)‖ ≤ 3 / 2 ^ 33 →
        ‖(divqX C.x.rm C.qinv ((fftW C 10 c o).mul C.x.rm (fftW C 10 g o))).toC -
          ce * evalAt (fun j => (g j : ℂ)) (pt 10 o) / 12289‖ ≤ 7 / 2 ^ 23 ∧
        ‖(divqX C.x.rm C.qinv ((fftW C 10 c o).mul C.x.rm (fftW C 10 g o)).neg).toC -
          -(ce * evalAt (fun j => (g j : ℂ)) (pt 10 o)) / 12289‖ ≤ 7 / 2 ^ 23 := by
      intro g B hg hB hE
      set P := (fftW C 10 c o).mul C.x.rm (fftW C 10 g o)
      have e := norm_prod_err (x := ce) (y := evalAt (fun j => (g j : ℂ)) (pt 10 o))
        (Cx.mul_err C.x.rm (fftW C 10 c o) (fftW C 10 g o))
      have m1 := mul_le_mul nc hE (norm_nonneg _) (by norm_num)
      have m2 := mul_le_mul Ec (hg.trans hB) (norm_nonneg _) (by norm_num)
      have hP : ‖P.toC - ce * evalAt (fun j => (g j : ℂ)) (pt 10 o)‖ ≤ 9 / 2 ^ 10 := by
        linarith
      have hPn : ‖P.toC‖ ≤ 2 ^ 37 := by
        have := mul_le_mul hcB (hg.trans hB) (norm_nonneg _) (by norm_num)
        rw [← norm_mul] at this
        linarith [norm_le_norm_add_norm_sub' P.toC (ce * evalAt (fun j => (g j : ℂ)) (pt 10 o))]
      have d1 := divqX_err C.x.rm C.qinv P
      have d2 := divqX_err C.x.rm C.qinv P.neg
      rw [Cx.toC_neg, norm_neg] at d2
      constructor
      · rw [show (divqX C.x.rm C.qinv P).toC - ce * evalAt (fun j => (g j : ℂ)) (pt 10 o) / 12289 =
          ((divqX C.x.rm C.qinv P).toC - P.toC / 12289) +
            (P.toC - ce * evalAt (fun j => (g j : ℂ)) (pt 10 o)) / 12289 by ring]
        refine (norm_add_le _ _).trans ?_
        rw [norm_div, Complex.norm_ofNat]
        linarith
      · rw [show (divqX C.x.rm C.qinv P.neg).toC - -(ce * evalAt (fun j => (g j : ℂ)) (pt 10 o)) /
          12289 = ((divqX C.x.rm C.qinv P.neg).toC - -P.toC / 12289) -
            (P.toC - ce * evalAt (fun j => (g j : ℂ)) (pt 10 o)) / 12289 by ring]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_div, Complex.norm_ofNat]
        linarith
    exact ⟨(key F 7365 hFB le_rfl (by linarith)).2, (key f 256 hfB (by norm_num) (by linarith)).1⟩

theorem norm_fftW_c1024 (o : Out 10) : ‖(fftW C 10 c o).toC‖ ≤ 12582913 := by
  have Ec := fftW_errN C hw htw _ 10 le_rfl c (norm_evalAt_c1024 hc) o
  norm_num at Ec
  linarith [norm_le_norm_add_norm_sub' (fftW C 10 c o).toC
    (evalAt (fun j => (c j : ℂ)) (pt 10 o)), norm_evalAt_c1024 hc o]

/-- The unbounded scale-first target within `checkRange`'s root bound at Falcon-1024. -/
theorem targetX_norm_sf1024 (ht : C.target = .scaleFirst) (o : Out 10) :
    ‖((targetX C f F c).1 o).toC‖ ≤ ((max ((2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
        (nmax 10 (fftW C 10 F) + 1) + 1) ((2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
        (nmax 10 (fftW C 10 f) + 1) + 1) : ℚ) : ℝ) ∧
      ‖((targetX C f F c).2 o).toC‖ ≤ ((max ((2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
        (nmax 10 (fftW C 10 F) + 1) + 1) ((2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
        (nmax 10 (fftW C 10 f) + 1) + 1) : ℚ) : ℝ) := by
  simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id]
  have hq := norm_divqX_le C.x.rm C.qinv (fftW C 10 c o) (norm_fftW_c1024 C hw htw c hc o)
  have h0 := norm_le_nmax (fftW C 10 F) o
  have h1 := norm_le_nmax (fftW C 10 f) o
  have m0 := mul_le_mul (hq.trans (by norm_num : _ ≤ (1024 : ℝ))) h0 (norm_nonneg _)
    (by norm_num)
  have m1 := mul_le_mul (hq.trans (by norm_num : _ ≤ (1024 : ℝ))) h1 (norm_nonneg _)
    (by norm_num)
  have p0 := Cx.norm_mul_le C.x.rm (divqX C.x.rm C.qinv (fftW C 10 c o)).neg (fftW C 10 F o)
  have p1 := Cx.norm_mul_le C.x.rm (divqX C.x.rm C.qinv (fftW C 10 c o)) (fftW C 10 f o)
  rw [Cx.toC_neg, norm_neg] at p0
  have n0 : (0 : ℝ) ≤ nmax 10 (fftW C 10 F) := (norm_nonneg _).trans h0
  have n1 : (0 : ℝ) ≤ nmax 10 (fftW C 10 f) := (norm_nonneg _).trans h1
  push_cast
  constructor
  · exact le_max_of_le_left (by linarith [p0, m0, n0])
  · exact le_max_of_le_right (by linarith [p1, m1, n1])

/-- The unbounded multiply-first target within `checkRange`'s root bound at Falcon-1024. -/
theorem targetX_norm_mf1024 (ht : C.target = .multiplyFirst) (o : Out 10) :
    ‖((targetX C f F c).1 o).toC‖ ≤ ((2 * ((2 * (1024 * 12288) + 1) *
        max (nmax 10 (fftW C 10 F) + 1) (nmax 10 (fftW C 10 f) + 1) + 1) / 12289 + 1 : ℚ) : ℝ) ∧
      ‖((targetX C f F c).2 o).toC‖ ≤ ((2 * ((2 * (1024 * 12288) + 1) *
        max (nmax 10 (fftW C 10 F) + 1) (nmax 10 (fftW C 10 f) + 1) + 1) / 12289 + 1 : ℚ) : ℝ) := by
  simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id]
  have hcn := norm_fftW_c1024 C hw htw c hc o
  have hM : (0 : ℝ) ≤ max ((nmax 10 (fftW C 10 F) : ℝ) + 1) ((nmax 10 (fftW C 10 f) : ℝ) + 1) :=
    le_max_of_le_left (by linarith [(norm_nonneg _).trans (norm_le_nmax (fftW C 10 F) o)])
  have key : ∀ g : ZPoly 10, (nmax 10 (fftW C 10 g) : ℝ) + 1 ≤
      max ((nmax 10 (fftW C 10 F) : ℝ) + 1) ((nmax 10 (fftW C 10 f) : ℝ) + 1) →
      ‖((fftW C 10 c o).mul C.x.rm (fftW C 10 g o)).toC‖ ≤ (2 * (1024 * 12288) + 1) *
        max ((nmax 10 (fftW C 10 F) : ℝ) + 1) ((nmax 10 (fftW C 10 f) : ℝ) + 1) + 1 :=
    fun g hg => by
      have m := mul_le_mul hcn ((norm_le_nmax (fftW C 10 g) o).trans (by linarith))
        (norm_nonneg _) (by norm_num)
      linarith [Cx.norm_mul_le C.x.rm (fftW C 10 c o) (fftW C 10 g o)]
  have kF := key F (le_max_left _ _)
  have kf := key f (le_max_right _ _)
  have d0 := norm_divqX_le C.x.rm C.qinv _ (B := (2 * (1024 * 12288) + 1) *
    max ((nmax 10 (fftW C 10 F) : ℝ) + 1) (nmax 10 (fftW C 10 f) + 1) + 1)
    (by rw [Cx.toC_neg, norm_neg]; exact kF)
  have d1 := norm_divqX_le C.x.rm C.qinv _ kf
  push_cast
  constructor <;> linarith

end Target

/-! ## Leaf centres -/

/-- The leaf-centre certificate at depth 10 (`lam1024`): for `K ≥ 2²⁶` and `d ≤ 7·2⁻²³`. -/
theorem gB_ten {K d : ℝ} (hK : 2 ^ 26 ≤ K) (hd : d ≤ 7 / 2 ^ 23) :
    gBP lam1024 K 10 d ≤ K / 2 ^ 32 := by
  simp only [gBP, mB, lam1024]
  norm_num
  linarith

theorem checkRange_sf1024 {C : Choices} {i W : ℕ} {k : RawKey 10} (ht : C.target = .scaleFirst)
    (h : checkRange C i W k σ1024q = true) : twOkN C.x.rc 10 = true ∧
      (2 * (1024 * 12288) + 1 : ℚ) < 2 ^ (i - 1) ∧ 2 * l1Q k.f + 1 < (2 : ℚ) ^ (i - 1) ∧
      2 * l1Q k.F + 1 < (2 : ℚ) ^ (i - 1) ∧ (2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
        (nmax 10 (fftW { C with word := none } 10 k.F) + 1) + 1 < (2 : ℚ) ^ (i - 1) ∧
      (2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
        (nmax 10 (fftW { C with word := none } 10 k.f) + 1) + 1 < (2 : ℚ) ^ (i - 1) ∧
      rangeT i W (imE i) (storeC C.x C.xn k σ1024q)
        (max ((2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
          (nmax 10 (fftW { C with word := none } 10 k.F) + 1) + 1)
        ((2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
          (nmax 10 (fftW { C with word := none } 10 k.f) + 1) + 1)) = true := by
  obtain ⟨x, xn, tg, qi, wd, rch, sl, cap, b2, ib, sc⟩ := C
  change tg = _ at ht
  subst ht
  simp only [checkRange, Bool.and_eq_true, List.all_eq_true, List.mem_append,
    List.mem_cons, List.not_mem_nil, fitsQ, decide_eq_true_eq] at h
  obtain ⟨⟨htw, hfit⟩, hrng⟩ := h
  exact ⟨htw, hfit _ (Or.inl (Or.inl rfl)), hfit _ (Or.inl (Or.inr (Or.inl rfl))),
    hfit _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))), hfit _ (Or.inr (Or.inr (Or.inl rfl))),
    hfit _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hrng⟩

theorem checkRange_mf1024 {C : Choices} {i W : ℕ} {k : RawKey 10}
    (ht : C.target = .multiplyFirst) (h : checkRange C i W k σ1024q = true) :
    twOkN C.x.rc 10 = true ∧
      (2 * (1024 * 12288) + 1 : ℚ) < 2 ^ (i - 1) ∧ 2 * l1Q k.f + 1 < (2 : ℚ) ^ (i - 1) ∧
      2 * l1Q k.F + 1 < (2 : ℚ) ^ (i - 1) ∧ (2 * (1024 * 12288) + 1) *
        max (nmax 10 (fftW { C with word := none } 10 k.F) + 1)
          (nmax 10 (fftW { C with word := none } 10 k.f) + 1) + 1 < (2 : ℚ) ^ (i - 1) ∧
      2 * ((2 * (1024 * 12288) + 1) * max (nmax 10 (fftW { C with word := none } 10 k.F) + 1)
        (nmax 10 (fftW { C with word := none } 10 k.f) + 1) + 1) / 12289 + 1 <
          (2 : ℚ) ^ (i - 1) ∧
      rangeT i W (imE i) (storeC C.x C.xn k σ1024q) (2 * ((2 * (1024 * 12288) + 1) *
        max (nmax 10 (fftW { C with word := none } 10 k.F) + 1)
          (nmax 10 (fftW { C with word := none } 10 k.f) + 1) + 1) / 12289 + 1) = true := by
  obtain ⟨x, xn, tg, qi, wd, rch, sl, cap, b2, ib, sc⟩ := C
  change tg = _ at ht
  subst ht
  simp only [checkRange, Bool.and_eq_true, List.all_eq_true, List.mem_append,
    List.mem_cons, List.not_mem_nil, fitsQ, decide_eq_true_eq] at h
  obtain ⟨⟨htw, hfit⟩, hrng⟩ := h
  exact ⟨htw, hfit _ (Or.inl (Or.inl rfl)), hfit _ (Or.inl (Or.inr (Or.inl rfl))),
    hfit _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))), hfit _ (Or.inr (Or.inl rfl)),
    hfit _ (Or.inr (Or.inr (Or.inl rfl))), hrng⟩

/-- The shared lemma at the root at Falcon-1024: on a key passing `check1024` and
`checkRange C i W k σ1024q` with `27 ≤ i ≤ 64`, every leaf centre of the unbounded signer on a hash
with `|c j| < q` has `|Im t̄| ≤ imE i`. -/
theorem leafR_root1024 (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi27 : 27 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey 10) (hk : check1024 C.x C.xn δq k = true)
    (hr : checkRange C i W k σ1024q = true) (c : ZPoly 10) (hc : ∀ j, |c j| < 12289) :
    ∀ x, LeafR { C with word := none } W (storeC C.x C.xn k σ1024q)
      (targetX { C with word := none } k.f k.F c).1
      (targetX { C with word := none } k.f k.F c).2 x → |x.im.toReal| ≤ imE i := by
  have hko := check_ok C.x C.xn
    (show check C.x C.xn δq k 256 7365 (1298280334 / 10 ^ 9) lam1024q σ1024q = true from hk)
  have hT : (storeC C.x C.xn k σ1024q).Ok (1298280334 / 10 ^ 9) lam1024q :=
    storeB_centreP C.x C.xn k σ1024q ▸ CTree.ok_of_okB _ hko.ok
  have hR : (storeC C.x C.xn k σ1024q).realB = true := storeB_centreP C.x C.xn k σ1024q ▸ hko.real
  have hf : ∀ o, ‖evalAt (fun j => (k.f j : ℂ)) (pt 10 o)‖ ≤ 256 := fun o => le_of_le_of_eq
    (CB.norm_le_of_normLeB (fftB_holds C.x _ 10 k.f o) (hko.hf o)) (by norm_num)
  have hF : ∀ o, ‖evalAt (fun j => (k.F j : ℂ)) (pt 10 o)‖ ≤ 7365 := fun o => le_of_le_of_eq
    (CB.norm_le_of_normLeB (fftB_holds C.x _ 10 k.F o) (hko.hF o)) (by norm_num)
  have hK : (2 : ℝ) ^ 26 ≤ 2 ^ (i - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hd := targetX_ref1024 { C with word := none } rfl
  rcases (show C.target = .scaleFirst ∨ C.target = .multiplyFirst by cases C.target <;> simp)
    with ht | ht
  · obtain ⟨htw, -, -, -, -, -, hrng⟩ := checkRange_sf1024 ht hr
    refine (ffsX_soundN { C with word := none } rfl htw lam1024q_bounds i W hi64 (imE i) _ le_rfl
      hT hR _ _ _ (fun o => targetX_norm_sf1024 { C with word := none } rfl htw k.f k.F c hc ht o)
      hrng _ _ (isReal_tRef k.f k.F c).1 (isReal_tRef k.f k.F c).2 (7 / 2 ^ 23)
      (hd htw k.f k.F c hc hf hF) ?_).1
    rw [imE_eq]
    exact gB_ten hK le_rfl
  · obtain ⟨htw, -, -, -, -, -, hrng⟩ := checkRange_mf1024 ht hr
    refine (ffsX_soundN { C with word := none } rfl htw lam1024q_bounds i W hi64 (imE i) _ le_rfl
      hT hR _ _ _ (fun o => targetX_norm_mf1024 { C with word := none } rfl htw k.f k.F c hc ht o)
      hrng _ _ (isReal_tRef k.f k.F c).1 (isReal_tRef k.f k.F c).2 (7 / 2 ^ 23)
      (hd htw k.f k.F c hc hf hF) ?_).1
    rw [imE_eq]
    exact gB_ten hK le_rfl

/-- **Leaf centres are nearly real at Falcon-1024**: on a key passing `check1024` (every stored
`ℓ̂` conjugate-symmetric; `‖ℓ̂‖ ≤ lam1024 L`; `‖f̂‖ ≤ 256`, `‖F̂‖ ≤ 7365`) and
`checkRange C i W k σ1024q` (tables `twOkN C.x.rc 10`, every value `< 2^(i - 1)`) with
`27 ≤ i ≤ 64`, every leaf centre of the unbounded signer on a hash with `|c j| < q` has
`|Im t̄| ≤ imE i`. -/
theorem leafX_im1024 (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi27 : 27 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey 10) (hk : check1024 C.x C.xn δq k = true)
    (hr : checkRange C i W k σ1024q = true) (c : ZPoly 10) (hc : ∀ j, |c j| < 12289) {x : Cx 64}
    (hx : LeafX { C with word := none } W (storeC C.x C.xn k σ1024q)
      (targetX { C with word := none } k.f k.F c).1
      (targetX { C with word := none } k.f k.F c).2 x) :
    |x.im.toRat| ≤ imE i := by
  have h := leafR_root1024 C δq i W hi27 hi64 k hk hr c hc x (leafR_of_leafX _ W _ _ _ x hx)
  rw [Fx.toReal_eq_toRat] at h
  exact_mod_cast h

/-! ## Words -/

section TargetWord

variable (C : Choices) (htw : twOkN C.x.rc 10 = true) {i : ℕ} (hi : 1 ≤ i) (f F c : ZPoly 10)
  (hc : ∀ j, |c j| < 12289) (hK : (2 : ℝ) ^ 25 ≤ 2 ^ (i - 1))
  (hf : 2 * l1Q f + 1 < (2 : ℚ) ^ (i - 1)) (hF : 2 * l1Q F + 1 < (2 : ℚ) ^ (i - 1))
include htw hi hc hK hf hF

theorem fftW_word_target1024 :
    fftW { C with word := some i } 10 c = fftW { C with word := none } 10 c ∧
      fftW { C with word := some i } 10 f = fftW { C with word := none } 10 f ∧
      fftW { C with word := some i } 10 F = fftW { C with word := none } 10 F := by
  have hf' : 2 * (l1Q f : ℝ) + 1 < 2 ^ (i - 1) := by exact_mod_cast hf
  have hF' : 2 * (l1Q F : ℝ) + 1 < 2 ^ (i - 1) := by exact_mod_cast hF
  exact ⟨fftW_wordN C le_rfl htw hi 12582912 (by linarith) 10 le_rfl c (norm_evalAt_c1024 hc),
    fftW_wordN C le_rfl htw hi _ hf' 10 le_rfl f (norm_evalAt_le_l1 f),
    fftW_wordN C le_rfl htw hi _ hF' 10 le_rfl F (norm_evalAt_le_l1 F)⟩

theorem targetX_word_sf1024 (ht : C.target = .scaleFirst)
    (h0 : (2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
      (nmax 10 (fftW { C with word := none } 10 F) + 1) + 1 < (2 : ℚ) ^ (i - 1))
    (h1 : (2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
      (nmax 10 (fftW { C with word := none } 10 f) + 1) + 1 < (2 : ℚ) ^ (i - 1)) :
    targetX { C with word := some i } f F c = targetX { C with word := none } f F c := by
  obtain ⟨ec, ef, eF⟩ := fftW_word_target1024 C htw hi f F c hc hK hf hF
  have h0' := (Rat.cast_lt (K := ℝ)).2 h0
  have h1' := (Rat.cast_lt (K := ℝ)).2 h1
  push_cast at h0' h1'
  have hq : ∀ o, ‖(divqX C.x.rm C.qinv (fftW { C with word := none } 10 c o)).toC‖ ≤ 1024 :=
    fun o => (norm_divqX_le C.x.rm C.qinv _
      (norm_fftW_c1024 { C with word := none } rfl htw c hc o)).trans (by norm_num)
  have key : ∀ (g : ZPoly 10) (o : Out 10), (2 * (2 * (1024 * 12288) + 1) / 12289 + 1) *
      ((nmax 10 (fftW { C with word := none } 10 g) : ℝ) + 1) + 1 < 2 ^ (i - 1) →
      ‖(divqX C.x.rm C.qinv (fftW { C with word := none } 10 c o)).toC‖ *
        ‖(fftW { C with word := none } 10 g o).toC‖ + 2 / 2 ^ 64 < 2 ^ (i - 1) :=
    fun g o hg => by
      have := mul_le_mul (hq o) (norm_le_nmax (fftW { C with word := none } 10 g) o)
        (norm_nonneg _) (by norm_num)
      have := (norm_nonneg _).trans (norm_le_nmax (fftW { C with word := none } 10 g) o)
      linarith
  obtain ⟨x, xn, tg, qi, wd, rch, sl, cap, b2, ib, sc⟩ := C
  change tg = _ at ht
  subst ht
  simp only [targetX, memo_eq, wordFn_none, Cx.wr_id, Cx.mulW_id]
  rw [ec, ef, eF]
  dsimp only at hq key ⊢
  refine Prod.ext (funext fun o => ?_) (funext fun o => ?_) <;> dsimp only
  · have hm := key F o h0'
    rw [← norm_neg, ← Cx.toC_neg] at hm
    rw [Cx.wr_some hi ((hq o).trans_lt (by linarith)),
      Cx.wr_some hi (by rw [Cx.toC_neg, norm_neg]; exact (hq o).trans_lt (by linarith)),
      Cx.mulW_some hi _ hm]
  · rw [Cx.wr_some hi ((hq o).trans_lt (by linarith)), Cx.mulW_some hi _ (key f o h1')]

theorem targetX_word_mf1024 (ht : C.target = .multiplyFirst)
    (h0 : (2 * (1024 * 12288) + 1) * max (nmax 10 (fftW { C with word := none } 10 F) + 1)
      (nmax 10 (fftW { C with word := none } 10 f) + 1) + 1 < (2 : ℚ) ^ (i - 1))
    (h1 : 2 * ((2 * (1024 * 12288) + 1) * max (nmax 10 (fftW { C with word := none } 10 F) + 1)
      (nmax 10 (fftW { C with word := none } 10 f) + 1) + 1) / 12289 + 1 < (2 : ℚ) ^ (i - 1)) :
    targetX { C with word := some i } f F c = targetX { C with word := none } f F c := by
  obtain ⟨ec, ef, eF⟩ := fftW_word_target1024 C htw hi f F c hc hK hf hF
  have h0' := (Rat.cast_lt (K := ℝ)).2 h0
  have h1' := (Rat.cast_lt (K := ℝ)).2 h1
  push_cast at h0' h1'
  have hcn := fun o => norm_fftW_c1024 { C with word := none } rfl htw c hc o
  have hM : (0 : ℝ) ≤ max ((nmax 10 (fftW { C with word := none } 10 F) : ℝ) + 1)
      ((nmax 10 (fftW { C with word := none } 10 f) : ℝ) + 1) :=
    le_max_of_le_left (by linarith [(norm_nonneg _).trans (norm_le_nmax
      (fftW { C with word := none } 10 F) (Out.ofIdx _ 0))])
  have key : ∀ (g : ZPoly 10) (o : Out 10),
      (nmax 10 (fftW { C with word := none } 10 g) : ℝ) + 1 ≤
        max ((nmax 10 (fftW { C with word := none } 10 F) : ℝ) + 1)
          ((nmax 10 (fftW { C with word := none } 10 f) : ℝ) + 1) →
      ‖(fftW { C with word := none } 10 c o).toC‖ * ‖(fftW { C with word := none } 10 g o).toC‖ ≤
        (2 * (1024 * 12288) + 1) * max ((nmax 10 (fftW { C with word := none } 10 F) : ℝ) + 1)
          ((nmax 10 (fftW { C with word := none } 10 f) : ℝ) + 1) - 1 := fun g o hg => by
    have := mul_le_mul (hcn o) ((norm_le_nmax (fftW { C with word := none } 10 g) o).trans
      (by linarith)) (norm_nonneg _) (by norm_num)
    linarith
  have fin : ∀ (g : ZPoly 10) (o : Out 10),
      (nmax 10 (fftW { C with word := none } 10 g) : ℝ) + 1 ≤
        max ((nmax 10 (fftW { C with word := none } 10 F) : ℝ) + 1)
          ((nmax 10 (fftW { C with word := none } 10 f) : ℝ) + 1) → ∀ z : Cx 64,
      ‖z.toC‖ = ‖((fftW { C with word := none } 10 c o).mul C.x.rm
        (fftW { C with word := none } 10 g o)).toC‖ →
      (fftW { C with word := none } 10 c o).mulW (wordFn (some i)) C.x.rm
          (fftW { C with word := none } 10 g o) =
        (fftW { C with word := none } 10 c o).mul C.x.rm (fftW { C with word := none } 10 g o) ∧
      z.wr (wordFn (some i)) = z ∧ (divqX C.x.rm C.qinv z).wr (wordFn (some i)) =
        divqX C.x.rm C.qinv z := fun g o hg z hz => by
    have k := key g o hg
    have hP := Cx.norm_mul_le C.x.rm (fftW { C with word := none } 10 c o)
      (fftW { C with word := none } 10 g o)
    have hd := norm_divqX_le C.x.rm C.qinv z (hz.trans_le hP)
    refine ⟨Cx.mulW_some hi _ (by linarith), Cx.wr_some hi (by linarith), Cx.wr_some hi ?_⟩
    refine hd.trans_lt ?_
    linarith
  obtain ⟨x, xn, tg, qi, wd, rch, sl, cap, b2, ib, sc⟩ := C
  change tg = _ at ht
  subst ht
  simp only [targetX, memo_eq, wordFn_none, Cx.wr_id, Cx.mulW_id]
  rw [ec, ef, eF]
  dsimp only at fin ⊢
  refine Prod.ext (funext fun o => ?_) (funext fun o => ?_) <;> dsimp only
  · obtain ⟨e1, e2, e3⟩ := fin F o (le_max_left _ _) _ (by rw [Cx.toC_neg, norm_neg])
    rw [e1, e2, e3]
  · obtain ⟨e1, -, e3⟩ := fin f o (le_max_right _ _) _ rfl
    rw [e1, e3]

end TargetWord

/-- **No reduction changes a value of the signing attempt `signX` at Falcon-1024**: on a key
passing `check1024` and `checkRange C i W k σ1024q` with `27 ≤ i ≤ 64`, with sampler answers
within `W` of `⌊t̄⌋`, the signing attempt on `(i + 64)`-bit words is the unbounded one, in every
lawful monad. -/
theorem signX_word1024 (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi27 : 27 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey 10) (hc : check1024 C.x C.xn δq k = true)
    (hk : checkRange C i W k σ1024q = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (samp : Fx 64 → Fx 64 → m ℤ) (c : ZPoly 10) :
    signX { C with word := some i } (clampS W samp) (storeC C.x C.xn k σ1024q) k c =
      signX { C with word := none } (clampS W samp) (storeC C.x C.xn k σ1024q) k c := by
  unfold signX
  by_cases hcq : ∀ j, |c j| < 12289
  swap
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hcq), ite_eq_right_of_eq_false _ _ (eq_false hcq)]
  have hlf := leafR_root1024 C δq i W hi27 hi64 k hc hk c hcq
  have hi : 1 ≤ i := by omega
  have hK : (2 : ℝ) ^ 25 ≤ 2 ^ (i - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcq), ite_eq_left_of_eq_true _ _ (eq_true hcq)]
  rcases (show C.target = .scaleFirst ∨ C.target = .multiplyFirst by cases C.target <;> simp)
    with ht | ht
  · obtain ⟨htw, -, hf, hF, h0, h1, hrng⟩ := checkRange_sf1024 ht hk
    rw [targetX_word_sf1024 C htw hi k.f k.F c hcq hK hf hF ht h0 h1,
      ffsX_wordN C htw i W hi hi64 (imE i) _ (storeC C.x C.xn k σ1024q) le_rfl _ _ _
        (fun o => targetX_norm_sf1024 { C with word := none } rfl htw k.f k.F c hcq ht o) hrng
        hlf]
  · obtain ⟨htw, -, hf, hF, h0, h1, hrng⟩ := checkRange_mf1024 ht hk
    rw [targetX_word_mf1024 C htw hi k.f k.F c hcq hK hf hF ht h0 h1,
      ffsX_wordN C htw i W hi hi64 (imE i) _ (storeC C.x C.xn k σ1024q) le_rfl _ _ _
        (fun o => targetX_norm_mf1024 { C with word := none } rfl htw k.f k.F c hcq ht o) hrng
        hlf]

/-- **32.64 = 64.64 at Falcon-1024**: on a key passing `check1024` and `checkRange … σ1024q` at
`i = 32` and `i = 64`, with sampler answers within `W` of `⌊t̄⌋`, the signing attempts `signX` on
96-bit and on 128-bit words are bit-identical. -/
theorem sign32_eq_sign64_1024 (C : Choices) (δq : ℕ → ℚ) (W : ℕ) (k : RawKey 10)
    (hc : check1024 C.x C.xn δq k = true) (h32 : checkRange C 32 W k σ1024q = true)
    (h64 : checkRange C 64 W k σ1024q = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (samp : Fx 64 → Fx 64 → m ℤ) (c : ZPoly 10) :
    signX { C with word := some 32 } (clampS W samp) (storeC C.x C.xn k σ1024q) k c =
      signX { C with word := some 64 } (clampS W samp) (storeC C.x C.xn k σ1024q) k c :=
  (signX_word1024 C δq 32 W (by norm_num) (by norm_num) k hc h32 samp c).trans
    (signX_word1024 C δq 64 W (by norm_num) le_rfl k hc h64 samp c).symm

end FalconPrecision.Exec
