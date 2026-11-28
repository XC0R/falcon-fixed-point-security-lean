/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignRangeN

/-! # Integer ranges and leaf centres of the executable signer

Every rounding of `RMode` is within `2⁻⁶⁴` (`floor` included), every computed table at levels
`≤ 8` within `δ = 0.7072·2⁻⁶⁴` of `ζ`, `ζ̄/2` (`twOk`, part of `checkRange`).

`ReachX C W T t0 t1 s`: `s` is an output of `ffsX C` on `T` from `(t0, t1)` for some sampler
answers within `W` of `⌊t̄⌋`, the checks ignored (`OutX` outputs are such, `reachX_of_outX`);
`LeafR` its leaf centres. `ffsX_bind_congr`: in every lawful monad, two continuations of
`ffsX C (clampS W samp)` that agree on `none` and on `ReachX` outputs give the same computation.

`ffsX_dev`: on inputs bounded by `A` with `rangeT i W E T A` and leaf centres `|Im| ≤ E`, every
output is within `devT W E T` of the input. `ffsX_sound` (the shared lemma, one induction in run
order): with exact conjugate-symmetric references within `d` of the inputs (`IsReal`), every leaf
centre has `|Im| ≤ gB (2^(i-1)) L d ≤ E`, and every output within `mB` of the exact FFT of its
integers. `ffsX_word`: then no reduction to `(i + 64)`-bit words changes a value. With the target
bounds (`fftW_err`, `targetX_ref`, `targetX_norm_sf`, `targetX_norm_mf`, `fftW_word`,
`targetX_word_sf`, `targetX_word_mf`) these give `leafX_im`, `signX_word` and `sign32_eq_sign64`.
The amplification of the leaf-centre error uses `‖ℓ̂‖ ≤ lam512 L` and `‖f̂‖ ≤ 255`, `‖F̂‖ ≤ 3500`
from `check`: the target is within `2⁻²²` of the exact one (`targetX_ref`) and
`gB (2^(i-1)) 9 2⁻²² ≤ imE i` for `2^(i-1) ≥ 2²⁴` (`gB_nine`; `checkRange` fails for `i < 25`).
The tree lemmas are the instances at the table cutoff `N = 9` of those of `Exec.SignRangeN` (any
cutoff, `fftW_wordN` at `N ≤ 10`; `gB K = gBP lam512 K` by `gB_eq_gBP`); Falcon-1024:
`Exec.SignRange1024`.

Not proved here: that any key passes `check` or `checkRange` (not proved for any key; round-3 KAT
entry 0 passes `checkFast` (ties to even, `xn = 0`) at `δ45q` and `checkRangeA` (`cKat`:
scale-first) at `i = 32`, `64`, `W = 19` by `#eval`, test/ExecRound3.lean); the theorems for
`i > 64`; sampler answers outside `⌊t̄⌋ ± W` (only the clamped sampler `clampS W` is covered); that
a word implementation of each operation computes `Fx.wrap` of the unbounded result; the whole
signer `signMsgX` on words (only the attempt `signX`). -/

@[expose] public section

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.FFTReal FalconPrecision.Errors.Fixed ComplexConjugate

namespace FalconPrecision.Exec

/-! ## Tables -/

section Tables

variable {rc : RMode} (h : twOk rc = true) {L : ℕ} (hL : L ≤ 8) (o : Out L)
include h hL

theorem tw_err : ‖(twB rc 64 L o).c.toC - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 64 :=
  tw_errN (N := 9) h (by omega) o

theorem tws_err :
    ‖(twsB rc 64 L o).c.toC - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 64 :=
  tws_errN (N := 9) h (by omega) o

theorem norm_tw_le : ‖(twB rc 64 L o).c.toC‖ ≤ 1 + 7072 / 10000 / 2 ^ 64 :=
  norm_tw_leN (N := 9) h (by omega) o

theorem norm_tws_le : ‖(twsB rc 64 L o).c.toC‖ ≤ 1 / 2 + 7072 / 10000 / 2 ^ 64 :=
  norm_tws_leN (N := 9) h (by omega) o

end Tables

/-! ## The FFT -/

/-- **FFT error**: with every exact output within `B`, every output of the unbounded `fftW` (any
rounding, tables within `δ`) is within `4^L·(δB + 4·2⁻⁶⁴)` of the exact one. -/
theorem fftW_err (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true) (B : ℝ) :
    ∀ (L : ℕ), L ≤ 9 → ∀ (a : Fin (2 ^ L) → ℤ),
      (∀ o, ‖evalAt (fun j => (a j : ℂ)) (pt L o)‖ ≤ B) → ∀ o,
        ‖(fftW C L a o).toC - evalAt (fun j => (a j : ℂ)) (pt L o)‖ ≤
          4 ^ L * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) :=
  fftW_errN C hw (N := 9) htw B

/-! ## One node of the unbounded run -/

section Node

variable (C : Choices) (hw : C.word = none) {L : ℕ} (htw : twOk C.x.rc = true) (hL : L ≤ 8)
include hw htw hL

theorem splitW_bound (t : Out (L + 1) → Cx 64) {A : ℝ} (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hA : A < 2 ^ 62) (o : Out L) :
    ‖((splitW C L t).1 o).toC‖ ≤ A + 1 ∧ ‖((splitW C L t).2 o).toC‖ ≤ A + 1 :=
  splitW_boundN C hw (N := 9) htw (by omega) t ht hA o

theorem mergeW_dev (t : Out (L + 1) → Cx 64) (c0 c1 : Out L → Cx 64) {A D : ℝ}
    (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hc : ∀ o, ‖(c0 o).toC - ((splitW C L t).1 o).toC‖ ≤ D ∧
      ‖(c1 o).toC - ((splitW C L t).2 o).toC‖ ≤ D)
    (hA : A < 2 ^ 62) (hD : D < 2 ^ 62) (x : Out (L + 1)) :
    ‖(mergeW C L c0 c1 x).toC - (t x).toC‖ ≤ 2 * D + 2 :=
  mergeW_devN C hw (N := 9) htw (by omega) t c0 c1 ht hc hA hD x

theorem split_ref (t : Out (L + 1) → Cx 64) (r : Out (L + 1) → ℂ) {A d : ℝ}
    (ht : ∀ x, ‖(t x).toC‖ ≤ A) (hd : ∀ x, ‖(t x).toC - r x‖ ≤ d) (o : Out L) :
    ‖((splitW C L t).1 o).toC - (splitE r).1 o‖ ≤
        d * (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 2 * (7072 / 10000 / 2 ^ 64) * A + 4 / 2 ^ 64 ∧
      ‖((splitW C L t).2 o).toC - (splitE r).2 o‖ ≤
        d * (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 2 * (7072 / 10000 / 2 ^ 64) * A + 4 / 2 ^ 64 :=
  split_refN C hw (N := 9) htw (by omega) t r ht hd o

theorem mergeW_ref (c0 c1 : Out L → Cx 64) (z0 z1 : Fin (2 ^ L) → ℤ) {m B : ℝ}
    (hm : ∀ o, ‖(c0 o).toC - evalAt (fun k => (z0 k : ℂ)) (pt L o)‖ ≤ m ∧
      ‖(c1 o).toC - evalAt (fun k => (z1 k : ℂ)) (pt L o)‖ ≤ m)
    (hc : ∀ o, ‖(c1 o).toC‖ ≤ B) (x : Out (L + 1)) :
    ‖(mergeW C L c0 c1 x).toC - evalAt (fun k => (ilv z0 z1 k : ℂ)) (pt (L + 1) x)‖ ≤
      (2 + 2 * (7072 / 10000 / 2 ^ 64)) * m + 7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64 :=
  mergeW_refN C hw (N := 9) htw (by omega) c0 c1 z0 z1 hm hc x

end Node

/-- **Deviations**: on inputs bounded by `A` with `rangeT i W E T A` and every leaf centre
`|Im| ≤ E`, every output of the unbounded run is within `devT W E T` of its input. -/
theorem ffsX_dev (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true) (i W : ℕ)
    (hi : i ≤ 64) (E : ℚ) : ∀ {L : ℕ} (T : CTree 64 L), L ≤ 9 → ∀ (t0 t1 : Out L → Cx 64) (A : ℚ),
      (∀ o, ‖(t0 o).toC‖ ≤ A ∧ ‖(t1 o).toC‖ ≤ A) → rangeT i W E T A = true →
      (∀ x, LeafR C W T t0 t1 x → |x.im.toReal| ≤ E) → ∀ s, ReachX C W T t0 t1 s → ∀ o,
        ‖(s.c0 o).toC - (t0 o).toC‖ ≤ devT W E T ∧ ‖(s.c1 o).toC - (t1 o).toC‖ ≤ devT W E T
  | _, T, hL, t0, t1, A, hA, hr, hl, s, hs, o =>
    ffsX_devN C hw (N := 9) htw i W hi E T hL t0 t1 A hA hr hl s hs o

/-! ## Leaf centres -/

/-- Bound on the leaf-centre error of a subtree of depth `L` whose inputs are within `d` of their
references, at values below `K`. -/
noncomputable def gB (K : ℝ) : ℕ → ℝ → ℝ
  | 0, d => d
  | L + 1, d => gB K L (((1 + lam512 L) * d + 4 / 2 ^ 64 + lam512 L * mB K (L + 1)) *
      (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 7072 / 10000 / 2 ^ 64 * K + 4 / 2 ^ 64)

theorem gB_eq_gBP (K : ℝ) : ∀ L d, gB K L d = gBP lam512 K L d
  | 0, _ => rfl
  | L + 1, d => by simp only [gB, gBP]; exact gB_eq_gBP K L _

/-- **The shared lemma** (one induction in run order): on a tree passing `check`'s `CTree.Ok` and
`CTree.realB`, inputs bounded by `A` with `rangeT i W E T A`, within `d` of conjugate-symmetric
references, and `gB (2^(i-1)) L d ≤ E`: every leaf centre of the unbounded run has `|Im| ≤ E`
(so `ffsX_dev` applies), and every output is within `mB (2^(i-1)) L` of the exact FFT of its
integers. -/
theorem ffsX_sound (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true) (i W : ℕ)
    (hi : i ≤ 64) (E : ℚ) : ∀ {L : ℕ} (T : CTree 64 L), L ≤ 9 → T.Ok → T.realB = true →
      ∀ (t0 t1 : Out L → Cx 64) (A : ℚ), (∀ o, ‖(t0 o).toC‖ ≤ A ∧ ‖(t1 o).toC‖ ≤ A) →
      rangeT i W E T A = true → ∀ (r0 r1 : Out L → ℂ), IsReal r0 → IsReal r1 → ∀ d : ℝ,
      (∀ o, ‖(t0 o).toC - r0 o‖ ≤ d ∧ ‖(t1 o).toC - r1 o‖ ≤ d) → gB (2 ^ (i - 1)) L d ≤ E →
      (∀ x, LeafR C W T t0 t1 x → |x.im.toReal| ≤ E) ∧ ∀ s, ReachX C W T t0 t1 s → ∀ o,
        ‖(s.c0 o).toC - evalAt (fun k => (s.z0 k : ℂ)) (pt L o)‖ ≤ mB (2 ^ (i - 1)) L ∧
          ‖(s.c1 o).toC - evalAt (fun k => (s.z1 k : ℂ)) (pt L o)‖ ≤ mB (2 ^ (i - 1)) L
  | _, T, hL, hok, hre, t0, t1, A, hA, hr, r0, r1, h0, h1, d, hd, hG =>
    ffsX_soundN C hw (N := 9) htw lam512q_bounds i W hi E T hL hok hre t0 t1 A hA hr r0 r1 h0 h1 d
      hd (gB_eq_gBP _ _ d ▸ hG)

theorem gB_nine {K d : ℝ} (hK : 2 ^ 24 ≤ K) (hd : d ≤ 1 / 2 ^ 22) :
    gB K 9 d ≤ K / 2 ^ 32 := by
  simp only [gB, mB, lam512]
  norm_num
  linarith

/-! ## The target -/

theorem fx_q_err {a : Fx 64} {y Q : ℝ} (hy : |y - a.toReal * Q| ≤ 1 / 2 ^ 64)
    (hQ : |Q - 1 / 12289| ≤ 1 / 2 ^ 64) :
    |y - a.toReal / 12289| ≤ 1 / 2 ^ 64 + |a.toReal| / 2 ^ 64 := by
  rw [show y - a.toReal / 12289 = (y - a.toReal * Q) + a.toReal * (Q - 1 / 12289) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have := mul_le_mul_of_nonneg_left hQ (abs_nonneg a.toReal)
  linarith

theorem divqX_err (r : RMode) (qi : QInv) (z : Cx 64) :
    ‖(divqX r qi z).toC - z.toC / 12289‖ ≤ 2 / 2 ^ 64 + 2 * ‖z.toC‖ / 2 ^ 64 := by
  have he : r.e / 2 ^ 64 ≤ 1 / 2 ^ 64 := div_le_div_of_nonneg_right r.e_le_one (by positivity)
  obtain ⟨h1, h2⟩ : |(divqX r qi z).re.toReal - z.re.toReal / 12289| ≤
        1 / 2 ^ 64 + |z.re.toReal| / 2 ^ 64 ∧
      |(divqX r qi z).im.toReal - z.im.toReal / 12289| ≤ 1 / 2 ^ 64 + |z.im.toReal| / 2 ^ 64 := by
    cases qi
    · have hQ : |(Cx.qinv r).toReal - 1 / 12289| ≤ 1 / 2 ^ 64 := by
        rw [Cx.toReal_qinv]
        refine (Fx.rnd_scale_err (f := 77) r _).trans ?_
        have := div_le_div_of_nonneg_right (c := (2 : ℝ) ^ 77) r.e_le_one (by positivity)
        linarith
      exact ⟨fx_q_err ((Fx.mulTo_err r z.re _).trans he) hQ,
        fx_q_err ((Fx.mulTo_err r z.im _).trans he) hQ⟩
    · have hQ : |(qinv64 r).toReal - 1 / 12289| ≤ 1 / 2 ^ 64 := by
        rw [toReal_qinv64]
        exact (Fx.rnd_scale_err (f := 64) r _).trans he
      exact ⟨fx_q_err (Fx.mul_err1 r z.re _) hQ, fx_q_err (Fx.mul_err1 r z.im _) hQ⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Cx.toC_re, Cx.toC_im]
  linarith [Cx.abs_re_le z, Cx.abs_im_le z]

theorem norm_evalAt_c {c : ZPoly} (hc : ∀ j, |c j| < 12289) (o : Out 9) :
    ‖evalAt (fun j => (c j : ℂ)) (pt 9 o)‖ ≤ 6291456 := by
  have := norm_evalAt_le (fun j => (c j : ℂ)) (pt 9 o) (norm_pt 9 o) 12288 fun j => by
    rw [Complex.norm_intCast]
    have : |c j| ≤ 12288 := by linarith [hc j]
    exact_mod_cast this
  norm_num at this
  exact this

/-- The exact target `(-(ĉ·F̂)/q, ĉ·f̂/q)` (both orders). -/
noncomputable def tRef {logn : ℕ} (f F c : ZPoly logn) : (Out logn → ℂ) × (Out logn → ℂ) :=
  (fun o => -(evalAt (fun j => (c j : ℂ)) (pt logn o) * evalAt (fun j => (F j : ℂ)) (pt logn o)) /
      12289,
    fun o => evalAt (fun j => (c j : ℂ)) (pt logn o) * evalAt (fun j => (f j : ℂ)) (pt logn o) /
      12289)

theorem isReal_tRef {logn : ℕ} (f F c : ZPoly logn) :
    IsReal (tRef f F c).1 ∧ IsReal (tRef f F c).2 := by
  have h : ∀ a : ZPoly logn, IsReal fun o => evalAt (fun j => (a j : ℂ)) (pt logn o) := fun a =>
    isReal_evalAt _ fun j => map_intCast (starRingEnd ℂ) _
  refine ⟨fun o => ?_, fun o => ?_⟩ <;>
    simp only [tRef, h c o, h f o, h F o, map_div₀, map_neg, map_mul, map_ofNat]

theorem norm_divqX_le (r : RMode) (qi : QInv) (z : Cx 64) {B : ℝ} (h : ‖z.toC‖ ≤ B) :
    ‖(divqX r qi z).toC‖ ≤ B / 12289 + 2 / 2 ^ 64 + 2 * B / 2 ^ 64 := by
  have := norm_le_norm_add_norm_sub' (divqX r qi z).toC (z.toC / 12289)
  rw [norm_div, Complex.norm_ofNat] at this
  linarith [divqX_err r qi z]

section Target

variable (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true) (f F c : ZPoly)
  (hc : ∀ j, |c j| < 12289)
include hw htw hc

/-- **Target error**: with `‖f̂‖ ≤ 255`, `‖F̂‖ ≤ 3500` (`check`), the unbounded target is within
`2⁻²²` of the exact one, in both orders. -/
theorem targetX_ref (hf : ∀ o, ‖evalAt (fun j => (f j : ℂ)) (pt 9 o)‖ ≤ 255)
    (hF : ∀ o, ‖evalAt (fun j => (F j : ℂ)) (pt 9 o)‖ ≤ 3500) (o : Out 9) :
    ‖((targetX C f F c).1 o).toC - (tRef f F c).1 o‖ ≤ 1 / 2 ^ 22 ∧
      ‖((targetX C f F c).2 o).toC - (tRef f F c).2 o‖ ≤ 1 / 2 ^ 22 := by
  have Ec := fftW_err C hw htw _ 9 le_rfl c (norm_evalAt_c hc) o
  have Ef := fftW_err C hw htw _ 9 le_rfl f hf o
  have EF := fftW_err C hw htw _ 9 le_rfl F hF o
  norm_num at Ec Ef EF
  have hcB := norm_evalAt_c hc o
  have hfB := hf o
  have hFB := hF o
  set ce := evalAt (fun j => (c j : ℂ)) (pt 9 o)
  set fe := evalAt (fun j => (f j : ℂ)) (pt 9 o)
  set Fe := evalAt (fun j => (F j : ℂ)) (pt 9 o)
  have nc : ‖(fftW C 9 c o).toC‖ ≤ 6291457 := by
    linarith [norm_le_norm_add_norm_sub' (fftW C 9 c o).toC ce]
  have nf : ‖(fftW C 9 f o).toC‖ ≤ 256 := by
    linarith [norm_le_norm_add_norm_sub' (fftW C 9 f o).toC fe]
  have nF : ‖(fftW C 9 F o).toC‖ ≤ 3501 := by
    linarith [norm_le_norm_add_norm_sub' (fftW C 9 F o).toC Fe]
  cases ht : C.target
  · simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id, tRef]
    set qh := divqX C.x.rm C.qinv (fftW C 9 c o)
    have hq : ‖qh.toC - ce / 12289‖ ≤ 1 / 2 ^ 37 := by
      have h1 : ‖qh.toC - (fftW C 9 c o).toC / 12289‖ ≤
          2 / 2 ^ 64 + 2 * ‖(fftW C 9 c o).toC‖ / 2 ^ 64 := divqX_err C.x.rm C.qinv _
      rw [show qh.toC - ce / 12289 = (qh.toC - (fftW C 9 c o).toC / 12289) +
        ((fftW C 9 c o).toC - ce) / 12289 by ring]
      refine (norm_add_le _ _).trans ?_
      rw [norm_div, Complex.norm_ofNat]
      linarith
    have hqn : ‖qh.toC‖ ≤ 512 := by
      have := norm_le_norm_add_norm_sub' qh.toC (ce / 12289)
      rw [norm_div, Complex.norm_ofNat] at this
      linarith
    constructor
    · have e := norm_prod_err (x := -(ce / 12289)) (y := Fe)
        (Cx.mul_err C.x.rm qh.neg (fftW C 9 F o))
      rw [Cx.toC_neg, norm_neg, neg_sub_neg, norm_sub_rev (ce / 12289)] at e
      rw [show -(ce * Fe) / 12289 = -(ce / 12289) * Fe by ring]
      have m1 := mul_le_mul hqn EF (norm_nonneg _) (by norm_num)
      have m2 := mul_le_mul hq hFB (norm_nonneg _) (by norm_num)
      linarith
    · have e := norm_prod_err (x := ce / 12289) (y := fe) (Cx.mul_err C.x.rm qh (fftW C 9 f o))
      rw [show ce * fe / 12289 = ce / 12289 * fe by ring]
      have m1 := mul_le_mul hqn Ef (norm_nonneg _) (by norm_num)
      have m2 := mul_le_mul hq hfB (norm_nonneg _) (by norm_num)
      linarith
  · simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id, tRef]
    have key : ∀ (g : ZPoly) (B : ℝ), ‖evalAt (fun j => (g j : ℂ)) (pt 9 o)‖ ≤ B → B ≤ 3500 →
        ‖(fftW C 9 g o).toC - evalAt (fun j => (g j : ℂ)) (pt 9 o)‖ ≤ 1 / 2 ^ 34 →
        ‖(divqX C.x.rm C.qinv ((fftW C 9 c o).mul C.x.rm (fftW C 9 g o))).toC -
          ce * evalAt (fun j => (g j : ℂ)) (pt 9 o) / 12289‖ ≤ 1 / 2 ^ 23 ∧
        ‖(divqX C.x.rm C.qinv ((fftW C 9 c o).mul C.x.rm (fftW C 9 g o)).neg).toC -
          -(ce * evalAt (fun j => (g j : ℂ)) (pt 9 o)) / 12289‖ ≤ 1 / 2 ^ 23 := by
      intro g B hg hB hE
      set P := (fftW C 9 c o).mul C.x.rm (fftW C 9 g o)
      have e := norm_prod_err (x := ce) (y := evalAt (fun j => (g j : ℂ)) (pt 9 o))
        (Cx.mul_err C.x.rm (fftW C 9 c o) (fftW C 9 g o))
      have m1 := mul_le_mul nc hE (norm_nonneg _) (by norm_num)
      have m2 := mul_le_mul Ec (hg.trans hB) (norm_nonneg _) (by norm_num)
      have hP : ‖P.toC - ce * evalAt (fun j => (g j : ℂ)) (pt 9 o)‖ ≤ 1 / 2 ^ 10 := by
        linarith
      have hPn : ‖P.toC‖ ≤ 2 ^ 35 := by
        have := mul_le_mul hcB (hg.trans hB) (norm_nonneg _) (by norm_num)
        rw [← norm_mul] at this
        linarith [norm_le_norm_add_norm_sub' P.toC (ce * evalAt (fun j => (g j : ℂ)) (pt 9 o))]
      have d1 := divqX_err C.x.rm C.qinv P
      have d2 := divqX_err C.x.rm C.qinv P.neg
      rw [Cx.toC_neg, norm_neg] at d2
      constructor
      · rw [show (divqX C.x.rm C.qinv P).toC - ce * evalAt (fun j => (g j : ℂ)) (pt 9 o) / 12289 =
          ((divqX C.x.rm C.qinv P).toC - P.toC / 12289) +
            (P.toC - ce * evalAt (fun j => (g j : ℂ)) (pt 9 o)) / 12289 by ring]
        refine (norm_add_le _ _).trans ?_
        rw [norm_div, Complex.norm_ofNat]
        linarith
      · rw [show (divqX C.x.rm C.qinv P.neg).toC - -(ce * evalAt (fun j => (g j : ℂ)) (pt 9 o)) /
          12289 = ((divqX C.x.rm C.qinv P.neg).toC - -P.toC / 12289) -
            (P.toC - ce * evalAt (fun j => (g j : ℂ)) (pt 9 o)) / 12289 by ring]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_div, Complex.norm_ofNat]
        linarith
    have kF := key F 3500 hFB le_rfl (by linarith)
    have kf := key f 255 hfB (by norm_num) (by linarith)
    exact ⟨kF.2.trans (by norm_num), kf.1.trans (by norm_num)⟩

theorem norm_fftW_c (o : Out 9) : ‖(fftW C 9 c o).toC‖ ≤ 6291457 := by
  have Ec := fftW_err C hw htw _ 9 le_rfl c (norm_evalAt_c hc) o
  norm_num at Ec
  linarith [norm_le_norm_add_norm_sub' (fftW C 9 c o).toC (evalAt (fun j => (c j : ℂ)) (pt 9 o)),
    norm_evalAt_c hc o]

/-- The unbounded scale-first target within `checkRange`'s root bound. -/
theorem targetX_norm_sf (ht : C.target = .scaleFirst) (o : Out 9) :
    ‖((targetX C f F c).1 o).toC‖ ≤ ((max ((2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
        (nmax 9 (fftW C 9 F) + 1) + 1) ((2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
        (nmax 9 (fftW C 9 f) + 1) + 1) : ℚ) : ℝ) ∧
      ‖((targetX C f F c).2 o).toC‖ ≤ ((max ((2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
        (nmax 9 (fftW C 9 F) + 1) + 1) ((2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
        (nmax 9 (fftW C 9 f) + 1) + 1) : ℚ) : ℝ) := by
  simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id]
  have hq := norm_divqX_le C.x.rm C.qinv (fftW C 9 c o) (norm_fftW_c C hw htw c hc o)
  have h0 := norm_le_nmax (fftW C 9 F) o
  have h1 := norm_le_nmax (fftW C 9 f) o
  have m0 := mul_le_mul (hq.trans (by norm_num : _ ≤ (512 : ℝ))) h0 (norm_nonneg _) (by norm_num)
  have m1 := mul_le_mul (hq.trans (by norm_num : _ ≤ (512 : ℝ))) h1 (norm_nonneg _) (by norm_num)
  have p0 := Cx.norm_mul_le C.x.rm (divqX C.x.rm C.qinv (fftW C 9 c o)).neg (fftW C 9 F o)
  have p1 := Cx.norm_mul_le C.x.rm (divqX C.x.rm C.qinv (fftW C 9 c o)) (fftW C 9 f o)
  rw [Cx.toC_neg, norm_neg] at p0
  have n0 : (0 : ℝ) ≤ nmax 9 (fftW C 9 F) := (norm_nonneg _).trans h0
  have n1 : (0 : ℝ) ≤ nmax 9 (fftW C 9 f) := (norm_nonneg _).trans h1
  push_cast
  constructor
  · exact le_max_of_le_left (by linarith [p0, m0, n0])
  · exact le_max_of_le_right (by linarith [p1, m1, n1])

/-- The unbounded multiply-first target within `checkRange`'s root bound. -/
theorem targetX_norm_mf (ht : C.target = .multiplyFirst) (o : Out 9) :
    ‖((targetX C f F c).1 o).toC‖ ≤ ((2 * ((2 * (512 * 12288) + 1) *
        max (nmax 9 (fftW C 9 F) + 1) (nmax 9 (fftW C 9 f) + 1) + 1) / 12289 + 1 : ℚ) : ℝ) ∧
      ‖((targetX C f F c).2 o).toC‖ ≤ ((2 * ((2 * (512 * 12288) + 1) *
        max (nmax 9 (fftW C 9 F) + 1) (nmax 9 (fftW C 9 f) + 1) + 1) / 12289 + 1 : ℚ) : ℝ) := by
  simp only [targetX, ht, hw, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id]
  have hcn := norm_fftW_c C hw htw c hc o
  have hM : (0 : ℝ) ≤ max ((nmax 9 (fftW C 9 F) : ℝ) + 1) ((nmax 9 (fftW C 9 f) : ℝ) + 1) :=
    le_max_of_le_left (by linarith [(norm_nonneg _).trans (norm_le_nmax (fftW C 9 F) o)])
  have key : ∀ g : ZPoly, (nmax 9 (fftW C 9 g) : ℝ) + 1 ≤
      max ((nmax 9 (fftW C 9 F) : ℝ) + 1) ((nmax 9 (fftW C 9 f) : ℝ) + 1) →
      ‖((fftW C 9 c o).mul C.x.rm (fftW C 9 g o)).toC‖ ≤ (2 * (512 * 12288) + 1) *
        max ((nmax 9 (fftW C 9 F) : ℝ) + 1) ((nmax 9 (fftW C 9 f) : ℝ) + 1) + 1 := fun g hg => by
    have m := mul_le_mul hcn ((norm_le_nmax (fftW C 9 g) o).trans (by linarith)) (norm_nonneg _)
      (by norm_num)
    linarith [Cx.norm_mul_le C.x.rm (fftW C 9 c o) (fftW C 9 g o)]
  have kF := key F (le_max_left _ _)
  have kf := key f (le_max_right _ _)
  have d0 := norm_divqX_le C.x.rm C.qinv _ (B := (2 * (512 * 12288) + 1) *
    max ((nmax 9 (fftW C 9 F) : ℝ) + 1) (nmax 9 (fftW C 9 f) + 1) + 1)
    (by rw [Cx.toC_neg, norm_neg]; exact kF)
  have d1 := norm_divqX_le C.x.rm C.qinv _ kf
  push_cast
  constructor <;> linarith

end Target

/-! ## 32.64 and 64.64 -/

theorem imE_eq (i : ℕ) : (imE i : ℝ) = 2 ^ (i - 1) / 2 ^ 32 := by
  simp only [imE]; push_cast; ring

theorem two_pow_ge_of_bc {i : ℕ} (h : (2 * (512 * 12288) + 1 : ℚ) < 2 ^ (i - 1)) :
    (2 : ℝ) ^ 24 ≤ 2 ^ (i - 1) := by
  refine pow_le_pow_right₀ (by norm_num) (not_lt.1 fun hi => ?_)
  have := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.le_of_lt_succ hi)
  norm_num at this
  linarith

theorem checkRange_sf {C : Choices} {i W : ℕ} {k : RawKey} (ht : C.target = .scaleFirst)
    (h : checkRange C i W k = true) : twOk C.x.rc = true ∧
      (2 * (512 * 12288) + 1 : ℚ) < 2 ^ (i - 1) ∧ 2 * l1Q k.f + 1 < (2 : ℚ) ^ (i - 1) ∧
      2 * l1Q k.F + 1 < (2 : ℚ) ^ (i - 1) ∧ (2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
        (nmax 9 (fftW { C with word := none } 9 k.F) + 1) + 1 < (2 : ℚ) ^ (i - 1) ∧
      (2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
        (nmax 9 (fftW { C with word := none } 9 k.f) + 1) + 1 < (2 : ℚ) ^ (i - 1) ∧
      rangeT i W (imE i) (storeC C.x C.xn k) (max ((2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
        (nmax 9 (fftW { C with word := none } 9 k.F) + 1) + 1)
        ((2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
          (nmax 9 (fftW { C with word := none } 9 k.f) + 1) + 1)) = true := by
  obtain ⟨x, xn, tg, qi, wd, rch, sl, cap, b2, ib, sc⟩ := C
  change tg = _ at ht
  subst ht
  simp only [checkRange, Bool.and_eq_true, List.all_eq_true, List.mem_append,
    List.mem_cons, List.not_mem_nil, fitsQ, decide_eq_true_eq] at h
  obtain ⟨⟨htw, hfit⟩, hrng⟩ := h
  exact ⟨htw, hfit _ (Or.inl (Or.inl rfl)), hfit _ (Or.inl (Or.inr (Or.inl rfl))),
    hfit _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))), hfit _ (Or.inr (Or.inr (Or.inl rfl))),
    hfit _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hrng⟩

theorem checkRange_mf {C : Choices} {i W : ℕ} {k : RawKey} (ht : C.target = .multiplyFirst)
    (h : checkRange C i W k = true) : twOk C.x.rc = true ∧
      (2 * (512 * 12288) + 1 : ℚ) < 2 ^ (i - 1) ∧ 2 * l1Q k.f + 1 < (2 : ℚ) ^ (i - 1) ∧
      2 * l1Q k.F + 1 < (2 : ℚ) ^ (i - 1) ∧ (2 * (512 * 12288) + 1) *
        max (nmax 9 (fftW { C with word := none } 9 k.F) + 1)
          (nmax 9 (fftW { C with word := none } 9 k.f) + 1) + 1 < (2 : ℚ) ^ (i - 1) ∧
      2 * ((2 * (512 * 12288) + 1) * max (nmax 9 (fftW { C with word := none } 9 k.F) + 1)
        (nmax 9 (fftW { C with word := none } 9 k.f) + 1) + 1) / 12289 + 1 < (2 : ℚ) ^ (i - 1) ∧
      rangeT i W (imE i) (storeC C.x C.xn k) (2 * ((2 * (512 * 12288) + 1) *
        max (nmax 9 (fftW { C with word := none } 9 k.F) + 1)
          (nmax 9 (fftW { C with word := none } 9 k.f) + 1) + 1) / 12289 + 1) = true := by
  obtain ⟨x, xn, tg, qi, wd, rch, sl, cap, b2, ib, sc⟩ := C
  change tg = _ at ht
  subst ht
  simp only [checkRange, Bool.and_eq_true, List.all_eq_true, List.mem_append,
    List.mem_cons, List.not_mem_nil, fitsQ, decide_eq_true_eq] at h
  obtain ⟨⟨htw, hfit⟩, hrng⟩ := h
  exact ⟨htw, hfit _ (Or.inl (Or.inl rfl)), hfit _ (Or.inl (Or.inr (Or.inl rfl))),
    hfit _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))), hfit _ (Or.inr (Or.inl rfl)),
    hfit _ (Or.inr (Or.inr (Or.inl rfl))), hrng⟩

/-- The shared lemma at the root: on a key passing `check` and `checkRange C i W`, every leaf
centre of the unbounded signer on a hash with `|c j| < q` has `|Im t̄| ≤ imE i`. -/
theorem leafR_root (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi64 : i ≤ 64) (k : RawKey)
    (hk : check C.x C.xn δq k = true) (hr : checkRange C i W k = true) (c : ZPoly)
    (hc : ∀ j, |c j| < 12289) : ∀ x, LeafR { C with word := none } W (storeC C.x C.xn k)
      (targetX { C with word := none } k.f k.F c).1
      (targetX { C with word := none } k.f k.F c).2 x → |x.im.toReal| ≤ imE i := by
  have hko := check_ok C.x C.xn hk
  have hT : (storeC C.x C.xn k).Ok := storeB_centre C.x C.xn k ▸ CTree.ok_of_okB _ hko.ok
  have hR : (storeC C.x C.xn k).realB = true := storeB_centre C.x C.xn k ▸ hko.real
  have hf : ∀ o, ‖evalAt (fun j => (k.f j : ℂ)) (pt 9 o)‖ ≤ 255 := fun o => le_of_le_of_eq
    (CB.norm_le_of_normLeB (fftB_holds C.x _ 9 k.f o) (hko.hf o)) (by norm_num)
  have hF : ∀ o, ‖evalAt (fun j => (k.F j : ℂ)) (pt 9 o)‖ ≤ 3500 := fun o => le_of_le_of_eq
    (CB.norm_le_of_normLeB (fftB_holds C.x _ 9 k.F o) (hko.hF o)) (by norm_num)
  have hd := targetX_ref { C with word := none } rfl
  rcases (show C.target = .scaleFirst ∨ C.target = .multiplyFirst by cases C.target <;> simp)
    with ht | ht
  · obtain ⟨htw, hbc, -, -, -, -, hrng⟩ := checkRange_sf ht hr
    refine (ffsX_sound { C with word := none } rfl htw i W hi64 (imE i) _ le_rfl hT hR _ _ _
      (fun o => targetX_norm_sf { C with word := none } rfl htw k.f k.F c hc ht o) hrng _ _
      (isReal_tRef k.f k.F c).1 (isReal_tRef k.f k.F c).2 (1 / 2 ^ 22)
      (hd htw k.f k.F c hc hf hF) ?_).1
    rw [imE_eq]
    exact gB_nine (two_pow_ge_of_bc hbc) le_rfl
  · obtain ⟨htw, hbc, -, -, -, -, hrng⟩ := checkRange_mf ht hr
    refine (ffsX_sound { C with word := none } rfl htw i W hi64 (imE i) _ le_rfl hT hR _ _ _
      (fun o => targetX_norm_mf { C with word := none } rfl htw k.f k.F c hc ht o) hrng _ _
      (isReal_tRef k.f k.F c).1 (isReal_tRef k.f k.F c).2 (1 / 2 ^ 22)
      (hd htw k.f k.F c hc hf hF) ?_).1
    rw [imE_eq]
    exact gB_nine (two_pow_ge_of_bc hbc) le_rfl

/-- **Leaf centres are nearly real**: on a key passing `check` (every stored `ℓ̂`
conjugate-symmetric, `CTree.realB`; `‖ℓ̂‖ ≤ lam512 L`; `‖f̂‖ ≤ 255`, `‖F̂‖ ≤ 3500`) and
`checkRange C i W` (tables `twOk`, every value `< 2^(i - 1)`), every leaf centre of the unbounded
signer on a hash with `|c j| < q` has `|Im t̄| ≤ imE i`. -/
theorem leafX_im (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi64 : i ≤ 64) (k : RawKey)
    (hk : check C.x C.xn δq k = true) (hr : checkRange C i W k = true) (c : ZPoly)
    (hc : ∀ j, |c j| < 12289) {x : Cx 64}
    (hx : LeafX { C with word := none } W (storeC C.x C.xn k)
      (targetX { C with word := none } k.f k.F c).1
      (targetX { C with word := none } k.f k.F c).2 x) :
    |x.im.toRat| ≤ imE i := by
  have h := leafR_root C δq i W hi64 k hk hr c hc x (leafR_of_leafX _ W _ _ _ x hx)
  rw [Fx.toReal_eq_toRat] at h
  exact_mod_cast h

/-! ## Words -/

section Word

variable (C : Choices) {i : ℕ} (hi : 1 ≤ i) (htw : twOk C.x.rc = true) {L : ℕ} (hL : L ≤ 8)
include hi htw hL

theorem splitW_word (t : Out (L + 1) → Cx 64) {A : ℝ} (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hA : 2 * A + 1 < 2 ^ (i - 1)) :
    splitW { C with word := some i } L t = splitW { C with word := none } L t :=
  splitW_wordN C hi (N := 9) htw (by omega) t ht hA

theorem mergeW_word (c0 c1 : Out L → Cx 64) {B : ℝ}
    (hc : ∀ o, ‖(c0 o).toC‖ ≤ B ∧ ‖(c1 o).toC‖ ≤ B) (hB : 2 * B + 1 < 2 ^ (i - 1))
    (hB62 : B < 2 ^ 62) :
    mergeW { C with word := some i } L c0 c1 = mergeW { C with word := none } L c0 c1 :=
  mergeW_wordN C hi (N := 9) htw (by omega) c0 c1 hc hB hB62

end Word

/-- **No reduction changes a value of `ffsX`**: on inputs bounded by `A` with `rangeT i W E T A`
and every leaf centre of the unbounded run `|Im| ≤ E`, `ffsX` on `(i + 64)`-bit words is the
unbounded one, in every lawful monad, for sampler answers within `W` of `⌊t̄⌋`. -/
theorem ffsX_word (C : Choices) (htw : twOk C.x.rc = true) (i W : ℕ) (hi : 1 ≤ i)
    (hi64 : i ≤ 64) (E : ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (samp : Fx 64 → Fx 64 → m ℤ) : ∀ {L : ℕ} (T : CTree 64 L), L ≤ 9 →
      ∀ (t0 t1 : Out L → Cx 64) (A : ℚ), (∀ o, ‖(t0 o).toC‖ ≤ A ∧ ‖(t1 o).toC‖ ≤ A) →
      rangeT i W E T A = true →
      (∀ x, LeafR { C with word := none } W T t0 t1 x → |x.im.toReal| ≤ E) →
      ffsX { C with word := some i } (clampS W samp) T t0 t1 =
        ffsX { C with word := none } (clampS W samp) T t0 t1 :=
  fun T hL => ffsX_wordN C (N := 9) htw i W hi hi64 E samp T hL

theorem fftW_word (C : Choices) (htw : twOk C.x.rc = true) {i : ℕ} (hi : 1 ≤ i) (B : ℝ)
    (hB : 2 * B + 1 < 2 ^ (i - 1)) : ∀ (L : ℕ), L ≤ 9 → ∀ (a : Fin (2 ^ L) → ℤ),
      (∀ o, ‖evalAt (fun j => (a j : ℂ)) (pt L o)‖ ≤ B) →
        fftW { C with word := some i } L a = fftW { C with word := none } L a
  | L, hL => fftW_wordN C (N := 9) (by norm_num) htw hi B hB L hL

theorem norm_evalAt_le_l1 {logn : ℕ} (a : ZPoly logn) (o : Out logn) :
    ‖evalAt (fun j => (a j : ℂ)) (pt logn o)‖ ≤ (l1Q a : ℝ) := by
  have e : (l1Q a : ℝ) = ∑ j, |(a j : ℝ)| := by
    norm_num [l1Q, ← Fin.sum_univ_def]
  rw [e, evalAt]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_pow, norm_pt, one_pow, mul_one, Complex.norm_intCast]

section TargetWord

variable (C : Choices) (htw : twOk C.x.rc = true) {i : ℕ} (hi : 1 ≤ i) (f F c : ZPoly)
  (hc : ∀ j, |c j| < 12289) (hK : (2 : ℝ) ^ 24 ≤ 2 ^ (i - 1))
  (hf : 2 * l1Q f + 1 < (2 : ℚ) ^ (i - 1)) (hF : 2 * l1Q F + 1 < (2 : ℚ) ^ (i - 1))
include htw hi hc hK hf hF

theorem fftW_word_target :
    fftW { C with word := some i } 9 c = fftW { C with word := none } 9 c ∧
      fftW { C with word := some i } 9 f = fftW { C with word := none } 9 f ∧
      fftW { C with word := some i } 9 F = fftW { C with word := none } 9 F := by
  have hf' : 2 * (l1Q f : ℝ) + 1 < 2 ^ (i - 1) := by exact_mod_cast hf
  have hF' : 2 * (l1Q F : ℝ) + 1 < 2 ^ (i - 1) := by exact_mod_cast hF
  exact ⟨fftW_word C htw hi 6291456 (by linarith) 9 le_rfl c (norm_evalAt_c hc),
    fftW_word C htw hi _ hf' 9 le_rfl f (norm_evalAt_le_l1 f),
    fftW_word C htw hi _ hF' 9 le_rfl F (norm_evalAt_le_l1 F)⟩

theorem targetX_word_sf (ht : C.target = .scaleFirst)
    (h0 : (2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
      (nmax 9 (fftW { C with word := none } 9 F) + 1) + 1 < (2 : ℚ) ^ (i - 1))
    (h1 : (2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
      (nmax 9 (fftW { C with word := none } 9 f) + 1) + 1 < (2 : ℚ) ^ (i - 1)) :
    targetX { C with word := some i } f F c = targetX { C with word := none } f F c := by
  obtain ⟨ec, ef, eF⟩ := fftW_word_target C htw hi f F c hc hK hf hF
  have h0' := (Rat.cast_lt (K := ℝ)).2 h0
  have h1' := (Rat.cast_lt (K := ℝ)).2 h1
  push_cast at h0' h1'
  have hq : ∀ o, ‖(divqX C.x.rm C.qinv (fftW { C with word := none } 9 c o)).toC‖ ≤ 512 :=
    fun o => (norm_divqX_le C.x.rm C.qinv _
      (norm_fftW_c { C with word := none } rfl htw c hc o)).trans (by norm_num)
  have key : ∀ (g : ZPoly) (o : Out 9), (2 * (2 * (512 * 12288) + 1) / 12289 + 1) *
      ((nmax 9 (fftW { C with word := none } 9 g) : ℝ) + 1) + 1 < 2 ^ (i - 1) →
      ‖(divqX C.x.rm C.qinv (fftW { C with word := none } 9 c o)).toC‖ *
        ‖(fftW { C with word := none } 9 g o).toC‖ + 2 / 2 ^ 64 < 2 ^ (i - 1) := fun g o hg => by
    have := mul_le_mul (hq o) (norm_le_nmax (fftW { C with word := none } 9 g) o) (norm_nonneg _)
      (by norm_num)
    have := (norm_nonneg _).trans (norm_le_nmax (fftW { C with word := none } 9 g) o)
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

theorem targetX_word_mf (ht : C.target = .multiplyFirst)
    (h0 : (2 * (512 * 12288) + 1) * max (nmax 9 (fftW { C with word := none } 9 F) + 1)
      (nmax 9 (fftW { C with word := none } 9 f) + 1) + 1 < (2 : ℚ) ^ (i - 1))
    (h1 : 2 * ((2 * (512 * 12288) + 1) * max (nmax 9 (fftW { C with word := none } 9 F) + 1)
      (nmax 9 (fftW { C with word := none } 9 f) + 1) + 1) / 12289 + 1 < (2 : ℚ) ^ (i - 1)) :
    targetX { C with word := some i } f F c = targetX { C with word := none } f F c := by
  obtain ⟨ec, ef, eF⟩ := fftW_word_target C htw hi f F c hc hK hf hF
  have h0' := (Rat.cast_lt (K := ℝ)).2 h0
  have h1' := (Rat.cast_lt (K := ℝ)).2 h1
  push_cast at h0' h1'
  have hcn := fun o => norm_fftW_c { C with word := none } rfl htw c hc o
  have hM : (0 : ℝ) ≤ max ((nmax 9 (fftW { C with word := none } 9 F) : ℝ) + 1)
      ((nmax 9 (fftW { C with word := none } 9 f) : ℝ) + 1) :=
    le_max_of_le_left (by linarith [(norm_nonneg _).trans (norm_le_nmax
      (fftW { C with word := none } 9 F) (Out.ofIdx _ 0))])
  have key : ∀ (g : ZPoly) (o : Out 9), (nmax 9 (fftW { C with word := none } 9 g) : ℝ) + 1 ≤
      max ((nmax 9 (fftW { C with word := none } 9 F) : ℝ) + 1)
        ((nmax 9 (fftW { C with word := none } 9 f) : ℝ) + 1) →
      ‖(fftW { C with word := none } 9 c o).toC‖ * ‖(fftW { C with word := none } 9 g o).toC‖ ≤
        (2 * (512 * 12288) + 1) * max ((nmax 9 (fftW { C with word := none } 9 F) : ℝ) + 1)
          ((nmax 9 (fftW { C with word := none } 9 f) : ℝ) + 1) - 1 := fun g o hg => by
    have := mul_le_mul (hcn o) ((norm_le_nmax (fftW { C with word := none } 9 g) o).trans
      (by linarith)) (norm_nonneg _) (by norm_num)
    linarith
  have fin : ∀ (g : ZPoly) (o : Out 9), (nmax 9 (fftW { C with word := none } 9 g) : ℝ) + 1 ≤
      max ((nmax 9 (fftW { C with word := none } 9 F) : ℝ) + 1)
        ((nmax 9 (fftW { C with word := none } 9 f) : ℝ) + 1) → ∀ z : Cx 64,
      ‖z.toC‖ = ‖((fftW { C with word := none } 9 c o).mul C.x.rm
        (fftW { C with word := none } 9 g o)).toC‖ →
      (fftW { C with word := none } 9 c o).mulW (wordFn (some i)) C.x.rm
          (fftW { C with word := none } 9 g o) =
        (fftW { C with word := none } 9 c o).mul C.x.rm (fftW { C with word := none } 9 g o) ∧
      z.wr (wordFn (some i)) = z ∧ (divqX C.x.rm C.qinv z).wr (wordFn (some i)) =
        divqX C.x.rm C.qinv z := fun g o hg z hz => by
    have k := key g o hg
    have hP := Cx.norm_mul_le C.x.rm (fftW { C with word := none } 9 c o)
      (fftW { C with word := none } 9 g o)
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

/-- **No reduction changes a value of the signing attempt `signX`**: on a key passing `check`
and `checkRange C i W`, with sampler answers within `W` of `⌊t̄⌋`, the signing attempt on
`(i + 64)`-bit words is the unbounded one, in every lawful monad. -/
theorem signX_word (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi : 1 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey) (hc : check C.x C.xn δq k = true) (hk : checkRange C i W k = true)
    {m : Type → Type*} [Monad m] [LawfulMonad m] (samp : Fx 64 → Fx 64 → m ℤ) (c : ZPoly) :
    signX { C with word := some i } (clampS W samp) (storeC C.x C.xn k) k c =
      signX { C with word := none } (clampS W samp) (storeC C.x C.xn k) k c := by
  unfold signX
  by_cases hcq : ∀ j, |c j| < 12289
  swap
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hcq), ite_eq_right_of_eq_false _ _ (eq_false hcq)]
  have hlf := leafR_root C δq i W hi64 k hc hk c hcq
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcq), ite_eq_left_of_eq_true _ _ (eq_true hcq)]
  rcases (show C.target = .scaleFirst ∨ C.target = .multiplyFirst by cases C.target <;> simp)
    with ht | ht
  · obtain ⟨htw, hbc, hf, hF, h0, h1, hrng⟩ := checkRange_sf ht hk
    rw [targetX_word_sf C htw hi k.f k.F c hcq (two_pow_ge_of_bc hbc) hf hF ht h0 h1,
      ffsX_word C htw i W hi hi64 (imE i) _ (storeC C.x C.xn k) le_rfl _ _ _
        (fun o => targetX_norm_sf { C with word := none } rfl htw k.f k.F c hcq ht o) hrng hlf]
  · obtain ⟨htw, hbc, hf, hF, h0, h1, hrng⟩ := checkRange_mf ht hk
    rw [targetX_word_mf C htw hi k.f k.F c hcq (two_pow_ge_of_bc hbc) hf hF ht h0 h1,
      ffsX_word C htw i W hi hi64 (imE i) _ (storeC C.x C.xn k) le_rfl _ _ _
        (fun o => targetX_norm_mf { C with word := none } rfl htw k.f k.F c hcq ht o) hrng hlf]

/-- **32.64 = 64.64**: on a key passing `check` and `checkRange` at `i = 32` and `i = 64`, with
sampler answers within `W` of `⌊t̄⌋`, the signing attempts `signX` on 96-bit and on 128-bit
words are bit-identical. -/
theorem sign32_eq_sign64 (C : Choices) (δq : ℕ → ℚ) (W : ℕ) (k : RawKey)
    (hc : check C.x C.xn δq k = true) (h32 : checkRange C 32 W k = true)
    (h64 : checkRange C 64 W k = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (samp : Fx 64 → Fx 64 → m ℤ) (c : ZPoly) :
    signX { C with word := some 32 } (clampS W samp) (storeC C.x C.xn k) k c =
      signX { C with word := some 64 } (clampS W samp) (storeC C.x C.xn k) k c :=
  (signX_word C δq 32 W (by norm_num) (by norm_num) k hc h32 samp c).trans
    (signX_word C δq 64 W (by norm_num) le_rfl k hc h64 samp c).symm

end FalconPrecision.Exec
