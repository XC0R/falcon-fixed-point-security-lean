/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignRefine

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

/-! ## Roundings and words -/

theorem RMode.e_le_one (r : RMode) : r.e ≤ 1 := by unfold RMode.e; split_ifs <;> norm_num

namespace Fx

theorem mul_err1 (r : RMode) (a b : Fx 64) :
    |(a.mul r b).toReal - a.toReal * b.toReal| ≤ 1 / 2 ^ 64 :=
  (mul_err r a b).trans (div_le_div_of_nonneg_right r.e_le_one (by positivity))

theorem half_err1 (r : RMode) (a : Fx 64) : |(a.half r).toReal - a.toReal / 2| ≤ 1 / 2 ^ 64 :=
  (half_err r a).trans (div_le_div_of_nonneg_right r.e_le_one (by positivity))

theorem wr_some {i : ℕ} (hi : 1 ≤ i) {x : Fx 64} (h : |x.toReal| < 2 ^ (i - 1)) :
    x.wr (wordFn (some i)) = x := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hr : x.InRange (j + 1) := by
    rw [inRange_iff, pow_succ]
    rw [Nat.add_sub_cancel] at h
    have := abs_lt.1 h
    constructor <;> linarith
  exact congrArg Fx.mk hr.wrap

end Fx

namespace Cx

theorem toC_im {f : ℕ} (z : Cx f) : z.toC.im = z.im.toReal := rfl

theorem abs_re_le {f : ℕ} (z : Cx f) : |z.re.toReal| ≤ ‖z.toC‖ := Complex.abs_re_le_norm z.toC

theorem abs_im_le {f : ℕ} (z : Cx f) : |z.im.toReal| ≤ ‖z.toC‖ := Complex.abs_im_le_norm z.toC

theorem mul_re_err (r : RMode) (z w : Cx 64) :
    |(z.mul r w).re.toReal - (z.toC * w.toC).re| ≤ 2 / 2 ^ 64 := by
  have h1 := abs_le.1 (Fx.mul_err1 r z.re w.re)
  have h2 := abs_le.1 (Fx.mul_err1 r z.im w.im)
  rw [Complex.mul_re, abs_le]
  simp only [Cx.mul, Fx.toReal_sub, toC_re, toC_im]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem mul_im_err (r : RMode) (z w : Cx 64) :
    |(z.mul r w).im.toReal - (z.toC * w.toC).im| ≤ 2 / 2 ^ 64 := by
  have h1 := abs_le.1 (Fx.mul_err1 r z.re w.im)
  have h2 := abs_le.1 (Fx.mul_err1 r z.im w.re)
  rw [Complex.mul_im, abs_le]
  simp only [Cx.mul, Fx.toReal_add, toC_re, toC_im]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem mul_err (r : RMode) (z w : Cx 64) : ‖(z.mul r w).toC - z.toC * w.toC‖ ≤ 4 / 2 ^ 64 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, toC_re, toC_im]
  linarith [mul_re_err r z w, mul_im_err r z w]

theorem half_err (r : RMode) (z : Cx 64) : ‖(z.half r).toC - z.toC / 2‖ ≤ 2 / 2 ^ 64 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 : |(z.half r).re.toReal - z.re.toReal / 2| ≤ 1 / 2 ^ 64 := Fx.half_err1 r z.re
  have h2 : |(z.half r).im.toReal - z.im.toReal / 2| ≤ 1 / 2 ^ 64 := Fx.half_err1 r z.im
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, toC_re,
    toC_im]
  linarith

theorem norm_mul_le (r : RMode) (z w : Cx 64) :
    ‖(z.mul r w).toC‖ ≤ ‖z.toC‖ * ‖w.toC‖ + 4 / 2 ^ 64 := by
  have := norm_le_norm_add_norm_sub' (z.mul r w).toC (z.toC * w.toC)
  rw [norm_mul] at this
  linarith [mul_err r z w]

theorem wr_some {i : ℕ} (hi : 1 ≤ i) {z : Cx 64} (h : ‖z.toC‖ < 2 ^ (i - 1)) :
    z.wr (wordFn (some i)) = z := by
  change (⟨z.re.wr _, z.im.wr _⟩ : Cx 64) = z
  rw [Fx.wr_some hi ((abs_re_le z).trans_lt h), Fx.wr_some hi ((abs_im_le z).trans_lt h)]

theorem mulW_some {i : ℕ} (hi : 1 ≤ i) (r : RMode) {z w : Cx 64}
    (h : ‖z.toC‖ * ‖w.toC‖ + 2 / 2 ^ 64 < 2 ^ (i - 1)) :
    z.mulW (wordFn (some i)) r w = z.mul r w := by
  have hp : ∀ a b : Fx 64, |a.toReal| ≤ ‖z.toC‖ → |b.toReal| ≤ ‖w.toC‖ →
      |(a.mul r b).toReal| < 2 ^ (i - 1) := fun a b ha hb => by
    have h1 := Fx.mul_err1 r a b
    have h2 : |a.toReal * b.toReal| ≤ ‖z.toC‖ * ‖w.toC‖ := by
      rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)
    have := abs_sub_abs_le_abs_sub (a.mul r b).toReal (a.toReal * b.toReal)
    linarith
  have hzw : ‖z.toC * w.toC‖ = ‖z.toC‖ * ‖w.toC‖ := norm_mul _ _
  have hre : |(z.mul r w).re.toReal| < 2 ^ (i - 1) := by
    have := abs_sub_abs_le_abs_sub (z.mul r w).re.toReal (z.toC * w.toC).re
    linarith [mul_re_err r z w, Complex.abs_re_le_norm (z.toC * w.toC)]
  have him : |(z.mul r w).im.toReal| < 2 ^ (i - 1) := by
    have := abs_sub_abs_le_abs_sub (z.mul r w).im.toReal (z.toC * w.toC).im
    linarith [mul_im_err r z w, Complex.abs_im_le_norm (z.toC * w.toC)]
  simp only [Cx.mulW, Fx.wr_some hi (hp _ _ (abs_re_le z) (abs_re_le w)),
    Fx.wr_some hi (hp _ _ (abs_im_le z) (abs_im_le w)),
    Fx.wr_some hi (hp _ _ (abs_re_le z) (abs_im_le w)),
    Fx.wr_some hi (hp _ _ (abs_im_le z) (abs_re_le w))]
  exact congrArg₂ Cx.mk (Fx.wr_some hi hre) (Fx.wr_some hi him)

end Cx

/-- A product error: `p` within `r` of `xh·yh`. -/
theorem norm_prod_err {x xh y yh p : ℂ} {r : ℝ} (hp : ‖p - xh * yh‖ ≤ r) :
    ‖p - x * y‖ ≤ r + ‖xh‖ * ‖yh - y‖ + ‖xh - x‖ * ‖y‖ := by
  have e : p - x * y = (p - xh * yh) + xh * (yh - y) + (xh - x) * y := by ring
  rw [e, ← norm_mul, ← norm_mul]
  exact (norm_add₃_le).trans (by linarith)

/-! ## Tables -/

section Tables

variable {rc : RMode} (h : twOk rc = true) {L : ℕ} (hL : L ≤ 8) (o : Out L)
include h hL

theorem tw_err : ‖(twB rc 64 L o).c.toC - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 64 := by
  have := twX_err64 rc h L o
  rwa [twX, ite_eq_left_of_eq_true _ _ (eq_true hL)] at this

theorem tws_err :
    ‖(twsB rc 64 L o).c.toC - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 64 := by
  have := twsX_err64 rc h L o
  rwa [twsX, ite_eq_left_of_eq_true _ _ (eq_true hL)] at this

theorem norm_tw_le : ‖(twB rc 64 L o).c.toC‖ ≤ 1 + 7072 / 10000 / 2 ^ 64 := by
  have := norm_le_norm_add_norm_sub' (twB rc 64 L o).c.toC (zeta L o)
  rw [norm_zeta] at this
  linarith [tw_err h hL o]

theorem norm_tws_le : ‖(twsB rc 64 L o).c.toC‖ ≤ 1 / 2 + 7072 / 10000 / 2 ^ 64 := by
  have := norm_le_norm_add_norm_sub' (twsB rc 64 L o).c.toC (starRingEnd ℂ (zeta L o) / 2)
  rw [norm_div, Complex.norm_conj, norm_zeta, Complex.norm_ofNat] at this
  linarith [tws_err h hL o]

end Tables

/-! ## `nmax` -/

theorem le_foldl_max {α : Type*} (g : α → ℚ) : ∀ (l : List α) (b : ℚ),
    b ≤ l.foldl (fun b j => max b (g j)) b ∧ ∀ j ∈ l, g j ≤ l.foldl (fun b j => max b (g j)) b
  | [], b => ⟨le_rfl, by simp⟩
  | j :: l, b => by
    obtain ⟨h1, h2⟩ := le_foldl_max g l (max b (g j))
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1, h2⟩

theorem norm_le_nmax {L : ℕ} (v : Out L → Cx 64) (o : Out L) : ‖(v o).toC‖ ≤ nmax L v := by
  have h := (le_foldl_max (fun j => (v (Out.ofIdx L j)).nUB) (List.range (2 ^ L)) 0).2
    (Out.idx L o) (List.mem_range.2 (Out.idx_lt L o))
  rw [Out.ofIdx_idx] at h
  unfold nmax
  exact (Cx.norm_le_nUB _).trans (by exact_mod_cast h)

/-! ## The FFT -/

theorem evens_castC {L : ℕ} (a : Fin (2 ^ (L + 1)) → ℤ) :
    evens (castC fun j => (a j : ℂ)) = fun j => (evensZ a j : ℂ) := rfl

theorem odds_castC {L : ℕ} (a : Fin (2 ^ (L + 1)) → ℤ) :
    odds (castC fun j => (a j : ℂ)) = fun j => (oddsZ a j : ℂ) := rfl

/-- **FFT error**: with every exact output within `B`, every output of the unbounded `fftW` (any
rounding, tables within `δ`) is within `4^L·(δB + 4·2⁻⁶⁴)` of the exact one. -/
theorem fftW_err (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true) (B : ℝ) :
    ∀ (L : ℕ), L ≤ 9 → ∀ (a : Fin (2 ^ L) → ℤ),
      (∀ o, ‖evalAt (fun j => (a j : ℂ)) (pt L o)‖ ≤ B) → ∀ o,
        ‖(fftW C L a o).toC - evalAt (fun j => (a j : ℂ)) (pt L o)‖ ≤
          4 ^ L * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64)
  | 0, _, a, hB, o => by
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB o)
    have e : evalAt (fun j => (a j : ℂ)) (pt 0 o) = a ⟨0, by norm_num⟩ := by simp [evalAt]
    simp only [fftW, hw, wordFn, Cx.wr_id, Cx.toC_ofInt, e, sub_self, norm_zero]
    positivity
  | L + 1, hL, a, hB, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (o, b))
    have hsub := half_eval_le B L (fun j => (a j : ℂ)) (zeta L) (pt L) (pt (L + 1))
      (fun o b => pt_succ L o b) (zeta_sq L) (norm_zeta L) hB
    rw [evens_castC, odds_castC] at hsub
    have hu := fftW_err C hw htw B L (by omega) (evensZ a) (fun o => (hsub o).1) o
    have hv := fftW_err C hw htw B L (by omega) (oddsZ a) (fun o => (hsub o).2) o
    have hbf := Errors.Butterfly.butterfly_err _ _ (zeta L o) _ _ _ _ _ _ _ (norm_zeta L o)
      (tw_err htw (by omega) o) hu hv (Cx.mul_err C.x.rm (twB C.x.rc 64 L o).c
        (fftW C L (oddsZ a) o))
    have hs := evalAt_split (castC fun j => (a j : ℂ)) (zeta L o)
    have hs' := evalAt_split (castC fun j => (a j : ℂ)) (-zeta L o)
    rw [evalAt_castC, zeta_sq, evens_castC, odds_castC] at hs
    rw [evalAt_castC, neg_sq, zeta_sq, evens_castC, odds_castC] at hs'
    have hX : (0 : ℝ) ≤ 4 ^ L * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) := by positivity
    have h1 : 7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64 ≤
        4 ^ L * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    have hV := (hsub o).2
    have hfin : ∀ y : ℝ, y ≤ 4 ^ L * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) * (2 +
        7072 / 10000 / 2 ^ 64) + 7072 / 10000 / 2 ^ 64 * ‖evalAt (fun j => (oddsZ a j : ℂ))
          (pt L o)‖ + 4 / 2 ^ 64 → y ≤ 4 ^ (L + 1) * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) :=
      fun y hy => by rw [pow_succ]; linarith [hy, hX, h1, hV]
    simp only [fftW]
    erw [memo_eq]
    cases b
    · refine hfin _ ?_
      simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, Bool.false_eq_true, ↓reduceIte, Cx.toC_add,
        pt_succ, hs]
      exact hbf.1
    · refine hfin _ ?_
      simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, ↓reduceIte, Cx.toC_sub, pt_succ, hs',
        neg_mul, ← sub_eq_add_neg]
      exact hbf.2

/-! ## Reachable outputs -/

/-- `s` is an output of `ffsX C` on `T` from `(t0, t1)` for sampler answers clamped into
`⌊t̄⌋ ± W`, the checks of `C.rchk` ignored. -/
def ReachX (C : Choices) (W : ℕ) :
    {L : ℕ} → CTree 64 L → (t0 t1 : Out L → Cx 64) → SampX L → Prop
  | _, .leaf _, t0, t1, s => ∃ y0 y1 : ℤ,
    s = ⟨fun _ => clampZ ((t0 ()).re.toInt .floor) W y0,
      fun _ => clampZ ((t1 ()).re.toInt .floor) W y1,
      fun _ => Cx.ofInt (clampZ ((t0 ()).re.toInt .floor) W y0),
      fun _ => Cx.ofInt (clampZ ((t1 ()).re.toInt .floor) W y1)⟩
  | _, @CTree.node _ L ℓ T0 T1, t0, t1, s => ∃ s1 s0,
    ReachX C W T1 (splitW C L t1).1 (splitW C L t1).2 s1 ∧
      ReachX C W T0 (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).1
        (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 s0 ∧
      s = ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1, mergeW C L s0.c0 s0.c1, mergeW C L s1.c0 s1.c1⟩

/-- `x` is a leaf centre of `ffsX C` on `T` from `(t0, t1)` (`LeafX` with `ReachX`). -/
def LeafR (C : Choices) (W : ℕ) :
    {L : ℕ} → CTree 64 L → (t0 t1 : Out L → Cx 64) → Cx 64 → Prop
  | _, .leaf _, t0, t1, x => x = t0 () ∨ x = t1 ()
  | _, @CTree.node _ L ℓ T0 T1, t0, t1, x =>
    LeafR C W T1 (splitW C L t1).1 (splitW C L t1).2 x ∨
      ∃ s1, ReachX C W T1 (splitW C L t1).1 (splitW C L t1).2 s1 ∧
        LeafR C W T0 (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).1
          (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 x

/-- **Continuations**: in every lawful monad, continuations of `ffsX C (clampS W samp)` agreeing
on `none` and on every `ReachX` output give the same computation. -/
theorem ffsX_bind_congr (C : Choices) (W : ℕ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (samp : Fx 64 → Fx 64 → m ℤ) {β : Type} :
    ∀ {L : ℕ} (T : CTree 64 L) (t0 t1 : Out L → Cx 64) (κ1 κ2 : Option (SampX L) → m β),
      κ1 none = κ2 none → (∀ s, ReachX C W T t0 t1 s → κ1 (some s) = κ2 (some s)) →
        ffsX C (clampS W samp) T t0 t1 >>= κ1 = ffsX C (clampS W samp) T t0 t1 >>= κ2
  | _, .leaf _, _, _, _, _, _, h => by
    simp only [ffsX, clampS, bind_map_left, bind_assoc, pure_bind]
    exact bind_congr fun y0 => bind_congr fun y1 => h _ ⟨y0, y1, rfl⟩
  | _, @CTree.node _ L ℓ T0 T1, t0, t1, κ1, κ2, hn, h => by
    simp only [ffsX]
    split_ifs
    · rw [bind_assoc, bind_assoc]
      refine ffsX_bind_congr C W samp T1 _ _ _ _ (by simp only [pure_bind, hn]) fun s1 h1 => ?_
      simp only
      split_ifs
      · rw [bind_assoc, bind_assoc]
        refine ffsX_bind_congr C W samp T0 _ _ _ _ (by simp only [pure_bind, hn])
          fun s0 h0 => ?_
        simp only
        split_ifs
        · simp only [pure_bind]
          exact h _ ⟨s1, s0, h1, h0, rfl⟩
        · simp only [pure_bind, hn]
      · simp only [pure_bind, hn]
    · simp only [pure_bind, hn]

theorem reachX_of_outX (C : Choices) (W : ℕ) {L : ℕ} (T : CTree 64 L) (t0 t1 : Out L → Cx 64)
    (s : SampX L) (h : OutX C W T t0 t1 s) : ReachX C W T t0 t1 s := by
  classical
  obtain ⟨g, j, h⟩ := h
  have e := ffsX_bind_congr C W (tapeS g) T t0 t1 pure
    (fun r => pure (if ∃ s, r = some s ∧ ReachX C W T t0 t1 s then r else none)) (by simp)
    fun s hs => by rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨s, rfl, hs⟩)]
  rw [bind_pure] at e
  have e2 : ffsX C (clampS W (tapeS g)) T t0 t1 =
      (fun r => if ∃ s, r = some s ∧ ReachX C W T t0 t1 s then r else none) <$>
        ffsX C (clampS W (tapeS g)) T t0 t1 := by
    rw [map_eq_bind_pure_comp]; exact e
  rw [e2] at h
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map] at h
  generalize StateT.run (ffsX C (clampS W (tapeS g)) T t0 t1) j = p at h
  change (if ∃ s, (Id.run p).1 = some s ∧ ReachX C W T t0 t1 s then (Id.run p).1 else none) =
    some s at h
  split_ifs at h with hr
  · obtain ⟨s', e', hs'⟩ := hr
    rw [e'] at h
    exact Option.some_injective _ h ▸ hs'

theorem leafR_of_leafX (C : Choices) (W : ℕ) : ∀ {L : ℕ} (T : CTree 64 L)
    (t0 t1 : Out L → Cx 64) (x : Cx 64), LeafX C W T t0 t1 x → LeafR C W T t0 t1 x
  | _, .leaf _, _, _, _, h => h
  | _, @CTree.node _ L _ T0 T1, _, _, x, h =>
    h.imp (leafR_of_leafX C W T1 _ _ x) fun ⟨s1, h1, h0⟩ =>
      ⟨s1, reachX_of_outX C W T1 _ _ s1 h1, leafR_of_leafX C W T0 _ _ x h0⟩

/-! ## One node of the unbounded run -/

theorem norm_add6_le (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a + b + c + d + e) f
  have h2 := norm_add_le (a + b + c + d) e
  have h3 := norm_add_le (a + b + c) d
  have h4 := norm_add_le (a + b) c
  have h5 := norm_add_le a b
  linarith

/-- A merge of a split misses its input by `2D + 2` when the merged values are within `D` of the
split and values stay below `2⁶²`. -/
theorem merge_split_dev {X Y a b c0 c1 τ σ ζ pm : ℂ} {A D : ℝ} (hX : ‖X‖ ≤ A) (hY : ‖Y‖ ≤ A)
    (hζ : ‖ζ‖ = 1) (hτ : ‖τ - ζ‖ ≤ 7072 / 10000 / 2 ^ 64)
    (hσ : ‖σ - starRingEnd ℂ ζ / 2‖ ≤ 7072 / 10000 / 2 ^ 64) (ha : ‖a - (X + Y) / 2‖ ≤ 2 / 2 ^ 64)
    (hb : ‖b - σ * (X - Y)‖ ≤ 4 / 2 ^ 64) (h0 : ‖c0 - a‖ ≤ D) (h1 : ‖c1 - b‖ ≤ D)
    (hp : ‖pm - τ * c1‖ ≤ 4 / 2 ^ 64) (hA : A < 2 ^ 62) (hD : D < 2 ^ 62) :
    ‖c0 + pm - X‖ ≤ 2 * D + 2 ∧ ‖c0 - pm - Y‖ ≤ 2 * D + 2 := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans h0
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hX
  have hτn : ‖τ‖ ≤ 1 + 7072 / 10000 / 2 ^ 64 := by
    linarith [norm_le_norm_add_norm_sub' τ ζ]
  have hk : ‖τ * σ - 1 / 2‖ ≤ (1 + 7072 / 10000 / 2 ^ 64) * (7072 / 10000 / 2 ^ 64) +
      7072 / 10000 / 2 ^ 64 / 2 := by
    have hc : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; norm_num
    have e : τ * σ - 1 / 2 = τ * (σ - starRingEnd ℂ ζ / 2) + (τ - ζ) * (starRingEnd ℂ ζ / 2) := by
      linear_combination (1 / 2 : ℂ) * hc
    have hz : ‖starRingEnd ℂ ζ / 2‖ = 1 / 2 := by
      rw [norm_div, Complex.norm_conj, hζ, Complex.norm_ofNat]
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hz]
    have := mul_le_mul hτn hσ (norm_nonneg _) (by positivity)
    linarith
  have hXY : ‖X - Y‖ ≤ 2 * A := by linarith [norm_sub_le X Y]
  have t3 : ‖τ * (c1 - b)‖ ≤ (1 + 7072 / 10000 / 2 ^ 64) * D := by
    rw [norm_mul]; exact mul_le_mul hτn h1 (norm_nonneg _) (by positivity)
  have t5 : ‖τ * (b - σ * (X - Y))‖ ≤ (1 + 7072 / 10000 / 2 ^ 64) * (4 / 2 ^ 64) := by
    rw [norm_mul]; exact mul_le_mul hτn hb (norm_nonneg _) (by positivity)
  have t6 : ‖(τ * σ - 1 / 2) * (X - Y)‖ ≤ ((1 + 7072 / 10000 / 2 ^ 64) * (7072 / 10000 / 2 ^ 64) +
      7072 / 10000 / 2 ^ 64 / 2) * (2 * A) := by
    rw [norm_mul]; exact mul_le_mul hk hXY (norm_nonneg _) (by positivity)
  constructor
  · rw [show c0 + pm - X = (c0 - a) + (pm - τ * c1) + τ * (c1 - b) + (a - (X + Y) / 2) +
      τ * (b - σ * (X - Y)) + (τ * σ - 1 / 2) * (X - Y) by ring]
    refine (norm_add6_le _ _ _ _ _ _).trans ?_
    linarith
  · rw [show c0 - pm - Y = (c0 - a) + -(pm - τ * c1) + -(τ * (c1 - b)) + (a - (X + Y) / 2) +
      -(τ * (b - σ * (X - Y))) + -((τ * σ - 1 / 2) * (X - Y)) by ring]
    refine (norm_add6_le _ _ _ _ _ _).trans ?_
    simp only [norm_neg]
    linarith

section Node

variable (C : Choices) (hw : C.word = none) {L : ℕ}
include hw

theorem splitW_fst (t : Out (L + 1) → Cx 64) (o : Out L) :
    (splitW C L t).1 o = ((t (o, false)).add (t (o, true))).half C.x.rm := by
  simp only [splitW, memo_eq, hw, wordFn, Cx.wr_id]

theorem splitW_snd (t : Out (L + 1) → Cx 64) (o : Out L) :
    (splitW C L t).2 o = (twsB C.x.rc 64 L o).c.mul C.x.rm ((t (o, false)).sub (t (o, true))) := by
  simp only [splitW, memo_eq, hw, wordFn, Cx.wr_id, Cx.mulW_id]

theorem updW_err (t0 t1 z ℓ : Out L → Cx 64) (o : Out L) :
    ‖(updW C t0 t1 z ℓ o).toC - ((t0 o).toC + ((t1 o).toC - (z o).toC) * (ℓ o).toC)‖ ≤
      4 / 2 ^ 64 := by
  simp only [updW, memo_eq, hw, wordFn, Cx.wr_id, Cx.mulW_id, Cx.toC_add, ← Cx.toC_sub,
    add_sub_add_left_eq_sub]
  exact Cx.mul_err _ _ _

theorem split_errs (t : Out (L + 1) → Cx 64) (o : Out L) :
    ‖((splitW C L t).1 o).toC - ((t (o, false)).toC + (t (o, true)).toC) / 2‖ ≤ 2 / 2 ^ 64 ∧
      ‖((splitW C L t).2 o).toC - (twsB C.x.rc 64 L o).c.toC *
        ((t (o, false)).toC - (t (o, true)).toC)‖ ≤ 4 / 2 ^ 64 := by
  rw [splitW_fst C hw, splitW_snd C hw, ← Cx.toC_add, ← Cx.toC_sub]
  exact ⟨Cx.half_err _ _, Cx.mul_err _ _ _⟩

theorem upd_dev (t0 t1 z ℓ : Out L → Cx 64) {D lam : ℝ} (hz : ∀ x, ‖(z x).toC - (t1 x).toC‖ ≤ D)
    (hℓ : ∀ x, ‖(ℓ x).toC‖ ≤ lam) (x : Out L) :
    ‖(updW C t0 t1 z ℓ x).toC - (t0 x).toC‖ ≤ D * lam + 4 / 2 ^ 64 := by
  have hm : ‖((t1 x).toC - (z x).toC) * (ℓ x).toC‖ ≤ D * lam := by
    rw [norm_mul, norm_sub_rev]
    exact mul_le_mul (hz x) (hℓ x) (norm_nonneg _) ((norm_nonneg _).trans (hz x))
  have := norm_sub_le_norm_sub_add_norm_sub (updW C t0 t1 z ℓ x).toC
    ((t0 x).toC + ((t1 x).toC - (z x).toC) * (ℓ x).toC) (t0 x).toC
  rw [add_sub_cancel_left] at this
  linarith [updW_err C hw t0 t1 z ℓ x]

variable (htw : twOk C.x.rc = true) (hL : L ≤ 8)
include htw hL

theorem splitW_bound (t : Out (L + 1) → Cx 64) {A : ℝ} (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hA : A < 2 ^ 62) (o : Out L) :
    ‖((splitW C L t).1 o).toC‖ ≤ A + 1 ∧ ‖((splitW C L t).2 o).toC‖ ≤ A + 1 := by
  obtain ⟨h1, h2⟩ := split_errs C hw t o
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (ht (o, false))
  have hs : ‖(t (o, false)).toC + (t (o, true)).toC‖ ≤ 2 * A := by
    linarith [norm_add_le (t (o, false)).toC (t (o, true)).toC, ht (o, false), ht (o, true)]
  have hd : ‖(t (o, false)).toC - (t (o, true)).toC‖ ≤ 2 * A := by
    linarith [norm_sub_le (t (o, false)).toC (t (o, true)).toC, ht (o, false), ht (o, true)]
  have hm := mul_le_mul (norm_tws_le htw hL o) hd (norm_nonneg _) (by positivity)
  rw [← norm_mul] at hm
  constructor
  · have := norm_le_norm_add_norm_sub' ((splitW C L t).1 o).toC
      (((t (o, false)).toC + (t (o, true)).toC) / 2)
    rw [norm_div, Complex.norm_ofNat] at this
    linarith
  · linarith [norm_le_norm_add_norm_sub' ((splitW C L t).2 o).toC
      ((twsB C.x.rc 64 L o).c.toC * ((t (o, false)).toC - (t (o, true)).toC))]

theorem mergeW_dev (t : Out (L + 1) → Cx 64) (c0 c1 : Out L → Cx 64) {A D : ℝ}
    (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hc : ∀ o, ‖(c0 o).toC - ((splitW C L t).1 o).toC‖ ≤ D ∧
      ‖(c1 o).toC - ((splitW C L t).2 o).toC‖ ≤ D)
    (hA : A < 2 ^ 62) (hD : D < 2 ^ 62) (x : Out (L + 1)) :
    ‖(mergeW C L c0 c1 x).toC - (t x).toC‖ ≤ 2 * D + 2 := by
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  obtain ⟨ha, hb⟩ := split_errs C hw t o
  have core := merge_split_dev (ht (o, false)) (ht (o, true)) (norm_zeta L o) (tw_err htw hL o)
    (tws_err htw hL o) ha hb (hc o).1 (hc o).2
    (Cx.mul_err C.x.rm (twB C.x.rc 64 L o).c (c1 o)) hA hD
  simp only [mergeW]
  erw [memo_eq]
  cases b
  · simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, Bool.false_eq_true, ↓reduceIte, Cx.toC_add]
    exact core.1
  · simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, ↓reduceIte, Cx.toC_sub]
    exact core.2

theorem split_ref (t : Out (L + 1) → Cx 64) (r : Out (L + 1) → ℂ) {A d : ℝ}
    (ht : ∀ x, ‖(t x).toC‖ ≤ A) (hd : ∀ x, ‖(t x).toC - r x‖ ≤ d) (o : Out L) :
    ‖((splitW C L t).1 o).toC - (splitE r).1 o‖ ≤
        d * (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 2 * (7072 / 10000 / 2 ^ 64) * A + 4 / 2 ^ 64 ∧
      ‖((splitW C L t).2 o).toC - (splitE r).2 o‖ ≤
        d * (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 2 * (7072 / 10000 / 2 ^ 64) * A + 4 / 2 ^ 64 := by
  obtain ⟨h1, h2⟩ := split_errs C hw t o
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (ht (o, false))
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd (o, false))
  have hdd : ‖((t (o, false)).toC - (t (o, true)).toC) - (r (o, false) - r (o, true))‖ ≤ 2 * d := by
    rw [show ((t (o, false)).toC - (t (o, true)).toC) - (r (o, false) - r (o, true)) =
      ((t (o, false)).toC - r (o, false)) - ((t (o, true)).toC - r (o, true)) by ring]
    linarith [norm_sub_le ((t (o, false)).toC - r (o, false)) ((t (o, true)).toC - r (o, true)),
      hd (o, false), hd (o, true)]
  have hr : ‖r (o, false) - r (o, true)‖ ≤ 2 * A + 2 * d := by
    linarith [norm_le_norm_add_norm_sub' (r (o, false) - r (o, true))
      ((t (o, false)).toC - (t (o, true)).toC), norm_sub_le (t (o, false)).toC (t (o, true)).toC,
      ht (o, false), ht (o, true), norm_sub_rev ((t (o, false)).toC - (t (o, true)).toC)
        (r (o, false) - r (o, true))]
  constructor
  · have e : ((splitW C L t).1 o).toC - (splitE r).1 o =
        (((splitW C L t).1 o).toC - ((t (o, false)).toC + (t (o, true)).toC) / 2) +
          (((t (o, false)).toC - r (o, false)) + ((t (o, true)).toC - r (o, true))) / 2 := by
      simp only [splitE]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le ((t (o, false)).toC - r (o, false)) ((t (o, true)).toC - r (o, true))
    linarith [hd (o, false), hd (o, true)]
  · have e := norm_prod_err (x := starRingEnd ℂ (zeta L o) / 2)
      (y := r (o, false) - r (o, true)) h2
    have m1 := mul_le_mul (norm_tws_le htw hL o) hdd (norm_nonneg _) (by positivity)
    have m2 := mul_le_mul (tws_err htw hL o) hr (norm_nonneg _) (by positivity)
    simp only [splitE]
    linarith [e, m1, m2]

theorem mergeW_ref (c0 c1 : Out L → Cx 64) (z0 z1 : Fin (2 ^ L) → ℤ) {m B : ℝ}
    (hm : ∀ o, ‖(c0 o).toC - evalAt (fun k => (z0 k : ℂ)) (pt L o)‖ ≤ m ∧
      ‖(c1 o).toC - evalAt (fun k => (z1 k : ℂ)) (pt L o)‖ ≤ m)
    (hc : ∀ o, ‖(c1 o).toC‖ ≤ B) (x : Out (L + 1)) :
    ‖(mergeW C L c0 c1 x).toC - evalAt (fun k => (ilv z0 z1 k : ℂ)) (pt (L + 1) x)‖ ≤
      (2 + 2 * (7072 / 10000 / 2 ^ 64)) * m + 7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64 := by
  rw [← congrFun (mergeL_ilv z0 z1) x]
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  have hbf := Errors.Butterfly.butterfly_err _ _ (zeta L o) _ _ _ _ _ _ _ (norm_zeta L o)
    (tw_err htw hL o) (hm o).1 (hm o).2 (Cx.mul_err C.x.rm (twB C.x.rc 64 L o).c (c1 o))
  have he : ‖evalAt (fun k => (z1 k : ℂ)) (pt L o)‖ ≤ B + m := by
    have := norm_le_norm_add_norm_sub' (evalAt (fun k => (z1 k : ℂ)) (pt L o)) (c1 o).toC
    rw [norm_sub_rev] at this
    linarith [hc o, (hm o).2]
  have hfin : ∀ y : ℝ, y ≤ m * (2 + 7072 / 10000 / 2 ^ 64) + 7072 / 10000 / 2 ^ 64 *
      ‖evalAt (fun k => (z1 k : ℂ)) (pt L o)‖ + 4 / 2 ^ 64 →
      y ≤ (2 + 2 * (7072 / 10000 / 2 ^ 64)) * m + 7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64 :=
    fun y hy => by linarith
  simp only [mergeW]
  erw [memo_eq]
  cases b
  · refine hfin _ ?_
    simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, Bool.false_eq_true, ↓reduceIte, Cx.toC_add,
      mergeL]
    exact hbf.1
  · refine hfin _ ?_
    simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, ↓reduceIte, Cx.toC_sub, mergeL]
    exact hbf.2

end Node

theorem leaf_dev (W : ℕ) (t : Cx 64) (y : ℤ) {E : ℝ} (hE : |t.im.toReal| ≤ E) :
    ‖(Cx.ofInt (clampZ (t.re.toInt .floor) W y) : Cx 64).toC - t.toC‖ ≤ W + 1 + E := by
  have hz : t.re.toInt .floor - W ≤ clampZ (t.re.toInt .floor) W y ∧
      clampZ (t.re.toInt .floor) W y ≤ t.re.toInt .floor + W := by
    simp only [clampZ]; omega
  have hb : ((t.re.toInt .floor : ℤ) : ℝ) = ⌊t.re.toReal⌋ := by
    rw [Fx.toInt_eq, RMode.rnd_floor]
  have h1 := Int.floor_le t.re.toReal
  have h2 := Int.lt_floor_add_one t.re.toReal
  have hz1 : ((t.re.toInt .floor : ℤ) : ℝ) - W ≤ clampZ (t.re.toInt .floor) W y := by
    exact_mod_cast hz.1
  have hz2 : (clampZ (t.re.toInt .floor) W y : ℝ) ≤ (t.re.toInt .floor : ℤ) + W := by
    exact_mod_cast hz.2
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Cx.toC_ofInt, Complex.sub_re, Complex.sub_im, Complex.intCast_re,
    Complex.intCast_im, Cx.toC_re, Cx.toC_im, zero_sub, abs_neg]
  have : |(clampZ (t.re.toInt .floor) W y : ℝ) - t.re.toReal| ≤ W + 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem fit63 {i : ℕ} (hi : i ≤ 64) {b : ℚ} (h : b < 2 ^ (i - 1)) : (b : ℝ) < 2 ^ 63 := by
  have h1 : (2 : ℚ) ^ (i - 1) ≤ 2 ^ 63 := pow_le_pow_right₀ (by norm_num) (by omega)
  exact_mod_cast h.trans_le h1

/-- **Deviations**: on inputs bounded by `A` with `rangeT i W E T A` and every leaf centre
`|Im| ≤ E`, every output of the unbounded run is within `devT W E T` of its input. -/
theorem ffsX_dev (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true) (i W : ℕ)
    (hi : i ≤ 64) (E : ℚ) : ∀ {L : ℕ} (T : CTree 64 L), L ≤ 9 → ∀ (t0 t1 : Out L → Cx 64) (A : ℚ),
      (∀ o, ‖(t0 o).toC‖ ≤ A ∧ ‖(t1 o).toC‖ ≤ A) → rangeT i W E T A = true →
      (∀ x, LeafR C W T t0 t1 x → |x.im.toReal| ≤ E) → ∀ s, ReachX C W T t0 t1 s → ∀ o,
        ‖(s.c0 o).toC - (t0 o).toC‖ ≤ devT W E T ∧ ‖(s.c1 o).toC - (t1 o).toC‖ ≤ devT W E T
  | _, .leaf _, _, t0, t1, _, _, _, hl, s, hs, o => by
    obtain ⟨y0, y1, rfl⟩ := hs
    simp only [devT]
    push_cast
    exact ⟨leaf_dev W (t0 ()) y0 (hl _ (Or.inl rfl)), leaf_dev W (t1 ()) y1 (hl _ (Or.inr rfl))⟩
  | _, @CTree.node _ L ℓ T0 T1, hL, t0, t1, A, hA, hr, hl, s, hs, o => by
    simp only [rangeT, Bool.and_eq_true, fitsQ, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, -⟩, -⟩, f5⟩, f6⟩, r1⟩, r0⟩ := hr
    have f1 := fit63 hi f1
    have f2 := fit63 hi f2
    have f5 := fit63 hi f5
    have f6 := fit63 hi f6
    push_cast at f1 f2 f5 f6
    obtain ⟨s1, s0, h1, h0, rfl⟩ := hs
    have hA0 : (0 : ℝ) ≤ A := (norm_nonneg _).trans (hA o).1
    have b1 := splitW_bound C hw htw (by omega) t1 (fun x => (hA x).2) (by linarith)
    have i1 := ffsX_dev C hw htw i W hi E T1 (by omega) _ _ (A + 1)
      (fun o => by push_cast; exact b1 o) r1 (fun x hx => hl x (Or.inl hx)) s1 h1
    have hD1 : (devT W E T1 : ℝ) < 2 ^ 62 := by linarith
    have z1 := mergeW_dev C hw htw (by omega) t1 s1.c0 s1.c1 (fun x => (hA x).2) i1
      (by linarith) hD1
    have hu := upd_dev C hw t0 t1 _ ℓ z1 (norm_le_nmax ℓ)
    have ha0 : ∀ x, ‖(updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC‖ ≤
        A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 := fun x => by
      linarith [norm_le_norm_add_norm_sub' (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC
        (t0 x).toC, hu x, (hA x).1]
    have b0 := splitW_bound C hw htw (by omega) _ ha0 (by linarith)
    have i0 := ffsX_dev C hw htw i W hi E T0 (by omega) _ _
      (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1) (fun o => by push_cast; exact b0 o)
      r0 (fun x hx => hl x (Or.inr ⟨s1, h1, hx⟩)) s0 h0
    have hp : (0 : ℝ) ≤ (2 * devT W E T1 + 2) * nmax (L + 1) ℓ :=
      mul_nonneg ((norm_nonneg _).trans (z1 o)) ((norm_nonneg _).trans (norm_le_nmax ℓ o))
    have hD0 : (devT W E T0 : ℝ) < 2 ^ 62 := by linarith
    have z0 := mergeW_dev C hw htw (by omega) _ s0.c0 s0.c1 ha0 i0 (by linarith) hD0 o
    simp only [devT]
    push_cast
    constructor
    · have := norm_sub_le_norm_sub_add_norm_sub (mergeW C L s0.c0 s0.c1 o).toC
        (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ o).toC (t0 o).toC
      exact le_max_of_le_right (by linarith [hu o])
    · exact le_max_of_le_left (z1 o)

/-! ## Leaf centres -/

/-- Bound on the error of a merged output of depth `L` against the exact FFT of its integers. -/
noncomputable def mB (K : ℝ) : ℕ → ℝ
  | 0 => 0
  | L + 1 => (2 + 3 * (7072 / 10000 / 2 ^ 64)) * mB K L + 7072 / 10000 / 2 ^ 64 * K + 4 / 2 ^ 64

/-- Bound on the leaf-centre error of a subtree of depth `L` whose inputs are within `d` of their
references, at values below `K`. -/
noncomputable def gB (K : ℝ) : ℕ → ℝ → ℝ
  | 0, d => d
  | L + 1, d => gB K L (((1 + lam512 L) * d + 4 / 2 ^ 64 + lam512 L * mB K (L + 1)) *
      (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 7072 / 10000 / 2 ^ 64 * K + 4 / 2 ^ 64)

theorem mB_nonneg {K : ℝ} (hK : 0 ≤ K) : ∀ L, 0 ≤ mB K L
  | 0 => le_rfl
  | L + 1 => by have := mB_nonneg hK L; simp only [mB]; positivity

theorem CTree.real_ℓ {L : ℕ} {ℓ : Out (L + 1) → Cx 64} {T0 T1 : CTree 64 L}
    (h : (CTree.node ℓ T0 T1).realB = true) : IsReal fun o => (ℓ o).toC := fun o => by
  simp only [CTree.realB, Bool.and_eq_true] at h
  change (ℓ (cj (L + 1) o)).toC = conj (ℓ o).toC
  rw [of_decide_eq_true ((allOut_iff _ _).1 h.1.1 o), Cx.toC_conjg]

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
  | _, .leaf _, _, _, _, t0, t1, _, _, _, r0, r1, h0, h1, d, hd, hG => by
    simp only [gB] at hG
    refine ⟨fun x hx => ?_, fun s hs o => ?_⟩
    · have key : ∀ (t : Cx 64) (r : Out 0 → ℂ), IsReal r → ‖t.toC - r ()‖ ≤ d →
          |t.im.toReal| ≤ E := fun t r hr ht => by
        have := Complex.abs_im_le_norm (t.toC - r ())
        rw [Complex.sub_im, im_eq_zero hr (), sub_zero] at this
        exact this.trans (ht.trans hG)
      rcases hx with rfl | rfl
      · exact key _ r0 h0 (hd ()).1
      · exact key _ r1 h1 (hd ()).2
    · obtain ⟨y0, y1, rfl⟩ := hs
      simp [mB, evalAt, Cx.toC_ofInt]
  | _, @CTree.node _ L ℓ T0 T1, hL, hok, hre, t0, t1, A, hA, hr, r0, r1, hR0, hR1, d, hd, hG => by
    have hrl := CTree.real_ℓ hre
    simp only [CTree.realB, Bool.and_eq_true] at hre
    have hℓ : ∀ o, ‖(ℓ o).toC‖ ≤ lam512 L := fun o => Cx.norm_le_lam512 (hok.1 o)
    simp only [rangeT, Bool.and_eq_true, fitsQ, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, -⟩, -⟩, f5⟩, f6⟩, r1'⟩, r0'⟩ := hr
    have g1 : (2 * A + 1 : ℝ) < 2 ^ (i - 1) := by exact_mod_cast f1
    have g2 : (2 * (A + 1 + devT W E T1) + 1 : ℝ) < 2 ^ (i - 1) := by exact_mod_cast f2
    have g5 : (2 * (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1) + 1 : ℝ) < 2 ^ (i - 1) := by
      exact_mod_cast f5
    have g6 : (2 * (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1 + devT W E T0) + 1 : ℝ) <
        2 ^ (i - 1) := by exact_mod_cast f6
    have k1 := fit63 hi f1
    have k2 := fit63 hi f2
    have k5 := fit63 hi f5
    have k6 := fit63 hi f6
    push_cast at k1 k2 k5 k6
    simp only [gB] at hG
    set K : ℝ := 2 ^ (i - 1) with hK
    have hK0 : 0 ≤ K := by positivity
    have hmB := mB_nonneg hK0 (L + 1)
    have hlam := lam512_nonneg L
    have hA0 : (0 : ℝ) ≤ A := (norm_nonneg _).trans (hA (Out.ofIdx _ 0)).1
    have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd (Out.ofIdx _ 0)).1
    set dc := ((1 + lam512 L) * d + 4 / 2 ^ 64 + lam512 L * mB K (L + 1)) *
      (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 7072 / 10000 / 2 ^ 64 * K + 4 / 2 ^ 64 with hdc
    have hp1 := mul_nonneg hlam hd0
    have hp2 := mul_nonneg hlam hmB
    have b1 := splitW_bound C hw htw (by omega) t1 (fun x => (hA x).2) (by linarith)
    have e1 : ∀ o, ‖((splitW C L t1).1 o).toC - (splitE r1).1 o‖ ≤ dc ∧
        ‖((splitW C L t1).2 o).toC - (splitE r1).2 o‖ ≤ dc := fun o => by
      obtain ⟨u1, u2⟩ := split_ref C hw htw (by omega) t1 r1 (fun x => (hA x).2)
        (fun x => (hd x).2) o
      constructor <;> linarith [u1, u2, hp1, hp2, g1]
    have i1 := ffsX_sound C hw htw i W hi E T1 (by omega) hok.2.2 hre.2 _ _ (A + 1)
      (fun o => by push_cast; exact b1 o) r1' _ _ (isReal_splitE hR1).1 (isReal_splitE hR1).2
      dc e1 hG
    have nodeOut : ∀ s1, ReachX C W T1 (splitW C L t1).1 (splitW C L t1).2 s1 →
        (∀ x, ‖(mergeW C L s1.c0 s1.c1 x).toC - (t1 x).toC‖ ≤ 2 * devT W E T1 + 2) ∧
        ∀ x, ‖(mergeW C L s1.c0 s1.c1 x).toC -
          evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x)‖ ≤ mB K (L + 1) := by
      intro s1 h1
      have dv := ffsX_dev C hw htw i W hi E T1 (by omega) _ _ (A + 1)
        (fun o => by push_cast; exact b1 o) r1' i1.1 s1 h1
      have hD1 : (devT W E T1 : ℝ) < 2 ^ 62 := by linarith
      refine ⟨mergeW_dev C hw htw (by omega) t1 s1.c0 s1.c1 (fun x => (hA x).2) dv
        (by linarith) hD1, fun x => ?_⟩
      have hc : ∀ o, ‖(s1.c1 o).toC‖ ≤ A + 1 + devT W E T1 := fun o => by
        linarith [norm_le_norm_add_norm_sub' (s1.c1 o).toC ((splitW C L t1).2 o).toC, (dv o).2,
          (b1 o).2]
      have := mergeW_ref C hw htw (by omega) s1.c0 s1.c1 s1.z0 s1.z1 (i1.2 s1 h1) hc x
      have hm := mB_nonneg hK0 L
      simp only [mB]
      linarith [this, hm, g2]
    have key : ∀ s1, ReachX C W T1 (splitW C L t1).1 (splitW C L t1).2 s1 →
        (∀ x, LeafR C W T0 (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).1
          (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 x → |x.im.toReal| ≤ E) ∧
        ∀ s0, ReachX C W T0 (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).1
          (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 s0 → ∀ x,
            ‖(mergeW C L s0.c0 s0.c1 x).toC -
              evalAt (fun k => (ilv s0.z0 s0.z1 k : ℂ)) (pt (L + 1) x)‖ ≤ mB K (L + 1) := by
      intro s1 h1
      obtain ⟨z1, m1⟩ := nodeOut s1 h1
      have hu := upd_dev C hw t0 t1 _ ℓ z1 (norm_le_nmax ℓ)
      have hp : (0 : ℝ) ≤ (2 * devT W E T1 + 2) * nmax (L + 1) ℓ := mul_nonneg
        ((norm_nonneg _).trans (z1 (Out.ofIdx _ 0)))
        ((norm_nonneg _).trans (norm_le_nmax ℓ (Out.ofIdx _ 0)))
      have ha0 : ∀ x, ‖(updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC‖ ≤
          A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 := fun x => by
        linarith [norm_le_norm_add_norm_sub' (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC
          (t0 x).toC, hu x, (hA x).1]
      have he : ∀ x, ‖(updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC -
          upd r0 r1 (fun x => evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x))
            (fun o => (ℓ o).toC) x‖ ≤ d + 4 / 2 ^ 64 + lam512 L * (d + mB K (L + 1)) := fun x => by
        have u := updW_err C hw t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x
        have hdz : ‖((t1 x).toC - (mergeW C L s1.c0 s1.c1 x).toC) -
            (r1 x - evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x))‖ ≤
              d + mB K (L + 1) := by
          rw [show ((t1 x).toC - (mergeW C L s1.c0 s1.c1 x).toC) -
            (r1 x - evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x)) =
            ((t1 x).toC - r1 x) - ((mergeW C L s1.c0 s1.c1 x).toC -
              evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x)) by ring]
          linarith [norm_sub_le ((t1 x).toC - r1 x) ((mergeW C L s1.c0 s1.c1 x).toC -
            evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x)), (hd x).2, m1 x]
        have hm := mul_le_mul hdz (hℓ x) (norm_nonneg _) (by positivity)
        rw [← norm_mul] at hm
        have e : (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC - upd r0 r1
            (fun x => evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x))
              (fun o => (ℓ o).toC) x =
            ((updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC - ((t0 x).toC +
              ((t1 x).toC - (mergeW C L s1.c0 s1.c1 x).toC) * (ℓ x).toC)) + ((t0 x).toC - r0 x) +
            (((t1 x).toC - (mergeW C L s1.c0 s1.c1 x).toC) -
              (r1 x - evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x))) * (ℓ x).toC := by
          simp only [upd]; ring
        rw [e]
        refine (norm_add₃_le).trans ?_
        linarith [(hd x).1, mul_comm (d + mB K (L + 1)) (lam512 L)]
      have e0 : ∀ o, ‖((splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).1 o).toC -
            (splitE (upd r0 r1 (fun x => evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ))
              (pt (L + 1) x)) (fun o => (ℓ o).toC))).1 o‖ ≤ dc ∧
          ‖((splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 o).toC -
            (splitE (upd r0 r1 (fun x => evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ))
              (pt (L + 1) x)) (fun o => (ℓ o).toC))).2 o‖ ≤ dc := fun o => by
        obtain ⟨u1, u2⟩ := split_ref C hw htw (by omega) _ _ ha0 he o
        constructor <;> linarith [u1, u2, g5]
      have hR0' := isReal_upd hR0 hR1 (isReal_evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ))
        fun k => map_intCast (starRingEnd ℂ) _) hrl
      have b0 := splitW_bound C hw htw (by omega) _ ha0 (by linarith)
      have i0 := ffsX_sound C hw htw i W hi E T0 (by omega) hok.2.1 hre.1.2 _ _
        (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1)
        (fun o => by push_cast; exact b0 o) r0' _ _ (isReal_splitE hR0').1 (isReal_splitE hR0').2
        dc e0 hG
      refine ⟨i0.1, fun s0 h0 x => ?_⟩
      have dv := ffsX_dev C hw htw i W hi E T0 (by omega) _ _
        (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1) (fun o => by push_cast; exact b0 o)
        r0' i0.1 s0 h0
      have hc : ∀ o, ‖(s0.c1 o).toC‖ ≤
          A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1 + devT W E T0 := fun o => by
        linarith [norm_le_norm_add_norm_sub' (s0.c1 o).toC
          ((splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 o).toC, (dv o).2, (b0 o).2]
      have := mergeW_ref C hw htw (by omega) s0.c0 s0.c1 s0.z0 s0.z1 (i0.2 s0 h0) hc x
      have hm := mB_nonneg hK0 L
      simp only [mB]
      linarith [this, hm, g6]
    refine ⟨fun x hx => ?_, fun s hs o => ?_⟩
    · rcases hx with hx | ⟨s1, h1, hx⟩
      · exact i1.1 x hx
      · exact (key s1 h1).1 x hx
    · obtain ⟨s1, s0, h1, h0, rfl⟩ := hs
      exact ⟨(key s1 h1).2 s0 h0 o, (nodeOut s1 h1).2 o⟩

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
noncomputable def tRef (f F c : ZPoly) : (Out 9 → ℂ) × (Out 9 → ℂ) :=
  (fun o => -(evalAt (fun j => (c j : ℂ)) (pt 9 o) * evalAt (fun j => (F j : ℂ)) (pt 9 o)) / 12289,
    fun o => evalAt (fun j => (c j : ℂ)) (pt 9 o) * evalAt (fun j => (f j : ℂ)) (pt 9 o) / 12289)

theorem isReal_tRef (f F c : ZPoly) : IsReal (tRef f F c).1 ∧ IsReal (tRef f F c).2 := by
  have h : ∀ a : ZPoly, IsReal fun o => evalAt (fun j => (a j : ℂ)) (pt 9 o) := fun a =>
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

theorem wordFn_none : wordFn none = id := rfl

section Word

variable (C : Choices) {i : ℕ} (hi : 1 ≤ i)
include hi

theorem updW_word {L : ℕ} (t0 t1 z ℓ : Out L → Cx 64) {A D lam : ℝ}
    (ht : ∀ o, ‖(t0 o).toC‖ ≤ A) (hz : ∀ o, ‖(t1 o).toC - (z o).toC‖ ≤ D)
    (hℓ : ∀ o, ‖(ℓ o).toC‖ ≤ lam) (h1 : D < 2 ^ (i - 1)) (h2 : D * lam + 1 < 2 ^ (i - 1))
    (h3 : A + D * lam + 1 < 2 ^ (i - 1)) :
    updW { C with word := some i } t0 t1 z ℓ = updW { C with word := none } t0 t1 z ℓ := by
  funext o
  have hm0 := mul_le_mul (hz o) (hℓ o) (norm_nonneg _) ((norm_nonneg _).trans (hz o))
  have hd : ‖((t1 o).sub (z o)).toC‖ < 2 ^ (i - 1) := by rw [Cx.toC_sub]; linarith [hz o]
  have hm : ‖((t1 o).sub (z o)).toC‖ * ‖(ℓ o).toC‖ + 2 / 2 ^ 64 < 2 ^ (i - 1) := by
    rw [Cx.toC_sub]; linarith
  have hp := Cx.norm_mul_le C.x.rm ((t1 o).sub (z o)) (ℓ o)
  rw [Cx.toC_sub] at hp
  have hs : ‖((t0 o).add (((t1 o).sub (z o)).mul C.x.rm (ℓ o))).toC‖ < 2 ^ (i - 1) := by
    rw [Cx.toC_add]
    linarith [norm_add_le (t0 o).toC (((t1 o).sub (z o)).mul C.x.rm (ℓ o)).toC, ht o]
  simp only [updW, memo_eq, wordFn_none, Cx.wr_id, Cx.mulW_id]
  rw [Cx.wr_some hi hd, Cx.mulW_some hi _ hm, Cx.wr_some hi hs]

variable (htw : twOk C.x.rc = true) {L : ℕ} (hL : L ≤ 8)
include htw hL

theorem splitW_word (t : Out (L + 1) → Cx 64) {A : ℝ} (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hA : 2 * A + 1 < 2 ^ (i - 1)) :
    splitW { C with word := some i } L t = splitW { C with word := none } L t := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (ht (Out.ofIdx _ 0))
  refine Prod.ext (funext fun o => ?_) (funext fun o => ?_)
  · have hs0 : ‖((t (o, false)).add (t (o, true))).toC‖ ≤ 2 * A := by
      rw [Cx.toC_add]
      linarith [norm_add_le (t (o, false)).toC (t (o, true)).toC, ht (o, false), ht (o, true)]
    have hs : ‖((t (o, false)).add (t (o, true))).toC‖ < 2 ^ (i - 1) := by linarith
    have hh : ‖(((t (o, false)).add (t (o, true))).half C.x.rm).toC‖ < 2 ^ (i - 1) := by
      have := norm_le_norm_add_norm_sub' (((t (o, false)).add (t (o, true))).half C.x.rm).toC
        (((t (o, false)).add (t (o, true))).toC / 2)
      rw [norm_div, Complex.norm_ofNat] at this
      linarith [Cx.half_err C.x.rm ((t (o, false)).add (t (o, true)))]
    simp only [splitW, memo_eq, wordFn_none, Cx.wr_id]
    rw [Cx.wr_some hi hs, Cx.wr_some hi hh]
  · have hd0 : ‖((t (o, false)).sub (t (o, true))).toC‖ ≤ 2 * A := by
      rw [Cx.toC_sub]
      linarith [norm_sub_le (t (o, false)).toC (t (o, true)).toC, ht (o, false), ht (o, true)]
    have hd : ‖((t (o, false)).sub (t (o, true))).toC‖ < 2 ^ (i - 1) := by linarith
    have hm0 := mul_le_mul (norm_tws_le htw hL o) hd0 (norm_nonneg _) (by positivity)
    have hm : ‖(twsB C.x.rc 64 L o).c.toC‖ * ‖((t (o, false)).sub (t (o, true))).toC‖ +
        2 / 2 ^ 64 < 2 ^ (i - 1) := by linarith
    simp only [splitW, memo_eq, wordFn_none, Cx.wr_id, Cx.mulW_id]
    rw [Cx.wr_some hi hd, Cx.mulW_some hi _ hm]

theorem mergeW_word (c0 c1 : Out L → Cx 64) {B : ℝ}
    (hc : ∀ o, ‖(c0 o).toC‖ ≤ B ∧ ‖(c1 o).toC‖ ≤ B) (hB : 2 * B + 1 < 2 ^ (i - 1))
    (hB62 : B < 2 ^ 62) :
    mergeW { C with word := some i } L c0 c1 = mergeW { C with word := none } L c0 c1 := by
  funext x
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hc o).1
  have hpp := mul_le_mul (norm_tw_le htw hL o) (hc o).2 (norm_nonneg _) (by positivity)
  have hm : ‖(twB C.x.rc 64 L o).c.toC‖ * ‖(c1 o).toC‖ + 2 / 2 ^ 64 < 2 ^ (i - 1) := by
    linarith
  have hp := Cx.norm_mul_le C.x.rm (twB C.x.rc 64 L o).c (c1 o)
  simp only [mergeW]
  erw [memo_eq, memo_eq]
  cases b
  · have hs : ‖((c0 o).add ((twB C.x.rc 64 L o).c.mul C.x.rm (c1 o))).toC‖ < 2 ^ (i - 1) := by
      rw [Cx.toC_add]
      linarith [norm_add_le (c0 o).toC ((twB C.x.rc 64 L o).c.mul C.x.rm (c1 o)).toC, (hc o).1]
    simp only [wordFn_none, Cx.wr_id, Cx.mulW_id, Bool.false_eq_true, ↓reduceIte]
    rw [Cx.mulW_some hi _ hm, Cx.wr_some hi hs]
  · have hs : ‖((c0 o).sub ((twB C.x.rc 64 L o).c.mul C.x.rm (c1 o))).toC‖ < 2 ^ (i - 1) := by
      rw [Cx.toC_sub]
      linarith [norm_sub_le (c0 o).toC ((twB C.x.rc 64 L o).c.mul C.x.rm (c1 o)).toC, (hc o).1]
    simp only [wordFn_none, Cx.wr_id, Cx.mulW_id, ↓reduceIte]
    rw [Cx.mulW_some hi _ hm, Cx.wr_some hi hs]

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
        ffsX { C with word := none } (clampS W samp) T t0 t1 := by
  intro L T
  induction T with
  | leaf _ => intros; simp only [ffsX]
  | @node L ℓ T0 T1 ih0 ih1 =>
    intro hL t0 t1 A hA hr hl
    simp only [rangeT, Bool.and_eq_true, fitsQ, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, -⟩, f4⟩, f5⟩, f6⟩, r1⟩, r0⟩ := hr
    have g1 : (2 * A + 1 : ℝ) < 2 ^ (i - 1) := by exact_mod_cast f1
    have g2 : (2 * (A + 1 + devT W E T1) + 1 : ℝ) < 2 ^ (i - 1) := by exact_mod_cast f2
    have g4 : ((2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 : ℝ) < 2 ^ (i - 1) := by
      exact_mod_cast f4
    have g5 : (2 * (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1) + 1 : ℝ) < 2 ^ (i - 1) := by
      exact_mod_cast f5
    have g6 : (2 * (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1 + devT W E T0) + 1 : ℝ) <
        2 ^ (i - 1) := by exact_mod_cast f6
    have k1 := fit63 hi64 f1
    have k2 := fit63 hi64 f2
    have k5 := fit63 hi64 f5
    have k6 := fit63 hi64 f6
    push_cast at k1 k2 k5 k6
    have hA0 : (0 : ℝ) ≤ A := (norm_nonneg _).trans (hA (Out.ofIdx _ 0)).1
    have b1 := splitW_bound { C with word := none } rfl htw (by omega) t1 (fun x => (hA x).2)
      (by linarith)
    have hl1 : ∀ x, LeafR { C with word := none } W T1 (splitW { C with word := none } L t1).1
        (splitW { C with word := none } L t1).2 x → |x.im.toReal| ≤ E := fun x hx =>
      hl x (Or.inl hx)
    simp only [ffsX]
    rw [splitW_word C hi htw (by omega) t1 (fun x => (hA x).2) g1,
      ih1 (by omega) _ _ (A + 1) (fun o => by push_cast; exact b1 o) r1 hl1]
    cases chkX C.rchk (L + 1) t1
    · simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [↓reduceIte]
    refine ffsX_bind_congr _ W samp T1 _ _ _ _ (by simp only) fun s1 h1 => ?_
    dsimp only
    have dv1 := ffsX_dev { C with word := none } rfl htw i W hi64 E T1 (by omega) _ _ (A + 1)
      (fun o => by push_cast; exact b1 o) r1 hl1 s1 h1
    have hc1 : ∀ o, ‖(s1.c0 o).toC‖ ≤ A + 1 + devT W E T1 ∧
        ‖(s1.c1 o).toC‖ ≤ A + 1 + devT W E T1 := fun o => ⟨by
      linarith [norm_le_norm_add_norm_sub' (s1.c0 o).toC
        ((splitW { C with word := none } L t1).1 o).toC, (dv1 o).1, (b1 o).1], by
      linarith [norm_le_norm_add_norm_sub' (s1.c1 o).toC
        ((splitW { C with word := none } L t1).2 o).toC, (dv1 o).2, (b1 o).2]⟩
    have z1 := mergeW_dev { C with word := none } rfl htw (by omega) t1 s1.c0 s1.c1
      (fun x => (hA x).2) dv1 (by linarith) (by linarith)
    have hu := upd_dev { C with word := none } rfl t0 t1 _ ℓ z1 (norm_le_nmax ℓ)
    have hp : (0 : ℝ) ≤ (2 * devT W E T1 + 2) * nmax (L + 1) ℓ := mul_nonneg
      ((norm_nonneg _).trans (z1 (Out.ofIdx _ 0)))
      ((norm_nonneg _).trans (norm_le_nmax ℓ (Out.ofIdx _ 0)))
    have ha0 : ∀ x, ‖(updW { C with word := none } t0 t1
        (mergeW { C with word := none } L s1.c0 s1.c1) ℓ x).toC‖ ≤
          A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 := fun x => by
      linarith [norm_le_norm_add_norm_sub' (updW { C with word := none } t0 t1
        (mergeW { C with word := none } L s1.c0 s1.c1) ℓ x).toC (t0 x).toC, hu x, (hA x).1]
    have b0 := splitW_bound { C with word := none } rfl htw (by omega) _ ha0 (by linarith)
    have hl0 : ∀ x, LeafR { C with word := none } W T0
        (splitW { C with word := none } L (updW { C with word := none } t0 t1
          (mergeW { C with word := none } L s1.c0 s1.c1) ℓ)).1
        (splitW { C with word := none } L (updW { C with word := none } t0 t1
          (mergeW { C with word := none } L s1.c0 s1.c1) ℓ)).2 x → |x.im.toReal| ≤ E :=
      fun x hx => hl x (Or.inr ⟨s1, h1, hx⟩)
    rw [mergeW_word C hi htw (by omega) s1.c0 s1.c1 hc1 (by linarith) (by linarith),
      updW_word C hi t0 t1 _ ℓ (fun o => (hA o).1) (fun o => by rw [norm_sub_rev]; exact z1 o)
        (norm_le_nmax ℓ) (by linarith) g4 (by linarith),
      splitW_word C hi htw (by omega) _ ha0 (by linarith),
      ih0 (by omega) _ _ (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1)
        (fun o => by push_cast; exact b0 o) r0 hl0]
    cases (chkX C.rchk L s1.c1 && chkX C.rchk (L + 1) (updW { C with word := none } t0 t1
      (mergeW { C with word := none } L s1.c0 s1.c1) ℓ))
    · simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [↓reduceIte]
    refine ffsX_bind_congr _ W samp T0 _ _ _ _ (by simp only) fun s0 h0 => ?_
    dsimp only
    have dv0 := ffsX_dev { C with word := none } rfl htw i W hi64 E T0 (by omega) _ _
      (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1) (fun o => by push_cast; exact b0 o)
      r0 hl0 s0 h0
    have hc0 : ∀ o, ‖(s0.c0 o).toC‖ ≤ A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1 +
        devT W E T0 ∧ ‖(s0.c1 o).toC‖ ≤ A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1 +
          devT W E T0 := fun o => ⟨by
      linarith [norm_le_norm_add_norm_sub' (s0.c0 o).toC
        ((splitW { C with word := none } L (updW { C with word := none } t0 t1
          (mergeW { C with word := none } L s1.c0 s1.c1) ℓ)).1 o).toC, (dv0 o).1, (b0 o).1], by
      linarith [norm_le_norm_add_norm_sub' (s0.c1 o).toC
        ((splitW { C with word := none } L (updW { C with word := none } t0 t1
          (mergeW { C with word := none } L s1.c0 s1.c1) ℓ)).2 o).toC, (dv0 o).2, (b0 o).2]⟩
    rw [mergeW_word C hi htw (by omega) s0.c0 s0.c1 hc0 (by linarith) (by linarith)]

theorem fftW_word (C : Choices) (htw : twOk C.x.rc = true) {i : ℕ} (hi : 1 ≤ i) (B : ℝ)
    (hB : 2 * B + 1 < 2 ^ (i - 1)) : ∀ (L : ℕ), L ≤ 9 → ∀ (a : Fin (2 ^ L) → ℤ),
      (∀ o, ‖evalAt (fun j => (a j : ℂ)) (pt L o)‖ ≤ B) →
        fftW { C with word := some i } L a = fftW { C with word := none } L a
  | 0, _, a, hB' => by
    funext o
    have e : evalAt (fun j => (a j : ℂ)) (pt 0 o) = a ⟨0, by norm_num⟩ := by simp [evalAt]
    have h := hB' o
    rw [e] at h
    simp only [fftW, wordFn_none, Cx.wr_id]
    exact Cx.wr_some hi
      (by rw [Cx.toC_ofInt]; linarith [norm_nonneg ((a ⟨0, by norm_num⟩ : ℤ) : ℂ)])
  | L + 1, hL, a, hB' => by
    funext x
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' (o, b))
    have hsub := half_eval_le B L (fun j => (a j : ℂ)) (zeta L) (pt L) (pt (L + 1))
      (fun o b => pt_succ L o b) (zeta_sq L) (norm_zeta L) hB'
    rw [evens_castC, odds_castC] at hsub
    have ev := fftW_word C htw hi B hB L (by omega) (evensZ a) fun o => (hsub o).1
    have od := fftW_word C htw hi B hB L (by omega) (oddsZ a) fun o => (hsub o).2
    have hx : (0 : ℝ) ≤ 7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64 := by positivity
    have Ev := (fftW_err { C with word := none } rfl htw B L (by omega) (oddsZ a)
      (fun o => (hsub o).2) o).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega : L ≤ 8)) hx)
    have Ex := (fftW_err { C with word := none } rfl htw B (L + 1) hL a hB' (o, b)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hL) hx)
    have hv : ‖(fftW { C with word := none } L (oddsZ a) o).toC‖ ≤
        B + 4 ^ 8 * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) := by
      linarith [norm_le_norm_add_norm_sub' (fftW { C with word := none } L (oddsZ a) o).toC
        (evalAt (fun j => (oddsZ a j : ℂ)) (pt L o)), (hsub o).2]
    have hm0 := mul_le_mul (norm_tw_le htw (by omega) o) hv (norm_nonneg _) (by positivity)
    have hm : ‖(twB C.x.rc 64 L o).c.toC‖ *
        ‖(fftW { C with word := none } L (oddsZ a) o).toC‖ + 2 / 2 ^ 64 < 2 ^ (i - 1) := by
      linarith
    have hs : ∀ z : Cx 64, ‖z.toC - evalAt (fun j => (a j : ℂ)) (pt (L + 1) (o, b))‖ ≤
        4 ^ 9 * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) → ‖z.toC‖ < 2 ^ (i - 1) := fun z hz => by
      linarith [norm_le_norm_add_norm_sub' z.toC (evalAt (fun j => (a j : ℂ)) (pt (L + 1) (o, b))),
        hB' (o, b)]
    simp only [fftW] at Ex ⊢
    rw [ev, od]
    erw [memo_eq, memo_eq]
    erw [memo_eq] at Ex
    cases b
    · simp only [wordFn_none, Cx.wr_id, Cx.mulW_id, Bool.false_eq_true, ↓reduceIte] at Ex ⊢
      rw [Cx.mulW_some hi _ hm, Cx.wr_some hi (hs _ Ex)]
    · simp only [wordFn_none, Cx.wr_id, Cx.mulW_id, ↓reduceIte] at Ex ⊢
      rw [Cx.mulW_some hi _ hm, Cx.wr_some hi (hs _ Ex)]

theorem norm_evalAt_le_l1 (a : ZPoly) (o : Out 9) :
    ‖evalAt (fun j => (a j : ℂ)) (pt 9 o)‖ ≤ (l1Q a : ℝ) := by
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
