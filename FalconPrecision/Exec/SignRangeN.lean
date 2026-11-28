/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignRefine

/-! # Integer ranges and leaf centres of the executable signer, at any table cutoff

The lemmas of `Exec.SignRange` that do not depend on the size, for trees of depth `L ≤ N` whose
tables at levels `< N` pass `twOkN rc N` (Falcon-512: `N = 9`, `twOk`; Falcon-1024: `N = 10`) and
whose stored factors satisfy `‖ℓ̂‖ ≤ Λ L` (Falcon-512: `lam512`; Falcon-1024: `lam1024`).

Every rounding of `RMode` is within `2⁻⁶⁴` (`floor` included), every computed table at levels
`< N` within `δ = 0.7072·2⁻⁶⁴` of `ζ`, `ζ̄/2` (`tw_errN`, `tws_errN`).

`ReachX C W T t0 t1 s`: `s` is an output of `ffsX C` on `T` from `(t0, t1)` for some sampler
answers within `W` of `⌊t̄⌋`, the checks ignored (`OutX` outputs are such, `reachX_of_outX`);
`LeafR` its leaf centres. `ffsX_bind_congr`: in every lawful monad, two continuations of
`ffsX C (clampS W samp)` that agree on `none` and on `ReachX` outputs give the same computation.

`ffsX_devN`: on inputs bounded by `A` with `rangeT i W E T A` and leaf centres `|Im| ≤ E`, every
output is within `devT W E T` of the input. `ffsX_soundN` (the shared lemma, one induction in run
order): with exact conjugate-symmetric references within `d` of the inputs (`IsReal`), every leaf
centre has `|Im| ≤ gBP Λ (2^(i-1)) L d ≤ E`, and every output within `mB` of the exact FFT of its
integers. `ffsX_wordN`, `fftW_wordN` (`N ≤ 10`): then no reduction to `(i + 64)`-bit words
changes a value.
The Falcon-512 statements (`ffsX_dev`, `ffsX_sound`, `ffsX_word`, …) are their instances at
`N = 9` (`Exec.SignRange`), the Falcon-1024 ones use `N = 10` (`Exec.SignRange1024`).

Not proved here: anything about a key (the bounds on the tree and the target are hypotheses);
the theorems for `i > 64`; sampler answers outside `⌊t̄⌋ ± W`. -/

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

section TablesN

variable {rc : RMode} {N : ℕ} (h : twOkN rc N = true) {L : ℕ} (hL : L < N) (o : Out L)
include h hL

theorem tw_errN : ‖(twB rc 64 L o).c.toC - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 64 := by
  have := twXN_err64 N rc h L o
  rwa [twXN, ite_eq_left_of_eq_true _ _ (eq_true hL)] at this

theorem tws_errN :
    ‖(twsB rc 64 L o).c.toC - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 64 := by
  have := twsXN_err64 N rc h L o
  rwa [twsXN, ite_eq_left_of_eq_true _ _ (eq_true hL)] at this

theorem norm_tw_leN : ‖(twB rc 64 L o).c.toC‖ ≤ 1 + 7072 / 10000 / 2 ^ 64 := by
  have := norm_le_norm_add_norm_sub' (twB rc 64 L o).c.toC (zeta L o)
  rw [norm_zeta] at this
  linarith [tw_errN h hL o]

theorem norm_tws_leN : ‖(twsB rc 64 L o).c.toC‖ ≤ 1 / 2 + 7072 / 10000 / 2 ^ 64 := by
  have := norm_le_norm_add_norm_sub' (twsB rc 64 L o).c.toC (starRingEnd ℂ (zeta L o) / 2)
  rw [norm_div, Complex.norm_conj, norm_zeta, Complex.norm_ofNat] at this
  linarith [tws_errN h hL o]

end TablesN

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
theorem fftW_errN (C : Choices) (hw : C.word = none) {N : ℕ} (htw : twOkN C.x.rc N = true)
    (B : ℝ) : ∀ (L : ℕ), L ≤ N → ∀ (a : Fin (2 ^ L) → ℤ),
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
    have hu := fftW_errN C hw htw B L (by omega) (evensZ a) (fun o => (hsub o).1) o
    have hv := fftW_errN C hw htw B L (by omega) (oddsZ a) (fun o => (hsub o).2) o
    have hbf := Errors.Butterfly.butterfly_err _ _ (zeta L o) _ _ _ _ _ _ _ (norm_zeta L o)
      (tw_errN htw (by omega) o) hu hv (Cx.mul_err C.x.rm (twB C.x.rc 64 L o).c
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

variable {N : ℕ} (htw : twOkN C.x.rc N = true) (hL : L < N)
include htw hL

theorem splitW_boundN (t : Out (L + 1) → Cx 64) {A : ℝ} (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hA : A < 2 ^ 62) (o : Out L) :
    ‖((splitW C L t).1 o).toC‖ ≤ A + 1 ∧ ‖((splitW C L t).2 o).toC‖ ≤ A + 1 := by
  obtain ⟨h1, h2⟩ := split_errs C hw t o
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (ht (o, false))
  have hs : ‖(t (o, false)).toC + (t (o, true)).toC‖ ≤ 2 * A := by
    linarith [norm_add_le (t (o, false)).toC (t (o, true)).toC, ht (o, false), ht (o, true)]
  have hd : ‖(t (o, false)).toC - (t (o, true)).toC‖ ≤ 2 * A := by
    linarith [norm_sub_le (t (o, false)).toC (t (o, true)).toC, ht (o, false), ht (o, true)]
  have hm := mul_le_mul (norm_tws_leN htw hL o) hd (norm_nonneg _) (by positivity)
  rw [← norm_mul] at hm
  constructor
  · have := norm_le_norm_add_norm_sub' ((splitW C L t).1 o).toC
      (((t (o, false)).toC + (t (o, true)).toC) / 2)
    rw [norm_div, Complex.norm_ofNat] at this
    linarith
  · linarith [norm_le_norm_add_norm_sub' ((splitW C L t).2 o).toC
      ((twsB C.x.rc 64 L o).c.toC * ((t (o, false)).toC - (t (o, true)).toC))]

theorem mergeW_devN (t : Out (L + 1) → Cx 64) (c0 c1 : Out L → Cx 64) {A D : ℝ}
    (ht : ∀ x, ‖(t x).toC‖ ≤ A)
    (hc : ∀ o, ‖(c0 o).toC - ((splitW C L t).1 o).toC‖ ≤ D ∧
      ‖(c1 o).toC - ((splitW C L t).2 o).toC‖ ≤ D)
    (hA : A < 2 ^ 62) (hD : D < 2 ^ 62) (x : Out (L + 1)) :
    ‖(mergeW C L c0 c1 x).toC - (t x).toC‖ ≤ 2 * D + 2 := by
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  obtain ⟨ha, hb⟩ := split_errs C hw t o
  have core := merge_split_dev (ht (o, false)) (ht (o, true)) (norm_zeta L o) (tw_errN htw hL o)
    (tws_errN htw hL o) ha hb (hc o).1 (hc o).2
    (Cx.mul_err C.x.rm (twB C.x.rc 64 L o).c (c1 o)) hA hD
  simp only [mergeW]
  erw [memo_eq]
  cases b
  · simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, Bool.false_eq_true, ↓reduceIte, Cx.toC_add]
    exact core.1
  · simp only [hw, wordFn, Cx.wr_id, Cx.mulW_id, ↓reduceIte, Cx.toC_sub]
    exact core.2

theorem split_refN (t : Out (L + 1) → Cx 64) (r : Out (L + 1) → ℂ) {A d : ℝ}
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
    have m1 := mul_le_mul (norm_tws_leN htw hL o) hdd (norm_nonneg _) (by positivity)
    have m2 := mul_le_mul (tws_errN htw hL o) hr (norm_nonneg _) (by positivity)
    simp only [splitE]
    linarith [e, m1, m2]

theorem mergeW_refN (c0 c1 : Out L → Cx 64) (z0 z1 : Fin (2 ^ L) → ℤ) {m B : ℝ}
    (hm : ∀ o, ‖(c0 o).toC - evalAt (fun k => (z0 k : ℂ)) (pt L o)‖ ≤ m ∧
      ‖(c1 o).toC - evalAt (fun k => (z1 k : ℂ)) (pt L o)‖ ≤ m)
    (hc : ∀ o, ‖(c1 o).toC‖ ≤ B) (x : Out (L + 1)) :
    ‖(mergeW C L c0 c1 x).toC - evalAt (fun k => (ilv z0 z1 k : ℂ)) (pt (L + 1) x)‖ ≤
      (2 + 2 * (7072 / 10000 / 2 ^ 64)) * m + 7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64 := by
  rw [← congrFun (mergeL_ilv z0 z1) x]
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  have hbf := Errors.Butterfly.butterfly_err _ _ (zeta L o) _ _ _ _ _ _ _ (norm_zeta L o)
    (tw_errN htw hL o) (hm o).1 (hm o).2 (Cx.mul_err C.x.rm (twB C.x.rc 64 L o).c (c1 o))
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
theorem ffsX_devN (C : Choices) (hw : C.word = none) {N : ℕ} (htw : twOkN C.x.rc N = true)
    (i W : ℕ) (hi : i ≤ 64) (E : ℚ) :
    ∀ {L : ℕ} (T : CTree 64 L), L ≤ N → ∀ (t0 t1 : Out L → Cx 64) (A : ℚ),
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
    have b1 := splitW_boundN C hw htw (by omega) t1 (fun x => (hA x).2) (by linarith)
    have i1 := ffsX_devN C hw htw i W hi E T1 (by omega) _ _ (A + 1)
      (fun o => by push_cast; exact b1 o) r1 (fun x hx => hl x (Or.inl hx)) s1 h1
    have hD1 : (devT W E T1 : ℝ) < 2 ^ 62 := by linarith
    have z1 := mergeW_devN C hw htw (by omega) t1 s1.c0 s1.c1 (fun x => (hA x).2) i1
      (by linarith) hD1
    have hu := upd_dev C hw t0 t1 _ ℓ z1 (norm_le_nmax ℓ)
    have ha0 : ∀ x, ‖(updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC‖ ≤
        A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 := fun x => by
      linarith [norm_le_norm_add_norm_sub' (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ x).toC
        (t0 x).toC, hu x, (hA x).1]
    have b0 := splitW_boundN C hw htw (by omega) _ ha0 (by linarith)
    have i0 := ffsX_devN C hw htw i W hi E T0 (by omega) _ _
      (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1) (fun o => by push_cast; exact b0 o)
      r0 (fun x hx => hl x (Or.inr ⟨s1, h1, hx⟩)) s0 h0
    have hp : (0 : ℝ) ≤ (2 * devT W E T1 + 2) * nmax (L + 1) ℓ :=
      mul_nonneg ((norm_nonneg _).trans (z1 o)) ((norm_nonneg _).trans (norm_le_nmax ℓ o))
    have hD0 : (devT W E T0 : ℝ) < 2 ^ 62 := by linarith
    have z0 := mergeW_devN C hw htw (by omega) _ s0.c0 s0.c1 ha0 i0 (by linarith) hD0 o
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
references, at values below `K`, with stored factors `‖ℓ̂‖ ≤ Λ L`. -/
noncomputable def gBP (Λ : ℕ → ℝ) (K : ℝ) : ℕ → ℝ → ℝ
  | 0, d => d
  | L + 1, d => gBP Λ K L (((1 + Λ L) * d + 4 / 2 ^ 64 + Λ L * mB K (L + 1)) *
      (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 7072 / 10000 / 2 ^ 64 * K + 4 / 2 ^ 64)

theorem mB_nonneg {K : ℝ} (hK : 0 ≤ K) : ∀ L, 0 ≤ mB K L
  | 0 => le_rfl
  | L + 1 => by have := mB_nonneg hK L; simp only [mB]; positivity

theorem CTree.real_ℓ {L : ℕ} {ℓ : Out (L + 1) → Cx 64} {T0 T1 : CTree 64 L}
    (h : (CTree.node ℓ T0 T1).realB = true) : IsReal fun o => (ℓ o).toC := fun o => by
  simp only [CTree.realB, Bool.and_eq_true] at h
  change (ℓ (cj (L + 1) o)).toC = conj (ℓ o).toC
  rw [of_decide_eq_true ((allOut_iff _ _).1 h.1.1 o), Cx.toC_conjg]

/-- **The shared lemma** (one induction in run order): on a tree passing `CTree.Ok σlo Λq`
(`‖ℓ̂‖ ≤ Λ L` by `hΛ`) and `CTree.realB`, inputs bounded by `A` with `rangeT i W E T A`, within `d`
of conjugate-symmetric references, and `gBP Λ (2^(i-1)) L d ≤ E`: every leaf centre of the
unbounded run has `|Im| ≤ E` (so `ffsX_devN` applies), and every output is within
`mB (2^(i-1)) L` of the exact FFT of its integers. -/
theorem ffsX_soundN (C : Choices) (hw : C.word = none) {N : ℕ} (htw : twOkN C.x.rc N = true)
    {σlo : ℚ} {Λq : ℕ → ℚ} {Λ : ℕ → ℝ} (hΛ : ∀ L, 0 ≤ Λq L ∧ (Λq L : ℝ) ≤ Λ L) (i W : ℕ)
    (hi : i ≤ 64) (E : ℚ) : ∀ {L : ℕ} (T : CTree 64 L), L ≤ N → T.Ok σlo Λq → T.realB = true →
      ∀ (t0 t1 : Out L → Cx 64) (A : ℚ), (∀ o, ‖(t0 o).toC‖ ≤ A ∧ ‖(t1 o).toC‖ ≤ A) →
      rangeT i W E T A = true → ∀ (r0 r1 : Out L → ℂ), IsReal r0 → IsReal r1 → ∀ d : ℝ,
      (∀ o, ‖(t0 o).toC - r0 o‖ ≤ d ∧ ‖(t1 o).toC - r1 o‖ ≤ d) → gBP Λ (2 ^ (i - 1)) L d ≤ E →
      (∀ x, LeafR C W T t0 t1 x → |x.im.toReal| ≤ E) ∧ ∀ s, ReachX C W T t0 t1 s → ∀ o,
        ‖(s.c0 o).toC - evalAt (fun k => (s.z0 k : ℂ)) (pt L o)‖ ≤ mB (2 ^ (i - 1)) L ∧
          ‖(s.c1 o).toC - evalAt (fun k => (s.z1 k : ℂ)) (pt L o)‖ ≤ mB (2 ^ (i - 1)) L
  | _, .leaf _, _, _, _, t0, t1, _, _, _, r0, r1, h0, h1, d, hd, hG => by
    simp only [gBP] at hG
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
    have hℓ : ∀ o, ‖(ℓ o).toC‖ ≤ Λ L := fun o => Cx.norm_le_of_nsq (hΛ L).1 (hΛ L).2 (hok.1 o)
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
    simp only [gBP] at hG
    set K : ℝ := 2 ^ (i - 1) with hK
    have hK0 : 0 ≤ K := by positivity
    have hmB := mB_nonneg hK0 (L + 1)
    have hlam : 0 ≤ Λ L := (Rat.cast_nonneg.2 (hΛ L).1).trans (hΛ L).2
    have hA0 : (0 : ℝ) ≤ A := (norm_nonneg _).trans (hA (Out.ofIdx _ 0)).1
    have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd (Out.ofIdx _ 0)).1
    set dc := ((1 + Λ L) * d + 4 / 2 ^ 64 + Λ L * mB K (L + 1)) *
      (1 + 4 * (7072 / 10000 / 2 ^ 64)) + 7072 / 10000 / 2 ^ 64 * K + 4 / 2 ^ 64 with hdc
    have hp1 := mul_nonneg hlam hd0
    have hp2 := mul_nonneg hlam hmB
    have b1 := splitW_boundN C hw htw (by omega) t1 (fun x => (hA x).2) (by linarith)
    have e1 : ∀ o, ‖((splitW C L t1).1 o).toC - (splitE r1).1 o‖ ≤ dc ∧
        ‖((splitW C L t1).2 o).toC - (splitE r1).2 o‖ ≤ dc := fun o => by
      obtain ⟨u1, u2⟩ := split_refN C hw htw (by omega) t1 r1 (fun x => (hA x).2)
        (fun x => (hd x).2) o
      constructor <;> linarith [u1, u2, hp1, hp2, g1]
    have i1 := ffsX_soundN C hw htw hΛ i W hi E T1 (by omega) hok.2.2 hre.2 _ _ (A + 1)
      (fun o => by push_cast; exact b1 o) r1' _ _ (isReal_splitE hR1).1 (isReal_splitE hR1).2
      dc e1 hG
    have nodeOut : ∀ s1, ReachX C W T1 (splitW C L t1).1 (splitW C L t1).2 s1 →
        (∀ x, ‖(mergeW C L s1.c0 s1.c1 x).toC - (t1 x).toC‖ ≤ 2 * devT W E T1 + 2) ∧
        ∀ x, ‖(mergeW C L s1.c0 s1.c1 x).toC -
          evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ)) (pt (L + 1) x)‖ ≤ mB K (L + 1) := by
      intro s1 h1
      have dv := ffsX_devN C hw htw i W hi E T1 (by omega) _ _ (A + 1)
        (fun o => by push_cast; exact b1 o) r1' i1.1 s1 h1
      have hD1 : (devT W E T1 : ℝ) < 2 ^ 62 := by linarith
      refine ⟨mergeW_devN C hw htw (by omega) t1 s1.c0 s1.c1 (fun x => (hA x).2) dv
        (by linarith) hD1, fun x => ?_⟩
      have hc : ∀ o, ‖(s1.c1 o).toC‖ ≤ A + 1 + devT W E T1 := fun o => by
        linarith [norm_le_norm_add_norm_sub' (s1.c1 o).toC ((splitW C L t1).2 o).toC, (dv o).2,
          (b1 o).2]
      have := mergeW_refN C hw htw (by omega) s1.c0 s1.c1 s1.z0 s1.z1 (i1.2 s1 h1) hc x
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
            (fun o => (ℓ o).toC) x‖ ≤ d + 4 / 2 ^ 64 + Λ L * (d + mB K (L + 1)) := fun x => by
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
        linarith [(hd x).1, mul_comm (d + mB K (L + 1)) (Λ L)]
      have e0 : ∀ o, ‖((splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).1 o).toC -
            (splitE (upd r0 r1 (fun x => evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ))
              (pt (L + 1) x)) (fun o => (ℓ o).toC))).1 o‖ ≤ dc ∧
          ‖((splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 o).toC -
            (splitE (upd r0 r1 (fun x => evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ))
              (pt (L + 1) x)) (fun o => (ℓ o).toC))).2 o‖ ≤ dc := fun o => by
        obtain ⟨u1, u2⟩ := split_refN C hw htw (by omega) _ _ ha0 he o
        constructor <;> linarith [u1, u2, g5]
      have hR0' := isReal_upd hR0 hR1 (isReal_evalAt (fun k => (ilv s1.z0 s1.z1 k : ℂ))
        fun k => map_intCast (starRingEnd ℂ) _) hrl
      have b0 := splitW_boundN C hw htw (by omega) _ ha0 (by linarith)
      have i0 := ffsX_soundN C hw htw hΛ i W hi E T0 (by omega) hok.2.1 hre.1.2 _ _
        (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1)
        (fun o => by push_cast; exact b0 o) r0' _ _ (isReal_splitE hR0').1 (isReal_splitE hR0').2
        dc e0 hG
      refine ⟨i0.1, fun s0 h0 x => ?_⟩
      have dv := ffsX_devN C hw htw i W hi E T0 (by omega) _ _
        (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1) (fun o => by push_cast; exact b0 o)
        r0' i0.1 s0 h0
      have hc : ∀ o, ‖(s0.c1 o).toC‖ ≤
          A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1 + devT W E T0 := fun o => by
        linarith [norm_le_norm_add_norm_sub' (s0.c1 o).toC
          ((splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 o).toC, (dv o).2, (b0 o).2]
      have := mergeW_refN C hw htw (by omega) s0.c0 s0.c1 s0.z0 s0.z1 (i0.2 s0 h0) hc x
      have hm := mB_nonneg hK0 L
      simp only [mB]
      linarith [this, hm, g6]
    refine ⟨fun x hx => ?_, fun s hs o => ?_⟩
    · rcases hx with hx | ⟨s1, h1, hx⟩
      · exact i1.1 x hx
      · exact (key s1 h1).1 x hx
    · obtain ⟨s1, s0, h1, h0, rfl⟩ := hs
      exact ⟨(key s1 h1).2 s0 h0 o, (nodeOut s1 h1).2 o⟩

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

variable {N : ℕ} (htw : twOkN C.x.rc N = true) {L : ℕ} (hL : L < N)
include htw hL

theorem splitW_wordN (t : Out (L + 1) → Cx 64) {A : ℝ} (ht : ∀ x, ‖(t x).toC‖ ≤ A)
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
    have hm0 := mul_le_mul (norm_tws_leN htw hL o) hd0 (norm_nonneg _) (by positivity)
    have hm : ‖(twsB C.x.rc 64 L o).c.toC‖ * ‖((t (o, false)).sub (t (o, true))).toC‖ +
        2 / 2 ^ 64 < 2 ^ (i - 1) := by linarith
    simp only [splitW, memo_eq, wordFn_none, Cx.wr_id, Cx.mulW_id]
    rw [Cx.wr_some hi hd, Cx.mulW_some hi _ hm]

theorem mergeW_wordN (c0 c1 : Out L → Cx 64) {B : ℝ}
    (hc : ∀ o, ‖(c0 o).toC‖ ≤ B ∧ ‖(c1 o).toC‖ ≤ B) (hB : 2 * B + 1 < 2 ^ (i - 1))
    (hB62 : B < 2 ^ 62) :
    mergeW { C with word := some i } L c0 c1 = mergeW { C with word := none } L c0 c1 := by
  funext x
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hc o).1
  have hpp := mul_le_mul (norm_tw_leN htw hL o) (hc o).2 (norm_nonneg _) (by positivity)
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
theorem ffsX_wordN (C : Choices) {N : ℕ} (htw : twOkN C.x.rc N = true) (i W : ℕ) (hi : 1 ≤ i)
    (hi64 : i ≤ 64) (E : ℚ) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (samp : Fx 64 → Fx 64 → m ℤ) : ∀ {L : ℕ} (T : CTree 64 L), L ≤ N →
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
    have b1 := splitW_boundN { C with word := none } rfl htw (by omega) t1 (fun x => (hA x).2)
      (by linarith)
    have hl1 : ∀ x, LeafR { C with word := none } W T1 (splitW { C with word := none } L t1).1
        (splitW { C with word := none } L t1).2 x → |x.im.toReal| ≤ E := fun x hx =>
      hl x (Or.inl hx)
    simp only [ffsX]
    rw [splitW_wordN C hi htw (by omega) t1 (fun x => (hA x).2) g1,
      ih1 (by omega) _ _ (A + 1) (fun o => by push_cast; exact b1 o) r1 hl1]
    cases chkX C.rchk (L + 1) t1
    · simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [↓reduceIte]
    refine ffsX_bind_congr _ W samp T1 _ _ _ _ (by simp only) fun s1 h1 => ?_
    dsimp only
    have dv1 := ffsX_devN { C with word := none } rfl htw i W hi64 E T1 (by omega) _ _ (A + 1)
      (fun o => by push_cast; exact b1 o) r1 hl1 s1 h1
    have hc1 : ∀ o, ‖(s1.c0 o).toC‖ ≤ A + 1 + devT W E T1 ∧
        ‖(s1.c1 o).toC‖ ≤ A + 1 + devT W E T1 := fun o => ⟨by
      linarith [norm_le_norm_add_norm_sub' (s1.c0 o).toC
        ((splitW { C with word := none } L t1).1 o).toC, (dv1 o).1, (b1 o).1], by
      linarith [norm_le_norm_add_norm_sub' (s1.c1 o).toC
        ((splitW { C with word := none } L t1).2 o).toC, (dv1 o).2, (b1 o).2]⟩
    have z1 := mergeW_devN { C with word := none } rfl htw (by omega) t1 s1.c0 s1.c1
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
    have b0 := splitW_boundN { C with word := none } rfl htw (by omega) _ ha0 (by linarith)
    have hl0 : ∀ x, LeafR { C with word := none } W T0
        (splitW { C with word := none } L (updW { C with word := none } t0 t1
          (mergeW { C with word := none } L s1.c0 s1.c1) ℓ)).1
        (splitW { C with word := none } L (updW { C with word := none } t0 t1
          (mergeW { C with word := none } L s1.c0 s1.c1) ℓ)).2 x → |x.im.toReal| ≤ E :=
      fun x hx => hl x (Or.inr ⟨s1, h1, hx⟩)
    rw [mergeW_wordN C hi htw (by omega) s1.c0 s1.c1 hc1 (by linarith) (by linarith),
      updW_word C hi t0 t1 _ ℓ (fun o => (hA o).1) (fun o => by rw [norm_sub_rev]; exact z1 o)
        (norm_le_nmax ℓ) (by linarith) g4 (by linarith),
      splitW_wordN C hi htw (by omega) _ ha0 (by linarith),
      ih0 (by omega) _ _ (A + (2 * devT W E T1 + 2) * nmax (L + 1) ℓ + 1 + 1)
        (fun o => by push_cast; exact b0 o) r0 hl0]
    cases (chkX C.rchk L s1.c1 && chkX C.rchk (L + 1) (updW { C with word := none } t0 t1
      (mergeW { C with word := none } L s1.c0 s1.c1) ℓ))
    · simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [↓reduceIte]
    refine ffsX_bind_congr _ W samp T0 _ _ _ _ (by simp only) fun s0 h0 => ?_
    dsimp only
    have dv0 := ffsX_devN { C with word := none } rfl htw i W hi64 E T0 (by omega) _ _
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
    rw [mergeW_wordN C hi htw (by omega) s0.c0 s0.c1 hc0 (by linarith) (by linarith)]

/-- **No reduction changes a value of `fftW`** (`N ≤ 10`): with every exact output within `B` and
`2B + 1 < 2^(i−1)`, `fftW` on `(i + 64)`-bit words is the unbounded one. -/
theorem fftW_wordN (C : Choices) {N : ℕ} (hN : N ≤ 10) (htw : twOkN C.x.rc N = true) {i : ℕ}
    (hi : 1 ≤ i) (B : ℝ) (hB : 2 * B + 1 < 2 ^ (i - 1)) : ∀ (L : ℕ), L ≤ N →
      ∀ (a : Fin (2 ^ L) → ℤ),
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
    have ev := fftW_wordN C hN htw hi B hB L (by omega) (evensZ a) fun o => (hsub o).1
    have od := fftW_wordN C hN htw hi B hB L (by omega) (oddsZ a) fun o => (hsub o).2
    have hx : (0 : ℝ) ≤ 7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64 := by positivity
    have Ev := (fftW_errN { C with word := none } rfl htw B L (by omega) (oddsZ a)
      (fun o => (hsub o).2) o).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega : L ≤ 10)) hx)
    have Ex := (fftW_errN { C with word := none } rfl htw B (L + 1) hL a hB' (o, b)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega : L + 1 ≤ 10)) hx)
    have hv : ‖(fftW { C with word := none } L (oddsZ a) o).toC‖ ≤
        B + 4 ^ 10 * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) := by
      linarith [norm_le_norm_add_norm_sub' (fftW { C with word := none } L (oddsZ a) o).toC
        (evalAt (fun j => (oddsZ a j : ℂ)) (pt L o)), (hsub o).2]
    have hm0 := mul_le_mul (norm_tw_leN htw (by omega) o) hv (norm_nonneg _) (by positivity)
    have hm : ‖(twB C.x.rc 64 L o).c.toC‖ *
        ‖(fftW { C with word := none } L (oddsZ a) o).toC‖ + 2 / 2 ^ 64 < 2 ^ (i - 1) := by
      linarith
    have hs : ∀ z : Cx 64, ‖z.toC - evalAt (fun j => (a j : ℂ)) (pt (L + 1) (o, b))‖ ≤
        4 ^ 10 * (7072 / 10000 / 2 ^ 64 * B + 4 / 2 ^ 64) → ‖z.toC‖ < 2 ^ (i - 1) := fun z hz => by
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

end FalconPrecision.Exec
