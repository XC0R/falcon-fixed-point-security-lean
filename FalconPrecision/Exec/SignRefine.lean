/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Sign
public import FalconPrecision.Exec.FixedPointArith64

/-! # The executable signer refines S8's model; 32.64 and 64.64 from a range check

`Adm C` (admissible choices): nearest rounding of every operation (`Arith` needs it,
`RMode.not_isRound_floor`); computed tables within `0.7072·2⁻⁶⁴` (`twOk`, decided); the
scale-first target (the only order S8 models: for multiply-first `sign164G`'s operation sequence
is not met); unbounded words (`word = none`; words enter by `signX_word`, `Exec.SignRange`);
range checks, if any, at `R ≥ 1`. Every other field is free. `AdmN N C`: the same with the tables
decided at levels `< N` (`twOkN`); `Adm C` gives `AdmN 9 C` (`Adm.toN`).

`arithX C h : Arith64 C.qinv.εq` is the executable arithmetic with the executable tables;
`arithXN N C h` the same with the executable tables at levels `< N` and exact ones above
(`twXN`, `twsXN`; `arithX C h = arithXN 9 C h.toN`). `ffsX_toSampN`, `ffsX_refinesN`: the
refinement of `ffsG (arithXN N C h)` by `ffsX` on trees of depth `≤ N` (Falcon-1024, `N = 10`:
`Exec.SignRefine1024`).
`signX_refines`: in every world whose SamplerZ answer depends only on `(σ̄, t̄)` through `samp`,
S8's `sign164G (arithX C h) (chkOf C.rchk)` on the checked key `toKeyB` is `signX` on the stored
tree `storeC` (S8's queries carry the exact centre, which the signer does not compute).
`falcon512_exec_vs_true`: `falcon512_fixed_vs_true_checked` with the fixed-point world replaced by
the executable signer's world (`execImpl`), for admissible choices without range checks
(`C.rchk = none`, the check of `runX`), at `C.qinv = w77`. `OutX`, `LeafX`: outputs and leaf
centres of `ffsX` for sampler answers within `W` of `⌊t̄⌋` (tape `tapeS`); the word theorems
`leafX_im`, `signX_word`, `sign32_eq_sign64` are in `Exec.SignRange`. `pathSum_signLoopX`: a
restart loop of cap `N` (not the table cutoff) makes at most `N` signing queries.

Not proved here: `ffsX_refines` at depth `L ≥ 10` (false: `arithX`'s tables are exact above level
8; it is stated for `L ≤ 9`), nor `ffsX_refinesN` at depth `> N` (stated for depth `≤ N`); hop B
for range checks (`C.rchk = some R`: `runX`, `runX1024` have none); a Lean term `Adm C` or
`AdmN N C` for a concrete `C` (`twOk` and `twOkN rc 10` are true only by `#eval` of `twOkFast`,
`twOkFastN`; `twOkN rc N` for `N > 10` is not evaluated); that the whole signer
`signMsgX` (loop, salt, norm check) is the hop-B experiment (only the attempt `signX` is its
signing oracle, with the query count `pathSum_signLoopX`); that a key passes `check` (not proved
for any key); multiply-first, the split path, half-spectrum storage; the sampler (`hE`, `hM`, `hF`);
32.64 inside hop B without the clamp. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

/-- The error of the stored `1/q`. -/
noncomputable def QInv.εq : QInv → ℝ
  | .w77 => 1 / 2 ^ 78
  | .w64 => 1 / 2 ^ 65

/-- The arithmetic of `r` with `1/q` stored as `qi`. -/
noncomputable def RMode.arith64q (r : RMode) (hr : r ≠ .floor) : (qi : QInv) → Arith64 qi.εq
  | .w77 => r.arith64 hr
  | .w64 => (r.toRnd hr).arith64 (1 / 2 ^ 64) (1 / 2 ^ 65) (by positivity) (by norm_num)

/-- The executable merge table at levels `< N`, `ζ` above. -/
noncomputable def twXN (N : ℕ) (rc : RMode) (L : ℕ) (o : Out L) : ℂ :=
  if L < N then (twB rc 64 L o).c.toC else zeta L o

/-- The executable split table at levels `< N`, `ζ̄/2` above. -/
noncomputable def twsXN (N : ℕ) (rc : RMode) (L : ℕ) (o : Out L) : ℂ :=
  if L < N then (twsB rc 64 L o).c.toC else starRingEnd ℂ (zeta L o) / 2

/-- The executable merge table (levels `≤ 8`), `ζ` above: `twXN 9`. -/
noncomputable def twX (rc : RMode) (L : ℕ) (o : Out L) : ℂ := twXN 9 rc L o

/-- The executable split table (levels `≤ 8`), `ζ̄/2` above: `twsXN 9`. -/
noncomputable def twsX (rc : RMode) (L : ℕ) (o : Out L) : ℂ := twsXN 9 rc L o

theorem twOkN_rad {rc : RMode} {N : ℕ} (h : twOkN rc N = true) {L : ℕ} (hL : L < N)
    (o : Out L) :
    (twB rc 64 L o).radLeB (7072 / 10000 / 2 ^ 64) = true ∧
      (twsB rc 64 L o).radLeB (7072 / 10000 / 2 ^ 64) = true := by
  simp only [twOkN, List.all_eq_true, List.mem_range] at h
  simpa only [Bool.and_eq_true] using (allOut_iff L _).1 (h L hL) o

theorem twOk_rad {rc : RMode} (h : twOk rc = true) {L : ℕ} (hL : L ≤ 8) (o : Out L) :
    (twB rc 64 L o).radLeB (7072 / 10000 / 2 ^ 64) = true ∧
      (twsB rc 64 L o).radLeB (7072 / 10000 / 2 ^ 64) = true :=
  twOkN_rad h (by omega) o

theorem twXN_err64 (N : ℕ) (rc : RMode) (h : twOkN rc N = true) (L : ℕ) (o : Out L) :
    ‖twXN N rc L o - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 64 := by
  unfold twXN
  split_ifs with hL
  · exact (CB.norm_sub_le_of_radLeB (twB_holds rc 64 L o) (twOkN_rad h hL o).1).trans_eq
      (by norm_num)
  · rw [sub_self, norm_zero]; positivity

theorem twsXN_err64 (N : ℕ) (rc : RMode) (h : twOkN rc N = true) (L : ℕ) (o : Out L) :
    ‖twsXN N rc L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 64 := by
  unfold twsXN
  split_ifs with hL
  · exact (CB.norm_sub_le_of_radLeB (twsB_holds rc 64 L o) (twOkN_rad h hL o).2).trans_eq
      (by norm_num)
  · rw [sub_self, norm_zero]; positivity

theorem twX_err64 (rc : RMode) (h : twOk rc = true) (L : ℕ) (o : Out L) :
    ‖twX rc L o - zeta L o‖ ≤ 7072 / 10000 / 2 ^ 64 :=
  twXN_err64 9 rc h L o

theorem twsX_err64 (rc : RMode) (h : twOk rc = true) (L : ℕ) (o : Out L) :
    ‖twsX rc L o - starRingEnd ℂ (zeta L o) / 2‖ ≤ 7072 / 10000 / 2 ^ 64 :=
  twsXN_err64 9 rc h L o

/-- Admissible choices for the refinement to `sign164G`, tables decided at levels `< N`. -/
structure AdmN (N : ℕ) (C : Choices) : Prop where
  near : C.x.rm ≠ .floor
  tw : twOkN C.x.rc N = true
  order : C.target = .scaleFirst
  word : C.word = none
  rchk : ∀ R, C.rchk = some R → 1 ≤ R

/-- Admissible choices for the refinement to `sign164G`. -/
structure Adm (C : Choices) : Prop where
  near : C.x.rm ≠ .floor
  tw : twOk C.x.rc = true
  order : C.target = .scaleFirst
  word : C.word = none
  rchk : ∀ R, C.rchk = some R → 1 ≤ R

/-- `Adm` is `AdmN 9`. -/
theorem Adm.toN {C : Choices} (h : Adm C) : AdmN 9 C := ⟨h.near, h.tw, h.order, h.word, h.rchk⟩

/-- **The executable arithmetic** with the tables cut at `N`: `RMode.arith64q` with the
executable tables at levels `< N` (`twXN`, `twsXN`). -/
noncomputable def arithXN (N : ℕ) (C : Choices) (h : AdmN N C) : Arith64 C.qinv.εq :=
  { RMode.arith64q C.x.rm h.near C.qinv with
    tw := twXN N C.x.rc
    tw_err := fun L o => (twXN_err64 N C.x.rc h.tw L o).trans (by norm_num)
    tws := twsXN N C.x.rc
    tws_err := fun L o => (twsXN_err64 N C.x.rc h.tw L o).trans (by norm_num)
    tw_err64 := twXN_err64 N C.x.rc h.tw
    tws_err64 := twsXN_err64 N C.x.rc h.tw }

/-- **The executable arithmetic**: `RMode.arith64q` with the executable tables (`arithXN 9`). -/
noncomputable def arithX (C : Choices) (h : Adm C) : Arith64 C.qinv.εq := arithXN 9 C h.toN

/-- The check of `sign164G` for `C.rchk`: none, or S8's `‖vh‖ ≤ R - 1`. -/
def chkOf : Option ℚ → (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop
  | none => fun _ _ _ => True
  | some R => fun _ vh _ => InCR (R : ℝ) vh

theorem chkX_iff (R : Option ℚ) (hR : ∀ R', R = some R' → 1 ≤ R') (L : ℕ)
    (vh : Out L → Cx 64) (v : Out L → ℂ) :
    chkX R L vh = true ↔ chkOf R L (fun o => (vh o).toC) v := by
  cases R with
  | none => simp [chkX, chkOf]
  | some R =>
    have h1 : (1 : ℝ) ≤ R := by exact_mod_cast hR R rfl
    simp only [chkX, chkOf, InCR, allOut_iff, decide_eq_true_eq]
    refine forall_congr' fun o => ?_
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero, Cx.norm_sq_eq_nsq]
    norm_cast

namespace Cx

variable {f : ℕ}

theorem wr_id (z : Cx f) : z.wr id = z := rfl

theorem mulW_id (r : RMode) (z u : Cx f) : z.mulW id r u = z.mul r u := rfl

theorem toC_re (z : Cx f) : z.toC.re = z.re.toReal := rfl

end Cx

/-- `1/q` at 64 fraction bits. -/
theorem toReal_qinv64 (r : RMode) : (qinv64 r).toReal = r.rnd (1 / 12289 * 2 ^ 64) / 2 ^ 64 := by
  simp only [Fx.toReal, qinv64]
  rw [r.rdiv_eq_rnd _ _ (by norm_num)]; push_cast; ring_nf

section ArithX

variable (N : ℕ) (C : Choices) (h : AdmN N C)

theorem arithXN_mul (z w : Cx 64) :
    (arithXN N C h).mul (1 / 2 ^ 64) z.toC w.toC = (z.mul C.x.rm w).toC := by
  rw [RMode.mul_toC _ h.near]
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  cases qi <;> rfl

theorem arithXN_halve (z : Cx 64) :
    (arithXN N C h).halve (1 / 2 ^ 64) z.toC = (z.half C.x.rm).toC := by
  rw [RMode.half_toC _ h.near]
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  cases qi <;> rfl

theorem arithXN_divq (z : Cx 64) :
    (arithXN N C h).divq z.toC = (divqX C.x.rm C.qinv z).toC := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  cases qi
  · exact RMode.arith64_divq _ h.near z
  · change (x.rm.toRnd h.near).divq (1 / 2 ^ 64) z.toC = _
    apply Complex.ext <;>
      simp only [divqX, Cx.toC, Rnd.divq, Rnd.cq, Fx.toReal_mul, toReal_qinv64, RMode.toRnd_q,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        zero_add]

theorem arithXN_tw {L : ℕ} (hL : L < N) (o : Out L) :
    (arithXN N C h).tw L o = (twB C.x.rc 64 L o).c.toC :=
  ite_eq_left_of_eq_true _ _ (eq_true hL)

theorem arithXN_tws {L : ℕ} (hL : L < N) (o : Out L) :
    (arithXN N C h).tws L o = (twsB C.x.rc 64 L o).c.toC :=
  ite_eq_left_of_eq_true _ _ (eq_true hL)

end ArithX

section ArithX

variable (C : Choices) (h : Adm C)

theorem arithX_mul (z w : Cx 64) :
    (arithX C h).mul (1 / 2 ^ 64) z.toC w.toC = (z.mul C.x.rm w).toC :=
  arithXN_mul 9 C h.toN z w

theorem arithX_halve (z : Cx 64) :
    (arithX C h).halve (1 / 2 ^ 64) z.toC = (z.half C.x.rm).toC :=
  arithXN_halve 9 C h.toN z

theorem arithX_divq (z : Cx 64) : (arithX C h).divq z.toC = (divqX C.x.rm C.qinv z).toC :=
  arithXN_divq 9 C h.toN z

theorem arithX_tw {L : ℕ} (hL : L ≤ 8) (o : Out L) :
    (arithX C h).tw L o = (twB C.x.rc 64 L o).c.toC :=
  arithXN_tw 9 C h.toN (by omega) o

theorem arithX_tws {L : ℕ} (hL : L ≤ 8) (o : Out L) :
    (arithX C h).tws L o = (twsB C.x.rc 64 L o).c.toC :=
  arithXN_tws 9 C h.toN (by omega) o

end ArithX

theorem fftW_toCN (N : ℕ) (C : Choices) (h : AdmN N C) (L : ℕ) (hL : L ≤ N)
    (a : Fin (2 ^ L) → ℤ) (o : Out L) :
    (fftW C L a o).toC = (arithXN N C h).fft (1 / 2 ^ 64) L (fun i => (a i : ℂ)) o := by
  induction L with
  | zero => simp only [fftW, h.word, wordFn, Cx.wr_id, Cx.toC_ofInt, Arith.fft]
  | succ L ih =>
    obtain ⟨o, b⟩ := (o : Out L × Bool)
    have e0 := ih (by omega) (evensZ a) o
    have e1 := ih (by omega) (oddsZ a) o
    simp only [fftW]
    erw [memo_eq]
    cases b <;>
      simp only [h.word, wordFn, Cx.wr_id, Cx.mulW_id, Arith.fft, Cx.toC_add, Cx.toC_sub,
        ← arithXN_mul N C h, arithXN_tw N C h (by omega : L < N), e0, e1, Bool.false_eq_true,
        ↓reduceIte] <;> rfl

theorem fftW_toC (C : Choices) (h : Adm C) (L : ℕ) (hL : L ≤ 9) (a : Fin (2 ^ L) → ℤ)
    (o : Out L) :
    (fftW C L a o).toC = (arithX C h).fft (1 / 2 ^ 64) L (fun i => (a i : ℂ)) o :=
  fftW_toCN 9 C h.toN L hL a o

theorem targetX_toCN (N : ℕ) (C : Choices) (h : AdmN N C) {logn : ℕ} (hN : logn ≤ N)
    {γf γF σlo : ℝ} {hlo : 12778 / 10000 ≤ σlo} {Λ : ℕ → ℝ} (K : KeyP logn γf γF σlo hlo Λ)
    (c : ZPoly logn) :
    t0C64 (arithXN N C h) K c = (fun o => ((targetX C K.f K.F c).1 o).toC) ∧
      t1C64 (arithXN N C h) K c = fun o => ((targetX C K.f K.F c).2 o).toC := by
  simp only [targetX, h.order, h.word, wordFn, memo_eq, Cx.wr_id, Cx.mulW_id]
  refine ⟨funext fun o => ?_, funext fun o => ?_⟩ <;>
    simp only [t0C64, t1C64, cqC64, chC64, ← arithXN_mul N C h, Cx.toC_neg,
      ← arithXN_divq N C h, fftW_toCN N C h logn hN]

theorem targetX_toC (C : Choices) (h : Adm C) (K : Key) (c : ZPoly) :
    t0C64 (arithX C h) K c = (fun o => ((targetX C K.f K.F c).1 o).toC) ∧
      t1C64 (arithX C h) K c = fun o => ((targetX C K.f K.F c).2 o).toC :=
  targetX_toCN 9 C h.toN le_rfl K c

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- A computed output as an output of `ffsG`: the exact values are the FFTs of `z0`, `z1`. -/
noncomputable def SampX.toSamp {L : ℕ} (s : SampX L) : Samp L :=
  ⟨s.z0, s.z1, fun o => evalAt (fun i => (s.z0 i : ℂ)) (pt L o),
    fun o => evalAt (fun i => (s.z1 i : ℂ)) (pt L o), fun o => (s.c0 o).toC, fun o => (s.c1 o).toC⟩

theorem leaf_toSamp (z0 z1 : ℤ) :
    Samp.leaf z0 z1 =
      SampX.toSamp ⟨fun _ => z0, fun _ => z1, fun _ => Cx.ofInt z0, fun _ => Cx.ofInt z1⟩ := by
  simp [Samp.leaf, SampX.toSamp, evalAt, Cx.toC_ofInt]

section ToC

variable (N : ℕ) (C : Choices) (h : AdmN N C)

theorem splitW_toCN {L : ℕ} (hL : L < N) (t : Out (L + 1) → Cx 64) :
    splitCU (arithXN N C h).toArith (1 / 2 ^ 64) (fun o => (t o).toC) =
      (fun o => ((splitW C L t).1 o).toC, fun o => ((splitW C L t).2 o).toC) := by
  simp only [splitCU, splitW, memo_eq, h.word, wordFn, Cx.wr_id, Cx.mulW_id, Cx.toC_add,
    Cx.toC_sub, ← arithXN_mul N C h, ← arithXN_halve N C h, arithXN_tws N C h hL]

theorem mergeW_toCN {L : ℕ} (hL : L < N) (s : SampX L) :
    mergeCU (arithXN N C h).toArith (1 / 2 ^ 64) s.toSamp =
      fun x => (mergeW C L s.c0 s.c1 x).toC := by
  funext x
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  simp only [mergeW]
  erw [memo_eq]
  cases b <;>
    simp only [mergeCU, mergeL, SampX.toSamp, h.word, wordFn, Cx.wr_id, Cx.mulW_id, Cx.toC_add,
      Cx.toC_sub, ← arithXN_mul N C h, arithXN_tw N C h hL, Bool.false_eq_true, ↓reduceIte]

theorem updW_toCN {L : ℕ} (t0 t1 z ℓ : Out L → Cx 64) :
    updCU (arithXN N C h).toArith (1 / 2 ^ 64) (fun o => (t0 o).toC) (fun o => (t1 o).toC)
        (fun o => (z o).toC) (fun o => (ℓ o).toC) = fun o => (updW C t0 t1 z ℓ o).toC := by
  funext o
  simp only [updW]
  erw [memo_eq]
  simp only [updCU, h.word, wordFn, Cx.wr_id, Cx.mulW_id, Cx.toC_add, Cx.toC_sub,
    ← arithXN_mul N C h]

theorem joinU_toSampN {L : ℕ} (hL : L < N) (s0 s1 : SampX L) :
    joinU (arithXN N C h).toArith (1 / 2 ^ 64) s0.toSamp s1.toSamp =
      SampX.toSamp ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1, mergeW C L s0.c0 s0.c1,
        mergeW C L s1.c0 s1.c1⟩ := by
  have e : ∀ s : SampX L, mergeE s.toSamp =
      fun x => evalAt (fun i => (ilv s.z0 s.z1 i : ℂ)) (pt (L + 1) x) :=
    fun s => mergeL_ilv s.z0 s.z1
  rw [joinU, e, e, mergeW_toCN N C h hL, mergeW_toCN N C h hL]
  rfl

end ToC

section ToC

variable (C : Choices) (h : Adm C)

theorem splitW_toC {L : ℕ} (hL : L ≤ 8) (t : Out (L + 1) → Cx 64) :
    splitCU (arithX C h).toArith (1 / 2 ^ 64) (fun o => (t o).toC) =
      (fun o => ((splitW C L t).1 o).toC, fun o => ((splitW C L t).2 o).toC) :=
  splitW_toCN 9 C h.toN (by omega) t

theorem mergeW_toC {L : ℕ} (hL : L ≤ 8) (s : SampX L) :
    mergeCU (arithX C h).toArith (1 / 2 ^ 64) s.toSamp = fun x => (mergeW C L s.c0 s.c1 x).toC :=
  mergeW_toCN 9 C h.toN (by omega) s

theorem updW_toC {L : ℕ} (t0 t1 z ℓ : Out L → Cx 64) :
    updCU (arithX C h).toArith (1 / 2 ^ 64) (fun o => (t0 o).toC) (fun o => (t1 o).toC)
        (fun o => (z o).toC) (fun o => (ℓ o).toC) = fun o => (updW C t0 t1 z ℓ o).toC :=
  updW_toCN 9 C h.toN t0 t1 z ℓ

theorem joinU_toSamp {L : ℕ} (hL : L ≤ 8) (s0 s1 : SampX L) :
    joinU (arithX C h).toArith (1 / 2 ^ 64) s0.toSamp s1.toSamp =
      SampX.toSamp ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1, mergeW C L s0.c0 s0.c1,
        mergeW C L s1.c0 s1.c1⟩ :=
  joinU_toSampN 9 C h.toN (by omega) s0 s1

end ToC

theorem simulateQ_query_inr {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (q : Falcon.CallP) :
    simulateQ impl (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inr q)) :
      OracleComp _ ℤ) = impl (.inr q) :=
  simulateQ_spec_query (impl := impl) (Sum.inr q)

open Classical in
/-- **`ffsX` is `ffsG`** with the tables cut at `N`, on trees of depth `≤ N` whose stored values
pass `CTree.Ok σlo Λq` (as `FTreeP σl hlo Λ` by `toFTreeP`), every output mapped by
`SampX.toSamp`. -/
theorem ffsX_toSampN (N : ℕ) (C : Choices) (h : AdmN N C) {m : Type → Type*} [Monad m]
    [LawfulMonad m] (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t)
    {σlo : ℚ} {Λq : ℕ → ℚ} {σl : ℝ} {hlo : 12778 / 10000 ≤ σl} {Λ : ℕ → ℝ} (hσ : σl ≤ σlo)
    (hΛ : ∀ L, 0 ≤ Λq L ∧ (Λq L : ℝ) ≤ Λ L) :
    ∀ {L : ℕ} (T : CTree 64 L) (hT : T.Ok σlo Λq) (_ : L ≤ N) (t0 t1 : Out L → ℂ)
      (t0h t1h : Out L → Cx 64),
      simulateQ impl (ffsG (aux := aux) (arithXN N C h).toArith (1 / 2 ^ 64) (chkOf C.rchk)
          (T.toFTreeP (hlo := hlo) hσ hΛ hT) t0 t1 (fun o => (t0h o).toC)
          (fun o => (t1h o).toC)) =
        (fun r => r.map SampX.toSamp) <$> ffsX C samp T t0h t1h
  | _, .leaf σ, _, _, t0, t1, t0h, t1h => by
    have hq : ∀ (t : Fx 64) (x : ℝ) hσ,
        (impl (.inr (Falcon.CallP.stored σ.toReal x t.toReal hσ)) : m ℤ) = samp σ t :=
      fun t _ _ => himpl σ t _ rfl rfl
    simp only [CTree.toFTreeP, ffsG, ffsX, simulateQ_bind, simulateQ_pure, Cx.toC_re, map_bind,
      map_pure, Option.map_some, leaf_toSamp]
    rw [simulateQ_query_inr, simulateQ_query_inr, hq, hq]
  | _, @CTree.node _ L ℓ T0 T1, hT, hL, t0, t1, t0h, t1h => by
    have hLN : L < N := by omega
    simp only [CTree.toFTreeP, ffsG, ffsX]
    by_cases c1 : chkX C.rchk (L + 1) t1h = true
    swap
    · have c1' := mt (chkX_iff C.rchk h.rchk (L + 1) t1h t1).2 c1
      simp only [c1, c1', Bool.false_eq_true, ↓reduceIte, simulateQ_pure, map_pure,
        Option.map_none]
    have c1' := (chkX_iff C.rchk h.rchk (L + 1) t1h t1).1 c1
    simp only [c1, c1', ↓reduceIte, splitW_toCN N C h hLN]
    rw [simulateQ_bind, ffsX_toSampN N C h impl samp himpl hσ hΛ T1 hT.2.2 (by omega), map_bind,
      bind_map_left]
    refine bind_congr fun r1 => ?_
    rcases r1 with _ | x1
    · simp only [Option.map_none, Option.elim, simulateQ_pure, map_pure]
    simp only [Option.map_some, Option.elim, mergeW_toCN N C h hLN, updW_toCN N C h]
    have e1 := chkX_iff C.rchk h.rchk L x1.c1 x1.toSamp.e1
    have e2 := chkX_iff C.rchk h.rchk (L + 1) (updW C t0h t1h (mergeW C L x1.c0 x1.c1) ℓ)
      (upd t0 t1 (mergeE x1.toSamp) fun o => (ℓ o).toC)
    by_cases c2 : chkX C.rchk L x1.c1 = true ∧
      chkX C.rchk (L + 1) (updW C t0h t1h (mergeW C L x1.c0 x1.c1) ℓ) = true
    swap
    · have c2' : ¬(chkOf C.rchk L x1.toSamp.c1 x1.toSamp.e1 ∧
          chkOf C.rchk (L + 1) (fun o => (updW C t0h t1h (mergeW C L x1.c0 x1.c1) ℓ o).toC)
            (upd t0 t1 (mergeE x1.toSamp) fun o => (ℓ o).toC)) :=
        fun hc => c2 ⟨e1.2 hc.1, e2.2 hc.2⟩
      simp only [Bool.and_eq_true, c2, c2', ↓reduceIte, simulateQ_pure, map_pure,
        Option.map_none]
    have c2' : chkOf C.rchk L x1.toSamp.c1 x1.toSamp.e1 ∧
        chkOf C.rchk (L + 1) (fun o => (updW C t0h t1h (mergeW C L x1.c0 x1.c1) ℓ o).toC)
          (upd t0 t1 (mergeE x1.toSamp) fun o => (ℓ o).toC) := ⟨e1.1 c2.1, e2.1 c2.2⟩
    simp only [Bool.and_eq_true, c2, c2', and_self, ↓reduceIte, splitW_toCN N C h hLN]
    rw [simulateQ_bind, ffsX_toSampN N C h impl samp himpl hσ hΛ T0 hT.2.1 (by omega), map_bind,
      bind_map_left]
    refine bind_congr fun r0 => ?_
    rcases r0 with _ | x0
    · simp only [Option.map_none, simulateQ_pure, map_pure]
    simp only [Option.map_some]
    have e0 := chkX_iff C.rchk h.rchk L x0.c1 x0.toSamp.e1
    by_cases c3 : chkX C.rchk L x0.c1 = true
    swap
    · have c3' : ¬chkOf C.rchk L x0.toSamp.c1 x0.toSamp.e1 := mt e0.2 c3
      simp only [c3, c3', Bool.false_eq_true, ↓reduceIte, simulateQ_pure, map_pure,
        Option.map_none]
    have c3' : chkOf C.rchk L x0.toSamp.c1 x0.toSamp.e1 := e0.1 c3
    simp only [c3, c3', ↓reduceIte, simulateQ_pure, map_pure, Option.map_some,
      joinU_toSampN N C h hLN]

open Classical in
/-- **`ffsX` is `ffsG`** on trees of depth `≤ 9` (the executable tables), every output mapped by
`SampX.toSamp`. -/
theorem ffsX_toSamp (C : Choices) (h : Adm C) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t) :
    ∀ {L : ℕ} (T : CTree 64 L) (hT : T.Ok) (_ : L ≤ 9) (t0 t1 : Out L → ℂ)
      (t0h t1h : Out L → Cx 64),
      simulateQ impl (ffsG (aux := aux) (arithX C h).toArith (1 / 2 ^ 64) (chkOf C.rchk)
          (T.toFTree hT) t0 t1 (fun o => (t0h o).toC) (fun o => (t1h o).toC)) =
        (fun r => r.map SampX.toSamp) <$> ffsX C samp T t0h t1h := by
  intro L T hT hL t0 t1 t0h t1h
  rw [CTree.toFTree_eq_toFTreeP (by norm_num) lam512q_bounds]
  exact ffsX_toSampN 9 C h.toN impl samp himpl _ _ T hT hL t0 t1 t0h t1h

/-- **`ffsX` refines `ffsG`** with the tables cut at `N`, on trees of depth `≤ N` (as
`FTreeP σl hlo Λ` by `toFTreeP`). -/
theorem ffsX_refinesN (N : ℕ) (C : Choices) (h : AdmN N C) {m : Type → Type*} [Monad m]
    [LawfulMonad m] (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t)
    {σlo : ℚ} {Λq : ℕ → ℚ} {σl : ℝ} {hlo : 12778 / 10000 ≤ σl} {Λ : ℕ → ℝ} (hσ : σl ≤ σlo)
    (hΛ : ∀ L, 0 ≤ Λq L ∧ (Λq L : ℝ) ≤ Λ L)
    {L : ℕ} (hL : L ≤ N) (T : CTree 64 L) (hT : T.Ok σlo Λq) (t0 t1 : Out L → ℂ)
    (t0h t1h : Out L → Cx 64) :
    (fun r => r.map fun s => (s.z0, s.z1)) <$> simulateQ impl
        (ffsG (aux := aux) (arithXN N C h).toArith (1 / 2 ^ 64) (chkOf C.rchk)
          (T.toFTreeP (hlo := hlo) hσ hΛ hT) t0 t1 (fun o => (t0h o).toC)
          (fun o => (t1h o).toC)) =
      (fun r => r.map fun s => (s.z0, s.z1)) <$> ffsX C samp T t0h t1h := by
  rw [ffsX_toSampN N C h impl samp himpl hσ hΛ T hT hL, Functor.map_map]
  congr 1
  funext r
  cases r <;> rfl

/-- **`ffsX` refines `ffsG`** on trees of depth `≤ 9` (not stated for `L ≥ 10`: `arithX`'s tables
are exact above level 8, `splitW`, `mergeW` use the rounded ones at every level; at depth `≤ N`
with `arithXN N`: `ffsX_refinesN`). -/
theorem ffsX_refines (C : Choices) (h : Adm C) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t)
    {L : ℕ} (hL : L ≤ 9) (T : CTree 64 L) (hT : T.Ok) (t0 t1 : Out L → ℂ)
    (t0h t1h : Out L → Cx 64) :
    (fun r => r.map fun s => (s.z0, s.z1)) <$> simulateQ impl
        (ffsG (aux := aux) (arithX C h).toArith (1 / 2 ^ 64) (chkOf C.rchk) (T.toFTree hT) t0 t1
          (fun o => (t0h o).toC) (fun o => (t1h o).toC)) =
      (fun r => r.map fun s => (s.z0, s.z1)) <$> ffsX C samp T t0h t1h := by
  rw [ffsX_toSamp C h impl samp himpl T hT hL, Functor.map_map]
  congr 1
  funext r
  cases r <;> rfl

/-- **Refinement**: in every world `impl` whose SamplerZ answer on `(σ̄, t̄)` is `samp σ̄ t̄`, S8's
`sign164G` with `arithX C h` and the checks `chkOf C.rchk`, on the key of a raw key passing
`check`, is the executable attempt `signX` on the stored tree `storeC`. -/
theorem signX_refines (C : Choices) (h : Adm C) (δq : ℕ → ℚ) (k : RawKey)
    (hk : check C.x C.xn δq k = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t) (c : ZPoly) :
    simulateQ impl (sign164G (aux := aux) (arithX C h) (chkOf C.rchk)
        (toKeyB C.x C.xn δq k hk).toKey c) = signX C samp (storeC C.x C.xn k) k c := by
  have hT : (storeC C.x C.xn k).Ok :=
    storeB_centre C.x C.xn k ▸ CTree.ok_of_okB _ (check_ok C.x C.xn hk).ok
  unfold sign164G signX
  by_cases hc : ∀ i, |c i| < 12289
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc),
      simulateQ_map, (targetX_toC C h _ c).1, (targetX_toC C h _ c).2]
    exact ffsX_refines C h impl samp himpl le_rfl (storeC C.x C.xn k) hT _ _ _ _
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc),
      simulateQ_pure]

/-- The executable signer's world: auxiliary queries by `implA`, a signing query `(k, c)` by
`signX` on `storeC k`. -/
def execImpl (C : Choices) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m] (implA : QueryImpl aux m)
    (samp : Fx 64 → Fx 64 → m ℤ) : QueryImpl (specK C.x C.xn aux δq) m
  | .inl x => implA x
  | .inr kc => signX C samp (storeC C.x C.xn kc.1.1) kc.1.1 kc.2

theorem world_eq (C : Choices) (h : Adm C) (δq : ℕ → ℚ) {m : Type → Type*} [Monad m]
    [LawfulMonad m] (hR : C.rchk = none) (implA : QueryImpl aux m)
    (implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (hAF : ∀ x, implF (.inl x) = implA x)
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} (oe : OracleComp (specK C.x C.xn aux δq) α) :
    simulateQ implF (runX (arithX C h) (embed C.x C.xn δq oe)) =
      simulateQ (execImpl C δq implA samp) oe := by
  unfold runX embed
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe,
    QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) oe]
  refine congrArg (fun impl => simulateQ impl oe) (funext fun t => ?_)
  rcases t with x | kc
  · exact ((congrArg (simulateQ implF) (simulateQ_spec_query (impl := signImpl
      (δ := fun j => (δq j : ℝ)) fun k c => sign164G (arithX C h) (fun _ _ _ => True) k.1.toKey c)
      (Sum.inl x))).trans (simulateQ_spec_query (impl := implF) (Sum.inl x))).trans (hAF x)
  · refine (congrArg (simulateQ implF) (simulateQ_spec_query (impl := signImpl
      (δ := fun j => (δq j : ℝ)) fun k c => sign164G (arithX C h) (fun _ _ _ => True) k.1.toKey c)
      (Sum.inr (kc.1.toGood, kc.2)))).trans ?_
    have e := signX_refines C h δq kc.1.1 kc.1.2 implF samp hsamp kc.2
    rw [show chkOf C.rchk = fun _ _ _ => True by rw [hR]; rfl] at e
    exact e

section HopB

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- **The executable signer against exact Falcon on checked keys**: for admissible choices without
range checks (`C.rchk = none`, the check of `runX`) with `1/q` at 77 bits, every experiment `oe`
on raw keys passing `check` with at most `K ≤ 2³⁹` signing queries along every execution, a
sampler `samp` that is `D_{σ̄,t̄}` (`hF` on a world `implF` agreeing with it on grid values):
success `> T·2⁻¹²⁶ + 2⁻¹⁴⁰` with the executable signer (`execImpl`) gives success
`> T·2⁻¹³¹ - 2⁻¹⁴¹` with exact signing on the true tree. Hypotheses and what is not proved
otherwise: those of `falcon512_fixed_vs_true_checked`. -/
theorem falcon512_exec_vs_true [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : Adm C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9)
    (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK C.x C.xn aux δq) α) (hq : PathSum (wKC C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ (execImpl C δq implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed C.x C.xn δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  obtain rfl : qi = QInv.w77 := hq77
  refine falcon512_fixed_vs_true_checked x xn δq (arithX _ hC) K hK hδ T hT implA implE implM
    implF hAE hAM hAF hE hM hF oe hq hs ?_
  have e : simulateQ implF (runX (εq := 1 / 2 ^ 78) (arithX _ hC) (embed x xn δq oe)) =
      simulateQ (execImpl _ δq implA samp) oe :=
    world_eq _ hC δq hR implA implF hAF samp hsamp oe
  rw [e]
  exact hwin

end HopB

/-! ## 32.64 and 64.64 -/

/-- The sampler answering query `j` by `g j` (a tape). -/
def tapeS (g : ℕ → ℤ) (_ _ : Fx 64) : StateM ℕ ℤ := modifyGet fun j => (g j, j + 1)

/-- `s` is an output of `ffsX` on `T` from `(t0, t1)` for some sampler answers within `W` of
`⌊t̄⌋`: a tape `g` read from position `j`. -/
def OutX (C : Choices) (W : ℕ) {L : ℕ} (T : CTree 64 L) (t0 t1 : Out L → Cx 64) (s : SampX L) :
    Prop :=
  ∃ (g : ℕ → ℤ) (j : ℕ), ((ffsX C (clampS W (tapeS g)) T t0 t1).run' j).run = some s

/-- `x` is a leaf centre of `ffsX` on `T` from `(t0, t1)` for some sampler answers within `W` of
`⌊t̄⌋` (the checks at the nodes on the path ignored; `OutX` keeps them). -/
def LeafX (C : Choices) (W : ℕ) : {L : ℕ} → CTree 64 L → (t0 t1 : Out L → Cx 64) → Cx 64 → Prop
  | _, .leaf _, t0, t1, x => x = t0 () ∨ x = t1 ()
  | _, @CTree.node _ L ℓ T0 T1, t0, t1, x =>
    LeafX C W T1 (splitW C L t1).1 (splitW C L t1).2 x ∨
      ∃ s1, OutX C W T1 (splitW C L t1).1 (splitW C L t1).2 s1 ∧
        LeafX C W T0 (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).1
          (splitW C L (updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ)).2 x

/-! ## The restart cap -/

theorem pathSum_map {ι : Type} {spec : OracleSpec.{0, 0} ι} {w : ι → ℝ} {α γ : Type}
    (f : α → γ) {oa : OracleComp spec α} {S : ℝ} (h : PathSum w oa S) : PathSum w (f <$> oa) S := by
  rw [map_eq_bind_pure_comp]
  exact (PathSum.bind h (T := 0) fun _ => .pure _ le_rfl).weaken (le_of_eq (add_zero _))

theorem pathSum_loopR {ι : Type} {spec : OracleSpec.{0, 0} ι} {w : ι → ℝ} {γ β : Type}
    {att : OracleComp spec γ} (acc : γ → Option β) (h : PathSum w att 1) :
    ∀ N : ℕ, PathSum w (loopR att acc N) N
  | 0 => .pure _ (Nat.cast_nonneg 0)
  | N + 1 => by
    rw [loopR]
    refine (PathSum.bind h (T := N) fun y => ?_).weaken (by push_cast; linarith)
    split
    · exact .pure _ (Nat.cast_nonneg N)
    · exact pathSum_loopR acc h N

theorem pathSum_signLoopX (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) (kc : CheckedKey P n δq)
    {S M β : Type} (mode : SaltMode) (salt : OracleComp (specK P n aux δq) S)
    (hash : S → M → OracleComp (specK P n aux δq) ZPoly)
    (hs : PathSum (wKC P n δq) salt 0) (hh : ∀ s x, PathSum (wKC P n δq) (hash s x) 0)
    (acc : ZPoly → Option (ZPoly × ZPoly) → Option β) (msg : M) (N : ℕ) :
    PathSum (wKC P n δq) (signLoopX mode salt hash
      (fun c => (liftM (OracleSpec.query (spec := specK P n aux δq) (.inr (kc, c))) :
        OracleComp (specK P n aux δq) (Option (ZPoly × ZPoly)))) acc msg N) N := by
  have hq : ∀ c, PathSum (wKC P n δq)
      (liftM (OracleSpec.query (spec := specK P n aux δq) (.inr (kc, c))) :
        OracleComp (specK P n aux δq) (Option (ZPoly × ZPoly))) 1 := fun c => by
    have := PathSum.query_bind (w := wKC P n δq) (S := 1) (Sum.inr (kc, c))
      (pure : _ → OracleComp (specK P n aux δq) _) fun _ => .pure _ (by simp [wKC])
    rwa [bind_pure] at this
  cases mode with
  | reused =>
    exact (hs.bind (T := N) fun s => ((hh s msg).bind (T := N) fun c =>
      pathSum_map _ (pathSum_loopR _ (hq c) N)).weaken (by simp)).weaken (by simp)
  | perAttempt =>
    exact pathSum_loopR _ ((hs.bind (T := 1) fun s => ((hh s msg).bind (T := 1) fun c =>
      pathSum_map _ (hq c)).weaken (by simp)).weaken (by simp)) N

end FalconPrecision.Exec
