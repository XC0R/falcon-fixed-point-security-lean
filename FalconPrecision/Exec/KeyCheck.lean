/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.KeyExpand
public import FalconPrecision.Errors.HopB

/-! # A per-key check of fixed-point key expansion, proved sound

`check P n δq k` is computable. It runs key expansion in balls at `64 + n` fraction bits on a raw
key `k`, rounds every stored ball once to 64 fraction bits (`storeB`), and decides: the FFTs of `f`
and `F` within `255` and `3500` (`Key.hf`, `Key.hF`); every stored leaf `σ̄` in
`[1.277833697, 1.8205]` and every stored factor `‖ℓ̂‖ ≤ lam512 L` (`FTree`); every stored `ℓ̂`
conjugate-symmetric, exactly (`FTree.Real`); every rounded factor ball of radius `≤ δq L` (`Close`,
nodes); every rounded leaf ball inside `[1.2778, 1.825]` with relative radius `≤ 2⁻⁴²` (`Close`,
leaves); and `fG - gF = q` in `ℤ[x]/(x⁵¹² + 1)` (`ntruB`), in every root mode.

`check_sound`: `check P n δq k = true` gives `KeyB.Good δ` for the key `toKeyB` built from `k`,
with `δ j = δq j`, stored tree `storeC` (the values at 64 fraction bits a signer stores) and true
tree `KeyB.trueTree` (exact ffLDL⋆ of `B·B⋆`). It is proved with no other hypothesis, from the
ball lemmas (`Ball`, `Twiddle`), `fftB_holds`, `ntru_det`, `ntru_root` and `expandB_centre`.

`falcon512_fixed_vs_true_checked`: `HopB.falcon512_fixed_vs_true` for experiments whose signing
queries carry raw keys passing `check` (`specK`), embedded into `specS` by `CheckedKey.toGood`.
Not proved here: that any Falcon key passes `check` (not proved for any key: `#eval` runs of
`checkFast` on round-3 KAT keys are not kernel proofs), at a given `δq` and `n` (`n = 0`: an
expansion at 64 fraction bits); the word size: key expansion runs in unbounded `Int`,
`InRange` of the stored values is not checked; and what `falcon512_fixed_vs_true` does not prove
apart from `KeyB.Good δ` (`FTree.Real`, `Close δ`, the true leaf range), the tie of the stored tree
to `f, F` (`storeC`) and `fG - gF = q` (given by `check`). -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

/-! ## Decisions on one ball -/

namespace CB

variable {f : ℕ}

/-- Every value of the ball has norm `≤ R`: radius known, `r ≤ R` and `‖c‖² ≤ (R - r)²`. -/
def normLeB (b : CB f) (R : ℚ) : Bool :=
  match b.r with
  | some r => decide (r ≤ R) && decide (b.c.nsq ≤ (R - r) ^ 2)
  | none => false

/-- The radius is known and `≤ d`. -/
def radLeB (b : CB f) (d : ℚ) : Bool :=
  match b.r with
  | some r => decide (r ≤ d)
  | none => false

/-- A leaf ball of centre `s` (real part) and radius `r`: `[s - r, s + r] ⊆ [1.2778, 1.825]` and
`2⁴²·r ≤ s - r`. -/
def leafOkB (b : CB f) : Bool :=
  match b.r with
  | some r =>
    decide (12778 / 10000 ≤ b.c.re.toRat - r) && decide (b.c.re.toRat + r ≤ 1825 / 1000) &&
      decide (r * 2 ^ 42 ≤ b.c.re.toRat - r)
  | none => false

theorem norm_le_of_normLeB {b : CB f} {z : ℂ} {R : ℚ} (h : b.Holds z)
    (hb : b.normLeB R = true) : ‖z‖ ≤ R := by
  cases hr : b.r with
  | none => simp [normLeB, hr] at hb
  | some r =>
    simp only [normLeB, hr, Bool.and_eq_true, decide_eq_true_eq] at hb
    have h1 : (r : ℝ) ≤ R := by exact_mod_cast hb.1
    have h2 : (b.c.nsq : ℝ) ≤ ((R : ℝ) - r) ^ 2 := by exact_mod_cast hb.2
    have hc : ‖b.c.toC‖ ≤ (R : ℝ) - r :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1
        (by rw [Cx.norm_sq_eq_nsq]; exact h2)
    have hz := h r hr
    have := norm_sub_norm_le z b.c.toC
    linarith

theorem norm_sub_le_of_radLeB {b : CB f} {z : ℂ} {d : ℚ} (h : b.Holds z)
    (hb : b.radLeB d = true) : ‖b.c.toC - z‖ ≤ d := by
  cases hr : b.r with
  | none => simp [radLeB, hr] at hb
  | some r =>
    simp only [radLeB, hr, decide_eq_true_eq] at hb
    rw [norm_sub_rev]
    exact (h r hr).trans (by exact_mod_cast hb)

theorem close_leaf {b : CB f} {σ : ℝ} (h : b.Holds (σ : ℂ)) (hb : b.leafOkB = true) :
    (12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000) ∧ |b.c.re.toReal / σ - 1| ≤ 1 / 2 ^ 42 := by
  cases hr : b.r with
  | none => simp [leafOkB, hr] at hb
  | some r =>
    simp only [leafOkB, hr, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hd : |σ - b.c.re.toReal| ≤ r := by
      have hre : ((σ : ℂ) - b.c.toC).re = σ - b.c.re.toReal := by simp [Cx.toC]
      rw [← hre]
      exact (Complex.abs_re_le_norm _).trans (h r hr)
    rw [Fx.toReal_eq_toRat] at hd ⊢
    have h1' := Rat.cast_le (K := ℝ) |>.2 h1
    have h2' := Rat.cast_le (K := ℝ) |>.2 h2
    have h3' := Rat.cast_le (K := ℝ) |>.2 h3
    push_cast at h1' h2' h3'
    obtain ⟨hl, hu⟩ := abs_le.1 hd
    have hσ : 0 < σ := by linarith
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have key : (r : ℝ) ≤ σ / 2 ^ 42 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    rw [div_sub_one hσ.ne', abs_div, abs_of_pos hσ, div_le_iff₀ hσ, abs_sub_comm]
    calc |σ - (b.c.re.toRat : ℝ)| ≤ r := hd
      _ ≤ σ / 2 ^ 42 := key
      _ = 1 / 2 ^ 42 * σ := by ring

end CB

/-! ## Stored trees as `FTree`s -/

/-- `lam512` as a rational. -/
def lam512q (L : ℕ) : ℚ := if L = 8 then 240001 / 10000 else 9923 / 10000

theorem lam512q_eq (L : ℕ) : (lam512q L : ℝ) = lam512 L := by
  unfold lam512q lam512; split_ifs <;> norm_num

theorem Cx.norm_le_lam512 {f L : ℕ} {z : Cx f} (h : z.nsq ≤ lam512q L ^ 2) :
    ‖z.toC‖ ≤ lam512 L := by
  rw [← lam512q_eq]
  have h0 : (0 : ℝ) ≤ lam512q L := by rw [lam512q_eq]; exact lam512_nonneg L
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1
    (by rw [Cx.norm_sq_eq_nsq]; exact_mod_cast h)

/-- The conditions of `FTree` on a stored tree: leaves in `[σmin, σmax]`, `‖ℓ̂‖ ≤ lam512 L`. -/
def CTree.Ok {f : ℕ} : {L : ℕ} → CTree f L → Prop
  | _, .leaf σ => 1277833697 / 10 ^ 9 ≤ σ.toRat ∧ σ.toRat ≤ 18205 / 10000
  | _, @CTree.node _ L ℓ T0 T1 => (∀ o, (ℓ o).nsq ≤ lam512q L ^ 2) ∧ T0.Ok ∧ T1.Ok

/-- `CTree.Ok`, decided. -/
def CTree.okB {f : ℕ} : {L : ℕ} → CTree f L → Bool
  | _, .leaf σ => decide (1277833697 / 10 ^ 9 ≤ σ.toRat) && decide (σ.toRat ≤ 18205 / 10000)
  | _, @CTree.node _ L ℓ T0 T1 =>
    allOut (L + 1) (fun o => decide ((ℓ o).nsq ≤ lam512q L ^ 2)) && T0.okB && T1.okB

/-- Every stored `ℓ̂` conjugate-symmetric, exactly. -/
def CTree.realB {f : ℕ} : {L : ℕ} → CTree f L → Bool
  | _, .leaf _ => true
  | _, @CTree.node _ L ℓ T0 T1 =>
    allOut (L + 1) (fun o => decide (ℓ (cj (L + 1) o) = (ℓ o).conjg)) && T0.realB && T1.realB

theorem CTree.ok_of_okB {f : ℕ} : {L : ℕ} → (T : CTree f L) → T.okB = true → T.Ok
  | _, .leaf σ, h => by
    simpa only [CTree.okB, CTree.Ok, Bool.and_eq_true, decide_eq_true_eq] using h
  | _, @CTree.node _ L ℓ T0 T1, h => by
    simp only [CTree.okB, Bool.and_eq_true] at h
    exact ⟨fun o => of_decide_eq_true ((allOut_iff _ _).1 h.1.1 o), ok_of_okB T0 h.1.2,
      ok_of_okB T1 h.2⟩

/-- A stored tree as an `FTree` (values in `ℂ`, `ℝ`). -/
noncomputable def CTree.toFTree {f : ℕ} : {L : ℕ} → (T : CTree f L) → T.Ok → FTree L
  | _, .leaf σ, h => .leaf σ.toReal (by
      have h1 := Rat.cast_le (K := ℝ) |>.2 h.1
      have h2 := Rat.cast_le (K := ℝ) |>.2 h.2
      rw [Fx.toReal_eq_toRat]; push_cast at h1 h2 ⊢; exact ⟨h1, h2⟩)
  | _, @CTree.node _ L ℓ T0 T1, h =>
    .node (fun o => (ℓ o).toC) (fun o => Cx.norm_le_lam512 (h.1 o)) (T0.toFTree h.2.1)
      (T1.toFTree h.2.2)

theorem CTree.toFTree_congr {f L : ℕ} {T T' : CTree f L} (e : T = T') (h : T.Ok) (h' : T'.Ok) :
    T.toFTree h = T'.toFTree h' := by
  subst e; rfl

theorem CTree.real_toFTree {f : ℕ} : {L : ℕ} → (T : CTree f L) → (h : T.Ok) → T.realB = true →
    (T.toFTree h).Real
  | _, .leaf _, _, _ => trivial
  | _, @CTree.node _ L ℓ T0 T1, h, hr => by
    simp only [CTree.realB, Bool.and_eq_true] at hr
    refine ⟨fun o => ?_, real_toFTree T0 h.2.1 hr.1.2, real_toFTree T1 h.2.2 hr.2⟩
    change (ℓ (cj (L + 1) o)).toC = conj (ℓ o).toC
    rw [of_decide_eq_true ((allOut_iff _ _).1 hr.1.1 o), Cx.toC_conjg]

/-! ## Ball trees against exact trees -/

/-- Every ball of `B` holds the corresponding value of `U`. -/
def BTree.HoldsT {f : ℕ} : {L : ℕ} → BTree f L → LTree L → Prop
  | _, .leaf s, .leaf σ => s.Holds (σ : ℂ)
  | _, .node ℓ T0 T1, .node ℓ' U0 U1 => (∀ o, (ℓ o).Holds (ℓ' o)) ∧ T0.HoldsT U0 ∧ T1.HoldsT U1

theorem BTree.holdsT_lower {f : ℕ} (rm : RMode) (n : ℕ) : {L : ℕ} → (B : BTree (f + n) L) →
    (U : LTree L) → B.HoldsT U → (B.lower rm n).HoldsT U
  | _, .leaf _, .leaf _, h => CB.Holds.lower rm n h
  | _, .node _ T0 T1, .node _ U0 U1, h =>
    ⟨fun o => CB.Holds.lower rm n (h.1 o), holdsT_lower rm n T0 U0 h.2.1,
      holdsT_lower rm n T1 U1 h.2.2⟩

/-- Factor radii `≤ δq L` at depth `L + 1`, leaves `CB.leafOkB`. -/
def BTree.radOkB {f : ℕ} (δq : ℕ → ℚ) : {L : ℕ} → BTree f L → Bool
  | _, .leaf s => s.leafOkB
  | _, @BTree.node _ L ℓ T0 T1 =>
    allOut (L + 1) (fun o => (ℓ o).radLeB (δq L)) && T0.radOkB δq && T1.radOkB δq

theorem BTree.close_of {f : ℕ} (δq : ℕ → ℚ) : {L : ℕ} → (B : BTree f L) → (U : LTree L) →
    B.HoldsT U → B.radOkB δq = true → (h : B.centre.Ok) →
    Close (fun j => (δq j : ℝ)) (B.centre.toFTree h) U
  | _, .leaf _, .leaf _, hH, hr, _ => CB.close_leaf hH hr
  | _, @BTree.node _ L ℓ T0 T1, .node ℓ' U0 U1, hH, hr, h => by
    simp only [BTree.radOkB, Bool.and_eq_true] at hr
    exact ⟨fun o => CB.norm_sub_le_of_radLeB (hH.1 o) ((allOut_iff _ _).1 hr.1.1 o),
      close_of δq T0 U0 hH.2.1 hr.1.2 h.2.1, close_of δq T1 U1 hH.2.2 hr.2 h.2.2⟩

/-! ## The ball expansion holds the true tree -/

variable (P : XChoices) (f : ℕ)

/-- The FFT in balls holds the exact FFT. -/
theorem fftB_holds : ∀ (L : ℕ) (a : Fin (2 ^ L) → ℤ) (o : Out L),
    (fftB P f L a o).Holds (evalAt (fun i => (a i : ℂ)) (pt L o))
  | 0, a, _ => (CB.ofInt_holds _).congr (by simp [evalAt])
  | L + 1, a, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    have hs := evalAt_split (castC fun i => (a i : ℂ))
    simp only [evalAt_castC] at hs
    have he := fftB_holds L (evensZ a) o
    have ho := (twB_holds P.rc f L o).mul P.rm (fftB_holds L (oddsZ a) o)
    cases b
    · simp only [fftB]; erw [memo_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, pt_succ]
      refine (he.add ho).congr ?_
      rw [hs, zeta_sq]; rfl
    · simp only [fftB]; erw [memo_eq]
      simp only [↓reduceIte, pt_succ]
      refine (he.sub ho).congr ?_
      rw [hs, neg_sq, zeta_sq, neg_mul, ← sub_eq_add_neg]; rfl

theorem splitB_holds (L : ℕ) {t : Out (L + 1) → CB f} {e : Out (L + 1) → ℂ}
    (h : ∀ o, (t o).Holds (e o)) :
    (∀ o, ((splitB P f L t).1 o).Holds ((splitE e).1 o)) ∧
      ∀ o, ((splitB P f L t).2 o).Holds ((splitE e).2 o) := by
  refine ⟨fun o => ?_, fun o => ?_⟩ <;> simp only [splitB, memo_eq, splitE]
  · exact ((h _).add (h _)).half P.rm
  · exact (twsB_holds P.rc f L o).mul P.rm ((h _).sub (h _))

theorem d11B_holds (L : ℕ) {b00 b10 b11 : Out L → CB f} {g00 g10 g11 : Out L → ℂ}
    (h00 : ∀ o, (b00 o).Holds (g00 o)) (h10 : ∀ o, (b10 o).Holds (g10 o))
    (h11 : ∀ o, (b11 o).Holds (g11 o)) (o : Out L) :
    (d11B P f L b00 b10 b11 o).Holds (g11 o - g10 o * conj (g10 o) / g00 o) := by
  simp only [d11B, memo_eq]
  exact (h11 o).sub (((h10 o).normSq P.rm).divR P.rm P.dm (h00 o))

theorem ldlStepB_holdsT (L : ℕ) {b00 b10 bd : Out (L + 1) → CB f}
    {g00 g10 gd : Out (L + 1) → ℂ} (h00 : ∀ o, (b00 o).Holds (g00 o))
    (h10 : ∀ o, (b10 o).Holds (g10 o)) (hd : ∀ o, (bd o).Holds (gd o))
    {rec : (Out L → CB f) → (Out L → CB f) → (Out L → CB f) → BTree f L}
    (hrec : ∀ (c00 c10 c11 : Out L → CB f) (e00 e10 e11 : Out L → ℂ),
      (∀ o, (c00 o).Holds (e00 o)) → (∀ o, (c10 o).Holds (e10 o)) →
      (∀ o, (c11 o).Holds (e11 o)) → (rec c00 c10 c11).HoldsT (ffldl σ512 L e00 e10 e11)) :
    (ldlStepB P f L b00 b10 bd rec).HoldsT (.node (fun o => g10 o / g00 o)
      (ffldl σ512 L (splitE g00).1 (fun o => conj ((splitE g00).2 o)) (splitE g00).1)
      (ffldl σ512 L (splitE gd).1 (fun o => conj ((splitE gd).2 o)) (splitE gd).1)) := by
  have s0 := splitB_holds P f L h00
  have s1 := splitB_holds P f L hd
  refine ⟨fun o => ?_, hrec _ _ _ _ _ _ s0.1 (fun o => (s0.2 o).conjg) s0.1,
    hrec _ _ _ _ _ _ s1.1 (fun o => (s1.2 o).conjg) s1.1⟩
  simp only [memo_eq]
  exact (h10 o).divR P.rm P.dm (h00 o)

theorem σ512_eq : σ512 = (σ512q : ℝ) := by norm_num [σ512, σ512q]

theorem ldlB_holdsT : ∀ (L : ℕ) (b00 b10 b11 : Out L → CB f) (g00 g10 g11 : Out L → ℂ),
    (∀ o, (b00 o).Holds (g00 o)) → (∀ o, (b10 o).Holds (g10 o)) →
    (∀ o, (b11 o).Holds (g11 o)) → (ldlB P f L b00 b10 b11).HoldsT (ffldl σ512 L g00 g10 g11)
  | 0, b00, _, _, g00, _, _, h00, _, _ => by
    change (CB.leaf P.rm P.rc σ512q (b00 ())).Holds ((σ512 / √(g00 ()).re : ℝ) : ℂ)
    rw [σ512_eq]
    exact (h00 ()).leaf P.rm P.rc σ512q (by norm_num [σ512q])
  | L + 1, _, _, _, _, _, _, h00, h10, h11 =>
    ldlStepB_holdsT P f L h00 h10 (d11B_holds P f (L + 1) h00 h10 h11) (ldlB_holdsT L)

/-! ## Raw keys -/

/-- `(B·B⋆)₀₀ = gg⋆ + ff⋆` of a raw key, exact: `KeyB.gram00` on the raw polynomials (a `KeyB`
needs `hf`, `hF` and a tree, which a raw key lacks; `toKeyB_trueTree` is `rfl`). -/
noncomputable def RawKey.g00 (k : RawKey) (o : Out 9) : ℂ :=
  fftZ k.g o * conj (fftZ k.g o) + fftZ k.f o * conj (fftZ k.f o)

/-- `(B·B⋆)₁₀ = Gg⋆ + Ff⋆` of a raw key, exact. -/
noncomputable def RawKey.g10 (k : RawKey) (o : Out 9) : ℂ :=
  fftZ k.G o * conj (fftZ k.g o) + fftZ k.F o * conj (fftZ k.f o)

/-- `(B·B⋆)₁₁ = GG⋆ + FF⋆` of a raw key, exact. -/
noncomputable def RawKey.g11 (k : RawKey) (o : Out 9) : ℂ :=
  fftZ k.G o * conj (fftZ k.G o) + fftZ k.F o * conj (fftZ k.F o)

/-- The true tree of a raw key: exact ffLDL⋆ of `B·B⋆` (`KeyB.trueTree`). -/
noncomputable def RawKey.trueTree (k : RawKey) : LTree 9 := ffldl σ512 9 k.g00 k.g10 k.g11

/-- Coefficient `i` of `a·b` in `ℤ[x]/(x⁵¹² + 1)`. -/
def ncoef (a b : Fin (2 ^ 9) → ℤ) (i : Fin (2 ^ 9)) : ℤ :=
  ∑ j : Fin (2 ^ 9), if h : j.1 ≤ i.1 then a j * b ⟨i.1 - j.1, by have := i.2; omega⟩
    else -(a j * b ⟨2 ^ 9 + i.1 - j.1, by omega⟩)

/-- The NTRU equation `fG - gF = q` in `ℤ[x]/(x⁵¹² + 1)`, decided. -/
def ntruB (k : RawKey) : Bool :=
  decide (∀ i : Fin (2 ^ 9), ncoef k.f k.G i - ncoef k.g k.F i = if i.1 = 0 then 12289 else 0)

/-- Evaluation at a root of `x⁵¹² + 1` turns the negacyclic product into the product. -/
theorem evalAt_ncoef (a b : Fin (2 ^ 9) → ℤ) {z : ℂ} (hz : z ^ 2 ^ 9 = -1) :
    evalAt (fun i => (ncoef a b i : ℂ)) z =
      evalAt (fun i => (a i : ℂ)) z * evalAt (fun i => (b i : ℂ)) z := by
  simp only [evalAt, ncoef]
  rw [Finset.sum_mul_sum]
  simp only [Int.cast_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ =>
    (Fintype.sum_equiv (Equiv.addLeft j) _ _ fun k => ?_).symm
  have hv : ((Equiv.addLeft j k : Fin (2 ^ 9)) : ℕ) = (j.1 + k.1) % 512 := Fin.val_add j k
  split_ifs with h
  · have e : b ⟨(Equiv.addLeft j k : Fin (2 ^ 9)).1 - j.1, by omega⟩ = b k :=
      congrArg b (Fin.ext (by dsimp only; omega))
    have hp : z ^ j.1 * z ^ k.1 = z ^ (Equiv.addLeft j k : Fin (2 ^ 9)).1 := by
      rw [← pow_add, show j.1 + k.1 = (Equiv.addLeft j k : Fin (2 ^ 9)).1 by omega]
    rw [e]; push_cast
    linear_combination ((a j : ℂ) * b k) * hp
  · have e : b ⟨2 ^ 9 + (Equiv.addLeft j k : Fin (2 ^ 9)).1 - j.1, by omega⟩ = b k :=
      congrArg b (Fin.ext (by dsimp only; omega))
    have hp : z ^ j.1 * z ^ k.1 = -z ^ (Equiv.addLeft j k : Fin (2 ^ 9)).1 := by
      rw [← pow_add, show j.1 + k.1 = 2 ^ 9 + (Equiv.addLeft j k : Fin (2 ^ 9)).1 by omega,
        pow_add, hz, neg_one_mul]
    rw [e]; push_cast
    linear_combination ((a j : ℂ) * b k) * hp

/-- `fG - gF = q` gives `f̂Ĝ - ĝF̂ = q` at every FFT point. -/
theorem ntru_det (k : RawKey) (h : ntruB k = true) (o : Out 9) :
    fftZ k.f o * fftZ k.G o - fftZ k.g o * fftZ k.F o = 12289 := by
  unfold ntruB at h
  have hc := of_decide_eq_true h
  have hz := pt_pow 9 o
  simp only [fftZ, fftE]
  rw [← evalAt_ncoef k.f k.G hz, ← evalAt_ncoef k.g k.F hz]
  simp only [evalAt, ← Finset.sum_sub_distrib, ← sub_mul, ← Int.cast_sub, hc]
  rw [Finset.sum_eq_single ⟨0, by norm_num⟩
    (fun i _ hi => by simp [show i.1 ≠ 0 from fun h => hi (Fin.ext h)]) (by simp)]
  simp

/-- The NTRU identity at the root: `D11 = g11 - |g10|²/g00 = q²/g00`. -/
theorem ntru_root (k : RawKey)
    (h : ∀ o, fftZ k.f o * fftZ k.G o - fftZ k.g o * fftZ k.F o = 12289) (o : Out 9) :
    ((12289 ^ 2 : ℤ) : ℂ) / k.g00 o = k.g11 o - k.g10 o * conj (k.g10 o) / k.g00 o := by
  have hd := h o
  have hd' := congrArg conj hd
  simp only [map_sub, map_mul, map_ofNat] at hd'
  have I : k.g00 o * k.g11 o - k.g10 o * conj (k.g10 o) = 12289 ^ 2 := by
    simp only [RawKey.g00, RawKey.g10, RawKey.g11, map_add, map_mul, Complex.conj_conj]
    linear_combination (conj (fftZ k.f o) * conj (fftZ k.G o) -
      conj (fftZ k.g o) * conj (fftZ k.F o)) * hd + 12289 * hd'
  have h0 : k.g00 o ≠ 0 := fun h0 => by
    rw [h0, zero_mul, zero_sub, Complex.mul_conj] at I
    have := congrArg Complex.re I
    simp only [Complex.neg_re, Complex.ofReal_re] at this
    norm_num [sq] at this
    linarith [Complex.normSq_nonneg (k.g10 o)]
  push_cast
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff h0]
  linear_combination -I

theorem gramB_holds (k : RawKey) :
    (∀ o, ((gramB P f k).1 o).Holds (k.g00 o)) ∧ (∀ o, ((gramB P f k).2.1 o).Holds (k.g10 o)) ∧
      ∀ o, ((gramB P f k).2.2 o).Holds (k.g11 o) := by
  have hf := fftB_holds P f 9 k.f
  have hg := fftB_holds P f 9 k.g
  have hF := fftB_holds P f 9 k.F
  have hG := fftB_holds P f 9 k.G
  refine ⟨fun o => ?_, fun o => ?_, fun o => ?_⟩ <;> simp only [gramB, memo_eq]
  · exact ((hg o).normSq P.rm).add ((hf o).normSq P.rm)
  · exact ((hG o).mul P.rm (hg o).conjg).add ((hF o).mul P.rm (hf o).conjg)
  · exact ((hG o).normSq P.rm).add ((hF o).normSq P.rm)

theorem rootB_holds (k : RawKey) (hn : P.root = .ntru → ntruB k = true) (o : Out 9) :
    (rootB P f (gramB P f k) o).Holds (k.g11 o - k.g10 o * conj (k.g10 o) / k.g00 o) := by
  obtain ⟨h00, h10, h11⟩ := gramB_holds P f k
  rcases hP : P.root with _ | _
  · simp only [rootB, hP]
    exact d11B_holds P f 9 h00 h10 h11 o
  · simp only [rootB, hP, memo_eq]
    exact ((CB.ofInt_holds _).divR P.rm P.dm (h00 o)).congr (ntru_root k (ntru_det k (hn hP)) o)

/-- **The ball expansion holds the true tree**: every ball of `expandB` contains the
corresponding factor or leaf of exact ffLDL⋆ of `B·B⋆`. -/
theorem expandB_holdsT (k : RawKey) (hn : P.root = .ntru → ntruB k = true) :
    (expandB P f k).HoldsT k.trueTree := by
  obtain ⟨h00, h10, _⟩ := gramB_holds P f k
  exact ldlStepB_holdsT P f 8 h00 h10 (rootB_holds P f k hn) (ldlB_holdsT P f 8)

/-! ## The check -/

variable (n : ℕ)

/-- The rounded ball tree holds the true tree. -/
theorem storeB_holdsT (k : RawKey) (hn : ntruB k = true) : (storeB P n k).HoldsT k.trueTree :=
  BTree.holdsT_lower P.rm n _ _ (expandB_holdsT P (64 + n) k fun _ => hn)

/-- **The per-key check** at working precision `64 + n` fraction bits: FFT bounds of `f`, `F`;
`FTree` conditions and conjugate symmetry of the stored tree at 64 fraction bits
`(storeB P n k).centre`; radii of the rounded stored balls `≤ δq`; rounded leaf balls;
`fG - gF = q`. That a key passes it (at any `n`; `n = 0`: expansion at 64 fraction bits) is not
proved for any key (`#eval` runs of `checkFast` on round-3 KAT keys are not kernel proofs). -/
def check (δq : ℕ → ℚ) (k : RawKey) : Bool :=
  let T := storeB P n k
  let C := T.centre
  allOut 9 (fun o => (fftB P (64 + n) 9 k.f o).normLeB 255) &&
    allOut 9 (fun o => (fftB P (64 + n) 9 k.F o).normLeB 3500) && C.okB && C.realB &&
    T.radOkB δq && ntruB k

/-- The parts of a passed check. -/
structure CheckOk (δq : ℕ → ℚ) (k : RawKey) : Prop where
  hf : ∀ o, (fftB P (64 + n) 9 k.f o).normLeB 255 = true
  hF : ∀ o, (fftB P (64 + n) 9 k.F o).normLeB 3500 = true
  ok : (storeB P n k).centre.okB = true
  real : (storeB P n k).centre.realB = true
  rad : (storeB P n k).radOkB δq = true
  ntru : ntruB k = true

theorem check_ok {δq : ℕ → ℚ} {k : RawKey} (h : check P n δq k = true) : CheckOk P n δq k := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨(allOut_iff _ _).1 h1, (allOut_iff _ _).1 h2, h3, h4, h5, h6⟩

/-- The `KeyB` of a raw key passing `check`: stored tree `storeC` (64 fraction bits). -/
noncomputable def toKeyB (δq : ℕ → ℚ) (k : RawKey) (h : check P n δq k = true) : KeyB where
  f := k.f
  F := k.F
  hf o := le_of_le_of_eq
    (CB.norm_le_of_normLeB (fftB_holds P _ 9 k.f o) ((check_ok P n h).hf o)) (by norm_num)
  hF o := le_of_le_of_eq
    (CB.norm_le_of_normLeB (fftB_holds P _ 9 k.F o) ((check_ok P n h).hF o)) (by norm_num)
  tree := (storeC P n k).toFTree (storeB_centre P n k ▸ CTree.ok_of_okB _ (check_ok P n h).ok)
  g := k.g
  G := k.G

theorem toKeyB_trueTree (δq : ℕ → ℚ) (k : RawKey) (h : check P n δq k = true) :
    (toKeyB P n δq k h).trueTree = k.trueTree := rfl

/-- **Soundness of the check**: a raw key passing `check P n δq` gives a key passing
`KeyB.Good δ` (`δ j = δq j`): stored tree at 64 fraction bits `storeC` real and `Close δ` to the
true tree.
`check … = true` is not proved for any key (`#eval` runs of `checkFast` are not kernel proofs). -/
theorem check_sound (δq : ℕ → ℚ) (k : RawKey) (h : check P n δq k = true) :
    (toKeyB P n δq k h).Good (fun j => (δq j : ℝ)) := by
  have hc := check_ok P n h
  have hB : (storeB P n k).centre.Ok := CTree.ok_of_okB _ hc.ok
  have e : (toKeyB P n δq k h).tree = (storeB P n k).centre.toFTree hB :=
    CTree.toFTree_congr (storeB_centre P n k).symm (storeB_centre P n k ▸ hB) hB
  refine ⟨?_, ?_⟩
  · rw [e]; exact CTree.real_toFTree _ hB hc.real
  · rw [e]; exact BTree.close_of δq _ _ (storeB_holdsT P n k hc.ntru) hc.rad hB

/-! ## Experiments on checked keys -/

/-- Raw keys passing `check P n δq`. -/
def CheckedKey (δq : ℕ → ℚ) : Type := {k : RawKey // check P n δq k = true}

/-- A checked key as a key passing `KeyB.Good`. -/
noncomputable def CheckedKey.toGood {P : XChoices} {n : ℕ} {δq : ℕ → ℚ}
    (k : CheckedKey P n δq) : GoodKey (fun j => (δq j : ℝ)) :=
  ⟨toKeyB P n δq k.1 k.2, check_sound P n δq k.1 k.2⟩

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

/-- Experiment oracles: auxiliary oracles and a signing oracle on (checked raw key, hash). -/
@[reducible] def specK (aux : OracleSpec.{0, 0} ιA) (δq : ℕ → ℚ) :
    OracleSpec (ιA ⊕ (CheckedKey P n δq × (Fin (2 ^ 9) → ℤ))) :=
  Sum.elim aux fun _ => Sig

/-- One per signing query. -/
def wKC (δq : ℕ → ℚ) : ιA ⊕ (CheckedKey P n δq × (Fin (2 ^ 9) → ℤ)) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

/-- Signing queries on checked raw keys as signing queries on `toGood` keys. -/
noncomputable def embedImpl (δq : ℕ → ℚ) :
    QueryImpl (specK P n aux δq) (OracleComp (specS aux fun j => (δq j : ℝ)))
  | .inl x => liftM (OracleSpec.query (spec := specS aux fun j => (δq j : ℝ)) (.inl x))
  | .inr kc => liftM (OracleSpec.query (spec := specS aux fun j => (δq j : ℝ))
      (.inr (kc.1.toGood, kc.2)))

/-- An experiment on checked raw keys as an experiment on `GoodKey`s. -/
noncomputable def embed (δq : ℕ → ℚ) {α : Type} (oe : OracleComp (specK P n aux δq) α) :
    OracleComp (specS aux fun j => (δq j : ℝ)) α :=
  simulateQ (embedImpl P n δq) oe

theorem pathSum_embed (δq : ℕ → ℚ) {α : Type} {oe : OracleComp (specK P n aux δq) α} {S : ℝ}
    (h : PathSum (wKC P n δq) oe S) : PathSum (wK _) (embed P n δq oe) S := by
  induction h with
  | pure x hS => rw [embed, simulateQ_pure]; exact .pure x hS
  | query_bind t k _ ih =>
    rw [embed, simulateQ_bind, show simulateQ (embedImpl P n δq) (liftM (OracleSpec.query t)) =
      embedImpl P n δq t from simulateQ_spec_query (impl := embedImpl P n δq) t]
    rcases t with x | kc
    · exact .query_bind (Sum.inl x) _ fun u => ih u
    · exact .query_bind (Sum.inr (kc.1.toGood, kc.2)) _ fun u => ih u

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]

/-- **Fixed-point signing against exact Falcon on checked keys**: `falcon512_fixed_vs_true` with
the key condition `KeyB.Good δ` replaced by `check P n δq k = true` on every raw signing key
(`δ j = δq j`, stored tree at 64 fraction bits, key expansion at `64 + n`). Hypotheses: those of
`falcon512_fixed_vs_true` (`ρ`, `K ≤ 2³⁹` signing-oracle calls (one ffSampling call each, restarts
included) along every execution, `K·s2B 30.5 δ ≤ 2⁻⁹`, SamplerZ perfect in every world). Not
proved: that a given Falcon key passes `check` (not proved for any key: `#eval` runs of `checkFast`
on round-3 KAT keys are not kernel proofs), at any `δq` and `n`; the word size (key expansion in
unbounded `Int`, `InRange` not checked); and what `falcon512_fixed_vs_true` does not prove apart
from `KeyB.Good δ` (`FTree.Real`, `Close δ`, the true leaf range), the tie of the stored tree to
`f, F` (`storeC`) and `fG - gF = q` (given by `check`). -/
theorem falcon512_fixed_vs_true_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (δq : ℕ → ℚ) (ρ : Arith64 (1 / 2 ^ 78))
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
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK P n aux δq) α) (hq : PathSum (wKC P n δq) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ (embed P n δq oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed P n δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  falcon512_fixed_vs_true ρ K hK hδ T hT implA implE implM implF hAE hAM hAF hE hM hF
    (embed P n δq oe) (pathSum_embed P n δq hq) hs hwin

/-- `δ127` as a rational. -/
def δ127q (L : ℕ) : ℚ := if L = 8 then 1 / 2 ^ 58 else 1 / 2 ^ 63

theorem δ127q_eq : (fun j => (δ127q j : ℝ)) = δ127 := by
  funext j; unfold δ127q δ127; split_ifs <;> norm_num

/-- **Instance** at the `p = 127` tree error (`δ127`), `K ≤ 2³⁹` (`s2B_falcon`). It is non-vacuous
only at a working precision `64 + n` at which the rounded radii meet `2⁻⁵⁸` (root) and `2⁻⁶³`
(below); that an expansion at 64 fraction bits (`n = 0`) or any given `n` meets them is not proved
for any key (`#eval` runs of `checkFast` on round-3 KAT keys are not kernel proofs). Hypotheses
and what is not proved otherwise: those of `falcon512_fixed_vs_true_checked`. -/
theorem falcon512_fixed_vs_true127_checked [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK P n aux δ127q) α) (hq : PathSum (wKC P n δ127q) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ (embed P n δ127q oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed P n δ127q oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) := by
  have hK' : (K : ℝ) ≤ 2 ^ 39 := by exact_mod_cast hK
  refine falcon512_fixed_vs_true_checked P n δ127q ρ K hK ?_ T hT implA implE implM implF hAE hAM
    hAF hE hM hF oe hq hs hwin
  rw [δ127q_eq]
  exact (mul_le_mul_of_nonneg_right hK' (s2B_nonneg _ _)).trans s2B_falcon

end FalconPrecision.Exec
