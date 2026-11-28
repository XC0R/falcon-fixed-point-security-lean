/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.FixedPoint
public import FalconPrecision.Errors.FxModel

/-! # Running error bounds for the executable fixed-point arithmetic

A ball `CB f` is a computed complex value `c : Cx f` together with a radius `r : Option ℚ`;
`CB.Holds b z` says `‖z - c‖ ≤ r` (`none`: no bound, holds for every `z`). Every operation computes
its centre with the executable operation of `FixedPoint` (the value a signer stores) and its radius
from the input radii, the computed magnitudes and the per-operation error of `FixedPoint`
(`Fx.mul_err`, `Fx.div_err`, `Fx.sqrt_err`, …), as a rational rounded up (`up`). The `Holds` lemmas
say that the radius bounds the distance to the exact result whenever the inputs' radii bound theirs;
an operation that cannot bound its result (for example a divisor ball not contained in `(0, ∞)`)
returns `none`.

`Out L` vectors: `Out.idx`, `Out.ofIdx` number the positions, `memo` stores a vector in an array
(`memo_eq`: it is the same function), `allOut` decides a property at every position. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec ComplexConjugate

/-! ## Vectors over `Out L` -/

/-- The index of a position: the sign choices read as binary digits, last choice lowest. -/
def Out.idx : (L : ℕ) → Out L → ℕ
  | 0, _ => 0
  | L + 1, x => 2 * Out.idx L (x : Out L × Bool).1 + if (x : Out L × Bool).2 then 1 else 0

/-- The position of an index. -/
def Out.ofIdx : (L : ℕ) → ℕ → Out L
  | 0, _ => ()
  | L + 1, n => (show Out L × Bool from (Out.ofIdx L (n / 2), n % 2 == 1))

theorem Out.idx_lt : ∀ (L : ℕ) (o : Out L), Out.idx L o < 2 ^ L
  | 0, _ => by simp [Out.idx]
  | L + 1, x => by
    have := Out.idx_lt L (x : Out L × Bool).1
    simp only [Out.idx, pow_succ]
    split_ifs <;> omega

theorem Out.ofIdx_idx : ∀ (L : ℕ) (o : Out L), Out.ofIdx L (Out.idx L o) = o
  | 0, _ => rfl
  | L + 1, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    change (Out.ofIdx L ((2 * Out.idx L o + if b then 1 else 0) / 2),
      (2 * Out.idx L o + if b then 1 else 0) % 2 == 1) = (o, b)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [show 2 * Out.idx L o / 2 = Out.idx L o by omega,
        Out.ofIdx_idx L o]
      simp
    · simp only [↓reduceIte]
      rw [show (2 * Out.idx L o + 1) / 2 = Out.idx L o by omega, Out.ofIdx_idx L o,
        show (2 * Out.idx L o + 1) % 2 = 1 by omega]
      rfl

/-- A vector stored in an array, read back by index. -/
def memo {X : Type} [Inhabited X] (L : ℕ) (v : Out L → X) : Out L → X :=
  let a : Array X := Array.ofFn (n := 2 ^ L) fun i => v (Out.ofIdx L i)
  fun o => a.getD (Out.idx L o) default

theorem memo_eq {X : Type} [Inhabited X] (L : ℕ) (v : Out L → X) : memo L v = v := by
  funext o
  simp [memo, Array.getD, Out.idx_lt L o, Out.ofIdx_idx]

/-- `p` holds at every position. -/
def allOut : (L : ℕ) → (Out L → Bool) → Bool
  | 0, p => p ()
  | L + 1, p => allOut L fun o => p (show Out L × Bool from (o, false)) &&
      p (show Out L × Bool from (o, true))

theorem allOut_iff : ∀ (L : ℕ) (p : Out L → Bool), allOut L p = true ↔ ∀ o, p o = true
  | 0, p => ⟨fun h _ => h, fun h => h ()⟩
  | L + 1, p => by
    rw [allOut, allOut_iff L, show (∀ x : Out (L + 1), p x = true) ↔
      ∀ x : Out L × Bool, p x = true from Iff.rfl, Prod.forall]
    simp only [Bool.and_eq_true, Bool.forall_bool]

/-! ## Rational helpers -/

/-- The error bound `RMode.e` as a rational. -/
def RMode.eQ (r : RMode) : ℚ := if r = .floor then 1 else 1 / 2

theorem RMode.eQ_eq (r : RMode) : (r.eQ : ℝ) = r.e := by
  unfold RMode.eQ RMode.e; split_ifs <;> norm_num

/-- A rational upper bound of `√2`. -/
def sqrt2Q : ℚ := 14143 / 10000

theorem sqrt_two_le_sqrt2Q : √2 ≤ (sqrt2Q : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num [sqrt2Q])]; norm_num [sqrt2Q]

/-- `q` rounded up to the grid `2⁻ᴷ`. -/
def up (K : ℕ) (q : ℚ) : ℚ := (⌈q * 2 ^ K⌉ : ℚ) / 2 ^ K

theorem le_up (K : ℕ) (q : ℚ) : q ≤ up K q := by
  rw [up, le_div_iff₀ (by positivity)]; exact Int.le_ceil _

/-- An upper bound of `√q` on the grid `2⁻ᴷ`. -/
def sqrtUB (K : ℕ) (q : ℚ) : ℚ := ((⌈q * 2 ^ (2 * K)⌉.toNat.sqrt + 1 : ℕ) : ℚ) / 2 ^ K

/-- A lower bound of `√q` on the grid `2⁻ᴷ`. -/
def sqrtLB (K : ℕ) (q : ℚ) : ℚ := ((⌊q * 2 ^ (2 * K)⌋.toNat.sqrt : ℕ) : ℚ) / 2 ^ K

theorem sqrt_mul_two_pow_two_mul (K : ℕ) (x : ℝ) : √(x * 2 ^ (2 * K)) = √x * 2 ^ K := by
  rw [Real.sqrt_mul' _ (by positivity), mul_comm 2 K, pow_mul, Real.sqrt_sq (by positivity)]

theorem sqrt_le_sqrtUB (K : ℕ) (q : ℚ) : √(q : ℝ) ≤ (sqrtUB K q : ℝ) := by
  have hN : (q : ℝ) * 2 ^ (2 * K) ≤ (⌈q * 2 ^ (2 * K)⌉.toNat : ℕ) := by
    have h := (Int.le_ceil (q * 2 ^ (2 * K))).trans (Int.cast_le.2 (Int.self_le_toNat _))
    exact_mod_cast h
  unfold sqrtUB; push_cast
  rw [le_div_iff₀ (by positivity), ← sqrt_mul_two_pow_two_mul]
  exact (Real.sqrt_le_sqrt hN).trans Real.real_sqrt_lt_nat_sqrt_succ.le

theorem sqrtLB_le_sqrt (K : ℕ) (q : ℚ) : (sqrtLB K q : ℝ) ≤ √(q : ℝ) := by
  unfold sqrtLB; push_cast
  rcases le_or_gt 0 ⌊q * 2 ^ (2 * K)⌋ with h | h
  · rw [div_le_iff₀ (by positivity), ← sqrt_mul_two_pow_two_mul]
    refine Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt ?_)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    exact_mod_cast Int.floor_le (q * 2 ^ (2 * K))
  · rw [Int.toNat_eq_zero.2 h.le]; simp [Real.sqrt_nonneg]

theorem RMode.e_nonneg (r : RMode) : 0 ≤ r.e := by linarith [r.half_le_e]

/-! ## Complex fixed-point helpers -/

namespace Cx

variable {f : ℕ}

instance : Inhabited (Cx f) := ⟨⟨⟨0⟩, ⟨0⟩⟩⟩

/-- Complex conjugate (exact). -/
def conjg (z : Cx f) : Cx f := ⟨z.re, z.im.neg⟩

/-- The integer `n`. -/
def ofInt (n : ℤ) : Cx f := ⟨Fx.ofInt n, ⟨0⟩⟩

/-- `‖z‖²` in `ℚ`, exact. -/
def nsq (z : Cx f) : ℚ := z.re.toRat ^ 2 + z.im.toRat ^ 2

/-- An upper bound of `‖z‖`. -/
def nUB (z : Cx f) : ℚ := ((z.re.m ^ 2 + z.im.m ^ 2).toNat.sqrt + 1 : ℕ) / 2 ^ f

/-- A lower bound of `‖z‖`. -/
def nLB (z : Cx f) : ℚ := ((z.re.m ^ 2 + z.im.m ^ 2).toNat.sqrt : ℕ) / 2 ^ f

/-- Division of a complex value by a real one. -/
inductive DivMode where
  /-- Each part divided once (`y/x`). -/
  | direct
  /-- The inverse rounded once, then two products (`1/x·y`). -/
  | invMul
  deriving DecidableEq, Repr

/-- `z·z̄` as a real value: `re·re + im·im`, two roundings. -/
def normSqR (rm : RMode) (z : Cx f) : Cx f := ⟨(z.re.mul rm z.re).add (z.im.mul rm z.im), ⟨0⟩⟩

/-- `z/d` for the real part `d` of a divisor. -/
def divR (rm : RMode) (dm : DivMode) (z : Cx f) (d : Fx f) : Cx f :=
  match dm with
  | .direct => ⟨z.re.div rm d, z.im.div rm d⟩
  | .invMul =>
    let i := (Fx.ofInt 1 : Fx f).div rm d
    ⟨z.re.mul rm i, z.im.mul rm i⟩

/-- A leaf `σ/√d`: `σ` stored by `rc`, the root and the quotient rounded once by `rm`. -/
def leafR (rm rc : RMode) (σq : ℚ) (d : Fx f) : Cx f :=
  ⟨(Fx.ofRat rc σq : Fx f).div rm (d.sqrt rm), ⟨0⟩⟩

theorem toC_conjg (z : Cx f) : z.conjg.toC = starRingEnd ℂ z.toC := by
  apply Complex.ext <;> simp [conjg, toC, Fx.toReal_neg]

theorem toC_ofInt (n : ℤ) : (ofInt n : Cx f).toC = n := by
  apply Complex.ext <;> simp [ofInt, toC, Fx.ofInt, Fx.toReal]

theorem toC_add (z w : Cx f) : (z.add w).toC = z.toC + w.toC := by
  apply Complex.ext <;> simp [add, toC, Fx.toReal_add]

theorem toC_sub (z w : Cx f) : (z.sub w).toC = z.toC - w.toC := by
  apply Complex.ext <;> simp [sub, toC, Fx.toReal_sub]

theorem toC_neg (z : Cx f) : z.neg.toC = -z.toC := by
  apply Complex.ext <;> simp [neg, toC, Fx.toReal_neg]

theorem sq_norm_toC (z : Cx f) :
    ‖z.toC‖ ^ 2 = ((z.re.m ^ 2 + z.im.m ^ 2).toNat : ℝ) / (2 ^ f) ^ 2 := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by positivity), Complex.sq_norm,
    Complex.normSq_apply]
  simp only [toC, Fx.toReal]; push_cast; ring

theorem norm_le_nUB (z : Cx f) : ‖z.toC‖ ≤ (z.nUB : ℝ) := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (Rat.cast_nonneg.2 (by unfold nUB; positivity))
    two_ne_zero).1 ?_
  rw [sq_norm_toC, nUB]; push_cast
  rw [div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have := (Nat.lt_succ_sqrt (z.re.m ^ 2 + z.im.m ^ 2).toNat).le
  rw [← sq] at this; exact_mod_cast this

theorem nLB_le_norm (z : Cx f) : (z.nLB : ℝ) ≤ ‖z.toC‖ := by
  refine (pow_le_pow_iff_left₀ (Rat.cast_nonneg.2 (by unfold nLB; positivity)) (norm_nonneg _)
    two_ne_zero).1 ?_
  rw [sq_norm_toC, nLB]; push_cast
  rw [div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have := Nat.sqrt_le (z.re.m ^ 2 + z.im.m ^ 2).toNat
  rw [← sq] at this; exact_mod_cast this

theorem norm_sq_eq_nsq (z : Cx f) : ‖z.toC‖ ^ 2 = (z.nsq : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [nsq, toC, Fx.toReal_eq_toRat]; ring

end Cx

/-! ## Balls -/

/-- A computed value and a bound on its distance to an exact value (`none`: no bound). -/
structure CB (f : ℕ) where
  c : Cx f
  r : Option ℚ
  deriving Repr

instance {f : ℕ} : Inhabited (CB f) := ⟨⟨⟨⟨0⟩, ⟨0⟩⟩, none⟩⟩

namespace CB

variable {f : ℕ}

/-- `b` bounds its distance to `z`. -/
def Holds (b : CB f) (z : ℂ) : Prop := ∀ r ∈ b.r, ‖z - b.c.toC‖ ≤ r

/-- The radii are rounded up to `2⁻⁽²ᶠ⁺⁶⁴⁾`. -/
def K (f : ℕ) : ℕ := 2 * f + 64

/-- The ulp `2⁻ᶠ`. -/
def ulp (f : ℕ) : ℚ := 1 / 2 ^ f

theorem e_div_eq (r : RMode) : r.e / 2 ^ f = (r.eQ : ℝ) * ulp f := by
  rw [RMode.eQ_eq, ulp]; push_cast; ring

theorem sqrt_two_e_le (r : RMode) : √2 * (r.e / 2 ^ f) ≤ (sqrt2Q : ℝ) * r.eQ * ulp f := by
  rw [mul_assoc, ← e_div_eq]
  exact mul_le_mul_of_nonneg_right sqrt_two_le_sqrt2Q (div_nonneg r.e_nonneg (by positivity))

theorem norm_sub_le_sqrt_two {w c : ℂ} {ε : ℝ} (h1 : |w.re - c.re| ≤ ε)
    (h2 : |w.im - c.im| ≤ ε) : ‖w - c‖ ≤ √2 * ε :=
  Errors.Fixed.norm_le_of_re_im _ _ (by rwa [Complex.sub_re]) (by rwa [Complex.sub_im])

/-- Triangle inequality through `X`, then rounding up. -/
theorem le_up_of {z X c : ℂ} {A B : ℝ} {q : ℚ} (h1 : ‖z - X‖ ≤ A) (h2 : ‖X - c‖ ≤ B)
    (hq : A + B ≤ q) : ‖z - c‖ ≤ (up (K f) q : ℝ) :=
  (norm_sub_le_norm_sub_add_norm_sub z X c).trans
    ((add_le_add h1 h2).trans (hq.trans (Rat.cast_le.2 (le_up _ q))))

/-- An exact value. -/
def exact (c : Cx f) : CB f := ⟨c, some 0⟩

/-- The integer `n`, exact. -/
def ofInt (n : ℤ) : CB f := exact (Cx.ofInt n)

/-- Conjugate (exact). -/
def conjg (a : CB f) : CB f := ⟨a.c.conjg, a.r⟩

/-- Negation (exact). -/
def neg (a : CB f) : CB f := ⟨a.c.neg, a.r⟩

/-- Sum (exact). -/
def add (a b : CB f) : CB f := ⟨a.c.add b.c, do let x ← a.r; let y ← b.r; pure (x + y)⟩

/-- Difference (exact). -/
def sub (a b : CB f) : CB f := ⟨a.c.sub b.c, do let x ← a.r; let y ← b.r; pure (x + y)⟩

/-- Product (`Cx.mul`, four roundings): `‖a‖·rb + ‖b‖·ra + ra·rb + 2√2·e·ulp`. -/
def mul (rm : RMode) (a b : CB f) : CB f :=
  ⟨a.c.mul rm b.c, do
    let x ← a.r; let y ← b.r
    pure (up (K f) (a.c.nUB * y + b.c.nUB * x + x * y + 2 * sqrt2Q * rm.eQ * ulp f))⟩

/-- `z/2` (`Cx.half`, one rounding per part). -/
def half (rm : RMode) (a : CB f) : CB f :=
  ⟨a.c.half rm, (fun x => up (K f) (x / 2 + sqrt2Q * rm.eQ * ulp f)) <$> a.r⟩

/-- `z·z̄ = ‖z‖²` as a real value: `re·re + im·im`, two roundings. -/
def normSq (rm : RMode) (a : CB f) : CB f :=
  ⟨a.c.normSqR rm,
    (fun x => up (K f) ((2 * a.c.nUB + x) * x + 2 * rm.eQ * ulp f)) <$> a.r⟩

/-- `a/d` for a real divisor: the divisor's centre is `d.c.re`, its imaginary part is added to its
radius; no bound unless the divisor ball lies in `(0, ∞)`. -/
def divR (rm : RMode) (dm : Cx.DivMode) (a d : CB f) : CB f :=
  let dc := d.c.re.toRat
  ⟨a.c.divR rm dm d.c.re, do
    let x ← a.r; let y ← d.r
    let yd := y + |d.c.im.toRat|
    let lo := dc - yd
    if 0 < lo then
      let loc : ℚ := match dm with
        | .direct => sqrt2Q * rm.eQ * ulp f
        | .invMul => a.c.nUB * rm.eQ * ulp f + sqrt2Q * rm.eQ * ulp f
      pure (up (K f) (x / dc + (a.c.nUB + x) * yd / (dc * lo) + loc))
    else none⟩

/-- A leaf `σ/√D` for a real `D` (`d.c.re`): `σ` stored by `rc`, `√D` and the quotient rounded once
by `rm`. The result is real. The radius bounds `σ` by `σq + rc.e·ulp`: sound for `0 ≤ σq`. -/
def leaf (rm rc : RMode) (σq : ℚ) (d : CB f) : CB f :=
  let s := d.c.re.sqrt rm
  ⟨Cx.leafR rm rc σq d.c.re, do
    let y ← d.r
    let yd := y + |d.c.im.toRat|
    let lo := d.c.re.toRat - yd
    let sl := sqrtLB (K f) lo
    if 0 < lo ∧ 0 < sl then
      let rs := rm.eQ * ulp f + yd / (2 * sl)
      let sc := s.toRat
      if 0 < sc - rs then
        pure (up (K f) (rm.eQ * ulp f + rc.eQ * ulp f / sc + (σq + rc.eQ * ulp f) * rs /
          (sc * (sc - rs))))
      else none
    else none⟩

/-! ### Soundness of each operation -/

theorem exact_holds (c : Cx f) : (exact c).Holds c.toC := by
  intro r hr; cases hr; simp [exact]

theorem ofInt_holds (n : ℤ) : (ofInt n : CB f).Holds n := by
  have h := exact_holds (Cx.ofInt n : Cx f)
  rwa [Cx.toC_ofInt] at h

theorem Holds.conjg {a : CB f} {z : ℂ} (h : a.Holds z) : a.conjg.Holds (starRingEnd ℂ z) := by
  intro r hr
  rw [CB.conjg, Cx.toC_conjg, ← map_sub, Complex.norm_conj]; exact h r hr

theorem Holds.neg {a : CB f} {z : ℂ} (h : a.Holds z) : a.neg.Holds (-z) := by
  intro r hr
  rw [CB.neg, Cx.toC_neg, show -z - -a.c.toC = -(z - a.c.toC) by ring, norm_neg]; exact h r hr

theorem Holds.add {a b : CB f} {z w : ℂ} (ha : a.Holds z) (hb : b.Holds w) :
    (a.add b).Holds (z + w) := by
  intro r hr
  cases hx : a.r with
  | none => simp [CB.add, hx] at hr
  | some x =>
  cases hy : b.r with
  | none => simp [CB.add, hx, hy] at hr
  | some y =>
  obtain rfl : x + y = r := by simpa [CB.add, hx, hy] using hr
  change ‖z + w - (a.c.add b.c).toC‖ ≤ _
  rw [Cx.toC_add, show z + w - (a.c.toC + b.c.toC) = (z - a.c.toC) + (w - b.c.toC) by ring]
  push_cast
  exact (norm_add_le _ _).trans (add_le_add (ha x hx) (hb y hy))

theorem Holds.sub {a b : CB f} {z w : ℂ} (ha : a.Holds z) (hb : b.Holds w) :
    (a.sub b).Holds (z - w) := by
  intro r hr
  cases hx : a.r with
  | none => simp [CB.sub, hx] at hr
  | some x =>
  cases hy : b.r with
  | none => simp [CB.sub, hx, hy] at hr
  | some y =>
  obtain rfl : x + y = r := by simpa [CB.sub, hx, hy] using hr
  change ‖z - w - (a.c.sub b.c).toC‖ ≤ _
  rw [Cx.toC_sub, show z - w - (a.c.toC - b.c.toC) = (z - a.c.toC) - (w - b.c.toC) by ring]
  push_cast
  exact (norm_sub_le _ _).trans (add_le_add (ha x hx) (hb y hy))

theorem Holds.mul (rm : RMode) {a b : CB f} {z w : ℂ} (ha : a.Holds z) (hb : b.Holds w) :
    (CB.mul rm a b).Holds (z * w) := by
  intro r hr
  cases hx : a.r with
  | none => simp only [CB.mul, hx] at hr; cases hr
  | some x =>
  cases hy : b.r with
  | none => simp only [CB.mul, hx, hy] at hr; cases hr
  | some y =>
  simp only [CB.mul, hx, hy] at hr; cases hr
  have h1 := ha x hx
  have h2 := hb y hy
  have hna := a.c.norm_le_nUB
  have hnb := b.c.norm_le_nUB
  have hzw : ‖z * w - a.c.toC * b.c.toC‖ ≤ a.c.nUB * y + b.c.nUB * x + x * y := calc
    _ = ‖a.c.toC * (w - b.c.toC) + b.c.toC * (z - a.c.toC) + (z - a.c.toC) * (w - b.c.toC)‖ := by
      congr 1; ring
    _ ≤ ‖a.c.toC‖ * ‖w - b.c.toC‖ + ‖b.c.toC‖ * ‖z - a.c.toC‖ +
        ‖z - a.c.toC‖ * ‖w - b.c.toC‖ := by
      rw [← norm_mul, ← norm_mul, ← norm_mul]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul hna h2 (norm_nonneg _) ((norm_nonneg _).trans hna))
        (mul_le_mul hnb h1 (norm_nonneg _) ((norm_nonneg _).trans hnb)))
        (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
  have hc := Errors.Fixed.cmul_err a.c.toC b.c.toC (a.c.mul rm b.c).toC (2 * (rm.e / 2 ^ f))
    (a.c.re.mul rm b.c.re).toReal (a.c.im.mul rm b.c.im).toReal (a.c.re.mul rm b.c.im).toReal
    (a.c.im.mul rm b.c.re).toReal ((Fx.mul_err rm _ _).trans_eq (by ring))
    ((Fx.mul_err rm _ _).trans_eq (by ring)) ((Fx.mul_err rm _ _).trans_eq (by ring))
    ((Fx.mul_err rm _ _).trans_eq (by ring)) (Fx.toReal_sub _ _) (Fx.toReal_add _ _)
  refine le_up_of hzw ((norm_sub_rev _ _).trans_le hc) ?_
  push_cast; linarith [sqrt_two_e_le (f := f) rm]

theorem Holds.half (rm : RMode) {a : CB f} {z : ℂ} (ha : a.Holds z) :
    (a.half rm).Holds (z / 2) := by
  intro r hr
  cases hx : a.r with
  | none => simp only [CB.half, hx] at hr; cases hr
  | some x =>
  simp only [CB.half, hx] at hr; cases hr
  refine le_up_of (X := a.c.toC / 2) (A := x / 2) ?_
    (norm_sub_le_sqrt_two (ε := rm.e / 2 ^ f) ?_ ?_) ?_
  · rw [← sub_div, norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_right (ha x hx) two_pos.le
  · rw [abs_sub_comm]; simpa [Cx.toC, Cx.half, CB.half] using Fx.half_err rm a.c.re
  · rw [abs_sub_comm]; simpa [Cx.toC, Cx.half, CB.half] using Fx.half_err rm a.c.im
  · push_cast; linarith [sqrt_two_e_le (f := f) rm]

theorem Holds.normSq (rm : RMode) {a : CB f} {z : ℂ} (ha : a.Holds z) :
    (a.normSq rm).Holds (z * starRingEnd ℂ z) := by
  intro r hr
  cases hx : a.r with
  | none => simp only [CB.normSq, hx] at hr; cases hr
  | some x =>
  simp only [CB.normSq, hx] at hr; cases hr
  have h1 := ha x hx
  have hx0 : (0 : ℝ) ≤ x := (norm_nonneg _).trans h1
  have hna := a.c.norm_le_nUB
  have hz : ‖z * conj z - a.c.toC * conj a.c.toC‖ ≤ (2 * a.c.nUB + x) * x := calc
    _ = ‖(z - a.c.toC) * conj (z - a.c.toC) + a.c.toC * conj (z - a.c.toC) +
        (z - a.c.toC) * conj a.c.toC‖ := by
      congr 1; simp only [map_sub]; ring
    _ ≤ x * x + a.c.nUB * x + x * a.c.nUB := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ?_ ?_)) ?_) <;> rw [norm_mul, Complex.norm_conj]
      · exact mul_le_mul h1 h1 (norm_nonneg _) hx0
      · exact mul_le_mul hna h1 (norm_nonneg _) ((norm_nonneg _).trans hna)
      · exact mul_le_mul h1 hna (norm_nonneg _) hx0
    _ = _ := by ring
  have e1 : a.c.toC * conj a.c.toC - (a.c.normSqR rm).toC =
      (((a.c.re.toReal * a.c.re.toReal - (a.c.re.mul rm a.c.re).toReal) +
        (a.c.im.toReal * a.c.im.toReal - (a.c.im.mul rm a.c.im).toReal) : ℝ) : ℂ) := by
    rw [show (a.c.normSqR rm).toC = (((a.c.re.mul rm a.c.re).toReal +
        (a.c.im.mul rm a.c.im).toReal : ℝ) : ℂ) from Complex.ext (Fx.toReal_add _ _)
        (by simp only [Cx.normSqR, Cx.toC, Complex.ofReal_im]; simp [Fx.toReal]),
      Complex.mul_conj, Complex.normSq_apply, ← Complex.ofReal_sub]
    simp only [Cx.toC]; push_cast; ring
  have hX : ‖a.c.toC * conj a.c.toC - (a.c.normSqR rm).toC‖ ≤ 2 * (rm.e / 2 ^ f) := by
    rw [e1, Complex.norm_real, Real.norm_eq_abs, two_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_sub_comm] <;>
      exact Fx.mul_err _ _ _
  refine le_up_of hz hX ?_
  push_cast; linarith [e_div_eq (f := f) rm]

theorem Holds.divR (rm : RMode) (dm : Cx.DivMode) {a d : CB f} {z w : ℂ} (ha : a.Holds z)
    (hd : d.Holds w) : (CB.divR rm dm a d).Holds (z / w) := by
  intro r hr
  cases hx : a.r with
  | none => simp only [CB.divR, hx] at hr; cases hr
  | some x =>
  cases hy : d.r with
  | none => simp only [CB.divR, hx, hy] at hr; cases hr
  | some y =>
  have h1 := ha x hx
  have hy0 : (0 : ℝ) ≤ y := (norm_nonneg _).trans (hd y hy)
  obtain ⟨δ, hδ⟩ : ∃ v : ℝ, (d.c.re.toRat : ℝ) = v := ⟨_, rfl⟩
  obtain ⟨yd, hyd⟩ : ∃ v : ℝ, (y : ℝ) + |(d.c.im.toRat : ℝ)| = v := ⟨_, rfl⟩
  have hyd0 : y ≤ yd := by rw [← hyd]; linarith [abs_nonneg (d.c.im.toRat : ℝ)]
  have hw : ‖w - (δ : ℂ)‖ ≤ yd := by
    have hc : ‖d.c.toC - (δ : ℂ)‖ ≤ |(d.c.im.toRat : ℝ)| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
      simp [← hδ, Cx.toC, Fx.toReal_eq_toRat]
    rw [← hyd]
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hd y hy) hc)
  have hzn : ‖z‖ ≤ a.c.nUB + x := by
    linarith [norm_sub_norm_le z a.c.toC, a.c.norm_le_nUB]
  cases dm <;>
  simp only [CB.divR, hx, hy, Option.mem_def, Option.bind_eq_bind, Option.bind_some] at hr <;>
  split_ifs at hr with hlo
  all_goals try cases hr
  all_goals
    have hlo' : 0 < δ - yd := by rw [← hδ, ← hyd]; exact_mod_cast hlo
    have hδ0 : 0 < δ := by linarith
    have hwn : δ - yd ≤ ‖w‖ := by
      have := norm_sub_norm_le (δ : ℂ) w
      rw [Complex.norm_real, Real.norm_of_nonneg hδ0.le, norm_sub_rev] at this
      linarith
    have hw0 : w ≠ 0 := norm_pos_iff.1 (by linarith)
    have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ0.ne'
    have hD0 : d.c.re.m ≠ 0 := fun h0 => by
      rw [← hδ] at hδ0; simp [Fx.toRat, h0] at hδ0
    have hDr : d.c.re.toReal = δ := (Fx.toReal_eq_toRat _).trans hδ
    have hmain : ‖z / w - a.c.toC / δ‖ ≤ x / δ + (a.c.nUB + x) * yd / (δ * (δ - yd)) := by
      rw [show z / w - a.c.toC / δ = (z - a.c.toC) / δ + z * ((δ : ℂ) - w) / (w * δ) by
        field_simp; ring]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hδ0.le]
        exact div_le_div_of_nonneg_right h1 hδ0.le
      · rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ0.le,
          norm_sub_rev]
        refine div_le_div₀ (mul_nonneg ((norm_nonneg _).trans hzn) (hy0.trans hyd0))
          (mul_le_mul hzn hw (norm_nonneg _) ((norm_nonneg _).trans hzn)) (mul_pos hδ0 hlo') ?_
        rw [mul_comm δ]; exact mul_le_mul_of_nonneg_right hwn hδ0.le
  · refine le_up_of hmain (norm_sub_le_sqrt_two (ε := rm.e / 2 ^ f) ?_ ?_) ?_
    · rw [Complex.div_ofReal_re, abs_sub_comm, ← hDr]; exact Fx.div_err rm _ _ hD0
    · rw [Complex.div_ofReal_im, abs_sub_comm, ← hDr]; exact Fx.div_err rm _ _ hD0
    · subst hδ hyd; push_cast; linarith [sqrt_two_e_le (f := f) rm]
  · have hi := Fx.div_err rm (Fx.ofInt 1) d.c.re hD0
    rw [Fx.toReal_ofInt, Int.cast_one, hDr, abs_sub_comm] at hi
    set i := (Fx.ofInt 1 : Fx f).div rm d.c.re
    have hr1 : ‖a.c.toC / δ - a.c.toC * (i.toReal : ℂ)‖ ≤ a.c.nUB * (rm.e / 2 ^ f) := by
      rw [show a.c.toC / δ - a.c.toC * (i.toReal : ℂ) = a.c.toC * ((1 / δ - i.toReal : ℝ) : ℂ) by
        push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul a.c.norm_le_nUB hi (abs_nonneg _) ((norm_nonneg _).trans a.c.norm_le_nUB)
    have hr2 : ‖a.c.toC * (i.toReal : ℂ) - (a.c.divR rm .invMul d.c.re).toC‖ ≤
        √2 * (rm.e / 2 ^ f) := by
      refine norm_sub_le_sqrt_two ?_ ?_
      · rw [Complex.re_mul_ofReal, abs_sub_comm]; exact Fx.mul_err rm _ _
      · rw [Complex.im_mul_ofReal, abs_sub_comm]; exact Fx.mul_err rm _ _
    refine le_up_of hmain ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hr1 hr2)) ?_
    have h2 := sqrt_two_e_le (f := f) rm
    rw [e_div_eq rm] at h2 ⊢
    subst hδ hyd; push_cast; linarith [h2]

theorem Holds.leaf (rm rc : RMode) (σq : ℚ) (hσ : 0 ≤ σq) {d : CB f} {w : ℂ} (hd : d.Holds w) :
    (CB.leaf rm rc σq d).Holds (((σq : ℝ) / √w.re : ℝ) : ℂ) := by
  intro r hr
  cases hy : d.r with
  | none => simp only [CB.leaf, hy] at hr; cases hr
  | some y =>
  simp only [CB.leaf, hy, Option.mem_def, Option.bind_eq_bind, Option.bind_some] at hr
  split_ifs at hr with h1 h2
  all_goals try cases hr
  have hy0 : (0 : ℝ) ≤ y := (norm_nonneg _).trans (hd y hy)
  have hσ0 : (0 : ℝ) ≤ σq := by exact_mod_cast hσ
  obtain ⟨D, hD⟩ : ∃ v : ℝ, (d.c.re.toRat : ℝ) = v := ⟨_, rfl⟩
  obtain ⟨yd, hyd⟩ : ∃ v : ℝ, (y : ℝ) + |(d.c.im.toRat : ℝ)| = v := ⟨_, rfl⟩
  obtain ⟨sl, hsl⟩ : ∃ v : ℝ,
    (sqrtLB (K f) (d.c.re.toRat - (y + |d.c.im.toRat|)) : ℝ) = v := ⟨_, rfl⟩
  obtain ⟨sr, hsr⟩ : ∃ v : ℝ, ((d.c.re.sqrt rm).toRat : ℝ) = v := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ v : ℝ, (rm.eQ : ℝ) * ulp f = v := ⟨_, rfl⟩
  obtain ⟨εc, hεc⟩ : ∃ v : ℝ, (rc.eQ : ℝ) * ulp f = v := ⟨_, rfl⟩
  have hyy : (y : ℝ) ≤ yd := by rw [← hyd]; linarith [abs_nonneg (d.c.im.toRat : ℝ)]
  have hε0 : 0 ≤ ε := by rw [← hε, ← e_div_eq]; exact div_nonneg rm.e_nonneg (by positivity)
  have hεc0 : 0 ≤ εc := by rw [← hεc, ← e_div_eq]; exact div_nonneg rc.e_nonneg (by positivity)
  have hlo : 0 < D - yd := by rw [← hD, ← hyd]; exact_mod_cast h1.1
  have hsl0 : 0 < sl := by rw [← hsl]; exact_mod_cast h1.2
  have hslle : sl ≤ √(D - yd) := by
    have := sqrtLB_le_sqrt (K f) (d.c.re.toRat - (y + |d.c.im.toRat|))
    push_cast at this; rwa [hsl, hD, hyd] at this
  have hw : |w.re - D| ≤ y := by
    have := (Complex.abs_re_le_norm (w - d.c.toC)).trans (hd y hy)
    rwa [Complex.sub_re, show d.c.toC.re = D from (Fx.toReal_eq_toRat _).trans hD] at this
  obtain ⟨hw1, hw2⟩ := abs_le.1 hw
  have hsw : sl ≤ √w.re := hslle.trans (Real.sqrt_le_sqrt (by linarith))
  have hsD : sl ≤ √D := hslle.trans (Real.sqrt_le_sqrt (by linarith))
  have h3 : |√D - √w.re| ≤ yd / (2 * sl) := by
    rw [le_div_iff₀ (by linarith)]
    have e : (√D - √w.re) * (√D + √w.re) = D - w.re := by
      linear_combination Real.sq_sqrt (by linarith : 0 ≤ D) - Real.sq_sqrt (by linarith : 0 ≤ w.re)
    calc |√D - √w.re| * (2 * sl) ≤ |√D - √w.re| * (√D + √w.re) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |D - w.re| := by rw [← abs_of_pos (by linarith : 0 < √D + √w.re), ← abs_mul, e]
      _ ≤ yd := by rw [abs_sub_comm]; linarith
  have hsq : |sr - √D| ≤ ε := by
    have := Fx.sqrt_err rm d.c.re
    rwa [Fx.toReal_eq_toRat (d.c.re.sqrt rm), Fx.toReal_eq_toRat d.c.re, hsr, hD, e_div_eq,
      hε] at this
  have h4 : |sr - √w.re| ≤ ε + yd / (2 * sl) := (abs_sub_le _ _ _).trans (add_le_add hsq h3)
  have hrs : 0 < sr - (ε + yd / (2 * sl)) := by
    rw [← hsr, ← hε, ← hyd, ← hsl]; exact_mod_cast h2
  have hρ0 : 0 ≤ ε + yd / (2 * sl) := add_nonneg hε0 (div_nonneg (hy0.trans hyy) (by linarith))
  have hsw' : sr - (ε + yd / (2 * sl)) ≤ √w.re := by linarith [(abs_le.1 h4).2]
  have hsr0 : 0 < sr := by linarith
  have hsw0 : 0 < √w.re := by linarith
  have hm : (d.c.re.sqrt rm).m ≠ 0 := fun h0 => by
    rw [← hsr] at hsr0; simp [Fx.toRat, h0] at hsr0
  have hσ' : |(Fx.ofRat rc σq : Fx f).toReal - σq| ≤ εc := by
    rw [← hεc, ← e_div_eq]; exact Fx.ofRat_err rc σq
  have hq : |((Fx.ofRat rc σq : Fx f).div rm (d.c.re.sqrt rm)).toReal -
      (Fx.ofRat rc σq : Fx f).toReal / sr| ≤ ε := by
    have := Fx.div_err rm (Fx.ofRat rc σq : Fx f) (d.c.re.sqrt rm) hm
    rwa [Fx.toReal_eq_toRat (d.c.re.sqrt rm), hsr, e_div_eq, hε] at this
  have hc : (CB.leaf rm rc σq d).c.toC =
      (((Fx.ofRat rc σq : Fx f).div rm (d.c.re.sqrt rm)).toReal : ℂ) :=
    Complex.ext rfl (by simp only [CB.leaf, Cx.leafR, Cx.toC, Complex.ofReal_im]; simp [Fx.toReal])
  set σt := (Fx.ofRat rc σq : Fx f).toReal
  have hmain : |(σq : ℝ) / √w.re - σt / sr| ≤ εc / sr +
      ((σq : ℝ) + εc) * (ε + yd / (2 * sl)) / (sr * (sr - (ε + yd / (2 * sl)))) := by
    rw [abs_sub_comm, show σt / sr - σq / √w.re =
      (σt - σq) / sr + σq * (√w.re - sr) / (sr * √w.re) by field_simp; ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hsr0]; exact div_le_div_of_nonneg_right hσ' hsr0.le
    · rw [abs_div, abs_mul, abs_of_nonneg hσ0, abs_of_pos (mul_pos hsr0 hsw0), abs_sub_comm]
      exact div_le_div₀ (mul_nonneg (by linarith) hρ0)
        (mul_le_mul (by linarith) h4 (abs_nonneg _) (by linarith)) (mul_pos hsr0 hrs)
        (mul_le_mul_of_nonneg_left hsw' hsr0.le)
  rw [hc]
  refine le_up_of (X := ((σt / sr : ℝ) : ℂ)) (A := εc / sr +
      ((σq : ℝ) + εc) * (ε + yd / (2 * sl)) / (sr * (sr - (ε + yd / (2 * sl))))) (B := ε) ?_ ?_ ?_
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hmain
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hq
  · subst hD hyd hsl hsr hε hεc; push_cast; linarith

theorem Holds.congr {a : CB f} {z w : ℂ} (h : a.Holds z) (e : z = w) : a.Holds w := e ▸ h

end CB

end FalconPrecision.Exec
