/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Executable Type 1 fixed-point arithmetic over `Int`

ePrint 2026/1531 §3.4 (pp. 14-16): a value of format `Q_{i,f}` is an integer `X` read as `X·2⁻ᶠ`,
in `[-2^(i-1), 2^(i-1) - 2⁻ᶠ]` (`i` counts the sign bit); addition and subtraction are integer
operations; the product is `mulf(X, Y) = ⌊XY/2ᶠ⌉`, ties to even in the reference code, ties
towards `+∞` in the bias-and-floor variant `(XY + 2^(f-1)) >> f` (p. 15); Type 1 `i.f` uses one
`i` and one `f` for every operand (p. 16); the C code is Type 1 `64.64` (§6.3, p. 35).

`Fx f` is such a value with `f` fractional bits and no word size: the integer range is the
predicate `InRange i`, so `64.64` and `32.64` are the same operations at `f = 64` with the ranges
`InRange 64` and `InRange 32`. `wrap k` is the value of a `(k+1)`-bit two's-complement word; on
values in range it is the identity (`InRange.wrap`); that a word implementation of each operation
computes the same integers is not proved here.

The rounding rule `RMode` is a parameter: `floor`, round to nearest with ties to even, ties up
(`+∞`), ties away from zero. `rdiv r n d` rounds `n/d` (`d > 0`) by integer division;
`rdiv_eq_rnd` equates it with the real rounding `rnd r (n/d)`, within `e r` (`1` for `floor`,
`1/2` otherwise). Operations: `add`, `sub`, `neg` (exact), `mulTo`/`mul` (one rounding), `half`,
`div` (the quotient rounded once), `sqrt` (the root rounded once; to nearest there are no ties),
`ofInt`, `toInt`, `ofRat`. §3.4 items 4-5 (p. 16) compute division and square root by
Newton–Raphson from seeds and iteration counts the paper does not pin; those variants are not
defined here. `toReal` is the value in `ℝ` (noncomputable, as every map into `ℝ`); `toRat` is its
computable twin. -/

@[expose] public section

namespace FalconPrecision.Exec

/-- A rounding rule for a quotient. -/
inductive RMode where
  | floor
  | halfEven
  | halfUp
  | halfAway
  deriving DecidableEq, Repr

namespace RMode

/-- The integer chosen at a tie `k + 1/2`. -/
def tie : RMode → ℤ → ℤ
  | floor, k => k
  | halfEven, k => if k % 2 = 0 then k else k + 1
  | halfUp, k => k + 1
  | halfAway, k => if 0 ≤ k then k + 1 else k

/-- The integer chosen for `k + t` (`0 ≤ t < 1`) from `compareOfLessAndEq (2t) 1`. -/
def pick (r : RMode) (k : ℤ) : Ordering → ℤ
  | .lt => k
  | .eq => r.tie k
  | .gt => if r = floor then k else k + 1

/-- `n / d` rounded to an integer by `r` (for `d > 0`). -/
def rdiv (r : RMode) (n d : ℤ) : ℤ := r.pick (n / d) (compareOfLessAndEq (2 * (n % d)) d)

/-- A real rounded to an integer by `r`. -/
noncomputable def rnd (r : RMode) (y : ℝ) : ℤ := r.pick ⌊y⌋ (compareOfLessAndEq (2 * Int.fract y) 1)

/-- The error bound of `r`: `1` for `floor`, `1/2` for the nearest rules. -/
noncomputable def e (r : RMode) : ℝ := if r = floor then 1 else 1 / 2

theorem tie_cases (r : RMode) (k : ℤ) : r.tie k = k ∨ r.tie k = k + 1 := by
  cases r <;> simp only [tie, true_or, or_true] <;> split_ifs <;> simp

theorem half_le_e (r : RMode) : 1 / 2 ≤ r.e := by
  unfold e; split_ifs <;> norm_num

theorem rnd_err (r : RMode) (y : ℝ) : |(r.rnd y : ℝ) - y| ≤ r.e := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  have hy := Int.floor_add_fract y
  have he := r.half_le_e
  unfold rnd compareOfLessAndEq
  split_ifs with ha hb
  · simp only [pick]; rw [abs_le]; constructor <;> linarith
  · simp only [pick]
    rcases r.tie_cases ⌊y⌋ with h | h <;> rw [h] <;> push_cast <;> rw [abs_le] <;>
      constructor <;> linarith
  · have h2 : 1 < 2 * Int.fract y := lt_of_le_of_ne (not_lt.1 ha) (Ne.symm hb)
    simp only [pick]
    split_ifs with hr
    · subst hr
      rw [show floor.e = 1 by simp [e], abs_le]; constructor <;> linarith
    · push_cast; rw [abs_le]; constructor <;> linarith

theorem rnd_near {r : RMode} (hr : r ≠ floor) (y : ℝ) : |(r.rnd y : ℝ) - y| ≤ 1 / 2 :=
  (r.rnd_err y).trans_eq (by simp [e, hr])

theorem rnd_floor (y : ℝ) : floor.rnd y = ⌊y⌋ := by
  unfold rnd; cases compareOfLessAndEq (2 * Int.fract y) 1 <;> simp [pick, tie]

/-- **Integer rounding is real rounding.** -/
theorem rdiv_eq_rnd (r : RMode) (n d : ℤ) (hd : 0 < d) : r.rdiv n d = r.rnd ((n : ℝ) / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (n : ℝ) = d * ((n / d : ℤ) : ℝ) + ((n % d : ℤ) : ℝ) := by
    have : n = d * (n / d) + n % d := by rw [Int.emod_def]; ring
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ ((n % d : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg n hd.ne'
  have h1 : ((n % d : ℤ) : ℝ) < d := by exact_mod_cast Int.emod_lt_of_pos n hd
  have hfl : ⌊(n : ℝ) / d⌋ = n / d := by
    rw [Int.floor_eq_iff, le_div_iff₀ hd', div_lt_iff₀ hd']; constructor <;> linarith
  have hfr : Int.fract ((n : ℝ) / d) = ((n % d : ℤ) : ℝ) / d := by
    rw [← Int.self_sub_floor, hfl, eq_div_iff hd'.ne', sub_mul, div_mul_cancel₀ _ hd'.ne']
    linarith
  have hlt : 2 * (n % d) < d ↔ 2 * (((n % d : ℤ) : ℝ) / d) < 1 := by
    rw [← mul_div_assoc, div_lt_one hd']; norm_cast
  have heq : 2 * (n % d) = d ↔ 2 * (((n % d : ℤ) : ℝ) / d) = 1 := by
    rw [← mul_div_assoc, div_eq_one_iff_eq hd'.ne']; norm_cast
  unfold rdiv rnd
  rw [hfl, hfr]
  congr 1
  simp only [compareOfLessAndEq, hlt, heq]

/-- `√n` (`n ≥ 0`) rounded by `r`: `floor` gives `Nat.sqrt`, the nearest rules agree (no ties);
`0` for `n < 0`. -/
def isqrt (r : RMode) (n : ℤ) : ℤ :=
  if r ≠ floor ∧ n.toNat.sqrt * n.toNat.sqrt + n.toNat.sqrt < n.toNat then n.toNat.sqrt + 1
  else n.toNat.sqrt

theorem isqrt_err (r : RMode) (n : ℤ) : |(r.isqrt n : ℝ) - √(n.toNat : ℝ)| ≤ r.e := by
  have hs1 : (n.toNat.sqrt : ℝ) ≤ √(n.toNat : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hs2 : √(n.toNat : ℝ) < n.toNat.sqrt + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have he := r.half_le_e
  unfold isqrt
  split_ifs with h
  · obtain ⟨-, hlt⟩ := h
    have h3 : ((n.toNat.sqrt : ℝ) + 1 / 2) < √(n.toNat : ℝ) := by
      rw [Real.lt_sqrt (by positivity)]
      have : (n.toNat.sqrt : ℝ) * n.toNat.sqrt + n.toNat.sqrt + 1 ≤ n.toNat := by
        exact_mod_cast hlt
      linarith [show ((n.toNat.sqrt : ℝ) + 1 / 2) ^ 2 =
          n.toNat.sqrt * n.toNat.sqrt + n.toNat.sqrt + 1 / 4 by ring]
    push_cast; rw [abs_le]; constructor <;> linarith
  · by_cases hr : r = floor
    · subst hr
      rw [show floor.e = 1 by simp [e], Int.cast_natCast, abs_le]; constructor <;> linarith
    · have hle : n.toNat ≤ n.toNat.sqrt * n.toNat.sqrt + n.toNat.sqrt := by
        rw [not_and, not_lt] at h; exact h hr
      have h3 : √(n.toNat : ℝ) < n.toNat.sqrt + 1 / 2 := by
        rw [Real.sqrt_lt' (by positivity)]
        have : (n.toNat : ℝ) ≤ n.toNat.sqrt * n.toNat.sqrt + n.toNat.sqrt := by exact_mod_cast hle
        linarith [show ((n.toNat.sqrt : ℝ) + 1 / 2) ^ 2 =
            n.toNat.sqrt * n.toNat.sqrt + n.toNat.sqrt + 1 / 4 by ring]
      rw [Int.cast_natCast, abs_le]; constructor <;> linarith

/-- `floor` is not within `1/2`: `⌊3/4⌋ = 0`. -/
theorem not_isRound_floor : ¬ |(floor.rnd (3 / 4) : ℝ) - 3 / 4| ≤ 1 / 2 := by
  rw [rnd_floor, show ⌊(3 / 4 : ℝ)⌋ = 0 from Int.floor_eq_iff.2 ⟨by norm_num, by norm_num⟩]
  norm_num [abs_of_neg]

end RMode

/-- A fixed-point value with `f` fractional bits: the integer `m` stands for `m·2⁻ᶠ`. -/
structure Fx (f : ℕ) where
  m : ℤ
  deriving DecidableEq, Repr

namespace Fx

variable {f g : ℕ}

/-- The value in `ℝ`. -/
noncomputable def toReal (x : Fx f) : ℝ := x.m / 2 ^ f

/-- The value in `ℚ`. -/
def toRat (x : Fx f) : ℚ := x.m / 2 ^ f

/-- Exact sum. -/
def add (a b : Fx f) : Fx f := ⟨a.m + b.m⟩

/-- Exact difference. -/
def sub (a b : Fx f) : Fx f := ⟨a.m - b.m⟩

/-- Exact negation. -/
def neg (a : Fx f) : Fx f := ⟨-a.m⟩

/-- The integer `n`. -/
def ofInt (n : ℤ) : Fx f := ⟨n * 2 ^ f⟩

/-- The value rounded to an integer. -/
def toInt (r : RMode) (x : Fx f) : ℤ := r.rdiv x.m (2 ^ f)

/-- A rational rounded to `f` fractional bits. -/
def ofRat (r : RMode) (q : ℚ) : Fx f := ⟨r.rdiv (q.num * 2 ^ f) q.den⟩

/-- Product with an operand of `g` fractional bits, rounded once to `f` fractional bits. -/
def mulTo (r : RMode) (a : Fx f) (b : Fx g) : Fx f := ⟨r.rdiv (a.m * b.m) (2 ^ g)⟩

/-- Product rounded once: `mulf(X, Y) = ⌊XY/2ᶠ⌉` (ePrint 2026/1531 §3.4 item 2, p. 15). -/
def mul (r : RMode) (a b : Fx f) : Fx f := mulTo r a b

/-- `a/2` rounded once. -/
def half (r : RMode) (a : Fx f) : Fx f := ⟨r.rdiv a.m 2⟩

/-- Quotient rounded once (divisor nonzero). -/
def div (r : RMode) (a b : Fx f) : Fx f :=
  if 0 < b.m then ⟨r.rdiv (a.m * 2 ^ f) b.m⟩ else ⟨r.rdiv (-(a.m * 2 ^ f)) (-b.m)⟩

/-- Square root rounded once (`0` for negative values). -/
def sqrt (r : RMode) (a : Fx f) : Fx f := ⟨r.isqrt (a.m * 2 ^ f)⟩

/-- Integer range of `i` bits including the sign bit: `-2^(i-1) ≤ x < 2^(i-1)`. -/
def InRange (i : ℕ) (x : Fx f) : Prop := -(2 : ℤ) ^ (i + f) ≤ 2 * x.m ∧ 2 * x.m < 2 ^ (i + f)

instance (i : ℕ) (x : Fx f) : Decidable (x.InRange i) := inferInstanceAs (Decidable (_ ∧ _))

/-- The value of a `(k+1)`-bit two's-complement word holding the low bits of `n`. -/
def wrap (k : ℕ) (n : ℤ) : ℤ := n.bmod (2 ^ (k + 1))

theorem toReal_eq_toRat (x : Fx f) : x.toReal = x.toRat := by
  simp [toReal, toRat]

theorem toReal_add (a b : Fx f) : (a.add b).toReal = a.toReal + b.toReal := by
  simp only [toReal, add]; push_cast; ring

theorem toReal_sub (a b : Fx f) : (a.sub b).toReal = a.toReal - b.toReal := by
  simp only [toReal, sub]; push_cast; ring

theorem toReal_neg (a : Fx f) : a.neg.toReal = -a.toReal := by
  simp only [toReal, neg]; push_cast; ring

theorem toReal_ofInt (n : ℤ) : (ofInt n : Fx f).toReal = n := by
  simp only [toReal, ofInt]; push_cast; field_simp

theorem toInt_eq (r : RMode) (x : Fx f) : x.toInt r = r.rnd x.toReal := by
  rw [toInt, r.rdiv_eq_rnd _ _ (by positivity), toReal]; push_cast; rfl

theorem toReal_ofRat (r : RMode) (q : ℚ) :
    (ofRat r q : Fx f).toReal = r.rnd (q * 2 ^ f) / 2 ^ f := by
  simp only [toReal, ofRat]
  rw [r.rdiv_eq_rnd _ _ (by exact_mod_cast q.pos), Rat.cast_def]; push_cast; ring_nf

theorem toReal_mulTo (r : RMode) (a : Fx f) (b : Fx g) :
    (a.mulTo r b).toReal = r.rnd (a.toReal * b.toReal * 2 ^ f) / 2 ^ f := by
  simp only [toReal, mulTo]
  rw [r.rdiv_eq_rnd _ _ (by positivity)]; push_cast; field_simp

theorem toReal_mul (r : RMode) (a b : Fx f) :
    (a.mul r b).toReal = r.rnd (a.toReal * b.toReal * 2 ^ f) / 2 ^ f :=
  toReal_mulTo r a b

theorem toReal_half (r : RMode) (a : Fx f) :
    (a.half r).toReal = r.rnd (a.toReal / 2 * 2 ^ f) / 2 ^ f := by
  simp only [toReal, half]
  rw [r.rdiv_eq_rnd _ _ (by norm_num)]; push_cast; field_simp

theorem toReal_div (r : RMode) (a b : Fx f) (hb : b.m ≠ 0) :
    (a.div r b).toReal = r.rnd (a.toReal / b.toReal * 2 ^ f) / 2 ^ f := by
  have hb' : (b.m : ℝ) ≠ 0 := by exact_mod_cast hb
  simp only [toReal, div]
  split_ifs with h
  · rw [r.rdiv_eq_rnd _ _ h]; push_cast; field_simp
  · rw [r.rdiv_eq_rnd _ _ (by omega)]; push_cast; field_simp

theorem toReal_sqrt (r : RMode) (a : Fx f) :
    (a.sqrt r).toReal = r.isqrt (a.m * 2 ^ f) / 2 ^ f := rfl

theorem abs_div_pow_sub (x y : ℝ) : |x / 2 ^ f - y| = |x - y * 2 ^ f| / 2 ^ f := by
  have h : (0 : ℝ) < 2 ^ f := by positivity
  rw [show x / 2 ^ f - y = (x - y * 2 ^ f) / 2 ^ f by field_simp, abs_div, abs_of_pos h]

theorem rnd_scale_err (r : RMode) (y : ℝ) :
    |(r.rnd (y * 2 ^ f) : ℝ) / 2 ^ f - y| ≤ r.e / 2 ^ f := by
  rw [abs_div_pow_sub]; exact div_le_div_of_nonneg_right (r.rnd_err _) (by positivity)

theorem toInt_err (r : RMode) (x : Fx f) : |(x.toInt r : ℝ) - x.toReal| ≤ r.e := by
  rw [toInt_eq]; exact r.rnd_err _

theorem ofRat_err (r : RMode) (q : ℚ) : |(ofRat r q : Fx f).toReal - q| ≤ r.e / 2 ^ f := by
  rw [toReal_ofRat]; exact rnd_scale_err r _

/-- **Product error.** -/
theorem mulTo_err (r : RMode) (a : Fx f) (b : Fx g) :
    |(a.mulTo r b).toReal - a.toReal * b.toReal| ≤ r.e / 2 ^ f := by
  rw [toReal_mulTo]; exact rnd_scale_err r _

theorem mul_err (r : RMode) (a b : Fx f) :
    |(a.mul r b).toReal - a.toReal * b.toReal| ≤ r.e / 2 ^ f :=
  mulTo_err r a b

theorem half_err (r : RMode) (a : Fx f) : |(a.half r).toReal - a.toReal / 2| ≤ r.e / 2 ^ f := by
  rw [toReal_half]; exact rnd_scale_err r _

/-- **Quotient error.** -/
theorem div_err (r : RMode) (a b : Fx f) (hb : b.m ≠ 0) :
    |(a.div r b).toReal - a.toReal / b.toReal| ≤ r.e / 2 ^ f := by
  rw [toReal_div r a b hb]; exact rnd_scale_err r _

theorem sqrt_toNat (a : Fx f) : √(((a.m * 2 ^ f).toNat : ℕ) : ℝ) = √a.toReal * 2 ^ f := by
  rcases le_or_gt 0 a.m with h | h
  · have e : (((a.m * 2 ^ f).toNat : ℕ) : ℝ) = a.toReal * (2 ^ f * 2 ^ f) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by positivity), toReal]; push_cast
      field_simp
    rw [e, Real.sqrt_mul' _ (by positivity), Real.sqrt_mul_self (by positivity)]
  · have h0 : (a.m * 2 ^ f).toNat = 0 :=
      Int.toNat_eq_zero.2 (mul_neg_of_neg_of_pos h (by positivity)).le
    have h1 : a.toReal ≤ 0 := by
      rw [toReal]; exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h.le) (by positivity)
    rw [h0, Real.sqrt_eq_zero_of_nonpos h1]; simp

/-- **Square-root error.** -/
theorem sqrt_err (r : RMode) (a : Fx f) : |(a.sqrt r).toReal - √a.toReal| ≤ r.e / 2 ^ f := by
  rw [toReal_sqrt, abs_div_pow_sub, ← sqrt_toNat]
  exact div_le_div_of_nonneg_right (r.isqrt_err _) (by positivity)

theorem inRange_iff {i : ℕ} (x : Fx f) :
    x.InRange i ↔ -(2 : ℝ) ^ i ≤ 2 * x.toReal ∧ 2 * x.toReal < 2 ^ i := by
  have h2 : (0 : ℝ) < 2 ^ f := by positivity
  simp only [InRange, toReal]
  rw [← mul_div_assoc, le_div_iff₀ h2, div_lt_iff₀ h2, neg_mul, ← pow_add]
  norm_cast

theorem InRange.mono {i j : ℕ} {x : Fx f} (h : x.InRange i) (hij : i ≤ j) : x.InRange j := by
  rw [inRange_iff] at h ⊢
  have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij
  constructor <;> linarith [h.1, h.2]

/-- A value within `c` of `y` is in range `i` when `2(|y| + c) < 2^i`. -/
theorem inRange_of_err {i : ℕ} {x : Fx f} {y c : ℝ} (hx : |x.toReal - y| ≤ c)
    (h : 2 * (|y| + c) < 2 ^ i) : x.InRange i := by
  rw [inRange_iff]
  have := abs_le.1 hx
  constructor <;> linarith [neg_abs_le y, le_abs_self y]

theorem add_inRange {i : ℕ} {a b : Fx f} (ha : a.InRange i) (hb : b.InRange i) :
    (a.add b).InRange (i + 1) := by
  rw [inRange_iff] at ha hb ⊢; rw [toReal_add, pow_succ]; constructor <;> linarith [ha, hb]

theorem sub_inRange {i : ℕ} {a b : Fx f} (ha : a.InRange i) (hb : b.InRange i) :
    (a.sub b).InRange (i + 1) := by
  rw [inRange_iff] at ha hb ⊢; rw [toReal_sub, pow_succ]; constructor <;> linarith [ha, hb]

theorem neg_inRange {i : ℕ} {a : Fx f} (ha : a.InRange i) : a.neg.InRange (i + 1) := by
  rw [inRange_iff] at ha ⊢
  rw [toReal_neg, pow_succ]
  have := pow_pos (by norm_num : (0 : ℝ) < 2) i
  constructor <;> linarith [ha]

theorem mulTo_inRange {i : ℕ} (r : RMode) (a : Fx f) (b : Fx g)
    (h : 2 * (|a.toReal * b.toReal| + r.e / 2 ^ f) < 2 ^ i) : (a.mulTo r b).InRange i :=
  inRange_of_err (mulTo_err r a b) h

theorem mul_inRange {i : ℕ} (r : RMode) (a b : Fx f)
    (h : 2 * (|a.toReal * b.toReal| + r.e / 2 ^ f) < 2 ^ i) : (a.mul r b).InRange i :=
  inRange_of_err (mul_err r a b) h

theorem half_inRange {i : ℕ} (r : RMode) (a : Fx f)
    (h : 2 * (|a.toReal / 2| + r.e / 2 ^ f) < 2 ^ i) : (a.half r).InRange i :=
  inRange_of_err (half_err r a) h

theorem div_inRange {i : ℕ} (r : RMode) (a b : Fx f) (hb : b.m ≠ 0)
    (h : 2 * (|a.toReal / b.toReal| + r.e / 2 ^ f) < 2 ^ i) : (a.div r b).InRange i :=
  inRange_of_err (div_err r a b hb) h

theorem sqrt_inRange {i : ℕ} (r : RMode) (a : Fx f)
    (h : 2 * (|√a.toReal| + r.e / 2 ^ f) < 2 ^ i) : (a.sqrt r).InRange i :=
  inRange_of_err (sqrt_err r a) h

theorem ofRat_inRange {i : ℕ} (r : RMode) (q : ℚ)
    (h : 2 * (|(q : ℝ)| + r.e / 2 ^ f) < 2 ^ i) : (ofRat r q : Fx f).InRange i :=
  inRange_of_err (ofRat_err r q) h

theorem wrap_of_bound {k : ℕ} {n : ℤ} (h1 : -2 ^ k ≤ n) (h2 : n < 2 ^ k) : wrap k n = n :=
  Int.bmod_eq_of_le_mul_two (by push_cast; rw [pow_succ]; omega)
    (by push_cast; rw [pow_succ]; omega)

/-- **Word size does not matter in range.** A value in `InRange (i+1)` is unchanged by an
`(i+1+f)`-bit word. -/
theorem InRange.wrap {i : ℕ} {x : Fx f} (h : x.InRange (i + 1)) : Fx.wrap (i + f) x.m = x.m := by
  have e : (2 : ℤ) ^ (i + 1 + f) = 2 * 2 ^ (i + f) := by
    rw [show i + 1 + f = (i + f) + 1 by omega, pow_succ]; ring
  obtain ⟨h1, h2⟩ := h
  rw [e] at h1 h2
  exact wrap_of_bound (by omega) (by omega)

/-- A value in range `i + 1` has the same two's-complement value in every word of at least
`i + 1 + f` bits. -/
theorem InRange.wrap_eq {i j : ℕ} {x : Fx f} (h : x.InRange (i + 1)) (hij : i ≤ j) :
    Fx.wrap (j + f) x.m = Fx.wrap (i + f) x.m := by
  rw [h.wrap, (h.mono (by omega : i + 1 ≤ j + 1)).wrap]

end Fx

/-- A complex fixed-point value. -/
structure Cx (f : ℕ) where
  re : Fx f
  im : Fx f
  deriving DecidableEq, Repr

namespace Cx

variable {f : ℕ}

/-- The value in `ℂ`. -/
noncomputable def toC (z : Cx f) : ℂ := ⟨z.re.toReal, z.im.toReal⟩

/-- Exact sum. -/
def add (z w : Cx f) : Cx f := ⟨z.re.add w.re, z.im.add w.im⟩

/-- Exact difference. -/
def sub (z w : Cx f) : Cx f := ⟨z.re.sub w.re, z.im.sub w.im⟩

/-- Exact negation. -/
def neg (z : Cx f) : Cx f := ⟨z.re.neg, z.im.neg⟩

/-- Complex product: four real products, each rounded once, combined exactly. -/
def mul (r : RMode) (z w : Cx f) : Cx f :=
  ⟨(z.re.mul r w.re).sub (z.im.mul r w.im), (z.re.mul r w.im).add (z.im.mul r w.re)⟩

/-- `z/2`, each part rounded once. -/
def half (r : RMode) (z : Cx f) : Cx f := ⟨z.re.half r, z.im.half r⟩

/-- `1/q` (`q = 12289`) rounded to 77 fractional bits (ePrint 2026/2431 §3.4, "Wide 1/q");
`2⁶³ < qinv < 2⁶⁴`: an unsigned 64-bit word, not an `i.64` operand. -/
def qinv (r : RMode) : Fx 77 := ⟨r.rdiv (2 ^ 77) 12289⟩

/-- The product by `qinv`, each part rounded once to 64 fractional bits. -/
def divq (r : RMode) (z : Cx 64) : Cx 64 := ⟨z.re.mulTo r (qinv r), z.im.mulTo r (qinv r)⟩

theorem toReal_qinv (r : RMode) : (qinv r).toReal = r.rnd (1 / 12289 * 2 ^ 77) / 2 ^ 77 := by
  simp only [Fx.toReal, qinv]
  rw [r.rdiv_eq_rnd _ _ (by norm_num)]; push_cast; ring_nf

end Cx

end FalconPrecision.Exec
