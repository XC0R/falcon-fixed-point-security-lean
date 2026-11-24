/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerZ
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Numeric facts about SamplerZ's arithmetic

ApproxExp (spec Alg. 13, p. 42) is the Horner evaluation `pAE` of a degree-12 polynomial with
floors: `|pAE ζ - exp(-ζ)| ≤ 2⁻⁴⁷` on `[0, 111/160]` (`pAE_sub_exp`: Taylor of `exp` to order
16 and, on three intervals, the difference polynomial `pAE - T₁₆` expanded at the interval
centre with its coefficients bounded in absolute value), and the floors move the result by at
most `12` units (`hornerN_err`). Hence ApproxExp is within relative `2⁻⁴⁵` of `2⁶³·ccs·exp(-x)`
on `[0, ln 2)` (`approxExp_err`), and `accW/2⁶⁴` with shift rejection is within relative `2⁻⁴⁴`
(plus `2⁻⁶²` below) of `ccs·exp(-x)` for every `x ≥ 0` (`accW_mem`; the stored
`ln 2` is within `2⁻⁵⁹` of `ln 2`, `ln2q_close`). -/

@[expose] public section

open Finset

namespace FalconPrecision.Exec

/-- `Σₖ cs[k]·δᵏ`. -/
noncomputable def polyE (cs : List ℚ) (δ : ℝ) : ℝ :=
  cs.foldr (fun (c : ℚ) acc => (c : ℝ) + δ * acc) 0

theorem abs_polyE_le : ∀ (cs : List ℚ) {δ h : ℝ}, |δ| ≤ h →
    |polyE cs δ| ≤ polyE (cs.map (|·|)) h
  | [], _, _, _ => by simp [polyE]
  | c :: cs, δ, h, hδ => by
    have h0 : 0 ≤ h := (abs_nonneg _).trans hδ
    have ih := abs_polyE_le cs hδ
    change |(c : ℝ) + δ * polyE cs δ| ≤ ((|c| : ℚ) : ℝ) + h * polyE (cs.map (|·|)) h
    rw [Rat.cast_abs]
    calc |(c : ℝ) + δ * polyE cs δ| ≤ |(c : ℝ)| + |δ| * |polyE cs δ| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(c : ℝ)| + h * polyE (cs.map (|·|)) h := by
          gcongr

/-- ApproxExp's polynomial in Horner form (spec Alg. 13 on reals, no floors). -/
noncomputable def pAE (ζ : ℝ) : ℝ :=
  facct.foldl (fun Y (c : ℕ) => (c : ℝ) / 2 ^ 63 - ζ * Y) ((0x00000004741183A3 : ℕ) / 2 ^ 63)

/-- The Taylor polynomial of `exp(-ζ)` of order `16`. -/
noncomputable def t16 (ζ : ℝ) : ℝ := ∑ m ∈ range 16, (-ζ) ^ m / m.factorial

/-- `pAE - T₁₆` around `1/8`. -/
def cs1 : List ℚ :=
  [20341593065569801168679 / 57815087803371600807799233334738944000,
    -2278372317967627211879 / 843136697132502511780405486131609600,
    -1530292309326617962399 / 30112024897589375420728767361843200,
    57833040406142624741 / 434308051407539068568203375411200,
    110004241027547639539 / 72384675234589844761367229235200,
    -988345839514014139 / 514095704791121056543801344000,
    -1334865472228599349 / 77114355718668158481570201600,
    4992964141942547 / 535516359157417767233126400,
    345219049771134709 / 3748614514101924370631884800,
    -445534635599449 / 150613976013023747034316800, -14645609613028501 / 62755823338759894597632000,
    -694055010215069 / 8628925709079485507174400, 2995433341913687 / 12943388563619228260761600,
    113 / 797058662400, -1 / 99632332800, 1 / 1307674368000]

/-- `pAE - T₁₆` around `3/8`. -/
def cs2 : List ℚ :=
  [83629192749211803849 / 555151734737450213517962460004352000,
    15198920525211214249 / 3469698342109063834487265375027200,
    -5135170413936368893 / 123917797932466565517402334822400,
    -692600826448347011 / 1787275931718267771885610598400,
    240380852260577159 / 178727593171826777188561059840,
    68970062586188719 / 6346860552976803167207424000,
    -4602390287761741 / 952029082946520475081113600,
    -49168469182413953 / 416512723789102707847987200,
    -66512308095205571 / 416512723789102707847987200, 1037280037185257 / 3346977244733861045207040,
    22939376307820369 / 20918607779586631532544000, 3601055301838171 / 2876308569693161835724800,
    2763560447094301 / 4314462854539742753587200, 89 / 797058662400, -1 / 139485265920,
    1 / 1307674368000]

/-- `pAE - T₁₆` around `19/32`. -/
def cs3 : List ℚ :=
  [63667852498500338345212991443 / 617257592086628738647959596003564451790848000,
    1836916291293708259937587003 / 272028586256126447320815527084904205516800,
    -1691748979258089699965647039 / 31574746619014676921166087965212095283200,
    -193958062393125550001504941 / 113851249828177921590743105643793612800,
    -12509748128690791421974541 / 4743802076174080066280962735158067200,
    811928515472589585467699 / 8422944027297727390413641220096000,
    239833465908311896934891 / 315860401023664777140511545753600,
    10496111710033182706931 / 3838581262440370555527050035200,
    5537028130330500088309 / 959645315610092638881762508800,
    73786979933727151169 / 9639294464833519810196275200,
    6477496781426120459 / 1004093173420158313562112000,
    10433819104385039 / 3137791166937994729881600, 12043726843742807 / 12943388563619228260761600,
    1193 / 12752938598400, -1 / 214592716800, 1 / 1307674368000]
theorem pAE_sub_t16_of {c h : ℚ} {cs : List ℚ}
    (hid : ∀ δ : ℝ, pAE (c + δ) - t16 (c + δ) = polyE cs δ)
    (hb : polyE (cs.map (|·|)) h ≤ 15 / 2 ^ 51) {ζ : ℝ} (hζ : |ζ - c| ≤ h) :
    |pAE ζ - t16 ζ| ≤ 15 / 2 ^ 51 := by
  have e := hid (ζ - c)
  rw [add_sub_cancel] at e
  rw [e]
  exact (abs_polyE_le cs hζ).trans hb

theorem t16_expand (ζ : ℝ) : t16 ζ = 1 - ζ + ζ ^ 2 / 2 - ζ ^ 3 / 6 + ζ ^ 4 / 24 - ζ ^ 5 / 120 +
    ζ ^ 6 / 720 - ζ ^ 7 / 5040 + ζ ^ 8 / 40320 - ζ ^ 9 / 362880 + ζ ^ 10 / 3628800 -
    ζ ^ 11 / 39916800 + ζ ^ 12 / 479001600 - ζ ^ 13 / 6227020800 + ζ ^ 14 / 87178291200 -
    ζ ^ 15 / 1307674368000 := by
  simp only [t16, sum_range_succ, sum_range_zero, Nat.factorial]
  push_cast
  ring

theorem pAE_sub_t16_1 {ζ : ℝ} (hζ : |ζ - (1 / 8 : ℚ)| ≤ (1 / 8 : ℚ)) :
    |pAE ζ - t16 ζ| ≤ 15 / 2 ^ 51 :=
  pAE_sub_t16_of (cs := cs1) (fun δ => by
    rw [t16_expand]
    simp only [pAE, facct, List.foldl_cons, List.foldl_nil, polyE, cs1, List.foldr_cons,
      List.foldr_nil]
    push_cast
    ring)
    (by norm_num [polyE, cs1]) hζ

theorem pAE_sub_t16_2 {ζ : ℝ} (hζ : |ζ - (3 / 8 : ℚ)| ≤ (1 / 8 : ℚ)) :
    |pAE ζ - t16 ζ| ≤ 15 / 2 ^ 51 :=
  pAE_sub_t16_of (cs := cs2) (fun δ => by
    rw [t16_expand]
    simp only [pAE, facct, List.foldl_cons, List.foldl_nil, polyE, cs2, List.foldr_cons,
      List.foldr_nil]
    push_cast
    ring)
    (by norm_num [polyE, cs2]) hζ

theorem pAE_sub_t16_3 {ζ : ℝ} (hζ : |ζ - (19 / 32 : ℚ)| ≤ (1 / 10 : ℚ)) :
    |pAE ζ - t16 ζ| ≤ 15 / 2 ^ 51 :=
  pAE_sub_t16_of (cs := cs3) (fun δ => by
    rw [t16_expand]
    simp only [pAE, facct, List.foldl_cons, List.foldl_nil, polyE, cs3, List.foldr_cons,
      List.foldr_nil]
    push_cast
    ring)
    (by norm_num [polyE, cs3]) hζ

/-- **ApproxExp's polynomial** is within `2⁻⁴⁷` of `exp(-ζ)` on `[0, 111/160]`. -/
theorem pAE_sub_exp {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 111 / 160) :
    |pAE ζ - Real.exp (-ζ)| ≤ 1 / 2 ^ 47 := by
  have hT : |Real.exp (-ζ) - t16 ζ| ≤ 1 / 2 ^ 51 := by
    have hb := Real.exp_bound (x := -ζ) (by rw [abs_neg, abs_of_nonneg h0]; linarith)
      (n := 16) (by norm_num)
    rw [abs_neg, abs_of_nonneg h0] at hb
    refine hb.trans ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 16)
      (by positivity)).trans ?_)
    norm_num [Nat.factorial]
  have hP : |pAE ζ - t16 ζ| ≤ 15 / 2 ^ 51 := by
    rcases le_or_gt ζ (1 / 4) with h | h
    · exact pAE_sub_t16_1 (by push_cast; rw [abs_le]; constructor <;> linarith)
    rcases le_or_gt ζ (1 / 2) with h' | h'
    · exact pAE_sub_t16_2 (by push_cast; rw [abs_le]; constructor <;> linarith)
    · exact pAE_sub_t16_3 (by push_cast; rw [abs_le]; constructor <;> linarith)
  calc |pAE ζ - Real.exp (-ζ)| ≤ |pAE ζ - t16 ζ| + |Real.exp (-ζ) - t16 ζ| := by
        rw [abs_sub_comm (Real.exp _)]; exact abs_sub_le _ _ _
    _ ≤ 15 / 2 ^ 51 + 1 / 2 ^ 51 := add_le_add hP hT
    _ = 1 / 2 ^ 47 := by norm_num

/-- No ℕ subtraction of Horner's steps truncates, from `y ≤ M`. -/
def chainOK (z : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | M, c :: l => z * M / 2 ^ 63 ≤ c ∧ chainOK z c l

theorem nat_div_gt (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b - 1 < ((a / b : ℕ) : ℝ) := by
  have h : ((a : ℕ) : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast Nat.lt_div_mul_add hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hb']
  linarith

/-- Horner's steps in `ℕ` with floors against the same steps in `ℝ`. -/
theorem horner_list {z : ℕ} (hz : z ≤ 2 ^ 63) : ∀ (l : List ℕ) (y M : ℕ) (Y e : ℝ), y ≤ M →
    |(y : ℝ) - 2 ^ 63 * Y| ≤ e → chainOK z M l →
    |((l.foldl (fun y c => c - z * y / 2 ^ 63) y : ℕ) : ℝ) -
      2 ^ 63 * l.foldl (fun Y (c : ℕ) => (c : ℝ) / 2 ^ 63 - (z / 2 ^ 63) * Y) Y| ≤ e + l.length
  | [], y, M, Y, e, _, he, _ => by simpa using he
  | c :: l, y, M, Y, e, hyM, he, hc => by
    obtain ⟨hc, hl⟩ := hc
    have hsub : z * y / 2 ^ 63 ≤ c :=
      (Nat.div_le_div_right (Nat.mul_le_mul_left z hyM)).trans hc
    have f1 : ((z * y / 2 ^ 63 : ℕ) : ℝ) ≤ (z * y : ℕ) / ((2 ^ 63 : ℕ) : ℝ) := Nat.cast_div_le
    have f2 := nat_div_gt (z * y) (2 ^ 63) (by positivity)
    push_cast at f1 f2
    have hζ0 : 0 ≤ (z : ℝ) / 2 ^ 63 := by positivity
    have hζ : (z : ℝ) / 2 ^ 63 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast hz
    have step : |((c - z * y / 2 ^ 63 : ℕ) : ℝ) -
        2 ^ 63 * ((c : ℝ) / 2 ^ 63 - (z / 2 ^ 63) * Y)| ≤ e + 1 := by
      rw [Nat.cast_sub hsub]
      have hb : |((z : ℝ) / 2 ^ 63) * ((y : ℝ) - 2 ^ 63 * Y)| ≤ e := by
        rw [abs_mul, abs_of_nonneg hζ0]
        exact (mul_le_of_le_one_left (abs_nonneg _) hζ).trans he
      have ha : |(z : ℝ) * y / 2 ^ 63 - ((z * y / 2 ^ 63 : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc |(c : ℝ) - ((z * y / 2 ^ 63 : ℕ) : ℝ) - 2 ^ 63 * ((c : ℝ) / 2 ^ 63 - z / 2 ^ 63 * Y)|
          = |((z : ℝ) * y / 2 ^ 63 - ((z * y / 2 ^ 63 : ℕ) : ℝ)) -
              ((z : ℝ) / 2 ^ 63) * ((y : ℝ) - 2 ^ 63 * Y)| := by ring_nf
        _ ≤ 1 + e := (abs_sub _ _).trans (add_le_add ha hb)
        _ = e + 1 := add_comm _ _
    have := horner_list hz l (c - z * y / 2 ^ 63) c _ (e + 1) (Nat.sub_le _ _) step hl
    simp only [List.foldl_cons, List.length_cons]
    push_cast
    linarith

/-- ApproxExp's Horner loop in `ℕ` (spec Alg. 13 l. 2-7). -/
def hornerN (z : ℕ) : ℕ := facct.foldl (fun y c => c - z * y / 2 ^ 63) 0x00000004741183A3

theorem approxExp_eq (x ccs : ℚ) :
    approxExp x ccs = ⌊ccs * 2 ^ 63⌋.toNat * hornerN ⌊x * 2 ^ 63⌋.toNat / 2 ^ 63 := by
  simp only [approxExp, hornerN]

theorem hornerN_err {z : ℕ} (hz : z ≤ 6393154322601327830) :
    |(hornerN z : ℝ) - 2 ^ 63 * pAE (z / 2 ^ 63)| ≤ 12 := by
  have h : ∀ M c, 6393154322601327830 * M / 2 ^ 63 ≤ c → z * M / 2 ^ 63 ≤ c :=
    fun M c hc => (Nat.div_le_div_right (Nat.mul_le_mul_right M hz)).trans hc
  have hch : chainOK z 0x00000004741183A3 facct := by
    simp only [chainOK, facct]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
      exact h _ _ (by norm_num)
  have := horner_list (by omega) facct 0x00000004741183A3 0x00000004741183A3
    ((0x00000004741183A3 : ℕ) / 2 ^ 63) 0 le_rfl
    (le_of_eq (by rw [abs_eq_zero, sub_eq_zero]; field_simp)) hch
  rw [show facct.length = 12 from rfl] at this
  simpa [hornerN, pAE] using this

theorem exp_neg_ge {x : ℝ} (h1 : x ≤ 7 / 10) : 49 / 100 ≤ Real.exp (-x) := by
  have hb := Real.exp_bound' (x := 7 / 10) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  have h7 : Real.exp (7 / 10) ≤ (49 / 100)⁻¹ :=
    hb.trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rw [← le_inv_comm₀ (by norm_num) (Real.exp_pos _), ← Real.exp_neg] at h7
  exact h7.trans (Real.exp_le_exp.2 (by linarith))

theorem floor_bounds (q : ℚ) : ((⌊q⌋ : ℤ) : ℝ) ≤ q ∧ (q : ℝ) - 1 < ⌊q⌋ :=
  ⟨by exact_mod_cast Int.floor_le q, by exact_mod_cast Int.sub_one_lt_floor q⟩

theorem ln2_cast : (falcon512S.ln2 : ℝ) = 12786308645202655660 / 2 ^ 64 := by
  simp [falcon512S]

/-- **ApproxExp** is within relative `2⁻⁴⁵` of `2⁶³·ccs·exp(-x)` on `[0, ln 2)`,
`ccs ∈ [1/2, 1]`. -/
theorem approxExp_err {x ccs : ℚ} (hx0 : 0 ≤ x) (hx1 : x < falcon512S.ln2) (hc0 : 1 / 2 ≤ ccs)
    (hc1 : ccs ≤ 1) :
    |(approxExp x ccs : ℝ) - 2 ^ 63 * ccs * Real.exp (-x)| ≤
      2 ^ 63 * ccs * Real.exp (-x) / 2 ^ 45 := by
  rw [approxExp_eq]
  have hxL : (x : ℝ) < 12786308645202655660 / 2 ^ 64 := by rw [← ln2_cast]; exact_mod_cast hx1
  have hx0' : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have hc0' : (1 / 2 : ℝ) ≤ ccs := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]; exact_mod_cast hc0
  have hc1' : (ccs : ℝ) ≤ 1 := by exact_mod_cast hc1
  have hfl : 0 ≤ ⌊x * 2 ^ 63⌋ := Int.floor_nonneg.2 (by positivity)
  set z := ⌊x * 2 ^ 63⌋.toNat with hz
  have hzr : (z : ℝ) = ((⌊x * 2 ^ 63⌋ : ℤ) : ℝ) := by
    rw [hz]; exact_mod_cast Int.toNat_of_nonneg hfl
  have hfz := floor_bounds (x * 2 ^ 63)
  push_cast at hfz
  have hz1 : (z : ℝ) ≤ x * 2 ^ 63 := hzr ▸ hfz.1
  have hz2 : (x : ℝ) * 2 ^ 63 - 1 < z := hzr ▸ hfz.2
  have hzN : z ≤ 6393154322601327830 := by
    have : (z : ℝ) ≤ 6393154322601327830 := by linarith
    exact_mod_cast this
  have hζ0 : (0 : ℝ) ≤ z / 2 ^ 63 := by positivity
  have hζx : (z : ℝ) / 2 ^ 63 ≤ x := by linarith
  have hxζ : (x : ℝ) - z / 2 ^ 63 ≤ 1 / 2 ^ 63 := by linarith
  have hP := abs_le.1 (pAE_sub_exp hζ0 (by linarith))
  have hH := abs_le.1 (hornerN_err hzN)
  set E := Real.exp (-x)
  set eζ := Real.exp (-((z : ℝ) / 2 ^ 63))
  have hE := exp_neg_ge (x := x) (by linarith)
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hEζ1 : E ≤ eζ := Real.exp_le_exp.2 (by linarith)
  have hEζ1' : eζ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hEζ2 : eζ ≤ E * (1 + 1 / 2 ^ 62) := by
    have ht := Real.exp_bound' (x := (x : ℝ) - z / 2 ^ 63) (by linarith) (by linarith) (n := 1)
      (by norm_num)
    norm_num at ht
    have e : eζ = E * Real.exp ((x : ℝ) - z / 2 ^ 63) := by
      rw [← Real.exp_add]
      change Real.exp _ = Real.exp _
      congr 1
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  set y := hornerN z
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  set C := ⌊ccs * 2 ^ 63⌋.toNat with hC
  have hCfl : 0 ≤ ⌊ccs * 2 ^ 63⌋ := Int.floor_nonneg.2 (by positivity)
  have hCr : (C : ℝ) = ((⌊ccs * 2 ^ 63⌋ : ℤ) : ℝ) := by
    rw [hC]; exact_mod_cast Int.toNat_of_nonneg hCfl
  have hfC := floor_bounds (ccs * 2 ^ 63)
  push_cast at hfC
  have hC1 : (C : ℝ) ≤ ccs * 2 ^ 63 := hCr ▸ hfC.1
  have hC2 : (ccs : ℝ) * 2 ^ 63 - 1 < C := hCr ▸ hfC.2
  have hA1 : ((C * y / 2 ^ 63 : ℕ) : ℝ) ≤ (C * y : ℕ) / ((2 ^ 63 : ℕ) : ℝ) := Nat.cast_div_le
  have hA2 := nat_div_gt (C * y) (2 ^ 63) (by positivity)
  push_cast at hA1 hA2
  have hCy1 : (C : ℝ) * y ≤ ccs * 2 ^ 63 * y := mul_le_mul_of_nonneg_right hC1 hy0
  have hCy2 : ((ccs : ℝ) * 2 ^ 63 - 1) * y ≤ C * y := mul_le_mul_of_nonneg_right hC2.le hy0
  have hcy1 : (ccs : ℝ) * y ≤ ccs * (2 ^ 63 * eζ + 2 ^ 16 + 12) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hcy2 : (ccs : ℝ) * (2 ^ 63 * eζ - 2 ^ 16 - 12) ≤ ccs * y :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hce1 : (ccs : ℝ) * eζ ≤ ccs * (E * (1 + 1 / 2 ^ 62)) :=
    mul_le_mul_of_nonneg_left hEζ2 (by linarith)
  have hce2 : (ccs : ℝ) * E ≤ ccs * eζ := mul_le_mul_of_nonneg_left hEζ1 (by linarith)
  have hcE : (ccs : ℝ) * (49 / 100) ≤ ccs * E := mul_le_mul_of_nonneg_left hE (by linarith)
  have hcE1 : (ccs : ℝ) * E ≤ ccs * 1 := mul_le_mul_of_nonneg_left hE1 (by linarith)
  rw [abs_le]
  constructor <;> linarith [hA1, hA2, hCy1, hCy2, hcy1, hcy2, hce1, hce2, hcE, hcE1, hH.1, hH.2,
    hP.1, hP.2]

/-- The stored `ln 2` is within `2⁻⁵⁹` of `ln 2` (the series of `-log(1 - 1/2)` to `60` terms). -/
theorem ln2q_close : |Real.log 2 - (falcon512S.ln2 : ℝ)| ≤ 1 / 2 ^ 59 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 2) (by norm_num) 60
  rw [show Real.log (1 - 1 / 2) = -Real.log 2 by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]] at h
  norm_num [Finset.sum_range_succ] at h
  rw [ln2_cast, abs_le]
  obtain ⟨h1, h2⟩ := abs_le.1 h
  constructor <;> linarith

theorem exp_neg44_le : Real.exp (-44) ≤ 1 / 2 ^ 62 := by
  have he : (2 : ℝ) ^ 62 ≤ Real.exp 44 := by
    have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
    calc (2 : ℝ) ^ 62 ≤ 2.7182818283 ^ 44 := by norm_num
      _ ≤ Real.exp 1 ^ 44 := pow_le_pow_left₀ (by norm_num) h1 44
      _ = Real.exp 44 := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) he

theorem nat_pred_cast (a : ℕ) : (a : ℝ) - 1 ≤ ((a - 1 : ℕ) : ℝ) := by
  have h : a ≤ a - 1 + 1 := by omega
  have h' : (a : ℝ) ≤ ((a - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast h
  linarith

/-- **BerExp's acceptance with shift rejection** (spec Alg. 14 l. 1-4, ePrint 2026/2902 Alg. 9
l. 14-15): within relative `2⁻⁴⁴` above and relative `2⁻⁴⁴` plus `2⁻⁶²` below of
`ccs·exp(-x)`, for every `x ≥ 0` and `ccs ∈ [1/2, 1]`. -/
theorem accW_mem {x ccs : ℚ} (hx : 0 ≤ x) (hc0 : 1 / 2 ≤ ccs) (hc1 : ccs ≤ 1) :
    (accW falcon512S true x ccs : ℝ) / 2 ^ 64 ≤ ccs * Real.exp (-x) * (1 + 1 / 2 ^ 44) ∧
      ccs * Real.exp (-x) * (1 - 1 / 2 ^ 44) - 1 / 2 ^ 62 ≤
        (accW falcon512S true x ccs : ℝ) / 2 ^ 64 := by
  have hL2 : (0 : ℚ) < falcon512S.ln2 := by norm_num [falcon512S]
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hc0' : (1 / 2 : ℝ) ≤ ccs := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]; exact_mod_cast hc0
  have hc1' : (ccs : ℝ) ≤ 1 := by exact_mod_cast hc1
  have hE1 : Real.exp (-(x : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hg0 : 0 ≤ (ccs : ℝ) * Real.exp (-x) := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hg1 : (ccs : ℝ) * Real.exp (-x) ≤ 1 :=
    (mul_le_mul hc1' hE1 (Real.exp_pos _).le zero_le_one).trans_eq (one_mul 1)
  simp only [accW]
  set s := ⌊x / falcon512S.ln2⌋ with hs
  have hs0 : 0 ≤ s := Int.floor_nonneg.2 (div_nonneg hx hL2.le)
  have hsL : (s : ℚ) * falcon512S.ln2 ≤ x := by
    have := Int.floor_le (x / falcon512S.ln2); rwa [le_div_iff₀ hL2] at this
  have hsU : x < ((s : ℚ) + 1) * falcon512S.ln2 := by
    have := Int.lt_floor_add_one (x / falcon512S.ln2); rwa [div_lt_iff₀ hL2] at this
  by_cases h64 : 64 ≤ s
  · simp only [h64, decide_true, Bool.and_self, ↓reduceIte, Nat.cast_zero, zero_div]
    have hx44 : (44 : ℝ) ≤ x := by
      have h1 : (64 : ℚ) * falcon512S.ln2 ≤ x :=
        le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast h64) hL2.le) hsL
      have h2 : (44 : ℚ) ≤ x := le_trans (by norm_num [falcon512S]) h1
      exact_mod_cast h2
    have hg : (ccs : ℝ) * Real.exp (-x) ≤ 1 / 2 ^ 62 :=
      (mul_le_of_le_one_left (Real.exp_pos _).le hc1').trans
        ((Real.exp_le_exp.2 (by linarith)).trans exp_neg44_le)
    have hgε : (ccs : ℝ) * Real.exp (-x) * (1 - 1 / 2 ^ 44) ≤ ccs * Real.exp (-x) :=
      mul_le_of_le_one_right hg0 (by norm_num)
    exact ⟨mul_nonneg hg0 (by norm_num), by linarith⟩
  · have h64' : ¬(64 ≤ s) := h64
    simp only [h64', decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rw [min_eq_left (show s ≤ 63 by omega)]
    set n := s.toNat with hn
    have hns : (n : ℤ) = s := Int.toNat_of_nonneg hs0
    have hn63 : n ≤ 63 := by omega
    have hsn : ((s : ℤ) : ℝ) = (n : ℝ) := by rw [← hns, Int.cast_natCast]
    set r : ℚ := x - s * falcon512S.ln2 with hr
    have hr0 : 0 ≤ r := by linarith
    have hr1 : r < falcon512S.ln2 := by linarith
    have hAE := abs_le.1 (approxExp_err hr0 hr1 hc0 hc1)
    set AE := approxExp r ccs
    set u : ℝ := n * ((falcon512S.ln2 : ℝ) - Real.log 2) with hu_def
    set P : ℝ := 2 ^ n with hP_def
    have hP1 : (1 : ℝ) ≤ P := one_le_pow₀ (by norm_num)
    have hP0 : (0 : ℝ) < P := by positivity
    set V : ℝ := ccs * Real.exp (-x) * Real.exp u with hV
    have hkey : (2 : ℝ) ^ 63 * ccs * Real.exp (-r) = 2 ^ 63 * V * P := by
      have h2n : P = Real.exp (n * Real.log 2) := by
        rw [hP_def, Real.exp_nat_mul, Real.exp_log two_pos]
      have harg : -((r : ℚ) : ℝ) = -(x : ℝ) + u + n * Real.log 2 := by
        rw [hr, hu_def]; push_cast; rw [hsn]; ring
      rw [h2n, hV, harg, Real.exp_add, Real.exp_add]
      ring
    rw [hkey] at hAE
    have hu : |u| ≤ 1 / 2 ^ 53 := by
      rw [hu_def, abs_mul, Nat.abs_cast]
      calc (n : ℝ) * |(falcon512S.ln2 : ℝ) - Real.log 2| ≤ 63 * (1 / 2 ^ 59) :=
            mul_le_mul (by exact_mod_cast hn63) (by rw [abs_sub_comm]; exact ln2q_close)
              (abs_nonneg _) (by norm_num)
        _ ≤ 1 / 2 ^ 53 := by norm_num
    have heu := abs_le.1 ((Real.abs_exp_sub_one_le (hu.trans (by norm_num))).trans
      (mul_le_mul_of_nonneg_left hu (by norm_num)))
    have hV1 : V ≤ ccs * Real.exp (-x) * (1 + 2 * (1 / 2 ^ 53)) :=
      mul_le_mul_of_nonneg_left (by linarith) hg0
    have hV2 : ccs * Real.exp (-x) * (1 - 2 * (1 / 2 ^ 53)) ≤ V :=
      mul_le_mul_of_nonneg_left (by linarith) hg0
    have hW1 : (((2 * AE - 1) / 2 ^ n : ℕ) : ℝ) ≤ ((2 * AE - 1 : ℕ) : ℝ) / P := by
      rw [hP_def]; exact_mod_cast Nat.cast_div_le
    have hW2 := nat_div_gt (2 * AE - 1) (2 ^ n) (by positivity)
    push_cast at hW2
    have hW3 : ((2 * AE - 1 : ℕ) : ℝ) ≤ 2 * AE := by exact_mod_cast Nat.sub_le _ _
    have hW4 := nat_pred_cast (2 * AE)
    push_cast at hW4
    have hup : ((2 * AE - 1 : ℕ) : ℝ) / P ≤ 2 ^ 64 * V * (1 + 1 / 2 ^ 45) := by
      rw [div_le_iff₀ hP0]; nlinarith [hAE.2, hW3]
    have hlo : 2 ^ 64 * V * (1 - 1 / 2 ^ 45) - 1 ≤ ((2 * AE - 1 : ℕ) : ℝ) / P := by
      rw [le_div_iff₀ hP0]; nlinarith [hAE.1, hW4, hP1]
    constructor
    · have hm : ((min ((2 * AE - 1) / 2 ^ n) (2 ^ 64 - 1) : ℕ) : ℝ) ≤
          (((2 * AE - 1) / 2 ^ n : ℕ) : ℝ) := by exact_mod_cast min_le_left _ _
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hm, hW1, hup, hV1, hg0]
    · rcases min_cases ((2 * AE - 1) / 2 ^ n) (2 ^ 64 - 1) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h, le_div_iff₀ (by positivity)]
        nlinarith [hW2, hlo, hV2, hg0]
      · rw [h]
        norm_num
        nlinarith [hg1, hg0]

/-- `1/(2σmax²)` at Falcon-512. -/
def kS : ℚ := 2000000 / 13256881

theorem kS_eq : 1 / (2 * falcon512S.σmax ^ 2) = kS := by norm_num [falcon512S, kS]

/-- A lower end of `exp(-kS)` (`2⁻⁶⁴` below the upper end `eHi`). -/
def eLo : ℚ := 7931765548225621581 / 2 ^ 63

/-- An upper end of `exp(-kS)`. -/
def eHi : ℚ := eLo + 1 / 2 ^ 64

/-- `exp(-kS) ∈ [eLo, eHi]` (Taylor to order `14`). -/
theorem exp_kS_mem : (eLo : ℝ) ≤ Real.exp (-kS) ∧ Real.exp (-kS) ≤ eHi := by
  have hb := Real.exp_bound (x := -(kS : ℝ)) (by rw [abs_neg]; norm_num [kS, abs_of_pos])
    (n := 14) (by norm_num)
  rw [abs_neg] at hb
  norm_num [Finset.sum_range_succ, Nat.factorial, kS] at hb
  obtain ⟨h1, h2⟩ := abs_le.1 hb
  norm_num [eLo, eHi, kS]
  constructor <;> linarith

theorem exp_mul_kS_mem (m : ℕ) :
    (eLo : ℝ) ^ m ≤ Real.exp (-(m * kS)) ∧ Real.exp (-(m * kS)) ≤ (eHi : ℝ) ^ m := by
  rw [neg_mul_eq_mul_neg, Real.exp_nat_mul]
  have h0 : (0 : ℝ) ≤ eLo := by norm_num [eLo]
  exact ⟨pow_le_pow_left₀ h0 exp_kS_mem.1 m,
    pow_le_pow_left₀ (Real.exp_pos _).le exp_kS_mem.2 m⟩

end FalconPrecision.Exec
