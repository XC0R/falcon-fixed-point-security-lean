/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SamplerNum
public import FalconPrecision.RenyiHybrid

/-! # The law of SamplerZ

`lawZ P S σ t` is the output law of `samplerZ` under uniform bits (`UnifBits`), computed in `ℚ`:
one round draws the candidate `(z0, b)` with probability `pdt[z0]/2^(w+1)` and accepts it with
probability `accW/2⁶⁴`; after `fuel` rejected rounds the output is `⌊t̄⌋`. `baseZ_law`: BaseSampler
draws `z0 = i` for `pdt[i]` of the `2ʷ` values; `berExp_law`: BerExp accepts with probability
`za/2⁶⁴`; `samplerZ_law`: the output law is `lawZ` (the `2⁸⁰` draws of a round give `(z0, b)`
with multiplicity `pdt[z0]·2^(79-w)`, `sum_z0Of`; induction on the rounds, `samplerLoop_apply`). -/

@[expose] public section

open MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.Exec

/-- Shape of a table: `72 ≤ w ≤ 79`, `rcdt` non-increasing, entries at most `2ʷ`. -/
def BaseTable.okB (T : BaseTable) : Bool :=
  decide (72 ≤ T.w) && decide (T.w ≤ 79) && decide (T.rcdt.Pairwise fun a b => b ≤ a) &&
    T.rcdt.all (· ≤ 2 ^ T.w)

/-- The number of `w`-bit draws with `baseZ = i`. -/
def pdtZ (T : BaseTable) (i : ℕ) : ℕ :=
  (if i = 0 then 2 ^ T.w else T.rcdt.getD (i - 1) 0) - T.rcdt.getD i 0

/-- Weight of the candidate `(z0, b)` in one round: drawn and accepted. -/
def wZ (P : SampParams) (S : SampChoices) (σ r : ℚ) (z0 : ℕ) (b : Bool) : ℚ :=
  pdtZ (P.tab S.base) z0 / 2 ^ ((P.tab S.base).w + 1) *
    (accW P S.shiftRej (xOf P σ r z0 b) (P.σmin / σ) / 2 ^ 64)

/-- Acceptance probability of one round. -/
def accZ (P : SampParams) (S : SampChoices) (σ r : ℚ) : ℚ :=
  ((List.range ((P.tab S.base).rcdt.length + 1)).map fun z0 =>
    wZ P S σ r z0 false + wZ P S σ r z0 true).sum

/-- Weight of the candidate `z`. -/
def wZz (P : SampParams) (S : SampChoices) (σ r : ℚ) (z : ℤ) : ℚ :=
  if 1 ≤ z then wZ P S σ r (z - 1).toNat true else wZ P S σ r (-z).toNat false

/-- **The law of `samplerZ`**: `y = ⌊t̄⌋ + z`. -/
def lawZ (P : SampParams) (S : SampChoices) (σ t : Fx 64) (y : ℤ) : ℚ :=
  let s := t.toInt .floor
  let r := t.toRat - s
  let ρ := 1 - accZ P S σ.toRat r
  (if y = s then ρ ^ P.fuel else 0) +
    (1 - ρ ^ P.fuel) / accZ P S σ.toRat r * wZz P S σ.toRat r (y - s)

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- `ub k` is uniform on `[0, 2ᵏ)`. -/
structure UnifBits (ub : ℕ → m ℕ) : Prop where
  eq : ∀ k n, 𝒟[ub k] {n} = if n < 2 ^ k then ((2 : ℝ≥0∞) ^ k)⁻¹ else 0

theorem getD_le_of_forall {l : List ℕ} {M : ℕ} (h : ∀ b ∈ l, b ≤ M) (k : ℕ) :
    l.getD k 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases e : l[k]? with
  | none => simp
  | some b => simpa using h b (List.mem_of_getElem? e)

/-- On a non-increasing list, `#{j | u < l[j]} = i` iff `l[i] ≤ u < l[i-1]` (`l[-1] = ∞`). -/
theorem length_filter_lt_eq_iff {l : List ℕ} (hl : l.Pairwise fun a b => b ≤ a) (u : ℕ) :
    ∀ i, (l.filter (u < ·)).length = i ↔ (i = 0 ∨ u < l.getD (i - 1) 0) ∧ ¬u < l.getD i 0 := by
  induction l with
  | nil => intro i; cases i <;> simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    intro i
    by_cases hua : u < a
    · rw [List.filter_cons_of_pos (by simpa using hua), List.length_cons]
      cases i with
      | zero => simp [hua]
      | succ j =>
        rw [Nat.add_right_cancel_iff, ih hl.2 j]
        cases j <;> simp [hua]
    · have h0 : l.filter (u < ·) = [] := List.filter_eq_nil_iff.2 fun b hb => by
        simpa using (hl.1 b hb).trans (not_lt.1 hua)
      rw [List.filter_cons_of_neg (by simpa using hua), h0, List.length_nil]
      cases i with
      | zero => simp [hua]
      | succ j =>
        cases j with
        | zero => simp [hua]
        | succ k =>
          refine iff_of_false (by simp) fun h => ?_
          rcases h with ⟨h | h, -⟩
          · omega
          · simp only [Nat.add_sub_cancel, List.getD_cons_succ] at h
            exact hua (h.trans_le (getD_le_of_forall hl.1 k))

/-- The count of `baseZ_law` over a `Finset`. -/
theorem card_filter_baseZ (T : BaseTable) (hT : T.okB = true) (i : ℕ) :
    ((Finset.range (2 ^ T.w)).filter fun u => baseZ T u = i).card = pdtZ T i := by
  simp only [BaseTable.okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hT
  obtain ⟨⟨_, hP⟩, hA⟩ := hT
  have hi : (if i = 0 then 2 ^ T.w else T.rcdt.getD (i - 1) 0) ≤ 2 ^ T.w := by
    split
    · exact le_rfl
    · exact getD_le_of_forall (fun b hb => by simpa using hA b hb) _
  rw [show (Finset.range (2 ^ T.w)).filter (fun u => baseZ T u = i) =
      Finset.Ico (T.rcdt.getD i 0) (if i = 0 then 2 ^ T.w else T.rcdt.getD (i - 1) 0) by
    ext u
    have hb : baseZ T u = i ↔ (i = 0 ∨ u < T.rcdt.getD (i - 1) 0) ∧ ¬u < T.rcdt.getD i 0 :=
      length_filter_lt_eq_iff hP u i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hb, not_lt]
    split <;> rename_i h0 <;> simp only [h0, true_or, false_or, true_and] <;> constructor <;>
      rintro ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
    · exact ⟨h2, h1⟩
    · exact ⟨h2.2, h2.1⟩
    · exact ⟨lt_of_lt_of_le h2 (by simpa [h0] using hi), h2, h1⟩, Nat.card_Ico]
  rfl

/-- **Node.** BaseSampler's law: `z0 = i` for `pdt[i]` of the `2ʷ` draws. -/
theorem baseZ_law (T : BaseTable) (hT : T.okB = true) (i : ℕ) :
    ((List.range (2 ^ T.w)).filter fun u => baseZ T u = i).length = pdtZ T i := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _), List.toFinset_filter,
    List.toFinset_range]
  simpa using card_filter_baseZ T hT i

/-- `Σ_{n<N} (α if n < d, β if n > d, γ at d)` for `d < N`. -/
theorem sum_range_ite3 {N d : ℕ} (hd : d < N) (α β γ : ℝ) :
    ∑ n ∈ Finset.range N, (if n < d then α else if d < n then β else γ) =
      d * α + ((N : ℝ) - 1 - d) * β + γ := by
  have h1 : ∑ n ∈ Finset.range d, (if n < d then α else if d < n then β else γ) =
      ∑ n ∈ Finset.range d, α :=
    Finset.sum_congr rfl fun n hn => ite_eq_left (Finset.mem_range.1 hn)
  have h2 : ∑ n ∈ Finset.Ico (d + 1) N, (if n < d then α else if d < n then β else γ) =
      ∑ n ∈ Finset.Ico (d + 1) N, β :=
    Finset.sum_congr rfl fun n hn => by
      rw [Finset.mem_Ico] at hn
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [← Finset.sum_range_add_sum_Ico _ hd.le, Finset.sum_eq_sum_Ico_succ_bot hd, h1, h2]
  simp only [lt_irrefl, ite_false, Finset.sum_const, Finset.card_range, Nat.card_Ico,
    nsmul_eq_mul]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

omit [LawfulMonad m] in
/-- A draw of `ub k` then `f`: the average of `f n` over `n < 2ᵏ`. -/
theorem unif_bind_apply {ub : ℕ → m ℕ} (hub : UnifBits ub) (k : ℕ) {β : Type}
    [MeasurableSpace β] (f : ℕ → m β) {s : Set β} (hs : MeasurableSet s) :
    𝒟[ub k >>= f] s = ∑ n ∈ Finset.range (2 ^ k), ((2 : ℝ≥0∞) ^ k)⁻¹ * 𝒟[f n] s := by
  rw [evalDist_bind_of_discrete, Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    lintegral_countable', tsum_eq_sum (s := Finset.range (2 ^ k)) fun n hn => by
      rw [hub.eq, ite_eq_right (by simpa using hn), mul_zero]]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hub.eq, ite_eq_left (Finset.mem_range.1 hn), mul_comm]

omit [LawfulMonad m] in
/-- BerExp on the low `i` bytes of `za`: `true` with probability `(za mod 2⁸ⁱ)/2⁸ⁱ`. -/
theorem berExp_apply {ub : ℕ → m ℕ} (hub : UnifBits ub) (za : ℕ) :
    ∀ i (b : Bool), 𝒟[berExp ub za i] {b} = ENNReal.ofReal
      (if b then ((za % 2 ^ (8 * i) : ℕ) : ℝ) / 2 ^ (8 * i)
        else 1 - ((za % 2 ^ (8 * i) : ℕ) : ℝ) / 2 ^ (8 * i))
  | 0, b => by cases b <;> simp [berExp, Nat.mod_one]
  | i + 1, b => by
    rw [berExp, unif_bind_apply hub 8 _ (measurableSet_singleton b)]
    set d := za / 2 ^ (8 * i) % 256
    set x : ℝ := ((za % 2 ^ (8 * i) : ℕ) : ℝ) / 2 ^ (8 * i)
    have hd : d < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := div_le_one_of_le₀ (by
      exact_mod_cast (Nat.mod_lt _ (by positivity)).le) (by positivity)
    have hrec := berExp_apply hub za i b
    have e : ∀ n, 𝒟[if n < d then (pure true : m Bool) else if d < n then pure false
        else berExp ub za i] {b} = ENNReal.ofReal (if n < d then (if b then 1 else 0)
          else if d < n then (if b then 0 else 1) else if b then x else 1 - x) := fun n => by
      by_cases h1 : n < d
      · simp only [h1, ↓reduceIte]
        cases b <;> simp
      by_cases h2 : d < n
      · simp only [h1, h2, ↓reduceIte]
        cases b <;> simp
      · simp only [h1, h2, ↓reduceIte]
        exact hrec
    have hD : ((2 : ℝ≥0∞) ^ 8)⁻¹ = ENNReal.ofReal (1 / 2 ^ 8) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    simp_rw [e, hD, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 8)]
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => mul_nonneg (by norm_num)
      (by split_ifs <;> linarith), ← Finset.mul_sum, sum_range_ite3 hd]
    congr 1
    have hm : ((za % 2 ^ (8 * (i + 1)) : ℕ) : ℝ) = ((za % 2 ^ (8 * i) : ℕ) : ℝ) +
        2 ^ (8 * i) * d := by
      rw [show 8 * (i + 1) = 8 * i + 8 by ring, pow_add, Nat.mod_mul]
      push_cast
      ring
    have hx : ((za % 2 ^ (8 * i) : ℕ) : ℝ) = x * 2 ^ (8 * i) := by
      rw [div_mul_cancel₀ _ (by positivity)]
    rw [hm, hx, show 8 * (i + 1) = 8 * i + 8 by ring, pow_add]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> field_simp <;> ring

omit [LawfulMonad m] in
/-- **Node.** BerExp accepts with probability `za/2⁶⁴` (`za < 2⁶⁴`). -/
theorem berExp_law (ub : ℕ → m ℕ) (hub : UnifBits ub) (za : ℕ) (hza : za < 2 ^ 64) :
    𝒟[berExp ub za 8] {true} = ENNReal.ofReal (za / 2 ^ 64) := by
  rw [berExp_apply hub za 8 true, ite_eq_left rfl, Nat.mod_eq_of_lt hza]

theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ x ∈ Finset.range (a * b), f x =
      ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem list_range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_range_map_sum f n,
      Finset.sum_range_succ]
    simp

theorem pdtZ_eq_zero (T : BaseTable) {k : ℕ} (hk : T.rcdt.length < k) : pdtZ T k = 0 := by
  rw [pdtZ, ite_eq_right (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by omega)]
  exact Nat.zero_sub _

/-- **The draws of one round**: the `2⁸⁰` pairs `(u, c)` give `(z0, b)` with multiplicity
`pdt[z0]·2^(79-w)`. -/
theorem sum_z0Of (T : BaseTable) (hT : T.okB = true) (G : ℕ → Bool → ℚ) :
    ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8),
        G (z0Of T u c) (decide (c % 2 = 1)) =
      2 ^ (79 - T.w) * ∑ i ∈ Finset.range (T.rcdt.length + 1),
        (pdtZ T i : ℚ) * (G i false + G i true) := by
  have hw : 72 ≤ T.w ∧ T.w ≤ 79 := by
    simp only [BaseTable.okB, Bool.and_eq_true, decide_eq_true_eq] at hT
    exact ⟨hT.1.1.1, hT.1.1.2⟩
  set e := T.w - 72 with he
  set H : ℕ → ℚ := fun U => G (baseZ T U) false + G (baseZ T U) true with hH
  have hc : ∀ u, ∑ c ∈ Finset.range (2 ^ 8), G (z0Of T u c) (decide (c % 2 = 1)) =
      2 ^ (7 - e) * ∑ v ∈ Finset.range (2 ^ e), H (u * 2 ^ e + v) := by
    intro u
    rw [show 2 ^ 8 = 2 ^ 7 * 2 by norm_num, sum_range_mul']
    have h2 : ∀ c', ∑ j ∈ Finset.range 2, G (z0Of T u (c' * 2 + j))
        (decide ((c' * 2 + j) % 2 = 1)) = H (u * 2 ^ e + c' % 2 ^ e) := by
      intro c'
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, z0Of, hH, ← he]
      rw [show (c' * 2 + 0) / 2 = c' by omega, show (c' * 2 + 1) / 2 = c' by omega,
        show (c' * 2 + 0) % 2 = 0 by omega, show (c' * 2 + 1) % 2 = 1 by omega]
      simp
    simp_rw [h2]
    rw [show 2 ^ 7 = 2 ^ (7 - e) * 2 ^ e by rw [← pow_add]; congr 1; omega, sum_range_mul']
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun v hv => by
      rw [show k * 2 ^ e + v = v + k * 2 ^ e by ring, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (Finset.mem_range.1 hv)]]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp_rw [hc, ← Finset.mul_sum]
  rw [← sum_range_mul' H, show 2 ^ 72 * 2 ^ e = 2 ^ T.w by rw [← pow_add]; congr 1; omega,
    show 7 - e = 79 - T.w by omega, hH]
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (g := baseZ T) (t := Finset.range (T.rcdt.length + 1))
    fun U _ => Finset.mem_range.2 (Nat.lt_succ_of_le (List.length_filter_le _ _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun U hU => by rw [(Finset.mem_filter.1 hU).2], Finset.sum_const,
    card_filter_baseZ T hT, nsmul_eq_mul]

/-- Averaging over the `2⁸⁰` draws of one round. -/
theorem avg_z0Of (T : BaseTable) (hT : T.okB = true) (G : ℕ → Bool → ℚ) :
    ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8),
        G (z0Of T u c) (decide (c % 2 = 1)) =
      2 ^ 80 * ∑ i ∈ Finset.range (T.rcdt.length + 1),
        ((pdtZ T i : ℚ) / 2 ^ (T.w + 1) * G i false + pdtZ T i / 2 ^ (T.w + 1) * G i true) := by
  have hw : T.w ≤ 79 := by
    simp only [BaseTable.okB, Bool.and_eq_true, decide_eq_true_eq] at hT
    exact hT.1.1.2
  rw [sum_z0Of T hT G, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (2 : ℚ) ^ 80 = 2 ^ (79 - T.w) * 2 ^ (T.w + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e]
  field_simp

/-- The law after `n` rounds at `σ̄`, `r`, `⌊t̄⌋ = s`. -/
def lawN (P : SampParams) (S : SampChoices) (σ r : ℚ) (s : ℤ) (n : ℕ) (y : ℤ) : ℚ :=
  (if y = s then (1 - accZ P S σ r) ^ n else 0) +
    (1 - (1 - accZ P S σ r) ^ n) / accZ P S σ r * wZz P S σ r (y - s)

theorem sum_one_range2 (a b : ℕ) :
    ∑ _u ∈ Finset.range (2 ^ a), ∑ _c ∈ Finset.range (2 ^ b), (1 : ℚ) = 2 ^ (a + b) := by
  simp [pow_add]

theorem accW_lt (P : SampParams) (rej : Bool) (x ccs : ℚ) : accW P rej x ccs < 2 ^ 64 := by
  simp only [accW]
  split
  · positivity
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)

/-- `wZz` selects the candidate `z`. -/
theorem sum_sel (P : SampParams) (S : SampChoices) (σ r : ℚ) (z : ℤ) :
    ∑ i ∈ Finset.range ((P.tab S.base).rcdt.length + 1),
      ((if zOf i false = z then wZ P S σ r i false else 0) +
        if zOf i true = z then wZ P S σ r i true else 0) = wZz P S σ r z := by
  have h0 : ∀ k, (P.tab S.base).rcdt.length + 1 ≤ k → ∀ b, wZ P S σ r k b = 0 := fun k hk b => by
    rw [wZ, pdtZ_eq_zero _ (by omega)]
    simp
  rw [Finset.sum_add_distrib, wZz]
  split_ifs with hz
  · have ht : ∀ i : ℕ, (zOf i true = z ↔ i = (z - 1).toNat) := fun i => by simp [zOf]; omega
    rw [Finset.sum_eq_zero fun i _ => ite_eq_right (by simp [zOf]; omega), zero_add]
    simp only [ht, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hk
    · rfl
    · exact (h0 _ (by omega) _).symm
  · have hf : ∀ i : ℕ, (zOf i false = z ↔ i = (-z).toNat) := fun i => by simp [zOf]; omega
    rw [Finset.sum_eq_zero (s := Finset.range _) (f := fun i =>
      if zOf i true = z then wZ P S σ r i true else 0) fun i _ => ite_eq_right
        (by simp [zOf]; omega), add_zero]
    simp only [hf, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hk
    · rfl
    · exact (h0 _ (by omega) _).symm

omit [LawfulMonad m] in
theorem bool_bind_apply {β : Type} [MeasurableSpace β] (mb : m Bool) (f : Bool → m β)
    {s : Set β} (hs : MeasurableSet s) :
    𝒟[mb >>= f] s = 𝒟[f true] s * 𝒟[mb] {true} + 𝒟[f false] s * 𝒟[mb] {false} := by
  rw [evalDist_bind_of_discrete, Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    lintegral_countable', tsum_fintype, Fintype.sum_bool]

theorem dirac_singleton (a y : ℤ) :
    (Measure.dirac a : Measure ℤ) {y} = if a = y then 1 else 0 := by
  rw [Measure.dirac_apply' _ (measurableSet_singleton y), Set.indicator_apply]
  simp

omit [LawfulMonad m] in
/-- The law of the rejection loop after `n` rounds. -/
theorem samplerLoop_apply (P : SampParams) (S : SampChoices) (hT : (P.tab S.base).okB = true)
    {ub : ℕ → m ℕ} (hub : UnifBits ub) (σ r : ℚ) (s : ℤ) :
    ∀ n y, 𝒟[samplerLoop P S ub σ r s n] {y} = ENNReal.ofReal (lawN P S σ r s n y) := by
  set T := P.tab S.base with hTdef
  set pa : ℕ → ℕ → ℚ := fun u c =>
    (accW P S.shiftRej (xOf P σ r (z0Of T u c) (decide (c % 2 = 1))) (P.σmin / σ) : ℚ) / 2 ^ 64
    with hpaDef
  have hpa0 : ∀ u c, 0 ≤ pa u c := fun u c => by positivity
  have hpa1 : ∀ u c, pa u c ≤ 1 := fun u c => by
    rw [div_le_one (by positivity)]
    exact_mod_cast (accW_lt _ _ _ _).le
  set A := accZ P S σ r with hAdef
  have hK2 : ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8), pa u c = 2 ^ 80 * A := by
    rw [avg_z0Of T hT (fun i b => (accW P S.shiftRej (xOf P σ r i b) (P.σmin / σ) : ℚ) / 2 ^ 64),
      hAdef, accZ, list_range_map_sum]
    rfl
  have hK1 : ∀ y, ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8),
      (if s + zOf (z0Of T u c) (decide (c % 2 = 1)) = y then pa u c else 0) =
        2 ^ 80 * wZz P S σ r (y - s) := fun y => by
    rw [avg_z0Of T hT (fun i b => if s + zOf i b = y then
      (accW P S.shiftRej (xOf P σ r i b) (P.σmin / σ) : ℚ) / 2 ^ 64 else 0),
      ← sum_sel P S σ r (y - s)]
    refine congrArg (fun t => (2 : ℚ) ^ 80 * t) (Finset.sum_congr rfl fun i _ => ?_)
    simp only [mul_ite, mul_zero, wZ, ← hTdef]
    exact congrArg₂ (· + ·) (if_congr (by omega) rfl rfl) (if_congr (by omega) rfl rfl)
  have hcount : ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8), (1 : ℚ) = 2 ^ 80 :=
    sum_one_range2 72 8
  have hA0 : 0 ≤ A := by
    have := Finset.sum_nonneg fun u (_ : u ∈ Finset.range (2 ^ 72)) =>
      Finset.sum_nonneg fun c (_ : c ∈ Finset.range (2 ^ 8)) => hpa0 u c
    rw [hK2] at this
    linarith
  have hA1 : A ≤ 1 := by
    have := Finset.sum_le_sum fun u (_ : u ∈ Finset.range (2 ^ 72)) =>
      Finset.sum_le_sum fun c (_ : c ∈ Finset.range (2 ^ 8)) => hpa1 u c
    rw [hK2, hcount] at this
    linarith
  have hw0 : ∀ z, 0 ≤ wZz P S σ r z := fun z => by
    unfold wZz wZ
    split_ifs <;> positivity
  have hwA : ∀ y, wZz P S σ r (y - s) ≤ A := fun y => by
    have := Finset.sum_le_sum fun u (_ : u ∈ Finset.range (2 ^ 72)) =>
      Finset.sum_le_sum fun c (_ : c ∈ Finset.range (2 ^ 8)) =>
        (show (if s + zOf (z0Of T u c) (decide (c % 2 = 1)) = y then pa u c else 0) ≤ pa u c by
          split_ifs
          · exact le_rfl
          · exact hpa0 u c)
    rw [hK1, hK2] at this
    linarith
  have hρ0 : 0 ≤ 1 - A := by linarith
  have hρ1 : 1 - A ≤ 1 := by linarith
  have hL0 : ∀ n y, 0 ≤ lawN P S σ r s n y := fun n y => by
    unfold lawN
    refine add_nonneg (by split_ifs <;> positivity) (mul_nonneg (div_nonneg ?_ hA0) (hw0 _))
    linarith [pow_le_one₀ hρ0 hρ1 (n := n)]
  intro n
  induction n with
  | zero =>
    intro y
    simp only [samplerLoop, evalDist_pure, dirac_singleton, lawN, pow_zero, sub_self, zero_div,
      zero_mul, add_zero]
    rcases eq_or_ne y s with h | h
    · simp [h]
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro y
    set L := lawN P S σ r s n y with hLdef
    set X : ℕ → ℕ → ℚ := fun u c =>
      if s + zOf (z0Of T u c) (decide (c % 2 = 1)) = y then pa u c else 0 with hX
    have hQnn : ∀ u c, 0 ≤ X u c + L * (1 - pa u c) := fun u c =>
      add_nonneg (by simp only [hX]; split_ifs; exacts [hpa0 u c, le_rfl])
        (mul_nonneg (hL0 n y) (sub_nonneg.2 (hpa1 u c)))
    have hQ : ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8),
        (X u c + L * (1 - pa u c)) = ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8),
          X u c + L * ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8), (1 : ℚ) -
            L * ∑ u ∈ Finset.range (2 ^ 72), ∑ c ∈ Finset.range (2 ^ 8), pa u c := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun c _ => by ring
    have hstep : ∑ u ∈ Finset.range (2 ^ 72), 1 / 2 ^ 72 * ∑ c ∈ Finset.range (2 ^ 8),
        1 / 2 ^ 8 * (X u c + L * (1 - pa u c)) = lawN P S σ r s (n + 1) y := by
      simp only [← Finset.mul_sum]
      rw [hQ, hK1, hcount, hK2, show (1 : ℚ) / 2 ^ 72 * (1 / 2 ^ 8 * (2 ^ 80 * wZz P S σ r (y - s) +
        L * 2 ^ 80 - L * (2 ^ 80 * A))) = wZz P S σ r (y - s) + L * (1 - A) by ring, hLdef]
      unfold lawN
      rw [← hAdef]
      by_cases hA : A = 0
      · have hw : wZz P S σ r (y - s) = 0 := le_antisymm (hA ▸ hwA y) (hw0 _)
        rw [hw, hA]
        simp
      · split_ifs <;> field_simp <;> ring
    have hD : ∀ k : ℕ, ((2 : ℝ≥0∞) ^ k)⁻¹ = ENNReal.ofReal (1 / 2 ^ k) := fun k => by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      norm_num
    rw [samplerLoop, unif_bind_apply hub 72 _ (measurableSet_singleton y)]
    calc _ = ∑ u ∈ Finset.range (2 ^ 72), ((2 : ℝ≥0∞) ^ 72)⁻¹ * ∑ c ∈ Finset.range (2 ^ 8),
          ((2 : ℝ≥0∞) ^ 8)⁻¹ * ENNReal.ofReal ((X u c + L * (1 - pa u c) : ℚ) : ℝ) := by
          refine Finset.sum_congr rfl fun u _ => congrArg _ ?_
          rw [unif_bind_apply hub 8 _ (measurableSet_singleton y)]
          refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
          rw [bool_bind_apply _ _ (measurableSet_singleton y), berExp_apply hub, berExp_apply hub]
          simp only [↓reduceIte, Bool.false_eq_true, evalDist_pure, dirac_singleton, ih,
            Nat.reduceMul, Nat.mod_eq_of_lt (accW_lt _ _ _ _)]
          rw [← ENNReal.ofReal_mul (by exact_mod_cast hL0 n y)]
          simp only [hX, hpaDef]
          split_ifs
          · rw [one_mul, ← ENNReal.ofReal_add (by positivity) (mul_nonneg
              (by exact_mod_cast hL0 n y) (by
                rw [sub_nonneg]
                exact div_le_one_of_le₀ (by exact_mod_cast (accW_lt _ _ _ _).le) (by positivity)))]
            refine congrArg ENNReal.ofReal ?_
            push_cast
            ring
          · rw [zero_mul, zero_add]
            refine congrArg ENNReal.ofReal ?_
            push_cast
            ring
      _ = ENNReal.ofReal (lawN P S σ r s (n + 1) y) := by
          rw [← hstep, Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg fun u _ => by
            exact_mod_cast mul_nonneg (by norm_num) (Finset.sum_nonneg fun c _ =>
              mul_nonneg (by norm_num) (hQnn u c))]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Rat.cast_mul, ENNReal.ofReal_mul (by positivity), Rat.cast_sum,
            ENNReal.ofReal_sum_of_nonneg fun c _ => by
              exact_mod_cast mul_nonneg (by norm_num) (hQnn u c), hD,
            show (((1 : ℚ) / 2 ^ 72 : ℚ) : ℝ) = 1 / 2 ^ 72 by norm_num]
          refine congrArg (ENNReal.ofReal (1 / 2 ^ 72) * ·) (Finset.sum_congr rfl fun c _ => ?_)
          rw [Rat.cast_mul, ENNReal.ofReal_mul (by positivity), hD,
            show (((1 : ℚ) / 2 ^ 8 : ℚ) : ℝ) = 1 / 2 ^ 8 by norm_num]

omit [LawfulMonad m] in
/-- **Node.** The output law of `samplerZ` is `lawZ`. -/
theorem samplerZ_law (P : SampParams) (S : SampChoices) (hT : (P.tab S.base).okB = true)
    (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64) (y : ℤ) :
    𝒟[samplerZ P S ub σ t] {y} = ENNReal.ofReal (lawZ P S σ t y) :=
  samplerLoop_apply P S hT hub _ _ _ _ y

end FalconPrecision.Exec
