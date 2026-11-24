/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.RefRun
public import FalconPrecision.Exec.SignRange
public import FalconPrecision.Exec.SignFast

/-! # The three arithmetics of the reference vectors

`opsX C`: the operations of the executable signer at the design point `C` (`Exec.Sign`: every
result reduced by `wordFn C.word`, products `Cx.mulW`, tables `twB`, `twsB` by `C.x.rc`).
`opsE`: exact complex arithmetic (tables `ζ`, `ζ̄/2`). `opsB`: balls `CB 64` with centres rounded
to nearest, ties to even, every rounded operation widened by its largest error over every
rounding mode (`Cx.half_err`, `Cx.mul_err`, `divqX_err` for both stored `1/q`), tables widened by
`0.7072·2⁻⁶⁴` (`twOk`); each value `MB` also carries the largest operation magnitude of its
derivation for each target order (`mS`, `mM`). `opsP C C'` runs two points side by side.

Relations: `RX` (the ball holds a computed value), `RE` (an exact value), `RW τ i` (the ball holds
the unbounded value, and the word value equals it when the magnitude of order `τ` is below
`2^(i-1)`). The reference tree `refTree δq k`: the balls `storeB` (`Exec.KeyExpand`) at ties to
even, `xn = 32`, node balls widened by `δq`, leaf balls by `1.825·2⁻⁴²` (what `check` at `δq`
allows). -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.HopB
  FalconPrecision.Errors.Fixed ComplexConjugate

/-! ## Balls -/

namespace CB

variable {f : ℕ}

/-- The radius increased by `e`. -/
def widen (b : CB f) (e : ℚ) : CB f := ⟨b.c, b.r.map (· + e)⟩

/-- A ball containing `a` and `b`, centred at `a`. -/
def hull (a b : CB f) : CB f :=
  ⟨a.c, a.r.bind fun x => b.r.map fun y => max x (y + (b.c.sub a.c).nUB)⟩

/-- The radius rounded up to the grid `2⁻⁹⁶`. -/
def coarse (b : CB f) : CB f := ⟨b.c, b.r.map (up 96)⟩

/-- An upper bound of every value of the ball (`0` if the radius is unknown). -/
def bnd (b : CB f) : ℚ := match b.r with
  | some r => b.c.nUB + r
  | none => 0

theorem Holds.widen {b : CB f} {z w : ℂ} {e : ℚ} (h : b.Holds z) (hw : ‖w - z‖ ≤ e) :
    (b.widen e).Holds w := by
  intro r hr
  change r ∈ b.r.map (· + e) at hr
  cases hb : b.r with
  | none => rw [hb] at hr; cases hr
  | some x =>
    rw [hb] at hr
    obtain rfl : x + e = r := Option.some.inj hr
    change ‖w - b.c.toC‖ ≤ ((x + e : ℚ) : ℝ)
    push_cast
    linarith [norm_sub_le_norm_sub_add_norm_sub w z b.c.toC, h x hb]

theorem Holds.widen_self {b : CB f} {z : ℂ} {e : ℚ} (h : b.Holds z) (he : 0 ≤ e) :
    (b.widen e).Holds z :=
  h.widen (by rw [sub_self, norm_zero]; exact_mod_cast he)

theorem Holds.hull_left {a : CB f} (b : CB f) {z : ℂ} (h : a.Holds z) : (a.hull b).Holds z := by
  intro r hr
  change r ∈ a.r.bind (fun x => b.r.map fun y => max x (y + (b.c.sub a.c).nUB)) at hr
  cases ha : a.r with
  | none => rw [ha] at hr; cases hr
  | some x =>
  cases hb : b.r with
  | none => rw [ha, hb] at hr; cases hr
  | some y =>
    rw [ha, hb] at hr
    obtain rfl : max x (y + (b.c.sub a.c).nUB) = r := Option.some.inj hr
    change ‖z - a.c.toC‖ ≤ ((max x (y + (b.c.sub a.c).nUB) : ℚ) : ℝ)
    exact (h x ha).trans (by exact_mod_cast le_max_left _ _)

theorem Holds.hull_right (a : CB f) {b : CB f} {z : ℂ} (h : b.Holds z) :
    (a.hull b).Holds z := by
  intro r hr
  change r ∈ a.r.bind (fun x => b.r.map fun y => max x (y + (b.c.sub a.c).nUB)) at hr
  cases ha : a.r with
  | none => rw [ha] at hr; cases hr
  | some x =>
  cases hb : b.r with
  | none => rw [ha, hb] at hr; cases hr
  | some y =>
    rw [ha, hb] at hr
    obtain rfl : max x (y + (b.c.sub a.c).nUB) = r := Option.some.inj hr
    change ‖z - a.c.toC‖ ≤ ((max x (y + (b.c.sub a.c).nUB) : ℚ) : ℝ)
    have hn := (b.c.sub a.c).norm_le_nUB
    rw [Cx.toC_sub] at hn
    have := norm_sub_le_norm_sub_add_norm_sub z b.c.toC a.c.toC
    have h2 : ((y + (b.c.sub a.c).nUB : ℚ) : ℝ) ≤ ((max x (y + (b.c.sub a.c).nUB) : ℚ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have h3 : ((y + (b.c.sub a.c).nUB : ℚ) : ℝ) = y + (b.c.sub a.c).nUB := by push_cast; ring
    linarith [h y hb]

theorem Holds.coarse {b : CB f} {z : ℂ} (h : b.Holds z) : b.coarse.Holds z := by
  intro r hr
  change r ∈ b.r.map (up 96) at hr
  cases hb : b.r with
  | none => rw [hb] at hr; cases hr
  | some x =>
    rw [hb] at hr
    obtain rfl : up 96 x = r := Option.some.inj hr
    exact (h x hb).trans (by exact_mod_cast le_up 96 x)

/-- `z/q` with the stored `1/q` of either width (`divqX_err`): centre `divqX .halfEven .w77`. -/
def divq (a : CB 64) : CB 64 :=
  ⟨divqX .halfEven .w77 a.c, a.r.map fun r => up (K 64) (r / 12289 + (2 + 2 * a.c.nUB) / 2 ^ 64 +
    (2 + 2 * (a.c.nUB + r)) / 2 ^ 64)⟩

end CB

/-- A ball and the largest operation magnitude of its derivation, scale-first and multiply-first
target. -/
structure MB where
  b : CB 64
  mS : ℚ
  mM : ℚ

instance : Inhabited MB := ⟨⟨default, 0, 0⟩⟩

/-- The magnitude bound of the order `τ`. -/
def MB.m : Target → MB → ℚ
  | .scaleFirst, x => x.mS
  | .multiplyFirst, x => x.mM

/-- A result `b` of an operation on `x`, `y` with local magnitude `e`. -/
def MB.lift2 (b : CB 64) (x y : MB) (e : ℚ) : MB :=
  ⟨b, max (max x.mS y.mS) e, max (max x.mM y.mM) e⟩

/-- A result `b` of an operation on `x` with local magnitude `e`. -/
def MB.lift1 (b : CB 64) (x : MB) (e : ℚ) : MB := ⟨b, max x.mS e, max x.mM e⟩

/-- The table error bound `0.7072·2⁻⁶⁴` of `twOk`. -/
def δtw : ℚ := 7072 / 10000 / 2 ^ 64

/-- The `ζ` tables at levels `< 9` (ties to even), widened by `δtw`. -/
def twTA : Array (Array (CB 64)) :=
  (Array.range 9).map fun L => (twBA .halfEven 64 L).map (·.widen δtw)

/-- The `ζ̄/2` tables at levels `< 9` (ties to even), widened by `δtw`. -/
def twsTA : Array (Array (CB 64)) :=
  (Array.range 9).map fun L => (twsBA .halfEven 64 L).map (·.widen δtw)

/-- The ball arithmetic with the tables `tA` (`ζ`), `sA` (`ζ̄/2`) per level. -/
def opsBT (tA sA : Array (Array (CB 64))) : VOps MB where
  add x y := let r := x.b.add y.b; .lift2 r x y r.bnd
  sub x y := let r := x.b.sub y.b; .lift2 r x y r.bnd
  neg x := let r := x.b.neg; .lift1 r x r.bnd
  half x := let r := (x.b.half .halfEven).widen (2 / 2 ^ 64); .lift1 r x r.bnd
  mul x y := let r := (CB.mul .halfEven x.b y.b).widen (4 / 2 ^ 64);
    .lift2 r x y (max r.bnd (x.b.bnd * y.b.bnd + 2 / 2 ^ 64))
  divq x := let r := x.b.divq; .lift1 r x r.bnd
  cst n := ⟨CB.ofInt n, |(n : ℚ)|, |(n : ℚ)|⟩
  ofInt n := ⟨CB.ofInt n, 0, 0⟩
  tw L o := ⟨(tA.getD L #[]).getD (Out.idx L o) default, 0, 0⟩
  tws L o := ⟨(sA.getD L #[]).getD (Out.idx L o) default, 0, 0⟩

/-- **The ball arithmetic of the vectors.** -/
def opsB : VOps MB := opsBT twTA twsTA

/-- The operations of the executable signer at `C` (`fftW`, `splitW`, `mergeW`, `updW`,
`targetX`). -/
def opsX (C : Choices) : VOps (Cx 64) where
  add a b := (a.add b).wr (wordFn C.word)
  sub a b := (a.sub b).wr (wordFn C.word)
  neg a := a.neg.wr (wordFn C.word)
  half a := (a.half C.x.rm).wr (wordFn C.word)
  mul a b := a.mulW (wordFn C.word) C.x.rm b
  divq a := (divqX C.x.rm C.qinv a).wr (wordFn C.word)
  cst n := (Cx.ofInt n : Cx 64).wr (wordFn C.word)
  ofInt n := Cx.ofInt n
  tw L o := (twB C.x.rc 64 L o).c
  tws L o := (twsB C.x.rc 64 L o).c

/-- Exact complex arithmetic. -/
noncomputable def opsE : VOps ℂ where
  add a b := a + b
  sub a b := a - b
  neg a := -a
  half a := a / 2
  mul a b := a * b
  divq a := a / 12289
  cst n := n
  ofInt n := n
  tw L o := zeta L o
  tws L o := conj (zeta L o) / 2

/-- Two points side by side. -/
def opsP (C C' : Choices) : VOps (Cx 64 × Cx 64) where
  add a b := ((opsX C).add a.1 b.1, (opsX C').add a.2 b.2)
  sub a b := ((opsX C).sub a.1 b.1, (opsX C').sub a.2 b.2)
  neg a := ((opsX C).neg a.1, (opsX C').neg a.2)
  half a := ((opsX C).half a.1, (opsX C').half a.2)
  mul a b := ((opsX C).mul a.1 b.1, (opsX C').mul a.2 b.2)
  divq a := ((opsX C).divq a.1, (opsX C').divq a.2)
  cst n := ((opsX C).cst n, (opsX C').cst n)
  ofInt n := ((opsX C).ofInt n, (opsX C').ofInt n)
  tw L o := ((opsX C).tw L o, (opsX C').tw L o)
  tws L o := ((opsX C).tws L o, (opsX C').tws L o)

/-! ## Relations -/

/-- The ball holds the computed value. -/
def RX (b : MB) (x : Cx 64) : Prop := b.b.Holds x.toC

/-- The ball holds the exact value. -/
def RE (b : MB) (z : ℂ) : Prop := b.b.Holds z

/-- The ball holds the unbounded value `p.2`; the word value `p.1` equals it when the radius is
known and the magnitude of order `τ` is below `2^(i-1)`. -/
def RW (τ : Target) (i : ℕ) (b : MB) (p : Cx 64 × Cx 64) : Prop :=
  b.b.Holds p.2.toC ∧ (b.b.r.isSome = true → MB.m τ b < 2 ^ (i - 1) → p.1 = p.2)

/-! ## Trees -/

/-- A stored tree over `Cx 64` (leaf `σ̄` as a real value). -/
def CTree.toG : {L : ℕ} → CTree 64 L → GTree (Cx 64) L
  | _, .leaf σ => .leaf ⟨σ, ⟨0⟩⟩
  | _, .node ℓ T0 T1 => .node ℓ T0.toG T1.toG

/-- The true tree over `ℂ`. -/
noncomputable def _root_.FalconPrecision.Errors.HopB.LTree.toG : {L : ℕ} → LTree L → GTree ℂ L
  | _, .leaf σ => .leaf (σ : ℂ)
  | _, .node ℓ T0 T1 => .node ℓ T0.toG T1.toG

/-- Every value mapped by `g`. -/
def GTree.map {V W : Type} (g : V → W) : {L : ℕ} → GTree V L → GTree W L
  | _, .leaf σ => .leaf (g σ)
  | _, .node ℓ T0 T1 => .node (fun o => g (ℓ o)) (T0.map g) (T1.map g)

theorem GTree.Rel.map_self {V W : Type} {R : W → V → Prop} (g : V → W) (hg : ∀ x, R (g x) x) :
    ∀ {L : ℕ} (T : GTree V L), (T.map g).Rel R T
  | _, .leaf _ => hg _
  | _, .node _ T0 T1 => ⟨fun _ => hg _, map_self g hg T0, map_self g hg T1⟩

/-- The leaf tolerance of `check`: `|σ̄/σ - 1| ≤ 2⁻⁴²`, `σ ≤ 1.825`. -/
def σtol : ℚ := 1825 / 1000 / 2 ^ 42

/-- A ball tree widened by `δq L` at the nodes of depth `L + 1` and by `σtol` at the leaves. -/
def BTree.toGW (δq : ℕ → ℚ) : {L : ℕ} → BTree 64 L → GTree MB L
  | _, .leaf s => .leaf ⟨s.widen σtol, 0, 0⟩
  | _, @BTree.node _ L ℓ T0 T1 =>
    .node (fun o => ⟨(ℓ o).widen (δq L), 0, 0⟩) (T0.toGW δq) (T1.toGW δq)

/-- The reference key-expansion point: ties to even, `y/x`, plain root. -/
def P0 : XChoices := ⟨.halfEven, .halfEven, .direct, .plain⟩

/-- **The reference tree**: `storeB P0 32 k` (array version) widened for `check` at `δq`. -/
def refTree (δq : ℕ → ℚ) (k : RawKey) : GTree MB 9 :=
  ((expandBA P0 (64 + 32) k).lower P0.rm 32).toGW δq

/-! ## Instances -/

theorem CB.Holds.divq {a : CB 64} {z w : ℂ} (h : a.Holds z)
    (hw : ‖w - z / 12289‖ ≤ 2 / 2 ^ 64 + 2 * ‖z‖ / 2 ^ 64) : a.divq.Holds w := by
  intro r hr
  cases hx : a.r with
  | none => change r ∈ a.r.map _ at hr; rw [hx] at hr; cases hr
  | some x =>
    obtain rfl : up (K 64) (x / 12289 + (2 + 2 * a.c.nUB) / 2 ^ 64 +
        (2 + 2 * (a.c.nUB + x)) / 2 ^ 64) = r := by
      change r ∈ a.r.map _ at hr; rw [hx] at hr; exact Option.some.inj hr
    have hc := divqX_err .halfEven .w77 a.c
    have hz := h x hx
    have hn := a.c.norm_le_nUB
    have hzn := norm_le_norm_add_norm_sub' z a.c.toC
    have hq : ‖z / 12289 - a.c.toC / 12289‖ ≤ x / 12289 := by
      rw [← sub_div, norm_div, Complex.norm_ofNat]
      exact div_le_div_of_nonneg_right hz (by norm_num)
    have hc' : ‖a.c.toC / 12289 - (divqX .halfEven .w77 a.c).toC‖ ≤
        2 / 2 ^ 64 + 2 * ‖a.c.toC‖ / 2 ^ 64 := by
      rw [norm_sub_rev]; exact hc
    refine CB.le_up_of (f := 64) (X := z / 12289) hw
      ((norm_sub_le_norm_sub_add_norm_sub _ (a.c.toC / 12289) _).trans (add_le_add hq hc')) ?_
    push_cast
    linarith

theorem CB.norm_le_bnd {f : ℕ} {b : CB f} {z : ℂ} (h : b.Holds z) (hs : b.r.isSome = true) :
    ‖z‖ ≤ (b.bnd : ℝ) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hs
  have hz := h r hr
  have e : (b.bnd : ℝ) = b.c.nUB + r := by simp only [CB.bnd, hr, Rat.cast_add]
  have := norm_le_norm_add_norm_sub' z b.c.toC
  linarith [b.c.norm_le_nUB]

/-- The `ζ` table of `opsB` at a level `< 9`. -/
theorem opsB_tw {L : ℕ} (hL : L < 9) (o : Out L) :
    (opsB.tw L o).b = (twB .halfEven 64 L o).widen δtw := by
  have e : twTA.getD L #[] = (twBA .halfEven 64 L).map (·.widen δtw) := by
    simp [twTA, Array.getD_eq_getD_getElem?, hL]
  change (twTA.getD L #[]).getD (Out.idx L o) default = _
  rw [e, ← ofArr_twBA]
  simp only [ofArr, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases (twBA .halfEven 64 L)[Out.idx L o]? <;> rfl

/-- The `ζ̄/2` table of `opsB` at a level `< 9`. -/
theorem opsB_tws {L : ℕ} (hL : L < 9) (o : Out L) :
    (opsB.tws L o).b = (twsB .halfEven 64 L o).widen δtw := by
  have e : twsTA.getD L #[] = (twsBA .halfEven 64 L).map (·.widen δtw) := by
    simp [twsTA, Array.getD_eq_getD_getElem?, hL]
  change (twsTA.getD L #[]).getD (Out.idx L o) default = _
  rw [e, ← ofArr_twsBA]
  simp only [ofArr, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases (twsBA .halfEven 64 L)[Out.idx L o]? <;> rfl

theorem wr_none (C : Choices) (hw : C.word = none) (z : Cx 64) : z.wr (wordFn C.word) = z := by
  rw [hw]; rfl

theorem mulW_none (C : Choices) (hw : C.word = none) (r : RMode) (z u : Cx 64) :
    z.mulW (wordFn C.word) r u = z.mul r u := by
  rw [hw]; rfl

/-- The ball arithmetic holds every unbounded computed run whose tables pass `twOk`. -/
theorem simX (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true) :
    VSim opsB (opsX C) RX where
  add ha hb := by
    change CB.Holds _ (Cx.toC (Cx.wr (wordFn C.word) (Cx.add _ _)))
    rw [wr_none C hw, Cx.toC_add]; exact CB.Holds.add ha hb
  sub ha hb := by
    change CB.Holds _ (Cx.toC (Cx.wr (wordFn C.word) (Cx.sub _ _)))
    rw [wr_none C hw, Cx.toC_sub]; exact CB.Holds.sub ha hb
  neg ha := by
    change CB.Holds _ (Cx.toC (Cx.wr (wordFn C.word) (Cx.neg _)))
    rw [wr_none C hw, Cx.toC_neg]; exact CB.Holds.neg ha
  half {_ x} ha := by
    change CB.Holds _ (Cx.toC (Cx.wr (wordFn C.word) (Cx.half C.x.rm _)))
    rw [wr_none C hw]
    exact (CB.Holds.half .halfEven ha).widen
      (by simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]; exact Cx.half_err C.x.rm x)
  mul {_ _ x y} ha hb := by
    change CB.Holds _ (Cx.toC (Cx.mulW (wordFn C.word) C.x.rm _ _))
    rw [mulW_none C hw]
    exact (CB.Holds.mul .halfEven ha hb).widen
      (by simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]; exact Cx.mul_err C.x.rm x y)
  divq ha := by
    change CB.Holds _ (Cx.toC (Cx.wr (wordFn C.word) (divqX C.x.rm C.qinv _)))
    rw [wr_none C hw]
    exact CB.Holds.divq ha (divqX_err _ _ _)
  cst n := by
    change CB.Holds _ (Cx.toC (Cx.wr (wordFn C.word) (Cx.ofInt n)))
    rw [wr_none C hw, Cx.toC_ofInt]; exact CB.ofInt_holds n
  ofInt n := by
    change CB.Holds _ (Cx.toC (Cx.ofInt n))
    rw [Cx.toC_ofInt]; exact CB.ofInt_holds n
  tw L o hL := by
    change CB.Holds (opsB.tw L o).b (twB C.x.rc 64 L o).c.toC
    rw [opsB_tw hL]
    exact (twB_holds .halfEven 64 L o).widen
      (by simp only [δtw, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
          exact tw_err htw (by omega) o)
  tws L o hL := by
    change CB.Holds (opsB.tws L o).b (twsB C.x.rc 64 L o).c.toC
    rw [opsB_tws hL]
    exact (twsB_holds .halfEven 64 L o).widen
      (by simp only [δtw, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
          exact tws_err htw (by omega) o)

/-- The ball arithmetic holds the exact run. -/
theorem simE : VSim opsB opsE RE where
  add ha hb := CB.Holds.add ha hb
  sub ha hb := CB.Holds.sub ha hb
  neg ha := CB.Holds.neg ha
  half ha := (CB.Holds.half .halfEven ha).widen_self (by norm_num)
  mul ha hb := (CB.Holds.mul .halfEven ha hb).widen_self (by norm_num)
  divq {_ x} ha := CB.Holds.divq ha
    (by change ‖x / 12289 - x / 12289‖ ≤ _; rw [sub_self, norm_zero]; positivity)
  cst n := CB.ofInt_holds n
  ofInt n := CB.ofInt_holds n
  tw L o hL := by
    change CB.Holds (opsB.tw L o).b (zeta L o)
    rw [opsB_tw hL]
    exact (twB_holds _ _ L o).widen_self (by norm_num [δtw])
  tws L o hL := by
    change CB.Holds (opsB.tws L o).b (starRingEnd ℂ (zeta L o) / 2)
    rw [opsB_tws hL]
    exact (twsB_holds _ _ L o).widen_self (by norm_num [δtw])

theorem MB.m_lift2 (τ : Target) (b : CB 64) (x y : MB) (e : ℚ) :
    MB.m τ (MB.lift2 b x y e) = max (max (MB.m τ x) (MB.m τ y)) e := by
  cases τ <;> rfl

theorem MB.m_lift1 (τ : Target) (b : CB 64) (x : MB) (e : ℚ) :
    MB.m τ (MB.lift1 b x e) = max (MB.m τ x) e := by
  cases τ <;> rfl

theorem MB.m_mk (τ : Target) (b : CB 64) (u : ℚ) : MB.m τ ⟨b, u, u⟩ = u := by
  cases τ <;> rfl

theorem CB.add_isSome {a b : CB 64} (h : (a.add b).r.isSome = true) :
    a.r.isSome = true ∧ b.r.isSome = true := by
  obtain ⟨_, _ | _⟩ := a <;> obtain ⟨_, _ | _⟩ := b <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h Bool.false_ne_true

theorem CB.sub_isSome {a b : CB 64} (h : (a.sub b).r.isSome = true) :
    a.r.isSome = true ∧ b.r.isSome = true := by
  obtain ⟨_, _ | _⟩ := a <;> obtain ⟨_, _ | _⟩ := b <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h Bool.false_ne_true

theorem CB.mul_isSome {a b : CB 64} {e : ℚ}
    (h : ((CB.mul .halfEven a b).widen e).r.isSome = true) :
    a.r.isSome = true ∧ b.r.isSome = true := by
  obtain ⟨_, _ | _⟩ := a <;> obtain ⟨_, _ | _⟩ := b <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h Bool.false_ne_true

theorem CB.half_isSome {a : CB 64} {e : ℚ} (h : ((a.half .halfEven).widen e).r.isSome = true) :
    a.r.isSome = true := by
  obtain ⟨_, _ | _⟩ := a
  · exact absurd h Bool.false_ne_true
  · rfl

theorem CB.divq_isSome {a : CB 64} (h : a.divq.r.isSome = true) : a.r.isSome = true := by
  obtain ⟨_, _ | _⟩ := a
  · exact absurd h Bool.false_ne_true
  · rfl

theorem wr_of_bnd {i : ℕ} (hi : 1 ≤ i) {B : MB} {z : Cx 64} (hh : B.b.Holds z.toC)
    (hs : B.b.r.isSome = true) (hm : B.b.bnd < 2 ^ (i - 1)) : z.wr (wordFn (some i)) = z :=
  Cx.wr_some hi ((CB.norm_le_bnd hh hs).trans_lt (by exact_mod_cast hm))

/-- Words: the ball arithmetic holds the unbounded run, and reductions to `(i + 64)`-bit words
change nothing below the magnitude bound. -/
theorem simW (C : Choices) {i : ℕ} (hi : 1 ≤ i) (hw : C.word = some i) (htw : twOk C.x.rc = true) :
    VSim opsB (opsP C { C with word := none }) (RW C.target i) := by
  have hX := simX { C with word := none } rfl htw
  refine ⟨fun {a b x y} ha hb => ⟨hX.add ha.1 hb.1, fun hs hm => ?_⟩,
    fun {a b x y} ha hb => ⟨hX.sub ha.1 hb.1, fun hs hm => ?_⟩,
    fun {a x} ha => ⟨hX.neg ha.1, fun hs hm => ?_⟩,
    fun {a x} ha => ⟨hX.half ha.1, fun hs hm => ?_⟩,
    fun {a b x y} ha hb => ⟨hX.mul ha.1 hb.1, fun hs hm => ?_⟩,
    fun {a x} ha => ⟨hX.divq ha.1, fun hs hm => ?_⟩,
    fun n => ⟨hX.cst n, fun _ hm => ?_⟩, fun n => ⟨hX.ofInt n, fun _ _ => rfl⟩,
    fun L o hL => ⟨hX.tw L o hL, fun _ _ => rfl⟩, fun L o hL => ⟨hX.tws L o hL, fun _ _ => rfl⟩⟩
  · obtain ⟨sa, sb⟩ := CB.add_isSome hs
    change MB.m _ (MB.lift2 _ a b _) < _ at hm
    rw [MB.m_lift2, max_lt_iff, max_lt_iff] at hm
    change (Cx.add x.1 y.1).wr (wordFn C.word) = (Cx.add x.2 y.2).wr (wordFn none)
    rw [ha.2 sa hm.1.1, hb.2 sb hm.1.2, hw]
    exact wr_of_bnd hi (B := opsB.add a b) (hX.add ha.1 hb.1) hs hm.2
  · obtain ⟨sa, sb⟩ := CB.sub_isSome hs
    change MB.m _ (MB.lift2 _ a b _) < _ at hm
    rw [MB.m_lift2, max_lt_iff, max_lt_iff] at hm
    change (Cx.sub x.1 y.1).wr (wordFn C.word) = (Cx.sub x.2 y.2).wr (wordFn none)
    rw [ha.2 sa hm.1.1, hb.2 sb hm.1.2, hw]
    exact wr_of_bnd hi (B := opsB.sub a b) (hX.sub ha.1 hb.1) hs hm.2
  · change MB.m _ (MB.lift1 _ a _) < _ at hm
    rw [MB.m_lift1, max_lt_iff] at hm
    change (Cx.neg x.1).wr (wordFn C.word) = (Cx.neg x.2).wr (wordFn none)
    rw [ha.2 hs hm.1, hw]
    exact wr_of_bnd hi (B := opsB.neg a) (hX.neg ha.1) hs hm.2
  · change MB.m _ (MB.lift1 _ a _) < _ at hm
    rw [MB.m_lift1, max_lt_iff] at hm
    change (Cx.half C.x.rm x.1).wr (wordFn C.word) = (Cx.half C.x.rm x.2).wr (wordFn none)
    rw [ha.2 (CB.half_isSome hs) hm.1, hw]
    exact wr_of_bnd hi (B := opsB.half a) (hX.half ha.1) hs hm.2
  · obtain ⟨sa, sb⟩ := CB.mul_isSome hs
    change MB.m _ (MB.lift2 _ a b _) < _ at hm
    rw [MB.m_lift2, max_lt_iff, max_lt_iff, max_lt_iff] at hm
    change Cx.mulW (wordFn C.word) C.x.rm x.1 y.1 = Cx.mulW (wordFn none) C.x.rm x.2 y.2
    rw [ha.2 sa hm.1.1, hb.2 sb hm.1.2, hw]
    have h1 := CB.norm_le_bnd ha.1 sa
    have h2 := CB.norm_le_bnd hb.1 sb
    have h3 : ((a.b.bnd * b.b.bnd + 2 / 2 ^ 64 : ℚ) : ℝ) < 2 ^ (i - 1) := by
      exact_mod_cast hm.2.2
    push_cast at h3
    have h4 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    rw [Cx.mulW_some hi C.x.rm (z := x.2) (w := y.2) (by linarith)]
    rfl
  · change MB.m _ (MB.lift1 _ a _) < _ at hm
    rw [MB.m_lift1, max_lt_iff] at hm
    change (divqX C.x.rm C.qinv x.1).wr (wordFn C.word) =
      (divqX C.x.rm C.qinv x.2).wr (wordFn none)
    rw [ha.2 (CB.divq_isSome hs) hm.1, hw]
    exact wr_of_bnd hi (B := opsB.divq a) (hX.divq ha.1) hs hm.2
  · change MB.m _ ⟨_, |(n : ℚ)|, |(n : ℚ)|⟩ < _ at hm
    rw [MB.m_mk] at hm
    change (Cx.ofInt n : Cx 64).wr (wordFn C.word) = (Cx.ofInt n : Cx 64).wr (wordFn none)
    rw [hw]
    exact Cx.wr_some hi (by rw [Cx.toC_ofInt, Complex.norm_intCast]; exact_mod_cast hm)

theorem GTree.Rel.map_right {V W W' : Type} {R : V → W → Prop} {R' : V → W' → Prop}
    (g : W → W') (hg : ∀ a x, R a x → R' a (g x)) :
    ∀ {L : ℕ} (A : GTree V L) (B : GTree W L), A.Rel R B → A.Rel R' (B.map g)
  | _, .leaf _, .leaf _, h => hg _ _ h
  | _, .node _ A0 A1, .node _ B0 B1, h =>
    ⟨fun o => hg _ _ (h.1 o), map_right g hg A0 B0 h.2.1, map_right g hg A1 B1 h.2.2⟩

theorem simP1 (C C' : Choices) : VSim (opsP C C') (opsX C) fun p x => p.1 = x where
  add h1 h2 := by subst h1 h2; rfl
  sub h1 h2 := by subst h1 h2; rfl
  neg h := by subst h; rfl
  half h := by subst h; rfl
  mul h1 h2 := by subst h1 h2; rfl
  divq h := by subst h; rfl
  cst _ := rfl
  ofInt _ := rfl
  tw _ _ _ := rfl
  tws _ _ _ := rfl

/-- A widened ball tree holding `U` holds every ball tree holding `U` whose radii pass
`radOkB δq`, at its centres. -/
theorem BTree.toGW_relX (δq : ℕ → ℚ) : ∀ {L : ℕ} (A B : BTree 64 L) (U : LTree L),
    A.HoldsT U → B.HoldsT U → B.radOkB δq = true → (A.toGW δq).Rel RX B.centre.toG
  | _, .leaf s, .leaf s', .leaf σ, hA, hB, hr => by
    cases hx : s'.r with
    | none => simp [BTree.radOkB, CB.leafOkB, hx] at hr
    | some r =>
      simp only [BTree.radOkB, CB.leafOkB, hx, Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨⟨-, h2⟩, h3⟩ := hr
      have hd := hB r hx
      have r0 : (0 : ℚ) ≤ r := by exact_mod_cast (norm_nonneg _).trans hd
      have hσ : r ≤ σtol := by
        rw [σtol, le_div_iff₀ (by positivity)]; linarith
      have e : (⟨s'.c.re, ⟨0⟩⟩ : Cx 64).toC = (s'.c.re.toReal : ℂ) :=
        Complex.ext rfl (by change (⟨0⟩ : Fx 64).toReal = 0; simp [Fx.toReal])
      have hre : |s'.c.re.toReal - σ| ≤ r := by
        have e2 : (s'.c.toC - (σ : ℂ)).re = s'.c.re.toReal - σ := by simp [Cx.toC]
        rw [← e2]
        exact (Complex.abs_re_le_norm _).trans (by rw [norm_sub_rev]; exact hd)
      refine CB.Holds.widen (z := (σ : ℂ)) hA ?_
      show ‖(⟨s'.c.re, ⟨0⟩⟩ : Cx 64).toC - (σ : ℂ)‖ ≤ _
      rw [e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hre.trans (by exact_mod_cast hσ)
  | _, @BTree.node _ L ℓ A0 A1, .node ℓ' B0 B1, .node ℓt U0 U1, hA, hB, hr => by
    simp only [BTree.radOkB, Bool.and_eq_true] at hr
    exact ⟨fun o => (hA.1 o).widen
        (CB.norm_sub_le_of_radLeB (hB.1 o) ((allOut_iff _ _).1 hr.1.1 o)),
      toGW_relX δq A0 B0 U0 hA.2.1 hB.2.1 hr.1.2, toGW_relX δq A1 B1 U1 hA.2.2 hB.2.2 hr.2⟩

/-- A widened ball tree holding `U` holds `U`. -/
theorem BTree.toGW_relE (δq : ℕ → ℚ) (hδ : ∀ L, 0 ≤ δq L) : ∀ {L : ℕ} (A : BTree 64 L)
    (U : LTree L), A.HoldsT U → (A.toGW δq).Rel RE U.toG
  | _, .leaf _, .leaf _, hA => CB.Holds.widen_self hA (by norm_num [σtol])
  | _, @BTree.node _ L _ A0 A1, .node _ U0 U1, hA =>
    ⟨fun o => (hA.1 o).widen_self (hδ L), toGW_relE δq hδ A0 U0 hA.2.1,
      toGW_relE δq hδ A1 U1 hA.2.2⟩

/-- The stored tree of every point passing `check` at `δq` lies in the reference tree. -/
theorem treeX (C : Choices) (δq : ℕ → ℚ) (k : RawKey) (hk : check C.x C.xn δq k = true) :
    (refTree δq k).Rel RX (storeC C.x C.xn k).toG := by
  have hc := check_ok C.x C.xn hk
  rw [← storeB_centre, refTree, expandBA_eq]
  exact BTree.toGW_relX δq _ _ _ (storeB_holdsT P0 32 k hc.ntru)
    (storeB_holdsT C.x C.xn k hc.ntru) hc.rad

/-- The true tree lies in the reference tree. -/
theorem treeE (δq : ℕ → ℚ) (hδ : ∀ L, 0 ≤ δq L) (k : RawKey) (hn : ntruB k = true) :
    (refTree δq k).Rel RE k.trueTree.toG := by
  rw [refTree, expandBA_eq]
  exact BTree.toGW_relE δq hδ _ _ (storeB_holdsT P0 32 k hn)

end FalconPrecision.Exec
