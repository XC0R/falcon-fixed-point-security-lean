/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Twiddle

/-! # Executable Falcon-512 key expansion with running error bounds

Key expansion (spec Alg. 4 l. 3-7; ePrint 2026/1531 Alg. 5 ffLDL⋆): the FFT of `f, g, F, G`, the
Gram matrix `B·B⋆` of `B = [[g, -f], [G, -F]]`, ffLDL⋆ (`ℓ = g10/g00`, `D11 = g11 - |g10|²/g00`,
children ffLDL⋆ of the splits of the diagonals) and the leaves `σ/√D`. Two versions with the same
operations: `expandC` computes the stored tree (`CTree`, the values a signer stores), `expandB`
computes it in balls (`BTree`): every value with a running bound on its distance to the exact
value. `expandB_centre`: the centres of `expandB` are `expandC`.

The choices (`XChoices`, ePrint 2026/2902 (iii), (iv)): the rounding rule of every operation `rm`
and of the stored constants `rc` (twiddles, `σ`), division `y/x` or `1/x·y`, and the root `D11`
directly or by the NTRU identity `q²/g00`. The fraction bits `f` are a parameter (the tables are
computed at `f + 64` bits and rounded once). Not parameters here: the FFT is the merge recursion
of `Arith.fft` (full spectrum), the leaf is `σ/√D` (root then quotient).

Storage: `storeC P n k` runs `expandC` at the working precision `64 + n` fraction bits and rounds
every stored `ℓ̂`, `σ̄` once to 64 fraction bits by `P.rm` (`CTree.lower`); `storeB` does the same
in balls (`CB.lower`). At `n = 0` the rounding is the identity (`CTree.lower_zero`). -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec ComplexConjugate

/-- The root `D11`: `g11 - |g10|²/g00`, or `q²/g00` (needs `fG - gF = q`). -/
inductive RootMode where
  | plain
  | ntru
  deriving DecidableEq, Repr

/-- Key-expansion choices. -/
structure XChoices where
  /-- Rounding of every operation. -/
  rm : RMode
  /-- Rounding of the stored constants (twiddle tables, `σ`). -/
  rc : RMode
  /-- Division by a diagonal entry. -/
  dm : Cx.DivMode
  /-- The root `D11`. -/
  root : RootMode
  deriving DecidableEq, Repr

/-- A raw Falcon-512 private basis `[[g, -f], [G, -F]]`. -/
structure RawKey where
  f : Fin (2 ^ 9) → ℤ
  g : Fin (2 ^ 9) → ℤ
  F : Fin (2 ^ 9) → ℤ
  G : Fin (2 ^ 9) → ℤ

/-- Falcon-512's `σ = 165.736617183` (spec Table 3.3). -/
def σ512q : ℚ := 165736617183 / 10 ^ 9

/-- Even-index coefficients. -/
def evensZ {L : ℕ} (a : Fin (2 ^ (L + 1)) → ℤ) : Fin (2 ^ L) → ℤ :=
  fun i => a ⟨2 * i, by have := i.2; rw [pow_succ]; omega⟩

/-- Odd-index coefficients. -/
def oddsZ {L : ℕ} (a : Fin (2 ^ (L + 1)) → ℤ) : Fin (2 ^ L) → ℤ :=
  fun i => a ⟨2 * i + 1, by have := i.2; rw [pow_succ]; omega⟩

/-- A stored Falcon tree: `ℓ̂` at the nodes, `σ̄` at the leaves. -/
inductive CTree (f : ℕ) : ℕ → Type
  | leaf (σ : Fx f) : CTree f 0
  | node {L : ℕ} (ℓ : Out (L + 1) → Cx f) (T0 T1 : CTree f L) : CTree f (L + 1)

/-- A stored tree in balls. -/
inductive BTree (f : ℕ) : ℕ → Type
  | leaf (s : CB f) : BTree f 0
  | node {L : ℕ} (ℓ : Out (L + 1) → CB f) (T0 T1 : BTree f L) : BTree f (L + 1)

/-- The stored values. -/
def BTree.centre {f : ℕ} : {L : ℕ} → BTree f L → CTree f L
  | _, .leaf s => .leaf s.c.re
  | _, .node ℓ T0 T1 => .node (fun o => (ℓ o).c) T0.centre T1.centre

variable (P : XChoices) (f : ℕ)

/-! ## Stored values -/

/-- The FFT: merge recursion with the table `ζ`. -/
def fftC : (L : ℕ) → (Fin (2 ^ L) → ℤ) → Out L → Cx f
  | 0, a => fun _ => Cx.ofInt (a ⟨0, by norm_num⟩)
  | L + 1, a =>
    let u := fftC L (evensZ a)
    let v := fftC L (oddsZ a)
    let t := twB P.rc f L
    memo (L + 1) fun x : Out L × Bool =>
      let p := (t x.1).c.mul P.rm (v x.1)
      if x.2 then (u x.1).sub p else (u x.1).add p

/-- `splitfft`: `(x + y)/2` and `ζ̄/2·(x - y)`. -/
def splitC (L : ℕ) (t : Out (L + 1) → Cx f) : (Out L → Cx f) × (Out L → Cx f) :=
  let s := twsB P.rc f L
  (memo L fun o => ((t (o, false)).add (t (o, true))).half P.rm,
    memo L fun o => (s o).c.mul P.rm ((t (o, false)).sub (t (o, true))))

/-- One ffLDL⋆ step from `g00, g10, D11`, children by `rec`. -/
def ldlStepC (L : ℕ) (g00 g10 d11 : Out (L + 1) → Cx f)
    (rec : (Out L → Cx f) → (Out L → Cx f) → (Out L → Cx f) → CTree f L) : CTree f (L + 1) :=
  let ℓ := memo (L + 1) fun o => (g10 o).divR P.rm P.dm (g00 o).re
  let s0 := splitC P f L g00
  let s1 := splitC P f L d11
  .node ℓ (rec s0.1 (fun o => (s0.2 o).conjg) s0.1) (rec s1.1 (fun o => (s1.2 o).conjg) s1.1)

/-- `D11 = g11 - |g10|²/g00`. -/
def d11C (L : ℕ) (g00 g10 g11 : Out L → Cx f) : Out L → Cx f :=
  memo L fun o => (g11 o).sub (((g10 o).normSqR P.rm).divR P.rm P.dm (g00 o).re)

/-- ffLDL⋆ with leaves `σ/√D`. -/
def ldlC : (L : ℕ) → (g00 g10 g11 : Out L → Cx f) → CTree f L
  | 0, g00, _, _ => .leaf (Cx.leafR P.rm P.rc σ512q (g00 ()).re).re
  | L + 1, g00, g10, g11 => ldlStepC P f L g00 g10 (d11C P f (L + 1) g00 g10 g11) (ldlC L)

/-- The Gram matrix `(g00, g10, g11)` of `B·B⋆` from the FFTs of `f, g, F, G`. -/
def gramC (k : RawKey) : (Out 9 → Cx f) × (Out 9 → Cx f) × (Out 9 → Cx f) :=
  let fb := fftC P f 9 k.f
  let gb := fftC P f 9 k.g
  let Fb := fftC P f 9 k.F
  let Gb := fftC P f 9 k.G
  (memo 9 fun o => ((gb o).normSqR P.rm).add ((fb o).normSqR P.rm),
    memo 9 fun o => ((Gb o).mul P.rm (gb o).conjg).add ((Fb o).mul P.rm (fb o).conjg),
    memo 9 fun o => ((Gb o).normSqR P.rm).add ((Fb o).normSqR P.rm))

/-- **Key expansion**: the stored tree of a raw key. -/
def expandC (k : RawKey) : CTree f 9 :=
  let gr := gramC P f k
  let d11 := match P.root with
    | .plain => d11C P f 9 gr.1 gr.2.1 gr.2.2
    | .ntru => memo 9 fun o => (Cx.ofInt (12289 ^ 2)).divR P.rm P.dm (gr.1 o).re
  ldlStepC P f 8 gr.1 gr.2.1 d11 (ldlC P f 8)

/-! ## The same in balls -/

/-- The FFT in balls. -/
def fftB : (L : ℕ) → (Fin (2 ^ L) → ℤ) → Out L → CB f
  | 0, a => fun _ => CB.ofInt (a ⟨0, by norm_num⟩)
  | L + 1, a =>
    let u := fftB L (evensZ a)
    let v := fftB L (oddsZ a)
    let t := twB P.rc f L
    memo (L + 1) fun x : Out L × Bool =>
      let p := CB.mul P.rm (t x.1) (v x.1)
      if x.2 then (u x.1).sub p else (u x.1).add p

/-- `splitfft` in balls. -/
def splitB (L : ℕ) (t : Out (L + 1) → CB f) : (Out L → CB f) × (Out L → CB f) :=
  let s := twsB P.rc f L
  (memo L fun o => ((t (o, false)).add (t (o, true))).half P.rm,
    memo L fun o => CB.mul P.rm (s o) ((t (o, false)).sub (t (o, true))))

/-- One ffLDL⋆ step in balls. -/
def ldlStepB (L : ℕ) (g00 g10 d11 : Out (L + 1) → CB f)
    (rec : (Out L → CB f) → (Out L → CB f) → (Out L → CB f) → BTree f L) : BTree f (L + 1) :=
  let ℓ := memo (L + 1) fun o => CB.divR P.rm P.dm (g10 o) (g00 o)
  let s0 := splitB P f L g00
  let s1 := splitB P f L d11
  .node ℓ (rec s0.1 (fun o => (s0.2 o).conjg) s0.1) (rec s1.1 (fun o => (s1.2 o).conjg) s1.1)

/-- `D11` in balls. -/
def d11B (L : ℕ) (g00 g10 g11 : Out L → CB f) : Out L → CB f :=
  memo L fun o => (g11 o).sub (CB.divR P.rm P.dm ((g10 o).normSq P.rm) (g00 o))

/-- ffLDL⋆ in balls. -/
def ldlB : (L : ℕ) → (g00 g10 g11 : Out L → CB f) → BTree f L
  | 0, g00, _, _ => .leaf (CB.leaf P.rm P.rc σ512q (g00 ()))
  | L + 1, g00, g10, g11 => ldlStepB P f L g00 g10 (d11B P f (L + 1) g00 g10 g11) (ldlB L)

/-- The Gram matrix in balls. -/
def gramB (k : RawKey) : (Out 9 → CB f) × (Out 9 → CB f) × (Out 9 → CB f) :=
  let fb := fftB P f 9 k.f
  let gb := fftB P f 9 k.g
  let Fb := fftB P f 9 k.F
  let Gb := fftB P f 9 k.G
  (memo 9 fun o => ((gb o).normSq P.rm).add ((fb o).normSq P.rm),
    memo 9 fun o => (CB.mul P.rm (Gb o) (gb o).conjg).add (CB.mul P.rm (Fb o) (fb o).conjg),
    memo 9 fun o => ((Gb o).normSq P.rm).add ((Fb o).normSq P.rm))

/-- `D11` at the root in balls. -/
def rootB (gr : (Out 9 → CB f) × (Out 9 → CB f) × (Out 9 → CB f)) : Out 9 → CB f :=
  match P.root with
  | .plain => d11B P f 9 gr.1 gr.2.1 gr.2.2
  | .ntru => memo 9 fun o => CB.divR P.rm P.dm (CB.ofInt (12289 ^ 2)) (gr.1 o)

/-- **Key expansion in balls.** -/
def expandB (k : RawKey) : BTree f 9 :=
  let gr := gramB P f k
  ldlStepB P f 8 gr.1 gr.2.1 (rootB P f gr) (ldlB P f 8)

theorem fftB_centre : ∀ (L : ℕ) (a : Fin (2 ^ L) → ℤ) (o : Out L),
    (fftB P f L a o).c = fftC P f L a o
  | 0, _, _ => rfl
  | L + 1, a, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    simp only [fftB, fftC]; erw [memo_eq, memo_eq]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, CB.add, CB.sub, CB.mul, fftB_centre L]

theorem ldlB_centre : ∀ (L : ℕ) (b00 b10 b11 : Out L → CB f),
    (ldlB P f L b00 b10 b11).centre =
      ldlC P f L (fun o => (b00 o).c) (fun o => (b10 o).c) (fun o => (b11 o).c)
  | 0, _, _, _ => rfl
  | L + 1, _, _, _ => by
    simp only [ldlB, ldlC, ldlStepB, ldlStepC, BTree.centre, ldlB_centre L, d11B, d11C, splitB,
      splitC, memo_eq, CB.divR, CB.half, CB.add, CB.sub, CB.mul, CB.conjg, CB.normSq]

/-- The centres of `expandB` are the stored tree `expandC`. -/
theorem expandB_centre (k : RawKey) : (expandB P f k).centre = expandC P f k := by
  obtain ⟨rm, rc, dm, root⟩ := P
  cases root <;>
  simp only [expandB, expandC, rootB, gramB, gramC, ldlStepB, ldlStepC, BTree.centre,
    ldlB_centre, d11B, d11C, splitB, splitC, memo_eq, CB.divR, CB.half, CB.add, CB.sub, CB.mul,
    CB.conjg, CB.normSq, CB.ofInt, CB.exact, fftB_centre]

/-! ## Storage at 64 fraction bits -/

/-- Every stored value rounded once from `f + n` to `f` fraction bits by `rm`. -/
def CTree.lower {f : ℕ} (rm : RMode) (n : ℕ) : {L : ℕ} → CTree (f + n) L → CTree f L
  | _, .leaf σ => .leaf (σ.lower rm n)
  | _, .node ℓ T0 T1 =>
    .node (fun o => ⟨(ℓ o).re.lower rm n, (ℓ o).im.lower rm n⟩) (T0.lower rm n) (T1.lower rm n)

/-- Every ball rounded once from `f + n` to `f` fraction bits by `rm` (`CB.lower`). -/
def BTree.lower {f : ℕ} (rm : RMode) (n : ℕ) : {L : ℕ} → BTree (f + n) L → BTree f L
  | _, .leaf s => .leaf (s.lower rm n)
  | _, .node ℓ T0 T1 => .node (fun o => (ℓ o).lower rm n) (T0.lower rm n) (T1.lower rm n)

theorem BTree.centre_lower {f : ℕ} (rm : RMode) (n : ℕ) : {L : ℕ} → (B : BTree (f + n) L) →
    (B.lower rm n).centre = B.centre.lower rm n
  | _, .leaf _ => rfl
  | _, .node ℓ T0 T1 => by
    simp only [BTree.lower, BTree.centre, CTree.lower, CB.lower, centre_lower rm n T0,
      centre_lower rm n T1]

theorem Fx.lower_zero {f : ℕ} (rm : RMode) (x : Fx f) : Fx.lower (f := f) rm 0 x = x := by
  obtain ⟨m⟩ := x
  simp [Fx.lower, RMode.rdiv, RMode.pick, compareOfLessAndEq]

/-- At `n = 0` the rounding is the identity. -/
theorem CTree.lower_zero {f : ℕ} (rm : RMode) : {L : ℕ} → (T : CTree f L) →
    CTree.lower (f := f) rm 0 T = T
  | _, .leaf σ => by rw [CTree.lower, Fx.lower_zero]
  | _, .node ℓ T0 T1 => by
    simp only [CTree.lower, Fx.lower_zero, lower_zero rm T0, lower_zero rm T1]

variable (n : ℕ)

/-- **The stored tree** (64 fraction bits): `expandC` at `64 + n` fraction bits, every value
rounded once to 64 fraction bits by `P.rm`. -/
def storeC (k : RawKey) : CTree 64 9 := (expandC P (64 + n) k).lower P.rm n

/-- `storeC` in balls. -/
def storeB (k : RawKey) : BTree 64 9 := (expandB P (64 + n) k).lower P.rm n

theorem storeB_centre (k : RawKey) : (storeB P n k).centre = storeC P n k := by
  rw [storeB, storeC, BTree.centre_lower, expandB_centre]

end FalconPrecision.Exec
