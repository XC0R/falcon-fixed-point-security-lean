/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Sign
public import FalconPrecision.Exec.CheckFast

/-! # A signing attempt conditioned on its SamplerZ outputs, over any arithmetic

`VOps V` is the arithmetic of one signing attempt over values `V`: sum, difference, negation,
halving, product, division by `q`, the reduced FFT input `cst`, the leaf integer `ofInt`, and the
tables `ζ`, `ζ̄/2`. Over it, in the operation order of `ffsX` (`Exec.Sign`): the FFT `fft`, `split`,
`merge`, line 10 `upd`, the target `target` in either order, and `run`: ffSampling on a tree
`GTree V L` whose leaf answers are given integers `(z0, z1)` (the outputs of SamplerZ), recording
every intermediate in a `RunT V L`; `sign` adds the FFTs and the target (`SignT V`). `tapeOf` lists
the answers in call order.

`VSim O P R`: every operation of `O` and `P` preserves `R`. `signT_sim`: the traces of two runs on
`R`-related trees and inputs are `R`-related entry by entry (`SignT.Rel`).

`fftA`, `splitA`, `mergeA`, `updA`, `targetA`, `runA`: the same on arrays (`toArr`, `ofArr`;
`memo` is not shared by the compiler, `Exec.CheckFast`), proved equal (`ofArr_fftA`, …,
`runA_eq`). -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec

/-- The arithmetic of a signing attempt over values `V`. -/
structure VOps (V : Type) where
  add : V → V → V
  sub : V → V → V
  neg : V → V
  half : V → V
  mul : V → V → V
  divq : V → V
  /-- An FFT input coefficient. -/
  cst : ℤ → V
  /-- A leaf output `z`. -/
  ofInt : ℤ → V
  /-- `ζ` at level `L`. -/
  tw : (L : ℕ) → Out L → V
  /-- `ζ̄/2` at level `L`. -/
  tws : (L : ℕ) → Out L → V

/-- A Falcon tree over `V`: `ℓ̂` at the nodes, `σ̄` at the leaves. -/
inductive GTree (V : Type) : ℕ → Type
  | leaf (σ : V) : GTree V 0
  | node {L : ℕ} (ℓ : Out (L + 1) → V) (T0 T1 : GTree V L) : GTree V (L + 1)

/-- The intermediates of ffSampling: at a leaf `σ̄`, the centres `t0, t1`, the answers `z0, z1`; at
a node the inputs `t0, t1`, `ℓ̂`, the run on `T1`, its merge `zh1`, line 10 `t0u`, the run on `T0`,
its merge `zh0`. -/
inductive RunT (V : Type) : ℕ → Type
  | leaf (σ t0 t1 : V) (z0 z1 : ℤ) : RunT V 0
  | node {L : ℕ} (t0 t1 ℓ : Out (L + 1) → V) (r1 : RunT V L) (zh1 t0u : Out (L + 1) → V)
      (r0 : RunT V L) (zh0 : Out (L + 1) → V) : RunT V (L + 1)

/-- The intermediates of a signing attempt: FFTs of `c`, `f`, `F`, the target, ffSampling. -/
structure SignT (V : Type) where
  ch : Out 9 → V
  fh : Out 9 → V
  Fh : Out 9 → V
  t0 : Out 9 → V
  t1 : Out 9 → V
  run : RunT V 9

/-- The answers of a run in call order: `T1` before `T0`, `z0` before `z1`. -/
def tapeOf : (L : ℕ) → (Fin (2 ^ L) → ℤ) → (Fin (2 ^ L) → ℤ) → List ℤ
  | 0, z0, z1 => [z0 ⟨0, by norm_num⟩, z1 ⟨0, by norm_num⟩]
  | L + 1, z0, z1 => tapeOf L (evensZ z1) (oddsZ z1) ++ tapeOf L (evensZ z0) (oddsZ z0)

theorem tapeOf_length : ∀ (L : ℕ) (z0 z1 : Fin (2 ^ L) → ℤ),
    (tapeOf L z0 z1).length = 2 ^ (L + 1)
  | 0, _, _ => rfl
  | L + 1, z0, z1 => by
    rw [tapeOf, List.length_append, tapeOf_length L, tapeOf_length L, pow_succ 2 (L + 1)]
    ring

variable {V W X : Type}

namespace VOps

variable [Inhabited V] (O : VOps V)

/-- The FFT (merge recursion). -/
def fft : (L : ℕ) → (Fin (2 ^ L) → ℤ) → Out L → V
  | 0, a => fun _ => O.cst (a ⟨0, by norm_num⟩)
  | L + 1, a =>
    let u := fft L (evensZ a)
    let v := fft L (oddsZ a)
    let t := O.tw L
    memo (L + 1) fun x : Out L × Bool =>
      let p := O.mul (t x.1) (v x.1)
      if x.2 then O.sub (u x.1) p else O.add (u x.1) p

/-- `splitfft`: `(x + y)/2` and `ζ̄/2·(x - y)`. -/
def split (L : ℕ) (t : Out (L + 1) → V) : (Out L → V) × (Out L → V) :=
  let s := O.tws L
  (memo L fun o => O.half (O.add (t (o, false)) (t (o, true))),
    memo L fun o => O.mul (s o) (O.sub (t (o, false)) (t (o, true))))

/-- `mergefft`: `c0 ± ζ·c1`. -/
def merge (L : ℕ) (c0 c1 : Out L → V) : Out (L + 1) → V :=
  let t := O.tw L
  memo (L + 1) fun x : Out L × Bool =>
    let p := O.mul (t x.1) (c1 x.1)
    if x.2 then O.sub (c0 x.1) p else O.add (c0 x.1) p

/-- Line 10: `t0 + (t1 - z)·ℓ̂`. -/
def upd {L : ℕ} (t0 t1 z ℓ : Out L → V) : Out L → V :=
  memo L fun o => O.add (t0 o) (O.mul (O.sub (t1 o) (z o)) (ℓ o))

/-- The target from `ĉ, f̂, F̂` in the order `τ`. -/
def target (τ : Target) (ch fh Fh : Out 9 → V) : (Out 9 → V) × (Out 9 → V) :=
  match τ with
  | .scaleFirst =>
    let cq := memo 9 fun o => O.divq (ch o)
    (memo 9 fun o => O.mul (O.neg (cq o)) (Fh o), memo 9 fun o => O.mul (cq o) (fh o))
  | .multiplyFirst =>
    (memo 9 fun o => O.divq (O.neg (O.mul (ch o) (Fh o))),
      memo 9 fun o => O.divq (O.mul (ch o) (fh o)))

end VOps

/-- The outputs `(ẑ0, ẑ1)` of a run. -/
def RunT.outs (O : VOps V) : {L : ℕ} → RunT V L → (Out L → V) × (Out L → V)
  | _, .leaf _ _ _ z0 z1 => (fun _ => O.ofInt z0, fun _ => O.ofInt z1)
  | _, .node _ _ _ _ zh1 _ _ zh0 => (zh0, zh1)

namespace VOps

variable [Inhabited V] (O : VOps V)

/-- **ffSampling conditioned on its answers** `(z0, z1)`, in the order of `ffsX`; the checks of
`C.rchk` are not part of it. -/
def run : {L : ℕ} → GTree V L → (t0 t1 : Out L → V) → (z0 z1 : Fin (2 ^ L) → ℤ) → RunT V L
  | _, .leaf σ, t0, t1, z0, z1 =>
    .leaf σ (t0 ()) (t1 ()) (z0 ⟨0, by norm_num⟩) (z1 ⟨0, by norm_num⟩)
  | _, @GTree.node _ L ℓ T0 T1, t0, t1, z0, z1 =>
    let s1 := O.split L t1
    let r1 := run T1 s1.1 s1.2 (evensZ z1) (oddsZ z1)
    let zh1 := O.merge L (r1.outs O).1 (r1.outs O).2
    let t0u := O.upd t0 t1 zh1 ℓ
    let s0 := O.split L t0u
    let r0 := run T0 s0.1 s0.2 (evensZ z0) (oddsZ z0)
    .node t0 t1 ℓ r1 zh1 t0u r0 (O.merge L (r0.outs O).1 (r0.outs O).2)

/-- **The conditioned signing attempt**: FFTs of `c, f, F`, the target in the order `τ`, then
`run` on `T` with answers `(z0, z1)`. -/
def sign (τ : Target) (T : GTree V 9) (f F c z0 z1 : ZPoly) : SignT V :=
  let ch := O.fft 9 c
  let fh := O.fft 9 f
  let Fh := O.fft 9 F
  let t := O.target τ ch fh Fh
  ⟨ch, fh, Fh, t.1, t.2, O.run T t.1 t.2 z0 z1⟩

end VOps

/-! ## Array versions -/

namespace VOps

variable [Inhabited V] (O : VOps V)

/-- `fft` as an array. -/
def fftA : (L : ℕ) → (Fin (2 ^ L) → ℤ) → Array V
  | 0, a => #[O.cst (a ⟨0, by norm_num⟩)]
  | L + 1, a =>
    let u := fftA L (evensZ a)
    let v := fftA L (oddsZ a)
    let t := O.tw L
    toArr (L + 1) fun x : Out L × Bool =>
      let p := O.mul (t x.1) (ofArr L v x.1)
      if x.2 then O.sub (ofArr L u x.1) p else O.add (ofArr L u x.1) p

theorem ofArr_fftA : ∀ (L : ℕ) (a : Fin (2 ^ L) → ℤ), ofArr L (O.fftA L a) = O.fft L a
  | 0, _ => rfl
  | L + 1, a => by
    simp only [fftA, fft, ofArr_fftA L]
    rfl

/-- `split` as arrays. -/
def splitA (L : ℕ) (t : Out (L + 1) → V) : Array V × Array V :=
  let s := O.tws L
  (toArr L fun o => O.half (O.add (t (o, false)) (t (o, true))),
    toArr L fun o => O.mul (s o) (O.sub (t (o, false)) (t (o, true))))

theorem ofArr_splitA_fst (L : ℕ) (t : Out (L + 1) → V) :
    ofArr L (O.splitA L t).1 = (O.split L t).1 := by
  simp only [splitA, split, ofArr_toArr, memo_eq]

theorem ofArr_splitA_snd (L : ℕ) (t : Out (L + 1) → V) :
    ofArr L (O.splitA L t).2 = (O.split L t).2 := by
  simp only [splitA, split, ofArr_toArr, memo_eq]

/-- `merge` as an array. -/
def mergeA (L : ℕ) (c0 c1 : Out L → V) : Array V :=
  let t := O.tw L
  toArr (L + 1) fun x : Out L × Bool =>
    let p := O.mul (t x.1) (c1 x.1)
    if x.2 then O.sub (c0 x.1) p else O.add (c0 x.1) p

theorem ofArr_mergeA (L : ℕ) (c0 c1 : Out L → V) :
    ofArr (L + 1) (O.mergeA L c0 c1) = O.merge L c0 c1 := by
  simp only [mergeA, merge]
  rfl

/-- `upd` as an array. -/
def updA {L : ℕ} (t0 t1 z ℓ : Out L → V) : Array V :=
  toArr L fun o => O.add (t0 o) (O.mul (O.sub (t1 o) (z o)) (ℓ o))

theorem ofArr_updA {L : ℕ} (t0 t1 z ℓ : Out L → V) :
    ofArr L (O.updA t0 t1 z ℓ) = O.upd t0 t1 z ℓ := by
  simp only [updA, upd, ofArr_toArr, memo_eq]

/-- `target` as arrays. -/
def targetA (τ : Target) (ch fh Fh : Out 9 → V) : Array V × Array V :=
  match τ with
  | .scaleFirst =>
    let cq := ofArr 9 (toArr 9 fun o => O.divq (ch o))
    (toArr 9 fun o => O.mul (O.neg (cq o)) (Fh o), toArr 9 fun o => O.mul (cq o) (fh o))
  | .multiplyFirst =>
    (toArr 9 fun o => O.divq (O.neg (O.mul (ch o) (Fh o))),
      toArr 9 fun o => O.divq (O.mul (ch o) (fh o)))

theorem ofArr_targetA (τ : Target) (ch fh Fh : Out 9 → V) :
    ofArr 9 (O.targetA τ ch fh Fh).1 = (O.target τ ch fh Fh).1 ∧
      ofArr 9 (O.targetA τ ch fh Fh).2 = (O.target τ ch fh Fh).2 := by
  cases τ <;> simp only [targetA, target, ofArr_toArr, memo_eq, and_self]

/-- `run` on arrays: each split, merge and line-10 update computed once. -/
def runA : {L : ℕ} → GTree V L → (t0 t1 : Out L → V) → (z0 z1 : Fin (2 ^ L) → ℤ) → RunT V L
  | _, .leaf σ, t0, t1, z0, z1 =>
    .leaf σ (t0 ()) (t1 ()) (z0 ⟨0, by norm_num⟩) (z1 ⟨0, by norm_num⟩)
  | _, @GTree.node _ L ℓ T0 T1, t0, t1, z0, z1 =>
    let p1 := O.splitA L t1
    let r1 := runA T1 (ofArr L p1.1) (ofArr L p1.2) (evensZ z1) (oddsZ z1)
    let zh1 := ofArr (L + 1) (O.mergeA L (r1.outs O).1 (r1.outs O).2)
    let t0u := ofArr (L + 1) (O.updA t0 t1 zh1 ℓ)
    let p0 := O.splitA L t0u
    let r0 := runA T0 (ofArr L p0.1) (ofArr L p0.2) (evensZ z0) (oddsZ z0)
    .node t0 t1 ℓ r1 zh1 t0u r0 (ofArr (L + 1) (O.mergeA L (r0.outs O).1 (r0.outs O).2))

theorem runA_eq : ∀ {L : ℕ} (T : GTree V L) (t0 t1 : Out L → V) (z0 z1 : Fin (2 ^ L) → ℤ),
    O.runA T t0 t1 z0 z1 = O.run T t0 t1 z0 z1
  | _, .leaf _, _, _, _, _ => rfl
  | _, @GTree.node _ L ℓ T0 T1, t0, t1, z0, z1 => by
    simp only [runA, run, ofArr_splitA_fst, ofArr_splitA_snd, ofArr_mergeA, ofArr_updA,
      runA_eq T0, runA_eq T1]

end VOps

/-! ## Relations -/

/-- `R` at every node and leaf value. -/
def GTree.Rel (R : V → W → Prop) : {L : ℕ} → GTree V L → GTree W L → Prop
  | _, .leaf a, .leaf b => R a b
  | _, .node ℓ A0 A1, .node ℓ' B0 B1 => (∀ o, R (ℓ o) (ℓ' o)) ∧ Rel R A0 B0 ∧ Rel R A1 B1

/-- `R` at every entry, equal answers. -/
def RunT.Rel (R : V → W → Prop) : {L : ℕ} → RunT V L → RunT W L → Prop
  | _, .leaf σ t0 t1 z0 z1, .leaf σ' t0' t1' z0' z1' =>
    R σ σ' ∧ R t0 t0' ∧ R t1 t1' ∧ z0 = z0' ∧ z1 = z1'
  | _, .node t0 t1 ℓ r1 zh1 t0u r0 zh0, .node t0' t1' ℓ' r1' zh1' t0u' r0' zh0' =>
    (∀ o, R (t0 o) (t0' o) ∧ R (t1 o) (t1' o) ∧ R (ℓ o) (ℓ' o) ∧ R (zh1 o) (zh1' o) ∧
      R (t0u o) (t0u' o) ∧ R (zh0 o) (zh0' o)) ∧ Rel R r1 r1' ∧ Rel R r0 r0'

/-- `R` at every entry. -/
def SignT.Rel (R : V → W → Prop) (A : SignT V) (B : SignT W) : Prop :=
  (∀ o, R (A.ch o) (B.ch o) ∧ R (A.fh o) (B.fh o) ∧ R (A.Fh o) (B.Fh o) ∧ R (A.t0 o) (B.t0 o) ∧
    R (A.t1 o) (B.t1 o)) ∧ A.run.Rel R B.run

/-- `p` at every entry, decided. -/
def RunT.allB (p : V → Bool) : {L : ℕ} → RunT V L → Bool
  | _, .leaf σ t0 t1 _ _ => p σ && p t0 && p t1
  | _, @RunT.node _ L t0 t1 ℓ r1 zh1 t0u r0 zh0 =>
    allOut (L + 1) (fun o => p (t0 o) && p (t1 o) && p (ℓ o) && p (zh1 o) && p (t0u o) &&
      p (zh0 o)) && r1.allB p && r0.allB p

/-- `p` at every entry, decided. -/
def SignT.allB (p : V → Bool) (A : SignT V) : Bool :=
  allOut 9 (fun o => p (A.ch o) && p (A.fh o) && p (A.Fh o) && p (A.t0 o) && p (A.t1 o)) &&
    A.run.allB p

/-- Every entry mapped by `g`. -/
def RunT.map (g : V → W) : {L : ℕ} → RunT V L → RunT W L
  | _, .leaf σ t0 t1 z0 z1 => .leaf (g σ) (g t0) (g t1) z0 z1
  | _, .node t0 t1 ℓ r1 zh1 t0u r0 zh0 =>
    .node (fun o => g (t0 o)) (fun o => g (t1 o)) (fun o => g (ℓ o)) (r1.map g)
      (fun o => g (zh1 o)) (fun o => g (t0u o)) (r0.map g) (fun o => g (zh0 o))

/-- Every entry mapped by `g`. -/
def SignT.map (g : V → W) (A : SignT V) : SignT W :=
  ⟨fun o => g (A.ch o), fun o => g (A.fh o), fun o => g (A.Fh o), fun o => g (A.t0 o),
    fun o => g (A.t1 o), A.run.map g⟩

theorem RunT.Rel.imp {R R' : V → W → Prop} (P : V → Bool)
    (hP : ∀ a x, P a = true → R a x → R' a x) :
    ∀ {L : ℕ} (A : RunT V L) (B : RunT W L), A.allB P = true → A.Rel R B → A.Rel R' B
  | _, .leaf _ _ _ _ _, .leaf _ _ _ _ _, hA, h => by
    simp only [RunT.allB, Bool.and_eq_true] at hA
    exact ⟨hP _ _ hA.1.1 h.1, hP _ _ hA.1.2 h.2.1, hP _ _ hA.2 h.2.2.1, h.2.2.2⟩
  | _, @RunT.node _ L _ _ _ r1 _ _ r0 _, .node _ _ _ r1' _ _ r0' _, hA, h => by
    simp only [RunT.allB, Bool.and_eq_true] at hA
    refine ⟨fun o => ?_, imp P hP r1 r1' hA.1.2 h.2.1, imp P hP r0 r0' hA.2 h.2.2⟩
    have e := (allOut_iff _ _).1 hA.1.1 o
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩ := e
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h.1 o
    exact ⟨hP _ _ e1 g1, hP _ _ e2 g2, hP _ _ e3 g3, hP _ _ e4 g4, hP _ _ e5 g5, hP _ _ e6 g6⟩

theorem SignT.Rel.imp {R R' : V → W → Prop} (P : V → Bool)
    (hP : ∀ a x, P a = true → R a x → R' a x) (A : SignT V) (B : SignT W) (hA : A.allB P = true)
    (h : A.Rel R B) : A.Rel R' B := by
  simp only [SignT.allB, Bool.and_eq_true] at hA
  refine ⟨fun o => ?_, RunT.Rel.imp P hP _ _ hA.2 h.2⟩
  have e := (allOut_iff _ _).1 hA.1 o
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ := e
  obtain ⟨g1, g2, g3, g4, g5⟩ := h.1 o
  exact ⟨hP _ _ e1 g1, hP _ _ e2 g2, hP _ _ e3 g3, hP _ _ e4 g4, hP _ _ e5 g5⟩

theorem RunT.Rel.mono {R R' : V → W → Prop} (hR : ∀ a x, R a x → R' a x) :
    ∀ {L : ℕ} (A : RunT V L) (B : RunT W L), A.Rel R B → A.Rel R' B
  | _, .leaf _ _ _ _ _, .leaf _ _ _ _ _, h => ⟨hR _ _ h.1, hR _ _ h.2.1, hR _ _ h.2.2.1, h.2.2.2⟩
  | _, .node _ _ _ r1 _ _ r0 _, .node _ _ _ r1' _ _ r0' _, h => by
    refine ⟨fun o => ?_, mono hR r1 r1' h.2.1, mono hR r0 r0' h.2.2⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.1 o
    exact ⟨hR _ _ a1, hR _ _ a2, hR _ _ a3, hR _ _ a4, hR _ _ a5, hR _ _ a6⟩

theorem SignT.Rel.mono {R R' : V → W → Prop} (hR : ∀ a x, R a x → R' a x) (A : SignT V)
    (B : SignT W) (h : A.Rel R B) : A.Rel R' B := by
  refine ⟨fun o => ?_, RunT.Rel.mono hR _ _ h.2⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.1 o
  exact ⟨hR _ _ a1, hR _ _ a2, hR _ _ a3, hR _ _ a4, hR _ _ a5⟩

theorem RunT.Rel.comp {R1 : V → W → Prop} {R2 : W → X → Prop} :
    ∀ {L : ℕ} (A : RunT V L) (B : RunT W L) (D : RunT X L), A.Rel R1 B → B.Rel R2 D →
      A.Rel (fun a d => ∃ b, R1 a b ∧ R2 b d) D
  | _, .leaf _ _ _ _ _, .leaf _ _ _ _ _, .leaf _ _ _ _ _, h1, h2 =>
    ⟨⟨_, h1.1, h2.1⟩, ⟨_, h1.2.1, h2.2.1⟩, ⟨_, h1.2.2.1, h2.2.2.1⟩, h1.2.2.2.1.trans h2.2.2.2.1,
      h1.2.2.2.2.trans h2.2.2.2.2⟩
  | _, .node _ _ _ r1 _ _ r0 _, .node _ _ _ s1 _ _ s0 _, .node _ _ _ u1 _ _ u0 _, h1, h2 => by
    refine ⟨fun o => ?_, comp r1 s1 u1 h1.2.1 h2.2.1, comp r0 s0 u0 h1.2.2 h2.2.2⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1.1 o
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2.1 o
    exact ⟨⟨_, a1, b1⟩, ⟨_, a2, b2⟩, ⟨_, a3, b3⟩, ⟨_, a4, b4⟩, ⟨_, a5, b5⟩, ⟨_, a6, b6⟩⟩

theorem SignT.Rel.comp {R1 : V → W → Prop} {R2 : W → X → Prop} (A : SignT V) (B : SignT W)
    (D : SignT X) (h1 : A.Rel R1 B) (h2 : B.Rel R2 D) :
    A.Rel (fun a d => ∃ b, R1 a b ∧ R2 b d) D := by
  refine ⟨fun o => ?_, RunT.Rel.comp _ _ _ h1.2 h2.2⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1.1 o
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2.1 o
  exact ⟨⟨_, a1, b1⟩, ⟨_, a2, b2⟩, ⟨_, a3, b3⟩, ⟨_, a4, b4⟩, ⟨_, a5, b5⟩⟩

theorem RunT.Rel.map_left {R : W → X → Prop} {R' : V → X → Prop} (g : V → W)
    (hg : ∀ a x, R' a x → R (g a) x) :
    ∀ {L : ℕ} (A : RunT V L) (B : RunT X L), A.Rel R' B → (A.map g).Rel R B
  | _, .leaf _ _ _ _ _, .leaf _ _ _ _ _, h =>
    ⟨hg _ _ h.1, hg _ _ h.2.1, hg _ _ h.2.2.1, h.2.2.2⟩
  | _, .node _ _ _ r1 _ _ r0 _, .node _ _ _ r1' _ _ r0' _, h => by
    refine ⟨fun o => ?_, map_left g hg r1 r1' h.2.1, map_left g hg r0 r0' h.2.2⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.1 o
    exact ⟨hg _ _ a1, hg _ _ a2, hg _ _ a3, hg _ _ a4, hg _ _ a5, hg _ _ a6⟩

theorem SignT.Rel.map_left {R : W → X → Prop} {R' : V → X → Prop} (g : V → W)
    (hg : ∀ a x, R' a x → R (g a) x) (A : SignT V) (B : SignT X) (h : A.Rel R' B) :
    (A.map g).Rel R B := by
  refine ⟨fun o => ?_, RunT.Rel.map_left g hg _ _ h.2⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.1 o
  exact ⟨hg _ _ a1, hg _ _ a2, hg _ _ a3, hg _ _ a4, hg _ _ a5⟩

/-! ## Simulation -/

/-- Every operation of `O` and `P` preserves `R` (tables at levels `< 9`). -/
structure VSim (O : VOps V) (P : VOps W) (R : V → W → Prop) : Prop where
  add : ∀ {a b x y}, R a x → R b y → R (O.add a b) (P.add x y)
  sub : ∀ {a b x y}, R a x → R b y → R (O.sub a b) (P.sub x y)
  neg : ∀ {a x}, R a x → R (O.neg a) (P.neg x)
  half : ∀ {a x}, R a x → R (O.half a) (P.half x)
  mul : ∀ {a b x y}, R a x → R b y → R (O.mul a b) (P.mul x y)
  divq : ∀ {a x}, R a x → R (O.divq a) (P.divq x)
  cst : ∀ n, R (O.cst n) (P.cst n)
  ofInt : ∀ n, R (O.ofInt n) (P.ofInt n)
  tw : ∀ L o, L < 9 → R (O.tw L o) (P.tw L o)
  tws : ∀ L o, L < 9 → R (O.tws L o) (P.tws L o)

section Sim

variable [Inhabited V] [Inhabited W] {O : VOps V} {P : VOps W} {R : V → W → Prop}

theorem fft_sim (h : VSim O P R) :
    ∀ (L : ℕ), L ≤ 9 → ∀ (a : Fin (2 ^ L) → ℤ) (o : Out L), R (O.fft L a o) (P.fft L a o)
  | 0, _, a, _ => h.cst _
  | L + 1, hL, a, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    have hu := fft_sim h L (by omega) (evensZ a) o
    have hp := h.mul (h.tw L o (by omega)) (fft_sim h L (by omega) (oddsZ a) o)
    simp only [VOps.fft]
    erw [memo_eq, memo_eq]
    cases b
    · exact h.add hu hp
    · exact h.sub hu hp

theorem split_sim (h : VSim O P R) {L : ℕ} (hL : L < 9) (t : Out (L + 1) → V)
    (t' : Out (L + 1) → W) (ht : ∀ x, R (t x) (t' x)) (o : Out L) :
    R ((O.split L t).1 o) ((P.split L t').1 o) ∧ R ((O.split L t).2 o) ((P.split L t').2 o) := by
  simp only [VOps.split, memo_eq]
  exact ⟨h.half (h.add (ht _) (ht _)), h.mul (h.tws L o hL) (h.sub (ht _) (ht _))⟩

theorem merge_sim (h : VSim O P R) {L : ℕ} (hL : L < 9) (c0 c1 : Out L → V) (c0' c1' : Out L → W)
    (hc : ∀ o, R (c0 o) (c0' o) ∧ R (c1 o) (c1' o)) (x : Out (L + 1)) :
    R (O.merge L c0 c1 x) (P.merge L c0' c1' x) := by
  obtain ⟨o, b⟩ := (x : Out L × Bool)
  have hp := h.mul (h.tw L o hL) (hc o).2
  simp only [VOps.merge]
  erw [memo_eq, memo_eq]
  cases b
  · exact h.add (hc o).1 hp
  · exact h.sub (hc o).1 hp

theorem upd_sim (h : VSim O P R) {L : ℕ} (t0 t1 z ℓ : Out L → V) (t0' t1' z' ℓ' : Out L → W)
    (h0 : ∀ o, R (t0 o) (t0' o)) (h1 : ∀ o, R (t1 o) (t1' o)) (hz : ∀ o, R (z o) (z' o))
    (hl : ∀ o, R (ℓ o) (ℓ' o)) (o : Out L) : R (O.upd t0 t1 z ℓ o) (P.upd t0' t1' z' ℓ' o) := by
  simp only [VOps.upd, memo_eq]
  exact h.add (h0 o) (h.mul (h.sub (h1 o) (hz o)) (hl o))

theorem target_sim (h : VSim O P R) (τ : Target) (ch fh Fh : Out 9 → V) (ch' fh' Fh' : Out 9 → W)
    (hc : ∀ o, R (ch o) (ch' o)) (hf : ∀ o, R (fh o) (fh' o)) (hF : ∀ o, R (Fh o) (Fh' o))
    (o : Out 9) : R ((O.target τ ch fh Fh).1 o) ((P.target τ ch' fh' Fh').1 o) ∧
      R ((O.target τ ch fh Fh).2 o) ((P.target τ ch' fh' Fh').2 o) := by
  cases τ <;> simp only [VOps.target, memo_eq]
  · exact ⟨h.mul (h.neg (h.divq (hc o))) (hF o), h.mul (h.divq (hc o)) (hf o)⟩
  · exact ⟨h.divq (h.neg (h.mul (hc o) (hF o))), h.divq (h.mul (hc o) (hf o))⟩

omit [Inhabited V] [Inhabited W] in
theorem outs_sim (h : VSim O P R) : ∀ {L : ℕ} (r : RunT V L) (r' : RunT W L), r.Rel R r' →
    ∀ o, R ((r.outs O).1 o) ((r'.outs P).1 o) ∧ R ((r.outs O).2 o) ((r'.outs P).2 o)
  | _, .leaf _ _ _ _ _, .leaf _ _ _ _ _, hr, _ => by
    obtain ⟨-, -, -, rfl, rfl⟩ := hr
    exact ⟨h.ofInt _, h.ofInt _⟩
  | _, .node _ _ _ _ _ _ _ _, .node _ _ _ _ _ _ _ _, hr, o =>
    ⟨(hr.1 o).2.2.2.2.2, (hr.1 o).2.2.2.1⟩

/-- **Simulation of the conditioned run.** -/
theorem run_sim (h : VSim O P R) : ∀ {L : ℕ} (T : GTree V L) (T' : GTree W L), L ≤ 9 →
    T.Rel R T' → ∀ (t0 t1 : Out L → V) (t0' t1' : Out L → W),
      (∀ o, R (t0 o) (t0' o) ∧ R (t1 o) (t1' o)) → ∀ z0 z1,
        (O.run T t0 t1 z0 z1).Rel R (P.run T' t0' t1' z0 z1)
  | _, .leaf _, .leaf _, _, hT, _, _, _, _, ht, _, _ => ⟨hT, (ht ()).1, (ht ()).2, rfl, rfl⟩
  | _, @GTree.node _ L ℓ A0 A1, .node ℓ' B0 B1, hL, hT, t0, t1, t0', t1', ht, z0, z1 => by
    have hs1 := split_sim h (by omega) t1 t1' fun o => (ht o).2
    have r1 := run_sim h A1 B1 (by omega) hT.2.2 _ _ _ _ hs1 (evensZ z1) (oddsZ z1)
    have hz1 := merge_sim h (by omega) _ _ _ _ (outs_sim h _ _ r1)
    have hu := upd_sim h t0 t1 _ ℓ t0' t1' _ ℓ' (fun o => (ht o).1) (fun o => (ht o).2) hz1 hT.1
    have hs0 := split_sim h (by omega) _ _ hu
    have r0 := run_sim h A0 B0 (by omega) hT.2.1 _ _ _ _ hs0 (evensZ z0) (oddsZ z0)
    have hz0 := merge_sim h (by omega) _ _ _ _ (outs_sim h _ _ r0)
    exact ⟨fun o => ⟨(ht o).1, (ht o).2, hT.1 o, hz1 o, hu o, hz0 o⟩, r1, r0⟩

/-- **Simulation of the conditioned attempt.** -/
theorem signT_sim (h : VSim O P R) (τ : Target) (T : GTree V 9) (T' : GTree W 9) (hT : T.Rel R T')
    (f F c z0 z1 : ZPoly) : (O.sign τ T f F c z0 z1).Rel R (P.sign τ T' f F c z0 z1) := by
  have hc := fft_sim h 9 le_rfl c
  have hf := fft_sim h 9 le_rfl f
  have hF := fft_sim h 9 le_rfl F
  have ht := target_sim h τ _ _ _ _ _ _ hc hf hF
  unfold SignT.Rel VOps.sign
  dsimp only
  exact ⟨fun o => ⟨hc o, hf o, hF o, (ht o).1, (ht o).2⟩,
    run_sim h T T' le_rfl hT _ _ _ _ ht z0 z1⟩

end Sim

end FalconPrecision.Exec
