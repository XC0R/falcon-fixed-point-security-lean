/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Sign

/-! # Array versions of the tables, key expansion in balls and the per-key check

The compiled code of `memo L v` takes the position as an argument and builds its array on every
call, so every `memo` level of `twHi`, `fftB`, … recomputes the levels below it. The definitions
here store every vector as an `Array` value (`toArr`, read back by `ofArr`) and are proved equal
to the originals: `ofArr_twHiA`, `ofArr_twBA`, `ofArr_twsBA`, `ofArr_fftBA`, `expandBA_eq`,
`checkFast_eq` (`checkFast = check`) and `twOkFastN_eq` (`twOkFastN = twOkN`). -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec

/-! ## Arrays over `Out L` -/

/-- A vector stored as an array: entry `Out.idx L o` holds position `o`. -/
def toArr {X : Type} (L : ℕ) (v : Out L → X) : Array X :=
  Array.ofFn (n := 2 ^ L) fun i => v (Out.ofIdx L i)

/-- The vector of an array. -/
def ofArr {X : Type} [Inhabited X] (L : ℕ) (a : Array X) : Out L → X :=
  fun o => a.getD (Out.idx L o) default

theorem ofArr_toArr {X : Type} [Inhabited X] (L : ℕ) (v : Out L → X) :
    ofArr L (toArr L v) = v :=
  memo_eq L v

/-! ## Twiddle tables -/

/-- `twHi` as arrays, level by level. -/
def twHiA (rc : RMode) (h : ℕ) : ℕ → Array (CB h)
  | 0 => #[CB.exact ⟨⟨0⟩, Fx.ofInt 1⟩]
  | L + 1 =>
    let t := twHiA rc h L
    toArr (L + 1) fun x =>
      CB.sqrtU rc (if (x : Out L × Bool).2 then (ofArr L t (x : Out L × Bool).1).neg
        else ofArr L t (x : Out L × Bool).1)

theorem ofArr_twHiA (rc : RMode) (h : ℕ) : ∀ L, ofArr L (twHiA rc h L) = twHi rc h L
  | 0 => rfl
  | L + 1 => by simp only [twHiA, twHi, ofArr_toArr, ofArr_twHiA rc h L, memo_eq]

/-- `twB` as an array. -/
def twBA (rc : RMode) (f L : ℕ) : Array (CB f) :=
  let t := twHiA rc (f + 64) L
  toArr L fun o => (ofArr L t o).lower rc 64

/-- `twsB` as an array. -/
def twsBA (rc : RMode) (f L : ℕ) : Array (CB f) :=
  let t := twHiA rc (f + 64) L
  toArr L fun o => (ofArr L t o).lowerConjHalf rc 64

theorem ofArr_twBA (rc : RMode) (f L : ℕ) : ofArr L (twBA rc f L) = twB rc f L := by
  simp only [twBA, twB, ofArr_toArr, ofArr_twHiA]

theorem ofArr_twsBA (rc : RMode) (f L : ℕ) : ofArr L (twsBA rc f L) = twsB rc f L := by
  simp only [twsBA, twsB, ofArr_toArr, ofArr_twHiA]

/-- `twOkN` on the array tables. -/
def twOkFastN (rc : RMode) (N : ℕ) : Bool :=
  (List.range N).all fun L =>
    let t := twBA rc 64 L
    let s := twsBA rc 64 L
    allOut L fun o => (ofArr L t o).radLeB (7072 / 10000 / 2 ^ 64) &&
      (ofArr L s o).radLeB (7072 / 10000 / 2 ^ 64)

/-- `twOk` on the array tables. -/
def twOkFast (rc : RMode) : Bool := twOkFastN rc 9

theorem twOkFastN_eq (rc : RMode) (N : ℕ) : twOkFastN rc N = twOkN rc N := by
  simp only [twOkFastN, twOkN, ofArr_twBA, ofArr_twsBA]

theorem twOkFast_eq (rc : RMode) : twOkFast rc = twOk rc := twOkFastN_eq rc 9

/-! ## Key expansion in balls -/

variable (P : XChoices) (f : ℕ)

/-- `fftB` as an array. -/
def fftBA : (L : ℕ) → (Fin (2 ^ L) → ℤ) → Array (CB f)
  | 0, a => #[CB.ofInt (a ⟨0, by norm_num⟩)]
  | L + 1, a =>
    let u := fftBA L (evensZ a)
    let v := fftBA L (oddsZ a)
    let t := twBA P.rc f L
    toArr (L + 1) fun x : Out L × Bool =>
      let p := CB.mul P.rm (ofArr L t x.1) (ofArr L v x.1)
      if x.2 then (ofArr L u x.1).sub p else (ofArr L u x.1).add p

theorem ofArr_fftBA : ∀ (L : ℕ) (a : Fin (2 ^ L) → ℤ), ofArr L (fftBA P f L a) = fftB P f L a
  | 0, _ => rfl
  | L + 1, a => by
    simp only [fftBA, fftB, ofArr_fftBA L, ofArr_twBA]
    rfl

/-- `splitB` on arrays. -/
def splitBA (L : ℕ) (t : Array (CB f)) : Array (CB f) × Array (CB f) :=
  let s := twsBA P.rc f L
  (toArr L fun o => ((ofArr (L + 1) t (o, false)).add (ofArr (L + 1) t (o, true))).half P.rm,
    toArr L fun o =>
      CB.mul P.rm (ofArr L s o) ((ofArr (L + 1) t (o, false)).sub (ofArr (L + 1) t (o, true))))

/-- `ldlStepB` on arrays. -/
def ldlStepBA (L : ℕ) (g00 g10 d11 : Array (CB f))
    (rec : Array (CB f) → Array (CB f) → Array (CB f) → BTree f L) : BTree f (L + 1) :=
  let ℓ := toArr (L + 1) fun o => CB.divR P.rm P.dm (ofArr (L + 1) g10 o) (ofArr (L + 1) g00 o)
  let s0 := splitBA P f L g00
  let s1 := splitBA P f L d11
  .node (ofArr (L + 1) ℓ) (rec s0.1 (toArr L fun o => (ofArr L s0.2 o).conjg) s0.1)
    (rec s1.1 (toArr L fun o => (ofArr L s1.2 o).conjg) s1.1)

/-- `d11B` on arrays. -/
def d11BA (L : ℕ) (g00 g10 g11 : Array (CB f)) : Array (CB f) :=
  toArr L fun o =>
    (ofArr L g11 o).sub (CB.divR P.rm P.dm ((ofArr L g10 o).normSq P.rm) (ofArr L g00 o))

/-- `ldlB` on arrays. -/
def ldlBA : (L : ℕ) → (g00 g10 g11 : Array (CB f)) → BTree f L
  | 0, g00, _, _ => .leaf (CB.leaf P.rm P.rc σ512q (ofArr 0 g00 ()))
  | L + 1, g00, g10, g11 => ldlStepBA P f L g00 g10 (d11BA P f (L + 1) g00 g10 g11) (ldlBA L)

theorem ldlStepBA_eq (L : ℕ) (g00 g10 d11 : Array (CB f))
    (rec : Array (CB f) → Array (CB f) → Array (CB f) → BTree f L)
    (rec' : (Out L → CB f) → (Out L → CB f) → (Out L → CB f) → BTree f L)
    (h : ∀ x y z, rec x y z = rec' (ofArr L x) (ofArr L y) (ofArr L z)) :
    ldlStepBA P f L g00 g10 d11 rec =
      ldlStepB P f L (ofArr (L + 1) g00) (ofArr (L + 1) g10) (ofArr (L + 1) d11) rec' := by
  simp only [ldlStepBA, ldlStepB, splitBA, splitB, h, ofArr_toArr, ofArr_twsBA, memo_eq]

theorem ldlBA_eq : ∀ (L : ℕ) (g00 g10 g11 : Array (CB f)),
    ldlBA P f L g00 g10 g11 = ldlB P f L (ofArr L g00) (ofArr L g10) (ofArr L g11)
  | 0, _, _, _ => rfl
  | L + 1, g00, g10, g11 => by
    rw [ldlBA, ldlB, ldlStepBA_eq P f L _ _ _ _ _ (ldlBA_eq L)]
    simp only [d11BA, d11B, ofArr_toArr, memo_eq]

/-- `gramB` on arrays. -/
def gramBA (k : RawKey) : Array (CB f) × Array (CB f) × Array (CB f) :=
  let fb := fftBA P f 9 k.f
  let gb := fftBA P f 9 k.g
  let Fb := fftBA P f 9 k.F
  let Gb := fftBA P f 9 k.G
  (toArr 9 fun o => ((ofArr 9 gb o).normSq P.rm).add ((ofArr 9 fb o).normSq P.rm),
    toArr 9 fun o => (CB.mul P.rm (ofArr 9 Gb o) (ofArr 9 gb o).conjg).add
      (CB.mul P.rm (ofArr 9 Fb o) (ofArr 9 fb o).conjg),
    toArr 9 fun o => ((ofArr 9 Gb o).normSq P.rm).add ((ofArr 9 Fb o).normSq P.rm))

/-- `rootB` on arrays. -/
def rootBA (gr : Array (CB f) × Array (CB f) × Array (CB f)) : Array (CB f) :=
  match P.root with
  | .plain => d11BA P f 9 gr.1 gr.2.1 gr.2.2
  | .ntru => toArr 9 fun o => CB.divR P.rm P.dm (CB.ofInt (12289 ^ 2)) (ofArr 9 gr.1 o)

/-- `expandB` on arrays. -/
def expandBA (k : RawKey) : BTree f 9 :=
  let gr := gramBA P f k
  ldlStepBA P f 8 gr.1 gr.2.1 (rootBA P f gr) (ldlBA P f 8)

theorem expandBA_eq (k : RawKey) : expandBA P f k = expandB P f k := by
  rw [expandBA, expandB, ldlStepBA_eq P f 8 _ _ _ _ _ (ldlBA_eq P f 8)]
  obtain ⟨rm, rc, dm, root⟩ := P
  cases root <;>
  simp only [rootBA, rootB, gramBA, gramB, d11BA, d11B, ofArr_toArr, ofArr_fftBA, memo_eq]

/-! ## The per-key check -/

variable (n : ℕ)

/-- `check` on the array versions. -/
def checkFast (δq : ℕ → ℚ) (k : RawKey) : Bool :=
  let T := (expandBA P (64 + n) k).lower P.rm n
  let C := T.centre
  let fb := fftBA P (64 + n) 9 k.f
  let Fb := fftBA P (64 + n) 9 k.F
  allOut 9 (fun o => (ofArr 9 fb o).normLeB 255) &&
    allOut 9 (fun o => (ofArr 9 Fb o).normLeB 3500) && C.okB && C.realB &&
    T.radOkB δq && ntruB k

theorem checkFast_eq (δq : ℕ → ℚ) (k : RawKey) : checkFast P n δq k = check P n δq k := by
  simp only [checkFast, check, storeB, expandBA_eq, ofArr_fftBA]

end FalconPrecision.Exec
