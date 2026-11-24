/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.KeyCheck

/-! # An executable Falcon-512 signer parametric in the FN-DSA design space

`Choices` collects the unpinned points that affect signing: key expansion (`XChoices`,
`Exec.KeyExpand`), the target order (ePrint 2026/2431 §3.1: scale-first `((-ĉ/q)⊙F̂, (ĉ/q)⊙f̂)` or
the multiply-first order of the reference code), the stored `1/q` (§3.4), the integer budget
(`word`: unbounded, or every operation result reduced to an `(i + 64)`-bit two's-complement word,
`InRange i`; 32.64 and 64.64 at `i = 32, 64`), S8's model range checks, salt per attempt or reused,
the restart cap, the norm bounds, and the SamplerZ choices (centre, shift rejection, base table),
which are only handed to the sampler.

`ffsX` is ffSampling in the operation order of S8's `ffsG`, on computed values only; a leaf asks
the sampler `samp σ̄ t̄`. `signX` is one signing attempt on a stored tree (`⊥` unless `|c i| < q`),
`signLoopX` the restart loop, `signMsgX` the whole signer. `checkRange` is an executable bound on
every operation result of `signX` for a key, from `‖f‖₁`, `‖F‖₁`, the computed `f̂`, `F̂`, the
stored `ℓ̂`, a window `W` of sampler answers around `⌊t̄⌋` (`clampS`) and the bound `imE i`
on `|Im t̄|` at the leaves (and the tables `twOk`). Statements: `Exec.SignRefine`,
`Exec.SignRange`. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFSamp

/-- An integer polynomial of degree `< 512`. -/
abbrev ZPoly : Type := Fin (2 ^ 9) → ℤ

/-- The target order (ePrint 2026/2431 §3.1). -/
inductive Target where
  /-- `(-ĉ/q)⊙F̂`, `(ĉ/q)⊙f̂`. -/
  | scaleFirst
  /-- `-(ĉ⊙F̂)/q`, `(ĉ⊙f̂)/q` (reference code, c-fn-dsa, fixed-point-c). -/
  | multiplyFirst
  deriving DecidableEq, Repr

/-- The stored `1/q` (ePrint 2026/2431 §3.4). -/
inductive QInv where
  /-- `⌊2⁷⁷/q⌉·2⁻⁷⁷`. -/
  | w77
  /-- `⌊2⁶⁴/q⌉·2⁻⁶⁴`. -/
  | w64
  deriving DecidableEq, Repr

/-- A fresh salt per attempt, or one salt for all attempts (spec Alg. 10 l. 1). -/
inductive SaltMode where
  | perAttempt
  | reused
  deriving DecidableEq, Repr

/-- SamplerZ centre handling (ePrint 2026/2902: plain or fractional centre). -/
inductive Centre where
  | plain
  | fractional
  deriving DecidableEq, Repr

/-- BaseSampler table width (spec Alg. 12: 72 bits; NIST Sep 2025 slides: 79). -/
inductive BaseBits where
  | b72
  | b79
  deriving DecidableEq, Repr

/-- SamplerZ choices, handed to the sampler. -/
structure SampChoices where
  centre : Centre
  /-- Reject a shift `≥ 64` instead of saturating it (ePrint 2026/2902 (i)). -/
  shiftRej : Bool
  base : BaseBits
  deriving DecidableEq, Repr

/-- The design-space point of a signer. -/
structure Choices where
  /-- Key expansion and the rounding of every operation and table. -/
  x : XChoices
  /-- Extra key-expansion fraction bits. -/
  xn : ℕ
  target : Target
  qinv : QInv
  /-- `none`: unbounded `Int`; `some i`: `(i + 64)`-bit words. -/
  word : Option ℕ
  /-- `some R`: S8's range checks `‖·‖ ≤ R - 1`. -/
  rchk : Option ℚ
  salt : SaltMode
  /-- Attempts before failure. -/
  cap : ℕ
  /-- `⌊β²⌋`. -/
  beta2 : ℕ
  /-- Optional bound on every `|sᵢ|`. -/
  infB : Option ℕ
  samp : SampChoices
  deriving DecidableEq, Repr

/-- The reduction of an operation result. -/
def wordFn : Option ℕ → ℤ → ℤ
  | none => id
  | some i => Fx.wrap (i - 1 + 64)

/-- `x` reduced by `w`. -/
def Fx.wr {f : ℕ} (w : ℤ → ℤ) (x : Fx f) : Fx f := ⟨w x.m⟩

namespace Cx

variable {f : ℕ}

/-- Both parts reduced by `w`. -/
def wr (w : ℤ → ℤ) (z : Cx f) : Cx f := ⟨z.re.wr w, z.im.wr w⟩

/-- `Cx.mul` with each of the four products and the two sums reduced by `w`. -/
def mulW (w : ℤ → ℤ) (r : RMode) (z u : Cx f) : Cx f :=
  ⟨(((z.re.mul r u.re).wr w).sub ((z.im.mul r u.im).wr w)).wr w,
    (((z.re.mul r u.im).wr w).add ((z.im.mul r u.re).wr w)).wr w⟩

end Cx

/-- `1/q` rounded to 64 fraction bits. -/
def qinv64 (r : RMode) : Fx 64 := ⟨r.rdiv (2 ^ 64) 12289⟩

/-- The product by the stored `1/q`, each part rounded once. -/
def divqX (r : RMode) : QInv → Cx 64 → Cx 64
  | .w77, z => z.divq r
  | .w64, z => ⟨z.re.mul r (qinv64 r), z.im.mul r (qinv64 r)⟩

/-- The tables at levels `< N` within `0.7072·2⁻⁶⁴` of `ζ`, `ζ̄/2` (decided on the balls). -/
def twOkN (rc : RMode) (N : ℕ) : Bool :=
  (List.range N).all fun L =>
    let t := twB rc 64 L
    let s := twsB rc 64 L
    allOut L fun o => (t o).radLeB (7072 / 10000 / 2 ^ 64) && (s o).radLeB (7072 / 10000 / 2 ^ 64)

/-- The tables of Falcon-512 (levels `< 9`). -/
def twOk (rc : RMode) : Bool := twOkN rc 9

variable (C : Choices)

/-- The FFT (merge recursion, table `ζ` by `C.x.rc`), every result reduced. -/
def fftW : (L : ℕ) → (Fin (2 ^ L) → ℤ) → Out L → Cx 64
  | 0, a => fun _ => (Cx.ofInt (a ⟨0, by norm_num⟩) : Cx 64).wr (wordFn C.word)
  | L + 1, a =>
    let u := fftW L (evensZ a)
    let v := fftW L (oddsZ a)
    let t := twB C.x.rc 64 L
    memo (L + 1) fun x : Out L × Bool =>
      let p := (t x.1).c.mulW (wordFn C.word) C.x.rm (v x.1)
      if x.2 then ((u x.1).sub p).wr (wordFn C.word) else ((u x.1).add p).wr (wordFn C.word)

/-- `splitfft`: `(x + y)/2` and `ζ̄/2·(x - y)`. -/
def splitW (L : ℕ) (t : Out (L + 1) → Cx 64) : (Out L → Cx 64) × (Out L → Cx 64) :=
  let w := wordFn C.word
  let s := twsB C.x.rc 64 L
  (memo L fun o => ((((t (o, false)).add (t (o, true))).wr w).half C.x.rm).wr w,
    memo L fun o => (s o).c.mulW w C.x.rm (((t (o, false)).sub (t (o, true))).wr w))

/-- `mergefft` of `(c0, c1)`: `c0 ± ζ·c1`. -/
def mergeW (L : ℕ) (c0 c1 : Out L → Cx 64) : Out (L + 1) → Cx 64 :=
  let w := wordFn C.word
  let t := twB C.x.rc 64 L
  memo (L + 1) fun x : Out L × Bool =>
    let p := (t x.1).c.mulW w C.x.rm (c1 x.1)
    if x.2 then ((c0 x.1).sub p).wr w else ((c0 x.1).add p).wr w

/-- Line 10: `t0 + (t1 - z)·ℓ̂`. -/
def updW {L : ℕ} (t0 t1 z ℓ : Out L → Cx 64) : Out L → Cx 64 :=
  let w := wordFn C.word
  memo L fun o => ((t0 o).add ((((t1 o).sub (z o)).wr w).mulW w C.x.rm (ℓ o))).wr w

/-- S8's range check `‖·‖ ≤ R - 1` on every slot, or none. -/
def chkX : Option ℚ → (L : ℕ) → (Out L → Cx 64) → Bool
  | none, _, _ => true
  | some R, L, v => allOut L fun o => decide ((v o).nsq ≤ (R - 1) ^ 2)

/-- An ffSampling output: the integers `z0, z1` and the computed FFTs `c0, c1`. -/
structure SampX (L : ℕ) where
  z0 : Fin (2 ^ L) → ℤ
  z1 : Fin (2 ^ L) → ℤ
  c0 : Out L → Cx 64
  c1 : Out L → Cx 64

/-- **ffSampling** on computed values, in the order of `ffsG`; `none` when a check fails. -/
def ffsX {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) :
    {L : ℕ} → CTree 64 L → (t0 t1 : Out L → Cx 64) → m (Option (SampX L))
  | _, .leaf σ, t0, t1 =>
    samp σ (t0 ()).re >>= fun z0 => samp σ (t1 ()).re >>= fun z1 =>
      pure (some ⟨fun _ => z0, fun _ => z1, fun _ => Cx.ofInt z0, fun _ => Cx.ofInt z1⟩)
  | _, @CTree.node _ L ℓ T0 T1, t0, t1 =>
    if chkX C.rchk (L + 1) t1 then
      ffsX samp T1 (splitW C L t1).1 (splitW C L t1).2 >>= fun r1 =>
        match r1 with
        | none => pure none
        | some s1 =>
          let t0' := updW C t0 t1 (mergeW C L s1.c0 s1.c1) ℓ
          if chkX C.rchk L s1.c1 && chkX C.rchk (L + 1) t0' then
            ffsX samp T0 (splitW C L t0').1 (splitW C L t0').2 >>= fun r0 =>
              match r0 with
              | none => pure none
              | some s0 =>
                if chkX C.rchk L s0.c1 then
                  pure (some ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1, mergeW C L s0.c0 s0.c1,
                    mergeW C L s1.c0 s1.c1⟩)
                else pure none
          else pure none
    else pure none

/-- The target `(t̂0, t̂1)` from `f`, `F` and the hash `c`, in the order `C.target`. -/
def targetX (f F c : ZPoly) : (Out 9 → Cx 64) × (Out 9 → Cx 64) :=
  let w := wordFn C.word
  let rm := C.x.rm
  let ch := fftW C 9 c
  let fh := fftW C 9 f
  let Fh := fftW C 9 F
  match C.target with
  | .scaleFirst =>
    let cq := memo 9 fun o => (divqX rm C.qinv (ch o)).wr w
    (memo 9 fun o => ((cq o).neg.wr w).mulW w rm (Fh o), memo 9 fun o => (cq o).mulW w rm (fh o))
  | .multiplyFirst =>
    (memo 9 fun o => (divqX rm C.qinv (((ch o).mulW w rm (Fh o)).neg.wr w)).wr w,
      memo 9 fun o => (divqX rm C.qinv ((ch o).mulW w rm (fh o))).wr w)

/-- **One signing attempt** on the stored tree `T` of `k`: `⊥` unless `|c i| < q`, else the
integers `z = (z0, z1)` of `ffsX` on `targetX`, or `⊥` when a check fails. -/
def signX {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9)
    (k : RawKey) (c : ZPoly) : m (Option (ZPoly × ZPoly)) :=
  if ∀ i, |c i| < 12289 then
    (fun r => r.map fun s => (s.z0, s.z1)) <$>
      ffsX C samp T (targetX C k.f k.F c).1 (targetX C k.f k.F c).2
  else pure none

/-- `s = (c, 0) - zB` for `B = [[g, -f], [G, -F]]`, exactly. -/
def sOf (k : RawKey) (c z0 z1 : ZPoly) : ZPoly × ZPoly :=
  (fun i => c i - ncoef z0 k.g i - ncoef z1 k.G i, fun i => ncoef z0 k.f i + ncoef z1 k.F i)

/-- `‖s‖² ≤ ⌊β²⌋` and, if set, `|sᵢ| ≤ B`. -/
def normOk (s : ZPoly × ZPoly) : Bool :=
  decide (((List.finRange (2 ^ 9)).map fun i => s.1 i ^ 2 + s.2 i ^ 2).sum ≤ (C.beta2 : ℤ)) &&
    (match C.infB with
      | none => true
      | some B => (List.finRange (2 ^ 9)).all fun i =>
        decide (|s.1 i| ≤ (B : ℤ) ∧ |s.2 i| ≤ (B : ℤ)))

/-- The signature of an attempt, if its norm passes. -/
def accX (k : RawKey) (c : ZPoly) (y : Option (ZPoly × ZPoly)) : Option (ZPoly × ZPoly) :=
  y.bind fun z => if normOk C (sOf k c z.1 z.2) then some (sOf k c z.1 z.2) else none

/-- At most `N` attempts `att`, until `acc` accepts. -/
def loopR {m : Type → Type*} [Monad m] {γ β : Type} (att : m γ) (acc : γ → Option β) :
    ℕ → m (Option β)
  | 0 => pure none
  | n + 1 => att >>= fun y =>
    match acc y with
    | some b => pure (some b)
    | none => loopR att acc n

/-- **The restart loop** (spec Alg. 10 l. 4-11) with at most `N` attempts: salt and hash once
(`reused`) or per attempt (`perAttempt`). -/
def signLoopX {m : Type → Type*} [Monad m] {S M β : Type} (mode : SaltMode) (salt : m S)
    (hash : S → M → m ZPoly) (att : ZPoly → m (Option (ZPoly × ZPoly)))
    (acc : ZPoly → Option (ZPoly × ZPoly) → Option β) (msg : M) (N : ℕ) : m (Option (S × β)) :=
  match mode with
  | .reused => salt >>= fun s => hash s msg >>= fun c =>
    (Option.map fun b => (s, b)) <$> loopR (att c) (acc c) N
  | .perAttempt =>
    loopR (salt >>= fun s => hash s msg >>= fun c => (fun y => (s, c, y)) <$> att c)
      (fun x => (acc x.2.1 x.2.2).map fun b => (x.1, b)) N

/-- **The signer**: stored tree `storeC`, attempts `signX`, loop `signLoopX`, the sampler given
the SamplerZ choices. -/
def signMsgX {m : Type → Type*} [Monad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (k : RawKey) (msg : M) : m (Option (S × (ZPoly × ZPoly))) :=
  let T := storeC C.x C.xn k
  signLoopX C.salt salt hash (signX C (sampF C.samp) T k) (accX C k) msg C.cap

/-! ## Integer ranges -/

/-- `z` clamped into `[b - W, b + W]`. -/
def clampZ (b : ℤ) (W : ℕ) (z : ℤ) : ℤ := max (b - W) (min (b + W) z)

/-- Sampler answers clamped into `⌊t̄⌋ ± W`. -/
def clampS {m : Type → Type*} [Monad m] (W : ℕ) (samp : Fx 64 → Fx 64 → m ℤ) :
    Fx 64 → Fx 64 → m ℤ :=
  fun σ t => clampZ (t.toInt .floor) W <$> samp σ t

/-- `b < 2^(i-1)`: a value bounded by `b` is in `InRange i`. -/
def fitsQ (i : ℕ) (b : ℚ) : Bool := decide (b < 2 ^ (i - 1))

/-- `‖a‖₁`. -/
def l1Q (a : ZPoly) : ℚ := (((List.finRange (2 ^ 9)).map fun j => |a j|).sum : ℤ)

/-- An upper bound of `max ‖v o‖`. -/
def nmax (L : ℕ) (v : Out L → Cx 64) : ℚ :=
  (List.range (2 ^ L)).foldl (fun b j => max b (v (Out.ofIdx L j)).nUB) 0

/-- The bound on `|Im t̄|` at a leaf at budget `InRange i`: `2^(i - 1)·2⁻³²`. -/
def imE (i : ℕ) : ℚ := 2 ^ (i - 1) / 2 ^ 32

/-- Deviation bound of the computed `ẑ` from the computed input on `T`: `|z - Re t̄| ≤ W + 1` and
`|Im t̄| ≤ E` at a leaf; line 10 adds `(t1 - ẑ1)·ℓ̂`. -/
def devT (W : ℕ) (E : ℚ) : {L : ℕ} → CTree 64 L → ℚ
  | _, .leaf _ => W + 1 + E
  | _, @CTree.node _ L ℓ T0 T1 =>
    let D' := 2 * devT W E T1 + 2
    max D' (2 * devT W E T0 + 2 + D' * nmax (L + 1) ℓ + 1)

/-- Every operation result of `ffsX` on `T` with inputs bounded by `A` fits `InRange i`. -/
def rangeT (i W : ℕ) (E : ℚ) : {L : ℕ} → CTree 64 L → ℚ → Bool
  | _, .leaf σ, A => fitsQ i (A + W + 2) && fitsQ i (|σ.toRat| + 1)
  | _, @CTree.node _ L ℓ T0 T1, A =>
    let D1 := devT W E T1
    let D0 := devT W E T0
    let lam := nmax (L + 1) ℓ
    let D' := 2 * D1 + 2
    let A0 := A + D' * lam + 1
    fitsQ i (2 * A + 1) && fitsQ i (2 * (A + 1 + D1) + 1) && fitsQ i lam &&
      fitsQ i (D' * lam + 1) && fitsQ i (2 * A0 + 1) && fitsQ i (2 * (A0 + 1 + D0) + 1) &&
      rangeT i W E T1 (A + 1) && rangeT i W E T0 (A0 + 1)

/-- **The integer-range check** of `signX` on the key `k` at budget `InRange i`, sampler answers
within `W` of `⌊t̄⌋`, `|Im t̄| ≤ imE i` at the leaves: the tables `twOk C.x.rc`; FFT bounds of `c`
(`|c i| < q`), `f`, `F`; the target in the order `C.target`; `rangeT` on the stored tree. -/
def checkRange (i W : ℕ) (k : RawKey) : Bool :=
  let C0 := { C with word := none }
  let bc : ℚ := 2 * (512 * 12288) + 1
  let mf := nmax 9 (fftW C0 9 k.f) + 1
  let mF := nmax 9 (fftW C0 9 k.F) + 1
  let tgt : List ℚ × ℚ := match C.target with
    | .scaleFirst =>
      let cq := 2 * bc / 12289 + 1
      ([cq, cq * mF + 1, cq * mf + 1], max (cq * mF + 1) (cq * mf + 1))
    | .multiplyFirst =>
      let p := bc * max mF mf + 1
      ([p, 2 * p / 12289 + 1], 2 * p / 12289 + 1)
  twOk C.x.rc && ([bc, 2 * l1Q k.f + 1, 2 * l1Q k.F + 1] ++ tgt.1).all (fitsQ i) &&
    rangeT i W (imE i) (storeC C.x C.xn k) tgt.2

end FalconPrecision.Exec
