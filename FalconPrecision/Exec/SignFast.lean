/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.CheckFast

/-! # Array versions of the signer and of the integer-range check

As in `Exec.CheckFast`: every vector of `fftW`, `splitW`, `mergeW`, `updW`, `targetX` is stored as
an `Array` (`toArr`, read back by `ofArr`), and `ffsXA`, `signXA` compute each split, merge, line-10
update and target once. Each is proved equal to the original: `ofArr_fftWA`, `ofArr_splitWA_fst`,
`ofArr_splitWA_snd`, `ofArr_mergeWA`, `ofArr_updWA`, `ofArr_targetXA_fst`, `ofArr_targetXA_snd`,
`ffsXA_eq`, `signXA_eq`, `storeCA_eq`, `nmaxA_toArr`, `checkRangeA_eq` (`ofArr_targetXAP`,
`signXA_eqP`: at every size `2^logn`; `storeCA_eqP`, `checkRangeA_eqP`: at every size `2^(L+1)` and
leaf `σq`; Falcon-1024: `L = 9`, `σ1024q`). -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFSamp

variable (C : Choices)

/-- `fftW` as an array. -/
def fftWA : (L : ℕ) → (Fin (2 ^ L) → ℤ) → Array (Cx 64)
  | 0, a => #[(Cx.ofInt (a ⟨0, by norm_num⟩) : Cx 64).wr (wordFn C.word)]
  | L + 1, a =>
    let u := fftWA L (evensZ a)
    let v := fftWA L (oddsZ a)
    let t := twBA C.x.rc 64 L
    toArr (L + 1) fun x : Out L × Bool =>
      let p := (ofArr L t x.1).c.mulW (wordFn C.word) C.x.rm (ofArr L v x.1)
      if x.2 then ((ofArr L u x.1).sub p).wr (wordFn C.word)
      else ((ofArr L u x.1).add p).wr (wordFn C.word)

theorem ofArr_fftWA : ∀ (L : ℕ) (a : Fin (2 ^ L) → ℤ), ofArr L (fftWA C L a) = fftW C L a
  | 0, _ => rfl
  | L + 1, a => by
    simp only [fftWA, fftW, ofArr_fftWA L, ofArr_twBA]
    rfl

/-- `splitW` as arrays. -/
def splitWA (L : ℕ) (t : Out (L + 1) → Cx 64) : Array (Cx 64) × Array (Cx 64) :=
  let w := wordFn C.word
  let s := twsBA C.x.rc 64 L
  (toArr L fun o => ((((t (o, false)).add (t (o, true))).wr w).half C.x.rm).wr w,
    toArr L fun o => (ofArr L s o).c.mulW w C.x.rm (((t (o, false)).sub (t (o, true))).wr w))

theorem ofArr_splitWA_fst (L : ℕ) (t : Out (L + 1) → Cx 64) :
    ofArr L (splitWA C L t).1 = (splitW C L t).1 :=
  rfl

theorem ofArr_splitWA_snd (L : ℕ) (t : Out (L + 1) → Cx 64) :
    ofArr L (splitWA C L t).2 = (splitW C L t).2 := by
  simp only [splitWA, splitW, ofArr_twsBA]
  rfl

/-- `mergeW` as an array. -/
def mergeWA (L : ℕ) (c0 c1 : Out L → Cx 64) : Array (Cx 64) :=
  let w := wordFn C.word
  let t := twBA C.x.rc 64 L
  toArr (L + 1) fun x : Out L × Bool =>
    let p := (ofArr L t x.1).c.mulW w C.x.rm (c1 x.1)
    if x.2 then ((c0 x.1).sub p).wr w else ((c0 x.1).add p).wr w

theorem ofArr_mergeWA (L : ℕ) (c0 c1 : Out L → Cx 64) :
    ofArr (L + 1) (mergeWA C L c0 c1) = mergeW C L c0 c1 := by
  simp only [mergeWA, mergeW, ofArr_twBA]
  rfl

/-- `updW` as an array. -/
def updWA {L : ℕ} (t0 t1 z ℓ : Out L → Cx 64) : Array (Cx 64) :=
  let w := wordFn C.word
  toArr L fun o => ((t0 o).add ((((t1 o).sub (z o)).wr w).mulW w C.x.rm (ℓ o))).wr w

theorem ofArr_updWA {L : ℕ} (t0 t1 z ℓ : Out L → Cx 64) :
    ofArr L (updWA C t0 t1 z ℓ) = updW C t0 t1 z ℓ :=
  rfl

/-- `targetX` as arrays. -/
def targetXA {logn : ℕ} (f F c : ZPoly logn) : Array (Cx 64) × Array (Cx 64) :=
  let w := wordFn C.word
  let rm := C.x.rm
  let ch := ofArr logn (fftWA C logn c)
  let fh := ofArr logn (fftWA C logn f)
  let Fh := ofArr logn (fftWA C logn F)
  match C.target with
  | .scaleFirst =>
    let cq := ofArr logn (toArr logn fun o => (divqX rm C.qinv (ch o)).wr w)
    (toArr logn fun o => ((cq o).neg.wr w).mulW w rm (Fh o),
      toArr logn fun o => (cq o).mulW w rm (fh o))
  | .multiplyFirst =>
    (toArr logn fun o => (divqX rm C.qinv (((ch o).mulW w rm (Fh o)).neg.wr w)).wr w,
      toArr logn fun o => (divqX rm C.qinv ((ch o).mulW w rm (fh o))).wr w)

/-- `ofArr_targetXA` at every size `2^logn`. -/
theorem ofArr_targetXAP {logn : ℕ} (f F c : ZPoly logn) :
    ofArr logn (targetXA C f F c).1 = (targetX C f F c).1 ∧
      ofArr logn (targetXA C f F c).2 = (targetX C f F c).2 := by
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  cases tg <;> simp only [targetXA, targetX, ofArr_fftWA, ofArr_toArr, memo_eq, and_self]

theorem ofArr_targetXA (f F c : ZPoly) :
    ofArr 9 (targetXA C f F c).1 = (targetX C f F c).1 ∧
      ofArr 9 (targetXA C f F c).2 = (targetX C f F c).2 :=
  ofArr_targetXAP C f F c

theorem ofArr_targetXA_fst (f F c : ZPoly) :
    ofArr 9 (targetXA C f F c).1 = (targetX C f F c).1 :=
  (ofArr_targetXA C f F c).1

theorem ofArr_targetXA_snd (f F c : ZPoly) :
    ofArr 9 (targetXA C f F c).2 = (targetX C f F c).2 :=
  (ofArr_targetXA C f F c).2

/-- `ffsX` on arrays: each split, merge and line-10 update computed once. -/
def ffsXA {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) :
    {L : ℕ} → CTree 64 L → (t0 t1 : Out L → Cx 64) → m (Option (SampX L))
  | _, .leaf σ, t0, t1 =>
    samp σ (t0 ()).re >>= fun z0 => samp σ (t1 ()).re >>= fun z1 =>
      pure (some ⟨fun _ => z0, fun _ => z1, fun _ => Cx.ofInt z0, fun _ => Cx.ofInt z1⟩)
  | _, @CTree.node _ L ℓ T0 T1, t0, t1 =>
    if chkX C.rchk (L + 1) t1 then
      let p1 := splitWA C L t1
      ffsXA samp T1 (ofArr L p1.1) (ofArr L p1.2) >>= fun r1 =>
        match r1 with
        | none => pure none
        | some s1 =>
          let z1 := ofArr (L + 1) (mergeWA C L s1.c0 s1.c1)
          let t0' := ofArr (L + 1) (updWA C t0 t1 z1 ℓ)
          if chkX C.rchk L s1.c1 && chkX C.rchk (L + 1) t0' then
            let p0 := splitWA C L t0'
            ffsXA samp T0 (ofArr L p0.1) (ofArr L p0.2) >>= fun r0 =>
              match r0 with
              | none => pure none
              | some s0 =>
                if chkX C.rchk L s0.c1 then
                  pure (some ⟨ilv s0.z0 s0.z1, ilv s1.z0 s1.z1,
                    ofArr (L + 1) (mergeWA C L s0.c0 s0.c1), z1⟩)
                else pure none
          else pure none
    else pure none

theorem ffsXA_eq {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) :
    ∀ {L : ℕ} (T : CTree 64 L) (t0 t1 : Out L → Cx 64),
      ffsXA C samp T t0 t1 = ffsX C samp T t0 t1
  | _, .leaf _, _, _ => rfl
  | _, @CTree.node _ L ℓ T0 T1, t0, t1 => by
    simp only [ffsXA, ffsX, ofArr_splitWA_fst, ofArr_splitWA_snd, ofArr_mergeWA, ofArr_updWA,
      ffsXA_eq samp T0, ffsXA_eq samp T1]
    rfl

/-- `signX` on arrays: the target computed once. -/
def signXA {m : Type → Type*} [Monad m] {logn : ℕ} (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 logn) (k : RawKey logn) (c : ZPoly logn) :
    m (Option (ZPoly logn × ZPoly logn)) :=
  if ∀ i, |c i| < 12289 then
    let tg := targetXA C k.f k.F c
    (fun r => r.map fun s => (s.z0, s.z1)) <$> ffsXA C samp T (ofArr logn tg.1) (ofArr logn tg.2)
  else pure none

/-- `signXA_eq` at every size `2^logn`. -/
theorem signXA_eqP {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) {logn : ℕ}
    (T : CTree 64 logn) (k : RawKey logn) (c : ZPoly logn) :
    signXA C samp T k c = signX C samp T k c := by
  unfold signXA signX
  by_cases hc : ∀ i, |c i| < 12289
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc)]
    dsimp only
    rw [ffsXA_eq, (ofArr_targetXAP C k.f k.F c).1, (ofArr_targetXAP C k.f k.F c).2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc)]

theorem signXA_eq {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9)
    (k : RawKey) (c : ZPoly) : signXA C samp T k c = signX C samp T k c :=
  signXA_eqP C samp T k c

/-- `storeC` from the array key expansion `expandBA`. -/
def storeCA {L : ℕ} (k : RawKey (L + 1)) (σq : ℚ := σ512q) : CTree 64 (L + 1) :=
  ((expandBA C.x (64 + C.xn) k σq).lower C.x.rm C.xn).centre

theorem storeCA_eqP {L : ℕ} (k : RawKey (L + 1)) (σq : ℚ) :
    storeCA C k σq = storeC C.x C.xn k σq := by
  rw [storeCA, expandBA_eqP]
  exact storeB_centreP C.x C.xn k σq

theorem storeCA_eq (k : RawKey) : storeCA C k = storeC C.x C.xn k := storeCA_eqP C k σ512q

/-- `nmax` of an array. -/
def nmaxA (L : ℕ) (a : Array (Cx 64)) : ℚ := nmax L (ofArr L a)

theorem nmaxA_toArr (L : ℕ) (v : Out L → Cx 64) : nmaxA L (toArr L v) = nmax L v := by
  rw [nmaxA, ofArr_toArr]

/-- `checkRange` on the array versions. -/
def checkRangeA {L : ℕ} (i W : ℕ) (k : RawKey (L + 1)) (σq : ℚ := σ512q) : Bool :=
  let C0 := { C with word := none }
  let bc : ℚ := 2 * (2 ^ (L + 1) * 12288) + 1
  let mf := nmaxA (L + 1) (fftWA C0 (L + 1) k.f) + 1
  let mF := nmaxA (L + 1) (fftWA C0 (L + 1) k.F) + 1
  let tgt : List ℚ × ℚ := match C.target with
    | .scaleFirst =>
      let cq := 2 * bc / 12289 + 1
      ([cq, cq * mF + 1, cq * mf + 1], max (cq * mF + 1) (cq * mf + 1))
    | .multiplyFirst =>
      let p := bc * max mF mf + 1
      ([p, 2 * p / 12289 + 1], 2 * p / 12289 + 1)
  twOkFastN C.x.rc (L + 1) && ([bc, 2 * l1Q k.f + 1, 2 * l1Q k.F + 1] ++ tgt.1).all (fitsQ i) &&
    rangeT i W (imE i) (storeCA C k σq) tgt.2

theorem checkRangeA_eqP {L : ℕ} (i W : ℕ) (k : RawKey (L + 1)) (σq : ℚ) :
    checkRangeA C i W k σq = checkRange C i W k σq := by
  have e := storeCA_eqP C k σq
  obtain ⟨x, xn, tg, qi, wd, rc, sm, cap, b2, ib, sc⟩ := C
  cases tg <;> simp only [checkRangeA, checkRange, nmaxA, ofArr_fftWA, twOkFastN_eq, e]

theorem checkRangeA_eq (i W : ℕ) (k : RawKey) : checkRangeA C i W k = checkRange C i W k :=
  checkRangeA_eqP C i W k σ512q

end FalconPrecision.Exec
