/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignWitness
public import FalconPrecision.Exec.KeyCheck1024
public import FalconPrecision.Exec.WitnessData1024

/-! # Inputs on which two design-space points sign differently, at Falcon-1024

`Exec.SignWitness` at every SamplerZ parameter set `P`, size `2^(L+1)` and leaf constant `σq`
(`sampDP`, `attDP`, `attDcP`, `msgDP`, their array versions `attDAP`, `attDcAP`, `msgDAP`, proved
equal; the Falcon-512 definitions agree with these at `falcon512S`, `σ512q`, `L = 8` by
unfolding; not stated as theorems), and the search
(`queriesAP`, `candAccP`, `flipScriptP`, `findWitP`, executable only).

At Falcon-1024 (`falcon1024S`, `σ1024q`, KAT entries 0 and 2 of `falcon1024-KAT.rsp`, base point
`cW1024`): the attempt witnesses `wit_*1024` (12 pairs, `wit_salt1024` and `wit_cap1024` at the
signer) and the signer witnesses `wit_*_sig1024`, `wit_word_mf_none1024` (9 pairs), each under a
premise `wit*B1024 = true` that is `#eval` evidence, not proved; the sampler witnesses
`samp_base1024`, `samp_shift1024`, kernel-checked. Draws and the PRNG as in `Exec.SignWitness`. -/

@[expose] public section

namespace FalconPrecision.Exec.Witness

open FalconPrecision.Errors.FFTRec Round3

/-! ## Draws, attempts and signers -/

/-- SamplerZ at `P` on the draws `drawD scr`, logging its query. -/
def sampDP (P : SampParams) (scr : List (ℕ × List ℕ)) (S : SampChoices) (σ t : Fx 64) :
    StateM DSt ℤ := do
  modify fun s => { s with i := 0, log := s.log.push (σ, t) }
  let z ← samplerZ P S (drawD scr) σ t
  modify fun s => { s with call := s.call + 1 }
  pure z

/-- The hash of salt `j`: the `j`-th polynomial of `cs`. -/
def hashDP {logn : ℕ} (cs : List (ZPoly logn)) (j : ℕ) (_ : Unit) : StateM DSt (ZPoly logn) :=
  pure (cs.getD j fun _ => 0)

section

variable (P : SampParams) (σq : ℚ) {L : ℕ}

/-- The signing attempt of `C` on `k`, `c` and the draws `scr`. -/
def attDP (C : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1)) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly (L + 1) × ZPoly (L + 1)) :=
  (signX C (sampDP P scr C.samp) (storeC C.x C.xn k σq) k c).run' {}

/-- The centre-aware signing attempt of `C`. -/
def attDcP (C : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1)) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly (L + 1) × ZPoly (L + 1)) :=
  (signXc C (sampDP P scr C.samp) (storeC C.x C.xn k σq) k c).run' {}

/-- The signer of `C` on `k`, salts `0, 1, …` hashed to `cs`, draws `scr`. -/
def msgDP (C : Choices) (k : RawKey (L + 1)) (cs : List (ZPoly (L + 1)))
    (scr : List (ℕ × List ℕ)) : Option (ℕ × (ZPoly (L + 1) × ZPoly (L + 1))) :=
  (signMsgX C (sampDP P scr) saltD (hashDP cs) k () σq).run' {}

end

/-- `targetFracX` with array FFTs. -/
def targetFracXAP (C : Choices) {logn : ℕ} (k : RawKey logn) (c : ZPoly logn) :
    Array (Cx 64) × Array (Cx 64) :=
  let w := wordFn C.word
  let f0 := ofArr logn (fftWA C logn fun i => modqC ((qtX k c).1 i))
  let f1 := ofArr logn (fftWA C logn fun i => modqC ((qtX k c).2 i))
  (toArr logn fun o => (divqX C.x.rm C.qinv (f0 o)).wr w,
    toArr logn fun o => (divqX C.x.rm C.qinv (f1 o)).wr w)

theorem ofArr_targetFracXAP (C : Choices) {logn : ℕ} (k : RawKey logn) (c : ZPoly logn) :
    ofArr logn (targetFracXAP C k c).1 = (targetFracX C k c).1 ∧
      ofArr logn (targetFracXAP C k c).2 = (targetFracX C k c).2 := by
  simp only [targetFracXAP, targetFracX, ofArr_fftWA, ofArr_toArr, memo_eq, and_self]

/-- `signXc` with array arithmetic. -/
def signXcAP (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    {logn : ℕ} (T : CTree 64 logn) (k : RawKey logn) (c : ZPoly logn) :
    m (Option (ZPoly logn × ZPoly logn)) :=
  match C.samp.centre with
  | .plain => signXA C samp T k c
  | .fractional =>
    if ∀ i, |c i| < 12289 then
      let tf := targetFracXAP C k c
      (fun r => r.map fun s => (fun i => (tIntX k c).1 i + s.z0 i,
        fun i => (tIntX k c).2 i + s.z1 i)) <$>
        ffsXA C samp T (ofArr logn tf.1) (ofArr logn tf.2)
    else pure none

theorem signXcAP_eq (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    {logn : ℕ} (T : CTree 64 logn) (k : RawKey logn) (c : ZPoly logn) :
    signXcAP C samp T k c = signXc C samp T k c := by
  unfold signXcAP signXc
  cases C.samp.centre
  · simp only [signXA_eqP]
  · simp only [ffsXA_eq, (ofArr_targetFracXAP C k c).1, (ofArr_targetFracXAP C k c).2]

/-- `tabEqBN` on the array tables. -/
def tabEqBAN (N : ℕ) (rc1 rc2 : RMode) (f : ℕ) : Bool :=
  (List.range N).all fun L =>
    let t1 := ofArr L (twBA rc1 f L)
    let t2 := ofArr L (twBA rc2 f L)
    let s1 := ofArr L (twsBA rc1 f L)
    let s2 := ofArr L (twsBA rc2 f L)
    allOut L fun o => decide ((t1 o).c = (t2 o).c) && decide ((s1 o).c = (s2 o).c)

theorem tabEqBAN_eq (N : ℕ) (rc1 rc2 : RMode) (f : ℕ) :
    tabEqBAN N rc1 rc2 f = tabEqBN N rc1 rc2 f := by
  simp only [tabEqBAN, tabEqBN, ofArr_twBA, ofArr_twsBA]

/-- A polynomial read from an array (not inlined, so that the array is built once). -/
@[noinline] def zArr {logn : ℕ} (a : Array ℤ) : ZPoly logn := fun i => a.getD i.1 0

theorem zArr_ofFn {logn : ℕ} (f : ZPoly logn) : zArr (Array.ofFn f) = f := by
  funext i
  simp [zArr, Array.getD, i.2]

/-- A pair of polynomials stored in arrays. -/
def memoP {logn : ℕ} (z : ZPoly logn × ZPoly logn) : ZPoly logn × ZPoly logn :=
  (zArr (Array.ofFn z.1), zArr (Array.ofFn z.2))

theorem memoP_eq {logn : ℕ} (z : ZPoly logn × ZPoly logn) : memoP z = z := by
  simp only [memoP, zArr_ofFn]

/-- `accX` on the attempt output stored in arrays. -/
def accXAP (C : Choices) {logn : ℕ} (k : RawKey logn) (c : ZPoly logn)
    (y : Option (ZPoly logn × ZPoly logn)) : Option (ZPoly logn × ZPoly logn) :=
  accX C k c (y.map memoP)

theorem accXAP_eq (C : Choices) {logn : ℕ} (k : RawKey logn) : accXAP C k = accX C k := by
  have e : (memoP : ZPoly logn × ZPoly logn → ZPoly logn × ZPoly logn) = id := funext memoP_eq
  funext c y
  simp only [accXAP, e, Option.map_id, id_eq]

section

variable (P : SampParams) (σq : ℚ) {L : ℕ}

def attDAP (C : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1)) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly (L + 1) × ZPoly (L + 1)) :=
  (signXA C (sampDP P scr C.samp) (storeCA C k σq) k c).run' {}

theorem attDAP_eq (C : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1))
    (scr : List (ℕ × List ℕ)) : attDAP P σq C k c scr = attDP P σq C k c scr := by
  rw [attDAP, attDP, signXA_eqP, storeCA_eqP]

def attDcAP (C : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1)) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly (L + 1) × ZPoly (L + 1)) :=
  (signXcAP C (sampDP P scr C.samp) (storeCA C k σq) k c).run' {}

theorem attDcAP_eq (C : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1))
    (scr : List (ℕ × List ℕ)) : attDcAP P σq C k c scr = attDcP P σq C k c scr := by
  rw [attDcAP, attDcP, signXcAP_eq, storeCA_eqP]

def msgDAP (C : Choices) (k : RawKey (L + 1)) (cs : List (ZPoly (L + 1)))
    (scr : List (ℕ × List ℕ)) : Option (ℕ × (ZPoly (L + 1) × ZPoly (L + 1))) :=
  (signLoopX C.salt saltD (hashDP cs) (signXA C (sampDP P scr C.samp) (storeCA C k σq) k)
    (accXAP C k) () C.cap).run' {}

theorem msgDAP_eq (C : Choices) (k : RawKey (L + 1)) (cs : List (ZPoly (L + 1)))
    (scr : List (ℕ × List ℕ)) : msgDAP P σq C k cs scr = msgDP P σq C k cs scr := by
  have e : signXA C (sampDP P scr C.samp) (storeCA C k σq) k =
      signX C (sampDP P scr C.samp) (storeC C.x C.xn k σq) k :=
    funext fun c => by rw [signXA_eqP, storeCA_eqP]
  rw [msgDAP, msgDP, e, accXAP_eq]
  rfl

end

/-! ## Comparison -/

/-- The coefficients of an output, for comparison. -/
def zlP {logn : ℕ} (z : Option (ZPoly logn × ZPoly logn)) : Option (List ℤ × List ℤ) :=
  z.map fun p => ((List.finRange (2 ^ logn)).map p.1, (List.finRange (2 ^ logn)).map p.2)

/-- A signer output, for comparison. -/
def zlmP {logn : ℕ} (r : Option (ℕ × (ZPoly logn × ZPoly logn))) :
    Option (ℕ × Option (List ℤ × List ℤ)) :=
  r.map fun p => (p.1, zlP (some p.2))

section

variable {P : SampParams} {σq : ℚ} {L : ℕ}

theorem attDP_ne {C1 C2 : Choices} {k : RawKey (L + 1)} {c : ZPoly (L + 1)}
    {s1 s2 : List (ℕ × List ℕ)} (h : zlP (attDAP P σq C1 k c s1) ≠ zlP (attDAP P σq C2 k c s2)) :
    attDP P σq C1 k c s1 ≠ attDP P σq C2 k c s2 := by
  rw [← attDAP_eq, ← attDAP_eq]
  exact fun e => h (congrArg zlP e)

theorem attDcP_ne {C1 C2 : Choices} {k : RawKey (L + 1)} {c : ZPoly (L + 1)}
    {s1 s2 : List (ℕ × List ℕ)}
    (h : zlP (attDcAP P σq C1 k c s1) ≠ zlP (attDcAP P σq C2 k c s2)) :
    attDcP P σq C1 k c s1 ≠ attDcP P σq C2 k c s2 := by
  rw [← attDcAP_eq, ← attDcAP_eq]
  exact fun e => h (congrArg zlP e)

theorem msgDP_ne {C1 C2 : Choices} {k : RawKey (L + 1)} {cs : List (ZPoly (L + 1))}
    {s1 s2 : List (ℕ × List ℕ)}
    (h : zlmP (msgDAP P σq C1 k cs s1) ≠ zlmP (msgDAP P σq C2 k cs s2)) :
    msgDP P σq C1 k cs s1 ≠ msgDP P σq C2 k cs s2 := by
  rw [← msgDAP_eq, ← msgDAP_eq]
  exact fun e => h (congrArg zlmP e)

end

section

variable (P : SampParams) (σq : ℚ) {L : ℕ}

/-- The attempts of `C1`, `C2` on `k`, `c`, draws `scr` differ (array versions). -/
def attNeBP (C1 C2 : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1))
    (scr : List (ℕ × List ℕ)) : Bool :=
  decide (zlP (attDAP P σq C1 k c scr) ≠ zlP (attDAP P σq C2 k c scr))

/-- The centre-aware attempts of `C1`, `C2` differ (array versions). -/
def attcNeBP (C1 C2 : Choices) (k : RawKey (L + 1)) (c : ZPoly (L + 1))
    (scr : List (ℕ × List ℕ)) : Bool :=
  decide (zlP (attDcAP P σq C1 k c scr) ≠ zlP (attDcAP P σq C2 k c scr))

/-- The signers of `C1`, `C2` differ (array versions). -/
def msgNeBP (C1 C2 : Choices) (k : RawKey (L + 1)) (cs : List (ZPoly (L + 1)))
    (scr : List (ℕ × List ℕ)) : Bool :=
  decide (zlmP (msgDAP P σq C1 k cs scr) ≠ zlmP (msgDAP P σq C2 k cs scr))

end

section

variable {P : SampParams} {σq : ℚ} {L : ℕ}

theorem attDP_ne_of {C1 C2 : Choices} {k : RawKey (L + 1)} {c : ZPoly (L + 1)}
    {scr : List (ℕ × List ℕ)} (h : attNeBP P σq C1 C2 k c scr = true) :
    attDP P σq C1 k c scr ≠ attDP P σq C2 k c scr :=
  attDP_ne (of_decide_eq_true h)

theorem attDcP_ne_of {C1 C2 : Choices} {k : RawKey (L + 1)} {c : ZPoly (L + 1)}
    {scr : List (ℕ × List ℕ)} (h : attcNeBP P σq C1 C2 k c scr = true) :
    attDcP P σq C1 k c scr ≠ attDcP P σq C2 k c scr :=
  attDcP_ne (of_decide_eq_true h)

theorem msgDP_ne_of {C1 C2 : Choices} {k : RawKey (L + 1)} {cs : List (ZPoly (L + 1))}
    {scr : List (ℕ × List ℕ)} (h : msgNeBP P σq C1 C2 k cs scr = true) :
    msgDP P σq C1 k cs scr ≠ msgDP P σq C2 k cs scr :=
  msgDP_ne (of_decide_eq_true h)

end

/-! ## Search (executable) -/

/-- The queries `(σ̄, t̄)` of the centre-aware attempt on policy draws. -/
def queriesAP (P : SampParams) (σq : ℚ) {L : ℕ} (C : Choices) (k : RawKey (L + 1))
    (c : ZPoly (L + 1)) : Array (Fx 64 × Fx 64) :=
  ((signXcAP C (sampDP P [] C.samp) (storeCA C k σq) k c).run {}).2.log

/-- `2⁶⁴·Pr[accept]` of the candidate `(u, c)` at the query `(σ̄, t̄)` under `S` at `P`. -/
def candAccP (P : SampParams) (S : SampChoices) (q : Fx 64 × Fx 64) (u c : ℕ) : ℕ :=
  let r := q.2.toRat - q.2.toInt .floor
  accW P S.shiftRej (xOf P q.1.toRat r (z0Of (P.tab S.base) u c) (c % 2 = 1)) (P.σmin / q.1.toRat)

/-- `flipScript` at `P`. -/
def flipScriptP (P : SampParams) (S1 S2 : SampChoices) (q1 q2 : Fx 64 × Fx 64) :
    Option (List ℕ) :=
  let cands :=
    (uFor 0, 1) :: (List.range' 1 5).flatMap fun z0 => [(uFor z0, 1), (uFor z0, 0)]
  cands.findSome? fun (u, c) =>
    let a1 := candAccP P S1 q1 u c
    let a2 := candAccP P S2 q2 u c
    if a1 ≠ a2 then some ([u, c] ++ bytesBE (min a1 a2)) else none

/-- `findWit` at `P`, `σq`, size `2^(L+1)`. -/
def findWitP (P : SampParams) (σq : ℚ) {L : ℕ} (C1 C2 : Choices) (k : RawKey (L + 1))
    (c : ZPoly (L + 1)) : Option (ℕ × Option (List ℕ)) :=
  let a := (queriesAP P σq C1 k c).toList
  let b := (queriesAP P σq C2 k c).toList
  let frac := decide (C1.samp.centre ≠ C2.samp.centre)
  (List.range (min a.length b.length)).findSome? fun j =>
    match a[j]?, b[j]? with
    | some q1, some q2 =>
      if q1 = q2 then none
      else if !frac && decide (q1.2.toInt .floor ≠ q2.2.toInt .floor) then some (j, none)
      else (flipScriptP P C1.samp C2.samp q1 q2).map fun l => (j, some l)
    | _, _ => none

/-! ## Witnesses at Falcon-1024

KAT entries 0 and 2 of `falcon1024-KAT.rsp` (`Exec.WitnessData1024`; both keys pass `check1024`,
E23), SamplerZ at `falcon1024S`, leaves `σ1024q`. As at Falcon-512, each witness holds under the
premise that a `Bool` (`wit*B1024`) is `true`, and the implication is proved (`attDP_ne_of`,
`attDcP_ne_of`, `msgDP_ne_of`). The premises are **not proved**: each evaluates to `true` by
`#eval` (Lean's interpreter; `test/ExecEquivEval1024.lean`, `test/ExecEquivEval1024Sig.lean`),
not by the kernel. The sampler witnesses `samp_base1024`, `samp_shift1024` are kernel-checked. -/

/-- The decoded key at `logn = 10` (the zero key if decoding fails; the tests check it does
not). -/
def keyOf1024 (s : String) : RawKey 10 :=
  ((ofHex s).bind (decodeKey · 10)).getD ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- A polynomial of degree `< 1024` from its coefficient list. -/
def polyOf1024 (l : List ℤ) : ZPoly 10 := fun i => l.getD i.1 0

/-- KAT entry 0: key and hashed message. -/
def key0_1024 : RawKey 10 := keyOf1024 wSk0_1024
def c0_1024 : ZPoly 10 := polyOf1024 wC0_1024

/-- KAT entry 2: key and hashed message. -/
def key2_1024 : RawKey 10 := keyOf1024 wSk2_1024
def c2_1024 : ZPoly 10 := polyOf1024 wC2_1024

/-- KAT entry 70: hashed message (second hash of `wit_salt1024`, `wit_cap1024`). -/
def c70_1024 : ZPoly 10 := polyOf1024 wC70_1024

/-- The base point at Falcon-1024: `cW` with `⌊β²⌋ = 70265242`. -/
def cW1024 : Choices := { cW with beta2 := 70265242 }

/-- `cW1024` with the stored-constant and operation roundings `rc`, `rm`. -/
def cR1024 (rm rc : RMode) : Choices := { cW1024 with x := { cW1024.x with rm := rm, rc := rc } }

/-- Multiply-first at 32.64 and at 64.64, Falcon-1024. -/
def cMF32_1024 : Choices := { cW1024 with target := .multiplyFirst, word := some 32 }
def cMF64_1024 : Choices := { cW1024 with target := .multiplyFirst, word := some 64 }

/-- Draws of `wit_target1024`: call 0 scripted. -/
def scrTarget1024 : List (ℕ × List ℕ) :=
  [(0, [636254429462080897534, 1, 77, 60, 187, 119, 145, 253, 138, 28])]

/-- Draws of `wit_dm1024`: call 0 scripted. -/
def scrDm1024 : List (ℕ × List ℕ) :=
  [(0, [2 ^ 72 - 1, 1, 170, 164, 79, 210, 105, 149, 118, 47])]

/-- Draws of `wit_root1024`, `wit_rm_floor1024`, `wit_qinv1024`: call 0 scripted. -/
def scrA1024 : List (ℕ × List ℕ) := [(0, [2 ^ 72 - 1, 1, 170, 164, 79, 210, 105, 150, 128, 73])]

/-- Draws of `wit_rm_up1024`, `wit_rm_away1024`: call 4 scripted. -/
def scrUp1024 : List (ℕ × List ℕ) :=
  [(4, [199560484645026482915, 0, 97, 230, 7, 221, 0, 163, 52, 81])]

/-- Draws of `wit_rc_floor1024`: call 0 scripted. -/
def scrRc1024 : List (ℕ × List ℕ) := [(0, [2 ^ 72 - 1, 1, 170, 164, 79, 210, 105, 150, 128, 35])]

/-- Draws of `wit_centre1024`: call 0 scripted. -/
def scrCentre1024 : List (ℕ × List ℕ) :=
  [(0, [2 ^ 72 - 1, 1, 170, 164, 79, 210, 105, 150, 128, 47])]

/-- Every call of the first attempt draws the candidate `z0 = 5` (rejected by the norm bound),
later calls the policy. -/
def scrRej1024 : List (ℕ × List ℕ) := (List.range 2048).map fun j => (j, [uFor 5, j % 2])

def witWordMfB1024 : Bool :=
  attNeBP falcon1024S σ1024q cMF32_1024 cMF64_1024 key2_1024 c2_1024 []
def witTargetB1024 : Bool :=
  attNeBP falcon1024S σ1024q cW1024 { cW1024 with target := .multiplyFirst } key0_1024 c0_1024
    scrTarget1024
def witDmB1024 : Bool :=
  attNeBP falcon1024S σ1024q cW1024 { cW1024 with x := { cW1024.x with dm := .invMul } }
    key0_1024 c0_1024 scrDm1024
def witRootB1024 : Bool :=
  attNeBP falcon1024S σ1024q cW1024 { cW1024 with x := { cW1024.x with root := .ntru } }
    key0_1024 c0_1024 scrA1024
def witRmUpB1024 : Bool :=
  attNeBP falcon1024S σ1024q cW1024 (cR1024 .halfUp .halfEven) key0_1024 c0_1024 scrUp1024
def witRmAwayB1024 : Bool :=
  attNeBP falcon1024S σ1024q (cR1024 .halfUp .halfEven) (cR1024 .halfAway .halfEven) key0_1024
    c0_1024 scrUp1024
def witRmFloorB1024 : Bool :=
  attNeBP falcon1024S σ1024q cW1024 (cR1024 .floor .halfEven) key0_1024 c0_1024 scrA1024
def witRcFloorB1024 : Bool :=
  attNeBP falcon1024S σ1024q cW1024 (cR1024 .halfEven .floor) key0_1024 c0_1024 scrRc1024
def witQinvB1024 : Bool :=
  attNeBP falcon1024S σ1024q cW1024 { cW1024 with qinv := .w64 } key0_1024 c0_1024 scrA1024
def witCentreB1024 : Bool :=
  attcNeBP falcon1024S σ1024q cW1024
    { cW1024 with samp := { cW1024.samp with centre := .fractional } } key0_1024 c0_1024
    scrCentre1024
def witSaltB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 { cW1024 with salt := .perAttempt } key0_1024
    [c0_1024, c70_1024] scrRej1024
def witCapB1024 : Bool :=
  msgNeBP falcon1024S σ1024q { cW1024 with cap := 1 } cW1024 key0_1024 [c0_1024, c70_1024]
    scrRej1024

/-- **Attempts at Falcon-1024, 32.64 ≠ 64.64, multiply-first**: attempt outputs `z` (before the
norm check) on KAT entry 2, policy draws (first coefficient `-26` vs `-709`), if
`witWordMfB1024` (true by `#eval`, not proved). -/
theorem wit_word_mf1024 (h : witWordMfB1024 = true) :
    attDP falcon1024S σ1024q cMF32_1024 key2_1024 c2_1024 [] ≠
      attDP falcon1024S σ1024q cMF64_1024 key2_1024 c2_1024 [] :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, scale-first ≠ multiply-first**: attempt outputs on entry 0, one
scripted call (`-178` vs `-179`), if `witTargetB1024` (true by `#eval`, not proved). -/
theorem wit_target1024 (h : witTargetB1024 = true) :
    attDP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrTarget1024 ≠
      attDP falcon1024S σ1024q { cW1024 with target := .multiplyFirst } key0_1024 c0_1024
        scrTarget1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, `y/x` ≠ `1/x·y`**: attempt outputs on entry 0, `xn = 0` (`-182` vs
`-179`), if `witDmB1024` (true by `#eval`, not proved). -/
theorem wit_dm1024 (h : witDmB1024 = true) :
    attDP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrDm1024 ≠
      attDP falcon1024S σ1024q { cW1024 with x := { cW1024.x with dm := .invMul } } key0_1024
        c0_1024 scrDm1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, root plain ≠ NTRU**: attempt outputs on entry 0, `xn = 0` (`-179`
vs `-182`), if `witRootB1024` (true by `#eval`, not proved). -/
theorem wit_root1024 (h : witRootB1024 = true) :
    attDP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrA1024 ≠
      attDP falcon1024S σ1024q { cW1024 with x := { cW1024.x with root := .ntru } } key0_1024
        c0_1024 scrA1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, operation rounding ties to even ≠ half up**: attempt outputs on
entry 0, call 4 (`-179` vs `-184`), if `witRmUpB1024` (true by `#eval`, not proved). -/
theorem wit_rm_up1024 (h : witRmUpB1024 = true) :
    attDP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrUp1024 ≠
      attDP falcon1024S σ1024q (cR1024 .halfUp .halfEven) key0_1024 c0_1024 scrUp1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, operation rounding half up ≠ half away**: attempt outputs on
entry 0, call 4 (`-184` vs `-179`), if `witRmAwayB1024` (true by `#eval`, not proved). -/
theorem wit_rm_away1024 (h : witRmAwayB1024 = true) :
    attDP falcon1024S σ1024q (cR1024 .halfUp .halfEven) key0_1024 c0_1024 scrUp1024 ≠
      attDP falcon1024S σ1024q (cR1024 .halfAway .halfEven) key0_1024 c0_1024 scrUp1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, operation rounding ties to even ≠ floor**: attempt outputs on
entry 0 (`-179` vs `-182`), if `witRmFloorB1024` (true by `#eval`, not proved). -/
theorem wit_rm_floor1024 (h : witRmFloorB1024 = true) :
    attDP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrA1024 ≠
      attDP falcon1024S σ1024q (cR1024 .floor .halfEven) key0_1024 c0_1024 scrA1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, stored constants ties to even ≠ floor**: attempt outputs on entry
0 (`-182` vs `-179`), if `witRcFloorB1024` (true by `#eval`, not proved). -/
theorem wit_rc_floor1024 (h : witRcFloorB1024 = true) :
    attDP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrRc1024 ≠
      attDP falcon1024S σ1024q (cR1024 .halfEven .floor) key0_1024 c0_1024 scrRc1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, `1/q` at 77 bits ≠ at 64 bits**: attempt outputs on entry 0
(`-179` vs `-182`), if `witQinvB1024` (true by `#eval`, not proved). -/
theorem wit_qinv1024 (h : witQinvB1024 = true) :
    attDP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrA1024 ≠
      attDP falcon1024S σ1024q { cW1024 with qinv := .w64 } key0_1024 c0_1024 scrA1024 :=
  attDP_ne_of h

/-- **Attempts at Falcon-1024, plain ≠ fractional centre**: centre-aware attempt outputs on entry
0 (`-182` vs `-179`), if `witCentreB1024` (true by `#eval`, not proved). -/
theorem wit_centre1024 (h : witCentreB1024 = true) :
    attDcP falcon1024S σ1024q cW1024 key0_1024 c0_1024 scrCentre1024 ≠
      attDcP falcon1024S σ1024q { cW1024 with samp := { cW1024.samp with centre := .fractional } }
        key0_1024 c0_1024 scrCentre1024 :=
  attDcP_ne_of h

/-- **Reused salt ≠ a fresh salt per attempt at Falcon-1024** after one rejected attempt (entry 0
key; stand-in hashes `c0_1024`, `c70_1024` for salts `0`, `1`, not the hashes of the salts with a
message; outputs salt `0` vs salt `1`), if `witSaltB1024` (true by `#eval`, not proved). -/
theorem wit_salt1024 (h : witSaltB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024, c70_1024] scrRej1024 ≠
      msgDP falcon1024S σ1024q { cW1024 with salt := .perAttempt } key0_1024 [c0_1024, c70_1024]
        scrRej1024 :=
  msgDP_ne_of h

/-- **Cap 1 ≠ cap 27 at Falcon-1024** (the first attempt is rejected; `none` vs a signature), if
`witCapB1024` (true by `#eval`, not proved). -/
theorem wit_cap1024 (h : witCapB1024 = true) :
    msgDP falcon1024S σ1024q { cW1024 with cap := 1 } key0_1024 [c0_1024, c70_1024] scrRej1024 ≠
      msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024, c70_1024] scrRej1024 :=
  msgDP_ne_of h

/-! ### Signer level at Falcon-1024: the same pairs, keys, hashed messages and draws

Reused salt, one hash (`cs = [c]`), cap 27; the outputs are signatures or `none`. -/

def witWordMfSigB1024 : Bool :=
  (msgDAP falcon1024S σ1024q cMF32_1024 key2_1024 [c2_1024] []).isNone &&
    (msgDAP falcon1024S σ1024q cMF64_1024 key2_1024 [c2_1024] []).isSome
def witTargetSigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 { cW1024 with target := .multiplyFirst } key0_1024 [c0_1024]
    scrTarget1024
def witDmSigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 { cW1024 with x := { cW1024.x with dm := .invMul } }
    key0_1024 [c0_1024] scrDm1024
def witRootSigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 { cW1024 with x := { cW1024.x with root := .ntru } }
    key0_1024 [c0_1024] scrA1024
def witRmUpSigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 (cR1024 .halfUp .halfEven) key0_1024 [c0_1024] scrUp1024
def witRmAwaySigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q (cR1024 .halfUp .halfEven) (cR1024 .halfAway .halfEven) key0_1024
    [c0_1024] scrUp1024
def witRmFloorSigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 (cR1024 .floor .halfEven) key0_1024 [c0_1024] scrA1024
def witRcFloorSigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 (cR1024 .halfEven .floor) key0_1024 [c0_1024] scrRc1024
def witQinvSigB1024 : Bool :=
  msgNeBP falcon1024S σ1024q cW1024 { cW1024 with qinv := .w64 } key0_1024 [c0_1024] scrA1024

/-- **Multiply-first at Falcon-1024: 32.64 gives no signature, 64.64 a signature** (KAT entry 2,
policy draws: all 27 attempts of the 32.64 signer are rejected), if `witWordMfSigB1024` (true by
`#eval`, not proved). -/
theorem wit_word_mf_none1024 (h : witWordMfSigB1024 = true) :
    msgDP falcon1024S σ1024q cMF32_1024 key2_1024 [c2_1024] [] = none ∧
      (msgDP falcon1024S σ1024q cMF64_1024 key2_1024 [c2_1024] []).isSome = true := by
  unfold witWordMfSigB1024 at h
  rw [msgDAP_eq, msgDAP_eq, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h

/-- **32.64 ≠ 64.64 signers at Falcon-1024, multiply-first** (entry 2, policy draws), if
`witWordMfSigB1024` (true by `#eval`, not proved). -/
theorem wit_word_mf_sig1024 (h : witWordMfSigB1024 = true) :
    msgDP falcon1024S σ1024q cMF32_1024 key2_1024 [c2_1024] [] ≠
      msgDP falcon1024S σ1024q cMF64_1024 key2_1024 [c2_1024] [] := by
  intro e
  have h2 := (wit_word_mf_none1024 h).2
  rw [← e, (wit_word_mf_none1024 h).1] at h2
  exact Bool.false_ne_true h2

/-- **Scale-first ≠ multiply-first signers at Falcon-1024** (entry 0, `scrTarget1024`; first
coefficients `-66` vs `-77`), if `witTargetSigB1024` (true by `#eval`, not proved). -/
theorem wit_target_sig1024 (h : witTargetSigB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024] scrTarget1024 ≠
      msgDP falcon1024S σ1024q { cW1024 with target := .multiplyFirst } key0_1024 [c0_1024]
        scrTarget1024 :=
  msgDP_ne_of h

/-- **`y/x` ≠ `1/x·y` signers at Falcon-1024** (entry 0, `xn = 0`, `scrDm1024`), if
`witDmSigB1024` (true by `#eval`, not proved). -/
theorem wit_dm_sig1024 (h : witDmSigB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024] scrDm1024 ≠
      msgDP falcon1024S σ1024q { cW1024 with x := { cW1024.x with dm := .invMul } } key0_1024
        [c0_1024] scrDm1024 :=
  msgDP_ne_of h

/-- **Root plain ≠ NTRU signers at Falcon-1024** (entry 0, `xn = 0`, `scrA1024`), if
`witRootSigB1024` (true by `#eval`, not proved). -/
theorem wit_root_sig1024 (h : witRootSigB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024] scrA1024 ≠
      msgDP falcon1024S σ1024q { cW1024 with x := { cW1024.x with root := .ntru } } key0_1024
        [c0_1024] scrA1024 :=
  msgDP_ne_of h

/-- **Ties to even ≠ half up signers at Falcon-1024** (entry 0, `scrUp1024`), if
`witRmUpSigB1024` (true by `#eval`, not proved). -/
theorem wit_rm_up_sig1024 (h : witRmUpSigB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024] scrUp1024 ≠
      msgDP falcon1024S σ1024q (cR1024 .halfUp .halfEven) key0_1024 [c0_1024] scrUp1024 :=
  msgDP_ne_of h

/-- **Half up ≠ half away signers at Falcon-1024** (entry 0, `scrUp1024`), if
`witRmAwaySigB1024` (true by `#eval`, not proved). -/
theorem wit_rm_away_sig1024 (h : witRmAwaySigB1024 = true) :
    msgDP falcon1024S σ1024q (cR1024 .halfUp .halfEven) key0_1024 [c0_1024] scrUp1024 ≠
      msgDP falcon1024S σ1024q (cR1024 .halfAway .halfEven) key0_1024 [c0_1024] scrUp1024 :=
  msgDP_ne_of h

/-- **Ties to even ≠ floor signers at Falcon-1024** (operation rounding; entry 0, `scrA1024`), if
`witRmFloorSigB1024` (true by `#eval`, not proved). -/
theorem wit_rm_floor_sig1024 (h : witRmFloorSigB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024] scrA1024 ≠
      msgDP falcon1024S σ1024q (cR1024 .floor .halfEven) key0_1024 [c0_1024] scrA1024 :=
  msgDP_ne_of h

/-- **Ties to even ≠ floor signers at Falcon-1024** (stored constants; entry 0, `scrRc1024`), if
`witRcFloorSigB1024` (true by `#eval`, not proved). -/
theorem wit_rc_floor_sig1024 (h : witRcFloorSigB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024] scrRc1024 ≠
      msgDP falcon1024S σ1024q (cR1024 .halfEven .floor) key0_1024 [c0_1024] scrRc1024 :=
  msgDP_ne_of h

/-- **`1/q` at 77 bits ≠ at 64 bits signers at Falcon-1024** (entry 0, `scrA1024`), if
`witQinvSigB1024` (true by `#eval`, not proved). -/
theorem wit_qinv_sig1024 (h : witQinvSigB1024 = true) :
    msgDP falcon1024S σ1024q cW1024 key0_1024 [c0_1024] scrA1024 ≠
      msgDP falcon1024S σ1024q { cW1024 with qinv := .w64 } key0_1024 [c0_1024] scrA1024 :=
  msgDP_ne_of h

/-- **Base table 72 bits ≠ 79 bits at Falcon-1024**, one SamplerZ call at `falcon1024S` (the
draws and `σ̄ = ⌊σmax·2⁶⁴⌋/2⁶⁴` of `samp_base`; outputs `-16` vs `-17`). Kernel-checked. -/
theorem samp_base1024 :
    Id.run ((sampDP falcon1024S [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
      ⟨33582297586188238716⟩ ⟨0⟩).run' {}) ≠
    Id.run ((sampDP falcon1024S [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b79⟩
      ⟨33582297586188238716⟩ ⟨0⟩).run' {}) := by
  decide +kernel

/-- **Saturated shift ≠ shift rejection at Falcon-1024**, one SamplerZ call at `falcon1024S`
(`σ̄ = ⌈σmin·2⁶⁴⌉/2⁶⁴` with `σmin = 1.298280334`, `t̄ = 0`, the draws of `samp_shift`; outputs
`-18` vs `0`). Kernel-checked. -/
theorem samp_shift1024 :
    Id.run ((sampDP falcon1024S [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
      ⟨23949045057228157292⟩ ⟨0⟩).run' {}) ≠
    Id.run ((sampDP falcon1024S [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, true, .b72⟩
      ⟨23949045057228157292⟩ ⟨0⟩).run' {}) := by
  decide +kernel

end FalconPrecision.Exec.Witness
