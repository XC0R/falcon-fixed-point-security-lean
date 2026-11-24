/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignEquiv
public import FalconPrecision.Exec.SignFast
public import FalconPrecision.Exec.WitnessData

/-! # Inputs on which two design-space points sign differently

A witness is a key, a hashed message `c` and the uniform draws of SamplerZ on which the signing
attempts (or signers) of two `Choices` differ. Draws (`sampD scr`): SamplerZ (`samplerZ
falcon512S`) whose `j`-th call reads the script `scr.lookup j` and then the policy draws (all ones
for a 72-bit draw, `0` otherwise: the candidate `z = 0`, accepted, so the output is `⌊t̄⌋`).
Draws are assigned per call (call `j` reads its script from its first draw); the draws each
signer reads form a finite sequence of positive probability under uniform draws. The PRNG that
produces the draws in an implementation (SHAKE-256) is not modelled.

`attD`, `attDc`, `msgD` are the attempt `signX`, the centre-aware attempt `signXc` and the signer
`signMsgX` on such draws; `attDA`, `attDcA`, `msgDA` the array versions used for evaluation,
proved equal. The search (`queriesA`, `firstDiff`, `flipScript`) is executable only. -/

@[expose] public section

namespace FalconPrecision.Exec.Witness

open FalconPrecision.Errors.FFTRec Round3

/-! ## Inputs -/

/-- The decoded key (the zero key if decoding fails; the tests check it does not). -/
def keyOf (s : String) : RawKey :=
  ((ofHex s).bind decodeKey).getD ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- A polynomial from its coefficient list. -/
def polyOf (l : List ℤ) : ZPoly := fun i => l.getD i.1 0

/-- KAT entry 0: key and hashed message. -/
def key0 : RawKey := keyOf wSk0
def c0 : ZPoly := polyOf wC0

/-- KAT entry 70: key and hashed message. -/
def key70 : RawKey := keyOf wSk70
def c70 : ZPoly := polyOf wC70

/-- The base point: ties to even everywhere, scale-first, `1/q` at 77 bits, unbounded words,
no range checks, reused salt, cap 27, `⌊β²⌋ = 34034726`, the spec's SamplerZ (plain centre,
saturated shifts, 72-bit table). -/
def cW : Choices :=
  { x := ⟨.halfEven, .halfEven, .direct, .plain⟩, xn := 0, target := .scaleFirst, qinv := .w77,
    word := none, rchk := none, salt := .reused, cap := 27, beta2 := 34034726, infB := none,
    samp := ⟨.plain, false, .b72⟩ }

/-! ## Draws -/

/-- Sampler state: call index, draw index within the call, salts drawn, queries `(σ̄, t̄)`. -/
structure DSt where
  call : ℕ := 0
  i : ℕ := 0
  salts : ℕ := 0
  log : Array (Fx 64 × Fx 64) := #[]

/-- The policy draw: all ones for a 72-bit draw, `0` otherwise. -/
def policy (k : ℕ) : ℕ := if k = 72 then 2 ^ 72 - 1 else 0

/-- A `k`-bit draw: the script of the current call, then the policy. -/
def drawD (scr : List (ℕ × List ℕ)) (k : ℕ) : StateM DSt ℕ :=
  modifyGet fun s =>
    ((((List.lookup s.call scr).bind (·[s.i]?)).map (· % 2 ^ k)).getD (policy k),
      { s with i := s.i + 1 })

/-- SamplerZ on the draws `drawD scr`, logging its query. -/
def sampD (scr : List (ℕ × List ℕ)) (S : SampChoices) (σ t : Fx 64) : StateM DSt ℤ := do
  modify fun s => { s with i := 0, log := s.log.push (σ, t) }
  let z ← samplerZ falcon512S S (drawD scr) σ t
  modify fun s => { s with call := s.call + 1 }
  pure z

/-- Salts `0, 1, 2, …`. -/
def saltD : StateM DSt ℕ := modifyGet fun s => (s.salts, { s with salts := s.salts + 1 })

/-- The hash of salt `j`: the `j`-th polynomial of `cs`. -/
def hashD (cs : List ZPoly) (j : ℕ) (_ : Unit) : StateM DSt ZPoly := pure (cs.getD j fun _ => 0)

/-! ## Attempts and signers on scripted draws -/

/-- The signing attempt of `C` on `k`, `c` and the draws `scr`. -/
def attD (C : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly × ZPoly) :=
  (signX C (sampD scr C.samp) (storeC C.x C.xn k) k c).run' {}

/-- The centre-aware signing attempt of `C`. -/
def attDc (C : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly × ZPoly) :=
  (signXc C (sampD scr C.samp) (storeC C.x C.xn k) k c).run' {}

/-- The signer of `C` on `k`, salts `0, 1, …` hashed to `cs`, draws `scr`. -/
def msgD (C : Choices) (k : RawKey) (cs : List ZPoly) (scr : List (ℕ × List ℕ)) :
    Option (ℕ × (ZPoly × ZPoly)) :=
  (signMsgX C (sampD scr) saltD (hashD cs) k ()).run' {}

/-- `targetFracX` with array FFTs. -/
def targetFracXA (C : Choices) (k : RawKey) (c : ZPoly) : Array (Cx 64) × Array (Cx 64) :=
  let w := wordFn C.word
  let f0 := ofArr 9 (fftWA C 9 fun i => modqC ((qtX k c).1 i))
  let f1 := ofArr 9 (fftWA C 9 fun i => modqC ((qtX k c).2 i))
  (toArr 9 fun o => (divqX C.x.rm C.qinv (f0 o)).wr w,
    toArr 9 fun o => (divqX C.x.rm C.qinv (f1 o)).wr w)

theorem ofArr_targetFracXA (C : Choices) (k : RawKey) (c : ZPoly) :
    ofArr 9 (targetFracXA C k c).1 = (targetFracX C k c).1 ∧
      ofArr 9 (targetFracXA C k c).2 = (targetFracX C k c).2 := by
  simp only [targetFracXA, targetFracX, ofArr_fftWA, ofArr_toArr, memo_eq, and_self]

/-- `signXc` with array arithmetic. -/
def signXcA (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 9) (k : RawKey) (c : ZPoly) : m (Option (ZPoly × ZPoly)) :=
  match C.samp.centre with
  | .plain => signXA C samp T k c
  | .fractional =>
    if ∀ i, |c i| < 12289 then
      let tf := targetFracXA C k c
      (fun r => r.map fun s => (fun i => (tIntX k c).1 i + s.z0 i,
        fun i => (tIntX k c).2 i + s.z1 i)) <$>
        ffsXA C samp T (ofArr 9 tf.1) (ofArr 9 tf.2)
    else pure none

theorem signXcA_eq (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 9) (k : RawKey) (c : ZPoly) : signXcA C samp T k c = signXc C samp T k c := by
  unfold signXcA signXc
  cases C.samp.centre
  · simp only [signXA_eq]
  · simp only [ffsXA_eq, (ofArr_targetFracXA C k c).1, (ofArr_targetFracXA C k c).2]

/-- `tabEqB` on the array tables. -/
def tabEqBA (rc1 rc2 : RMode) (f : ℕ) : Bool :=
  (List.range 9).all fun L =>
    let t1 := ofArr L (twBA rc1 f L)
    let t2 := ofArr L (twBA rc2 f L)
    let s1 := ofArr L (twsBA rc1 f L)
    let s2 := ofArr L (twsBA rc2 f L)
    allOut L fun o => decide ((t1 o).c = (t2 o).c) && decide ((s1 o).c = (s2 o).c)

theorem tabEqBA_eq (rc1 rc2 : RMode) (f : ℕ) : tabEqBA rc1 rc2 f = tabEqB rc1 rc2 f := by
  simp only [tabEqBA, tabEqB, ofArr_twBA, ofArr_twsBA]

def attDA (C : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly × ZPoly) :=
  (signXA C (sampD scr C.samp) (storeCA C k) k c).run' {}

theorem attDA_eq (C : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) :
    attDA C k c scr = attD C k c scr := by
  rw [attDA, attD, signXA_eq, storeCA_eq]

def attDcA (C : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) :
    Option (ZPoly × ZPoly) :=
  (signXcA C (sampD scr C.samp) (storeCA C k) k c).run' {}

theorem attDcA_eq (C : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) :
    attDcA C k c scr = attDc C k c scr := by
  rw [attDcA, attDc, signXcA_eq, storeCA_eq]

def msgDA (C : Choices) (k : RawKey) (cs : List ZPoly) (scr : List (ℕ × List ℕ)) :
    Option (ℕ × (ZPoly × ZPoly)) :=
  (signLoopX C.salt saltD (hashD cs) (signXA C (sampD scr C.samp) (storeCA C k) k) (accX C k) ()
    C.cap).run' {}

theorem msgDA_eq (C : Choices) (k : RawKey) (cs : List ZPoly) (scr : List (ℕ × List ℕ)) :
    msgDA C k cs scr = msgD C k cs scr := by
  have e : signXA C (sampD scr C.samp) (storeCA C k) k =
      signX C (sampD scr C.samp) (storeC C.x C.xn k) k :=
    funext fun c => by rw [signXA_eq, storeCA_eq]
  rw [msgDA, msgD, e]
  rfl

/-! ## Search (executable) -/

/-- The coefficients of an output, for comparison. -/
def zl (z : Option (ZPoly × ZPoly)) : Option (List ℤ × List ℤ) :=
  z.map fun p => ((List.finRange (2 ^ 9)).map p.1, (List.finRange (2 ^ 9)).map p.2)

/-- The first position where two lists differ. -/
def firstDiffL {α : Type} [DecidableEq α] (a b : List α) : Option ℕ :=
  (List.range (max a.length b.length)).find? fun j => a[j]? ≠ b[j]?

/-- The queries `(σ̄, t̄)` of the centre-aware attempt on policy draws. -/
def queriesA (C : Choices) (k : RawKey) (c : ZPoly) : Array (Fx 64 × Fx 64) :=
  ((signXcA C (sampD [] C.samp) (storeCA C k) k c).run {}).2.log

/-- A 72-bit draw giving `z0` under the 72-bit table (`2⁷² - 1` for `z0 = 0`). -/
def uFor (z0 : ℕ) : ℕ := if z0 = 0 then 2 ^ 72 - 1 else rcdt72.getD (z0 - 1) 1 - 1

/-- The eight bytes of `v`, most significant first (BerExp's order). -/
def bytesBE (v : ℕ) : List ℕ := (List.range 8).reverse.map fun i => v / 2 ^ (8 * i) % 256

/-- `2⁶⁴·Pr[accept]` of the candidate `(u, c)` at the query `(σ̄, t̄)` under `S`. -/
def candAcc (S : SampChoices) (q : Fx 64 × Fx 64) (u c : ℕ) : ℕ :=
  let P := falcon512S
  let r := q.2.toRat - q.2.toInt .floor
  accW P S.shiftRej (xOf P q.1.toRat r (z0Of (P.tab S.base) u c) (c % 2 = 1)) (P.σmin / q.1.toRat)

/-- A script for one call on which `S1` at `q1` and `S2` at `q2` decide differently: a candidate
`(u, c)` with `z ≠ 0` (`z0 ≤ 5`) whose acceptance weights differ, then the smaller weight's
bytes (rejected by the smaller weight, accepted by the larger). -/
def flipScript (S1 S2 : SampChoices) (q1 q2 : Fx 64 × Fx 64) : Option (List ℕ) :=
  let cands :=
    (uFor 0, 1) :: (List.range' 1 5).flatMap fun z0 => [(uFor z0, 1), (uFor z0, 0)]
  cands.findSome? fun (u, c) =>
    let a1 := candAcc S1 q1 u c
    let a2 := candAcc S2 q2 u c
    if a1 ≠ a2 then some ([u, c] ++ bytesBE (min a1 a2)) else none

/-- The first call where the queries of `C1`, `C2` differ and either their floors differ (policy
draws already give different outputs; not used across centre handlings, whose floors differ by
`t_int`) or `flipScript` finds a script. -/
def findWit (C1 C2 : Choices) (k : RawKey) (c : ZPoly) : Option (ℕ × Option (List ℕ)) :=
  let a := (queriesA C1 k c).toList
  let b := (queriesA C2 k c).toList
  let frac := decide (C1.samp.centre ≠ C2.samp.centre)
  (List.range (min a.length b.length)).findSome? fun j =>
    match a[j]?, b[j]? with
    | some q1, some q2 =>
      if q1 = q2 then none
      else if !frac && decide (q1.2.toInt .floor ≠ q2.2.toInt .floor) then some (j, none)
      else (flipScript C1.samp C2.samp q1 q2).map fun l => (j, some l)
    | _, _ => none

/-! ## Witnesses

Attempt-level witnesses `wit_*` (other than `wit_salt`, `wit_cap`) state that the attempt
outputs `z` (`signX`, before the norm check) of two choice points differ on a KAT key, its hashed
message and scripted draws; signer-level witnesses (`wit_salt`, `wit_cap`, `wit_*_sig`,
`wit_word_mf_none`) state it for the signer outputs `signMsgX` (a signature or `none`). Each holds
under the premise that a `Bool` (`wit*B`) is `true`; the implication is proved (`attD_ne`,
`attDc_ne`, `msgD_ne`: the `Bool` decides an inequality of the array versions, `zl`, `zlm`).
The premises are **not proved**: each `wit*B` evaluates to `true` by `#eval` (the compiler's code,
run by Lean's interpreter; `test/ExecEquivEval.lean`), not by the
kernel: `decide +kernel` did not finish decoding one key coefficient in 229 s. The sampler
witnesses `samp_base`, `samp_shift` are checked by the kernel. -/

/-- A signer output, for comparison. -/
def zlm (r : Option (ℕ × (ZPoly × ZPoly))) : Option (ℕ × Option (List ℤ × List ℤ)) :=
  r.map fun p => (p.1, zl (some p.2))

theorem attD_ne {C1 C2 : Choices} {k : RawKey} {c : ZPoly} {s1 s2 : List (ℕ × List ℕ)}
    (h : zl (attDA C1 k c s1) ≠ zl (attDA C2 k c s2)) : attD C1 k c s1 ≠ attD C2 k c s2 := by
  rw [← attDA_eq, ← attDA_eq]
  exact fun e => h (congrArg zl e)

theorem attDc_ne {C1 C2 : Choices} {k : RawKey} {c : ZPoly} {s1 s2 : List (ℕ × List ℕ)}
    (h : zl (attDcA C1 k c s1) ≠ zl (attDcA C2 k c s2)) : attDc C1 k c s1 ≠ attDc C2 k c s2 := by
  rw [← attDcA_eq, ← attDcA_eq]
  exact fun e => h (congrArg zl e)

theorem msgD_ne {C1 C2 : Choices} {k : RawKey} {cs : List ZPoly} {s1 s2 : List (ℕ × List ℕ)}
    (h : zlm (msgDA C1 k cs s1) ≠ zlm (msgDA C2 k cs s2)) : msgD C1 k cs s1 ≠ msgD C2 k cs s2 := by
  rw [← msgDA_eq, ← msgDA_eq]
  exact fun e => h (congrArg zlm e)

/-- The attempts of `C1`, `C2` on `k`, `c`, draws `scr` differ (array versions). -/
def attNeB (C1 C2 : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) : Bool :=
  decide (zl (attDA C1 k c scr) ≠ zl (attDA C2 k c scr))

/-- The centre-aware attempts of `C1`, `C2` differ (array versions). -/
def attcNeB (C1 C2 : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) : Bool :=
  decide (zl (attDcA C1 k c scr) ≠ zl (attDcA C2 k c scr))

/-- The signers of `C1`, `C2` differ (array versions). -/
def msgNeB (C1 C2 : Choices) (k : RawKey) (cs : List ZPoly) (scr : List (ℕ × List ℕ)) : Bool :=
  decide (zlm (msgDA C1 k cs scr) ≠ zlm (msgDA C2 k cs scr))

theorem attD_ne_of {C1 C2 : Choices} {k : RawKey} {c : ZPoly} {scr : List (ℕ × List ℕ)}
    (h : attNeB C1 C2 k c scr = true) : attD C1 k c scr ≠ attD C2 k c scr :=
  attD_ne (of_decide_eq_true h)

theorem attDc_ne_of {C1 C2 : Choices} {k : RawKey} {c : ZPoly} {scr : List (ℕ × List ℕ)}
    (h : attcNeB C1 C2 k c scr = true) : attDc C1 k c scr ≠ attDc C2 k c scr :=
  attDc_ne (of_decide_eq_true h)

theorem msgD_ne_of {C1 C2 : Choices} {k : RawKey} {cs : List ZPoly} {scr : List (ℕ × List ℕ)}
    (h : msgNeB C1 C2 k cs scr = true) : msgD C1 k cs scr ≠ msgD C2 k cs scr :=
  msgD_ne (of_decide_eq_true h)

/-- Base point with the stored-constant and operation roundings `rc`, `rm`. -/
def cR (rm rc : RMode) : Choices := { cW with x := { cW.x with rm := rm, rc := rc } }

/-- Draws of `wit_target`: call 0 scripted. -/
def scrTarget : List (ℕ × List ℕ) :=
  [(0, [3024686241123004913665, 0, 142, 67, 230, 149, 109, 205, 151, 65])]

/-- Draws of `wit_dm`, `wit_rm_floor`, `wit_rc_floor`: call 0 scripted. -/
def scrA : List (ℕ × List ℕ) := [(0, [2 ^ 72 - 1, 1, 182, 166, 81, 65, 87, 49, 76, 195])]

/-- Draws of `wit_root`: call 0 scripted. -/
def scrRoot : List (ℕ × List ℕ) :=
  [(0, [3024686241123004913665, 1, 158, 199, 109, 157, 144, 65, 106, 49])]

/-- Draws of `wit_rm_up`: call 4 scripted. -/
def scrUp : List (ℕ × List ℕ) :=
  [(4,[636254429462080897534, 1, 87, 168, 232, 124, 3, 31, 254, 31])]

/-- Draws of `wit_rm_away`: call 5 scripted. -/
def scrAway : List (ℕ × List ℕ) :=
  [(5, [1564742784480091954049, 0, 88, 101, 60, 87, 240, 101, 237, 101])]

/-- Draws of `wit_qinv`: call 0 scripted. -/
def scrQinv : List (ℕ × List ℕ) := [(0, [2 ^ 72 - 1, 1, 182, 166, 81, 65, 87, 49, 75, 137])]

/-- Draws of `wit_centre`: call 0 scripted. -/
def scrCentre : List (ℕ × List ℕ) := [(0, [2 ^ 72 - 1, 1, 182, 166, 81, 65, 87, 49, 76, 183])]

/-- Every call of the first attempt draws the candidate `z0 = 5` (rejected by the norm bound),
later calls the policy. -/
def scrRej : List (ℕ × List ℕ) := (List.range 1024).map fun j => (j, [uFor 5, j % 2])

/-- Multiply-first at 32.64 and at 64.64. -/
def cMF32 : Choices := { cW with target := .multiplyFirst, word := some 32 }
def cMF64 : Choices := { cW with target := .multiplyFirst, word := some 64 }

def witWordMfB : Bool := attNeB cMF32 cMF64 key70 c70 []
def witTargetB : Bool := attNeB cW { cW with target := .multiplyFirst } key0 c0 scrTarget
def witDmB : Bool := attNeB cW { cW with x := { cW.x with dm := .invMul } } key0 c0 scrA
def witRootB : Bool := attNeB cW { cW with x := { cW.x with root := .ntru } } key0 c0 scrRoot
def witRmUpB : Bool := attNeB cW (cR .halfUp .halfEven) key0 c0 scrUp
def witRmAwayB : Bool := attNeB (cR .halfUp .halfEven) (cR .halfAway .halfEven) key0 c0 scrAway
def witRmFloorB : Bool := attNeB cW (cR .floor .halfEven) key0 c0 scrA
def witRcFloorB : Bool := attNeB cW (cR .halfEven .floor) key0 c0 scrA
def witQinvB : Bool := attNeB cW { cW with qinv := .w64 } key0 c0 scrQinv
def witCentreB : Bool :=
  attcNeB cW { cW with samp := { cW.samp with centre := .fractional } } key0 c0 scrCentre
def witSaltB : Bool := msgNeB cW { cW with salt := .perAttempt } key0 [c0, c70] scrRej
def witCapB : Bool := msgNeB { cW with cap := 1 } cW key0 [c0, c70] scrRej

/-- **Attempts, 32.64 ≠ 64.64, multiply-first**: attempt outputs `z` (before the norm check) on
KAT entry 70, policy draws (first coefficient `-201` vs `-202`), if `witWordMfB` (true by `#eval`,
not proved). -/
theorem wit_word_mf (h : witWordMfB = true) :
    attD cMF32 key70 c70 [] ≠ attD cMF64 key70 c70 [] :=
  attD_ne_of h

/-- **Attempts, scale-first ≠ multiply-first**: attempt outputs `z` (before the norm check) on
entry 0, one scripted call (`-77` vs `-75`), if `witTargetB` (true by `#eval`, not proved). -/
theorem wit_target (h : witTargetB = true) :
    attD cW key0 c0 scrTarget ≠ attD { cW with target := .multiplyFirst } key0 c0 scrTarget :=
  attD_ne_of h

/-- **Attempts, `y/x` ≠ `1/x·y`**: attempt outputs `z` (before the norm check) on entry 0,
`xn = 0` (`-75` vs `-76`), if `witDmB` (true by `#eval`, not proved). -/
theorem wit_dm (h : witDmB = true) :
    attD cW key0 c0 scrA ≠ attD { cW with x := { cW.x with dm := .invMul } } key0 c0 scrA :=
  attD_ne_of h

/-- **Attempts, root plain ≠ NTRU**: attempt outputs `z` (before the norm check) on entry 0,
`xn = 0` (second coefficient `-4` vs `-5`), if `witRootB` (true by `#eval`, not proved). -/
theorem wit_root (h : witRootB = true) :
    attD cW key0 c0 scrRoot ≠ attD { cW with x := { cW.x with root := .ntru } } key0 c0 scrRoot :=
  attD_ne_of h

/-- **Attempts, operation rounding ties to even ≠ half up**: attempt outputs `z` (before the
norm check) on entry 0, call 4 (`-75` vs `-81`), if `witRmUpB` (true by `#eval`, not proved). -/
theorem wit_rm_up (h : witRmUpB = true) :
    attD cW key0 c0 scrUp ≠ attD (cR .halfUp .halfEven) key0 c0 scrUp :=
  attD_ne_of h

/-- **Attempts, operation rounding half up ≠ half away**: attempt outputs `z` (before the norm
check) on entry 0, call 5 (`-81` vs `-75`), if `witRmAwayB` (true by `#eval`, not proved). -/
theorem wit_rm_away (h : witRmAwayB = true) :
    attD (cR .halfUp .halfEven) key0 c0 scrAway ≠ attD (cR .halfAway .halfEven) key0 c0 scrAway :=
  attD_ne_of h

/-- **Attempts, operation rounding ties to even ≠ floor**: attempt outputs `z` (before the norm
check) on entry 0 (`-75` vs `-76`), if `witRmFloorB` (true by `#eval`, not proved). -/
theorem wit_rm_floor (h : witRmFloorB = true) :
    attD cW key0 c0 scrA ≠ attD (cR .floor .halfEven) key0 c0 scrA :=
  attD_ne_of h

/-- **Attempts, stored constants ties to even ≠ floor**: attempt outputs `z` (before the norm
check) on entry 0 (`-75` vs `-76`), if `witRcFloorB` (true by `#eval`, not proved). -/
theorem wit_rc_floor (h : witRcFloorB = true) :
    attD cW key0 c0 scrA ≠ attD (cR .halfEven .floor) key0 c0 scrA :=
  attD_ne_of h

/-- **Attempts, `1/q` at 77 bits ≠ at 64 bits**: attempt outputs `z` (before the norm check) on
entry 0 (`-76` vs `-75`), if `witQinvB` (true by `#eval`, not proved). -/
theorem wit_qinv (h : witQinvB = true) :
    attD cW key0 c0 scrQinv ≠ attD { cW with qinv := .w64 } key0 c0 scrQinv :=
  attD_ne_of h

/-- **Attempts, plain ≠ fractional centre**: centre-aware attempt outputs (before the norm
check) on entry 0 (`-76` vs `-75`), if `witCentreB` (true by `#eval`, not proved). -/
theorem wit_centre (h : witCentreB = true) :
    attDc cW key0 c0 scrCentre ≠
      attDc { cW with samp := { cW.samp with centre := .fractional } } key0 c0 scrCentre :=
  attDc_ne_of h

/-- **Reused salt ≠ a fresh salt per attempt** after one rejected attempt (entry 0 key; stand-in
hashes `c0`, `c70` for salts `0`, `1`, not the hashes of the salts with a message; outputs salt `0`
vs salt `1`), if `witSaltB` (true by `#eval`, not proved). -/
theorem wit_salt (h : witSaltB = true) :
    msgD cW key0 [c0, c70] scrRej ≠ msgD { cW with salt := .perAttempt } key0 [c0, c70] scrRej :=
  msgD_ne_of h

/-- **Cap 1 ≠ cap 27** (the first attempt is rejected; `none` vs a signature), if `witCapB` (true
by `#eval`, not proved). -/
theorem wit_cap (h : witCapB = true) :
    msgD { cW with cap := 1 } key0 [c0, c70] scrRej ≠ msgD cW key0 [c0, c70] scrRej :=
  msgD_ne_of h

/-! ### Signer level: the same pairs, keys, hashed messages and draws, through `signMsgX`

Reused salt, one hash (`cs = [c]`), cap 27; the outputs are signatures or `none`. -/

def witWordMfSigB : Bool :=
  (msgDA cMF32 key70 [c70] []).isNone && (msgDA cMF64 key70 [c70] []).isSome
def witTargetSigB : Bool :=
  msgNeB cW { cW with target := .multiplyFirst } key0 [c0] scrTarget
def witDmSigB : Bool := msgNeB cW { cW with x := { cW.x with dm := .invMul } } key0 [c0] scrA
def witRootSigB : Bool :=
  msgNeB cW { cW with x := { cW.x with root := .ntru } } key0 [c0] scrRoot
def witRmUpSigB : Bool := msgNeB cW (cR .halfUp .halfEven) key0 [c0] scrUp
def witRmAwaySigB : Bool :=
  msgNeB (cR .halfUp .halfEven) (cR .halfAway .halfEven) key0 [c0] scrAway
def witRmFloorSigB : Bool := msgNeB cW (cR .floor .halfEven) key0 [c0] scrA
def witRcFloorSigB : Bool := msgNeB cW (cR .halfEven .floor) key0 [c0] scrA
def witQinvSigB : Bool := msgNeB cW { cW with qinv := .w64 } key0 [c0] scrQinv

/-- **Multiply-first: 32.64 gives no signature, 64.64 a signature** (KAT entry 70, policy draws:
every attempt of the 32.64 signer is rejected), if `witWordMfSigB` (true by `#eval`, not
proved). -/
theorem wit_word_mf_none (h : witWordMfSigB = true) :
    msgD cMF32 key70 [c70] [] = none ∧ (msgD cMF64 key70 [c70] []).isSome = true := by
  unfold witWordMfSigB at h
  rw [msgDA_eq, msgDA_eq, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h

/-- **32.64 ≠ 64.64 signers, multiply-first** (entry 70, policy draws), if `witWordMfSigB` (true by
`#eval`, not proved). -/
theorem wit_word_mf_sig (h : witWordMfSigB = true) :
    msgD cMF32 key70 [c70] [] ≠ msgD cMF64 key70 [c70] [] := by
  intro e
  have h2 := (wit_word_mf_none h).2
  rw [← e, (wit_word_mf_none h).1] at h2
  exact Bool.false_ne_true h2

/-- **Scale-first ≠ multiply-first signers** (entry 0, `scrTarget`), if `witTargetSigB` (true by
`#eval`, not proved). -/
theorem wit_target_sig (h : witTargetSigB = true) :
    msgD cW key0 [c0] scrTarget ≠ msgD { cW with target := .multiplyFirst } key0 [c0] scrTarget :=
  msgD_ne_of h

/-- **`y/x` ≠ `1/x·y` signers** (entry 0, `xn = 0`, `scrA`), if `witDmSigB` (true by `#eval`, not
proved). -/
theorem wit_dm_sig (h : witDmSigB = true) :
    msgD cW key0 [c0] scrA ≠ msgD { cW with x := { cW.x with dm := .invMul } } key0 [c0] scrA :=
  msgD_ne_of h

/-- **Root plain ≠ NTRU signers** (entry 0, `xn = 0`, `scrRoot`), if `witRootSigB` (true by
`#eval`, not proved). -/
theorem wit_root_sig (h : witRootSigB = true) :
    msgD cW key0 [c0] scrRoot ≠
      msgD { cW with x := { cW.x with root := .ntru } } key0 [c0] scrRoot :=
  msgD_ne_of h

/-- **Ties to even ≠ half up signers** (entry 0, `scrUp`), if `witRmUpSigB` (true by `#eval`, not
proved). -/
theorem wit_rm_up_sig (h : witRmUpSigB = true) :
    msgD cW key0 [c0] scrUp ≠ msgD (cR .halfUp .halfEven) key0 [c0] scrUp :=
  msgD_ne_of h

/-- **Half up ≠ half away signers** (entry 0, `scrAway`), if `witRmAwaySigB` (true by `#eval`,
not proved). -/
theorem wit_rm_away_sig (h : witRmAwaySigB = true) :
    msgD (cR .halfUp .halfEven) key0 [c0] scrAway ≠
      msgD (cR .halfAway .halfEven) key0 [c0] scrAway :=
  msgD_ne_of h

/-- **Ties to even ≠ floor signers** (operation rounding; entry 0, `scrA`), if `witRmFloorSigB`
(true by `#eval`, not proved). -/
theorem wit_rm_floor_sig (h : witRmFloorSigB = true) :
    msgD cW key0 [c0] scrA ≠ msgD (cR .floor .halfEven) key0 [c0] scrA :=
  msgD_ne_of h

/-- **Ties to even ≠ floor signers** (stored constants; entry 0, `scrA`), if `witRcFloorSigB`
(true by `#eval`, not proved). -/
theorem wit_rc_floor_sig (h : witRcFloorSigB = true) :
    msgD cW key0 [c0] scrA ≠ msgD (cR .halfEven .floor) key0 [c0] scrA :=
  msgD_ne_of h

/-- **`1/q` at 77 bits ≠ at 64 bits signers** (entry 0, `scrQinv`), if `witQinvSigB` (true by
`#eval`, not proved). -/
theorem wit_qinv_sig (h : witQinvSigB = true) :
    msgD cW key0 [c0] scrQinv ≠ msgD { cW with qinv := .w64 } key0 [c0] scrQinv :=
  msgD_ne_of h

/-- **Base table 72 bits ≠ 79 bits**, one SamplerZ call (`σ̄ = ⌊σmax·2⁶⁴⌋/2⁶⁴`, `t̄ = 0`, draws
`u = 198`, sign byte `12`, zero bytes: `z0 = 16` vs `17`, outputs `-16` vs `-17`). It depends on
our `rcdt79` and on our 79-bit draw (`u72·2⁷` plus the 7 high bits of the sign byte, `SamplerZ`).
Kernel-checked. -/
theorem samp_base :
    Id.run ((sampD [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
      ⟨33582297586188238716⟩ ⟨0⟩).run' {}) ≠
    Id.run ((sampD [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b79⟩
      ⟨33582297586188238716⟩ ⟨0⟩).run' {}) := by
  decide +kernel

/-- **Saturated shift ≠ shift rejection**, one SamplerZ call (`σ̄ = ⌈σmin·2⁶⁴⌉/2⁶⁴`, `t̄ = 0`,
draws `u = 0`, sign byte `0`, zero bytes: candidate `z = -18`, shift `72`, saturated weight `1`;
outputs `-18` vs `0`, the policy candidate after the rejection). Kernel-checked. -/
theorem samp_shift :
    Id.run ((sampD [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
      ⟨23571871177321116846⟩ ⟨0⟩).run' {}) ≠
    Id.run ((sampD [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, true, .b72⟩
      ⟨23571871177321116846⟩ ⟨0⟩).run' {}) := by
  decide +kernel

end FalconPrecision.Exec.Witness
