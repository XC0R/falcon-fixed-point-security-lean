/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignRange
public import FalconPrecision.Exec.SamplerZ

/-! # Equivalences of design-space points of the executable signer

NIST's plan (Perlner, pqc-forum 2026-09-28 and 2026-10-15) allows implementation methods that
produce the same outputs as the specified one "on the full range of possible inputs". For pairs
of `Choices` this file proves such equalities on every input under stated conditions.

* `signX_congr`: the signing attempt reads only `rm`, `word`, `target`, `qinv`, `rchk` and the
  computed tables at levels `≤ 8` (`SameAttempt`); `signMsgX_congr`: the signer reads the attempt,
  the norm bounds, the salt mode and the cap.
* `signMsgX_word`, `signMsgX_32_64`: `signX_word` and `sign32_eq_sign64` (`Exec.SignRange`)
  lifted to the signer `signMsgX` (restart loop, salt, norm check; words reduce the attempt only,
  key expansion `storeC` is unbounded in both), for every sampler clamped to `⌊t̄⌋ ± W`;
  `clampS_samplerZ`: SamplerZ is its own clamp at `W = 19`; `signMsgZ_word`, `signMsgZ_32_64`: the
  signer with the executable SamplerZ on any random-bit source, unclamped.
* Stored constants: `tabEqB` decides that two roundings give the same tables; `signX_rc`, and
  with `expandC_rc_congr` (key expansion reads `rc` only through the tables and `σ`),
  `signMsgX_rc` for every key.
* Stored trees: `CTree.eqB` decides equality of stored trees; `signMsgX_store`: choices that differ
  only in key expansion (`dm`, `root`) sign identically on every key whose stored trees are equal.
* Restart loop: `loopR_add` (a cap `N + j` is the cap `N` followed by `j` more attempts when the
  first `N` fail), `signMsgX_cap_add`; `signLoopX_one`: reused and per-attempt salts are equal
  with one attempt (cap 1).
* Fractional centre (ePrint 2026/2902 Alg. 17, p. 622; Alg. 10 l. 5-7, 25-30, p. 28):
  `targetFracX`, `signXc`.

Not proved here: equalities for pairs that differ (witnesses: `Exec.SignWitness`); key checks for
any key; the theorems for samplers outside `⌊t̄⌋ ± W` other than SamplerZ; key expansion `storeC`
on words (it runs in unbounded `Int` in both signers: words reduce only the attempt); Compress and
its restart (spec Alg. 10 l. 10-11), which `signMsgX` does not model. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFSamp

/-! ## The signing attempt reads few fields -/

/-- Two choice points whose signing attempts read the same values: the same operation rounding,
words, target order, `1/q`, range checks, and the same computed tables at levels `≤ 8`. -/
structure SameAttempt (C1 C2 : Choices) : Prop where
  rm : C1.x.rm = C2.x.rm
  word : C1.word = C2.word
  target : C1.target = C2.target
  qinv : C1.qinv = C2.qinv
  rchk : C1.rchk = C2.rchk
  tw : ∀ L ≤ 8, ∀ o : Out L, (twB C1.x.rc 64 L o).c = (twB C2.x.rc 64 L o).c
  tws : ∀ L ≤ 8, ∀ o : Out L, (twsB C1.x.rc 64 L o).c = (twsB C2.x.rc 64 L o).c

namespace SameAttempt

variable {C1 C2 : Choices} (h : SameAttempt C1 C2)
include h

theorem fftW_eq : ∀ L, L ≤ 9 → ∀ a : Fin (2 ^ L) → ℤ, fftW C1 L a = fftW C2 L a
  | 0, _, a => by simp only [fftW, h.word]
  | L + 1, hL, a => by
    simp only [fftW, fftW_eq L (by omega), h.word, h.rm, h.tw L (by omega)]

theorem splitW_eq {L : ℕ} (hL : L ≤ 8) (t : Out (L + 1) → Cx 64) :
    splitW C1 L t = splitW C2 L t := by
  simp only [splitW, h.word, h.rm, h.tws L hL]

theorem mergeW_eq {L : ℕ} (hL : L ≤ 8) (c0 c1 : Out L → Cx 64) :
    mergeW C1 L c0 c1 = mergeW C2 L c0 c1 := by
  simp only [mergeW, h.word, h.rm, h.tw L hL]

theorem updW_eq {L : ℕ} (t0 t1 z ℓ : Out L → Cx 64) : updW C1 t0 t1 z ℓ = updW C2 t0 t1 z ℓ := by
  simp only [updW, h.word, h.rm]

theorem ffsX_eq {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) :
    ∀ {L : ℕ} (T : CTree 64 L), L ≤ 9 → ∀ t0 t1 : Out L → Cx 64,
      ffsX C1 samp T t0 t1 = ffsX C2 samp T t0 t1
  | _, .leaf _, _, _, _ => by simp only [ffsX]
  | _, @CTree.node _ L ℓ T0 T1, hL, t0, t1 => by
    simp only [ffsX, h.rchk, h.splitW_eq (L := L) (by omega), h.mergeW_eq (L := L) (by omega),
      h.updW_eq, ffsX_eq samp T0 (by omega), ffsX_eq samp T1 (by omega)]

theorem targetX_eq (f F c : ZPoly) : targetX C1 f F c = targetX C2 f F c := by
  have e := h.fftW_eq 9 le_rfl
  unfold targetX
  rw [e c, e f, e F, h.word, h.rm, h.qinv, h.target]

end SameAttempt

theorem SameAttempt.of_eq (C1 C2 : Choices) (hrm : C1.x.rm = C2.x.rm) (hw : C1.word = C2.word)
    (ht : C1.target = C2.target) (hq : C1.qinv = C2.qinv) (hr : C1.rchk = C2.rchk)
    (hrc : C1.x.rc = C2.x.rc) : SameAttempt C1 C2 :=
  ⟨hrm, hw, ht, hq, hr, fun _ _ _ => by rw [hrc], fun _ _ _ => by rw [hrc]⟩

/-- **The signing attempt depends only on `SameAttempt` data.** -/
theorem signX_congr {C1 C2 : Choices} (h : SameAttempt C1 C2) {m : Type → Type*} [Monad m]
    (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9) (k : RawKey) (c : ZPoly) :
    signX C1 samp T k c = signX C2 samp T k c := by
  unfold signX
  rw [h.targetX_eq k.f k.F c, h.ffsX_eq samp T le_rfl]

theorem accX_congr {C1 C2 : Choices} (hb : C1.beta2 = C2.beta2) (hi : C1.infB = C2.infB)
    (k : RawKey) : accX C1 k = accX C2 k := by
  have e : normOk C1 = normOk C2 := by
    funext s
    unfold normOk
    rw [hb, hi]
  funext c y
  unfold accX
  rw [e]

/-- **The signer depends only on its attempts, norm bounds, salt mode and cap.** -/
theorem signMsgX_congr {C1 C2 : Choices} {m : Type → Type*} [Monad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (k : RawKey) (msg : M) (hs : C1.salt = C2.salt) (hcap : C1.cap = C2.cap)
    (hacc : accX C1 k = accX C2 k)
    (hatt : signX C1 (sampF C1.samp) (storeC C1.x C1.xn k) k =
      signX C2 (sampF C2.samp) (storeC C2.x C2.xn k) k) :
    signMsgX C1 sampF salt hash k msg = signMsgX C2 sampF salt hash k msg := by
  simp only [signMsgX, hs, hcap, hacc, hatt]

/-! ## Words: the signer -/

/-- **No reduction changes the signer's output**: `signX_word` (`Exec.SignRange`) for the signer
`signMsgX` (restart loop, salt, norm check; key expansion unbounded in both), every sampler family
clamped to `⌊t̄⌋ ± W`, every salt source, hash and message, every lawful monad, on a key passing
`check` and `checkRange C i W`. -/
theorem signMsgX_word (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi : 1 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey) (hc : check C.x C.xn δq k = true) (hk : checkRange C i W k = true)
    {m : Type → Type*} [Monad m] [LawfulMonad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (msg : M) :
    signMsgX { C with word := some i } (fun s => clampS W (sampF s)) salt hash k msg =
      signMsgX { C with word := none } (fun s => clampS W (sampF s)) salt hash k msg :=
  signMsgX_congr _ salt hash k msg rfl rfl (accX_congr rfl rfl k)
    (funext fun c => signX_word C δq i W hi hi64 k hc hk (sampF C.samp) c)

/-- **32.64 = 64.64 for the signer `signMsgX`**: on a key passing `check` and `checkRange` at
`i = 32` and `i = 64`, with every sampler family clamped to `⌊t̄⌋ ± W`, the signers whose attempts
run on 96-bit and 128-bit words give the same output on every message, salt source and hash. Key
expansion `storeC` runs in unbounded `Int` in both; Compress and its restart are not modelled. -/
theorem signMsgX_32_64 (C : Choices) (δq : ℕ → ℚ) (W : ℕ) (k : RawKey)
    (hc : check C.x C.xn δq k = true) (h32 : checkRange C 32 W k = true)
    (h64 : checkRange C 64 W k = true) {m : Type → Type*} [Monad m] [LawfulMonad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (msg : M) :
    signMsgX { C with word := some 32 } (fun s => clampS W (sampF s)) salt hash k msg =
      signMsgX { C with word := some 64 } (fun s => clampS W (sampF s)) salt hash k msg :=
  (signMsgX_word C δq 32 W (by norm_num) (by norm_num) k hc h32 sampF salt hash msg).trans
    (signMsgX_word C δq 64 W (by norm_num) le_rfl k hc h64 sampF salt hash msg).symm

/-! ## SamplerZ is its own clamp at `W = 19` -/

theorem clampZ_of_abs_le {b z : ℤ} {W : ℕ} (h : |z - b| ≤ W) : clampZ b W z = z := by
  rw [abs_le] at h
  unfold clampZ
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

theorem z0Of_le (S : SampChoices) (u c : ℕ) : z0Of (falcon512S.tab S.base) u c ≤ 18 := by
  unfold z0Of baseZ
  cases S.base
  · exact (List.length_filter_le _ _).trans (by decide)
  · exact (List.length_filter_le _ _).trans (by decide)

theorem abs_zOf_le {z0 : ℕ} (h : z0 ≤ 18) (b : Bool) : |zOf z0 b| ≤ 19 := by
  have h' : (z0 : ℤ) ≤ 18 := by exact_mod_cast h
  unfold zOf
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

theorem clamp_samplerLoop {m : Type → Type*} [Monad m] [LawfulMonad m] (S : SampChoices)
    (ub : ℕ → m ℕ) (σ r : ℚ) (s : ℤ) :
    ∀ n, clampZ s 19 <$> samplerLoop falcon512S S ub σ r s n = samplerLoop falcon512S S ub σ r s n
  | 0 => by simp [samplerLoop, clampZ_of_abs_le]
  | n + 1 => by
    simp only [samplerLoop, map_bind]
    refine congrArg (ub 72 >>= ·) (funext fun u => congrArg (ub 8 >>= ·) (funext fun c =>
      congrArg (_ >>= ·) (funext fun a => ?_)))
    split
    · rw [map_pure, clampZ_of_abs_le (by
        rw [add_sub_cancel_left]; exact_mod_cast abs_zOf_le (z0Of_le S u c) _)]
    · exact clamp_samplerLoop S ub σ r s n

/-- **SamplerZ answers within `19` of `⌊t̄⌋`** (`z = b + (2b - 1)z0`, `z0 ≤ 18`; the output `⌊t̄⌋`
after `fuel` rejections), so clamping it at `W = 19` changes nothing. -/
theorem clampS_samplerZ {m : Type → Type*} [Monad m] [LawfulMonad m] (S : SampChoices)
    (ub : ℕ → m ℕ) : clampS 19 (samplerZ falcon512S S ub) = samplerZ falcon512S S ub := by
  funext σ t
  exact clamp_samplerLoop S ub _ _ _ _

/-- **The signer with the executable SamplerZ on words**: on a key passing `check` and
`checkRange C i 19`, for every random-bit source `ub` in every lawful monad, the signer whose
attempts run on `(i + 64)`-bit words is the unbounded one (key expansion unbounded in both). -/
theorem signMsgZ_word (C : Choices) (δq : ℕ → ℚ) (i : ℕ) (hi : 1 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey) (hc : check C.x C.xn δq k = true) (hk : checkRange C i 19 k = true)
    {m : Type → Type*} [Monad m] [LawfulMonad m] {S M : Type} (ub : ℕ → m ℕ) (salt : m S)
    (hash : S → M → m ZPoly) (msg : M) :
    signMsgX { C with word := some i } (fun s => samplerZ falcon512S s ub) salt hash k msg =
      signMsgX { C with word := none } (fun s => samplerZ falcon512S s ub) salt hash k msg := by
  have e : (fun s => samplerZ falcon512S s ub) = fun s => clampS 19 (samplerZ falcon512S s ub) :=
    funext fun s => (clampS_samplerZ s ub).symm
  rw [e]
  exact signMsgX_word C δq i 19 hi hi64 k hc hk _ salt hash msg

/-- **32.64 = 64.64 for the signer with the executable SamplerZ**: on a key passing `check` and
`checkRange` at `i = 32` and `i = 64` (`W = 19`), bit-identical outputs on every message, salt
source, hash and random-bit source. -/
theorem signMsgZ_32_64 (C : Choices) (δq : ℕ → ℚ) (k : RawKey)
    (hc : check C.x C.xn δq k = true) (h32 : checkRange C 32 19 k = true)
    (h64 : checkRange C 64 19 k = true) {m : Type → Type*} [Monad m] [LawfulMonad m] {S M : Type}
    (ub : ℕ → m ℕ) (salt : m S) (hash : S → M → m ZPoly) (msg : M) :
    signMsgX { C with word := some 32 } (fun s => samplerZ falcon512S s ub) salt hash k msg =
      signMsgX { C with word := some 64 } (fun s => samplerZ falcon512S s ub) salt hash k msg :=
  (signMsgZ_word C δq 32 (by norm_num) (by norm_num) k hc h32 ub salt hash msg).trans
    (signMsgZ_word C δq 64 (by norm_num) le_rfl k hc h64 ub salt hash msg).symm

/-! ## Stored constants -/

/-- The tables `ζ`, `ζ̄/2` at levels `≤ 8` and `f` fraction bits are the same under `rc1`, `rc2`. -/
def tabEqB (rc1 rc2 : RMode) (f : ℕ) : Bool :=
  (List.range 9).all fun L =>
    let t1 := twB rc1 f L
    let t2 := twB rc2 f L
    let s1 := twsB rc1 f L
    let s2 := twsB rc2 f L
    allOut L fun o => decide ((t1 o).c = (t2 o).c) && decide ((s1 o).c = (s2 o).c)

theorem tabEq_of_tabEqB {rc1 rc2 : RMode} {f : ℕ} (h : tabEqB rc1 rc2 f = true) {L : ℕ}
    (hL : L ≤ 8) (o : Out L) :
    (twB rc1 f L o).c = (twB rc2 f L o).c ∧ (twsB rc1 f L o).c = (twsB rc2 f L o).c := by
  have h1 := List.all_eq_true.1 h L (List.mem_range.2 (by omega))
  have h2 := (allOut_iff L _).1 h1 o
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact h2

/-- **Stored-constant rounding, signing attempt**: if the tables at 64 bits agree, the attempts of
`C` and of `C` with stored constants rounded by `rc` are equal on every input. -/
theorem signX_rc (C : Choices) (rc : RMode) (h : tabEqB C.x.rc rc 64 = true) {m : Type → Type*}
    [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9) (k : RawKey) (c : ZPoly) :
    signX C samp T k c = signX { C with x := { C.x with rc := rc } } samp T k c :=
  signX_congr (C1 := C) (C2 := { C with x := { C.x with rc := rc } })
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ hL o => (tabEq_of_tabEqB h hL o).1,
      fun _ hL o => (tabEq_of_tabEqB h hL o).2⟩ samp T k c

theorem fftC_rc_congr (P : XChoices) (rc : RMode) (f : ℕ) (h : tabEqB P.rc rc f = true) :
    ∀ L, L ≤ 9 → ∀ a : Fin (2 ^ L) → ℤ, fftC P f L a = fftC { P with rc := rc } f L a
  | 0, _, _ => rfl
  | L + 1, hL, a => by
    have ht : ∀ o, (twB P.rc f L o).c = (twB rc f L o).c :=
      fun o => (tabEq_of_tabEqB h (by omega) o).1
    simp only [fftC, fftC_rc_congr P rc f h L (by omega), ht]

theorem splitC_rc_congr (P : XChoices) (rc : RMode) (f : ℕ) (h : tabEqB P.rc rc f = true)
    {L : ℕ} (hL : L ≤ 8) (t : Out (L + 1) → Cx f) :
    splitC P f L t = splitC { P with rc := rc } f L t := by
  have hs : ∀ o, (twsB P.rc f L o).c = (twsB rc f L o).c :=
    fun o => (tabEq_of_tabEqB h hL o).2
  simp only [splitC, hs]

theorem ldlC_rc_congr (P : XChoices) (rc : RMode) (f : ℕ) (h : tabEqB P.rc rc f = true)
    (hσ : (Fx.ofRat P.rc σ512q : Fx f) = Fx.ofRat rc σ512q) :
    ∀ L, L ≤ 8 → ∀ g00 g10 g11 : Out L → Cx f,
      ldlC P f L g00 g10 g11 = ldlC { P with rc := rc } f L g00 g10 g11
  | 0, _, _, _, _ => by simp only [ldlC, Cx.leafR, hσ]
  | L + 1, hL, g00, g10, g11 => by
    simp only [ldlC, ldlStepC, d11C, splitC_rc_congr P rc f h (L := L) (by omega),
      ldlC_rc_congr P rc f h hσ L (by omega)]

/-- Key expansion reads `rc` only through the tables at `f` bits and the stored `σ`. -/
theorem expandC_rc_congr (P : XChoices) (rc : RMode) (f : ℕ) (h : tabEqB P.rc rc f = true)
    (hσ : (Fx.ofRat P.rc σ512q : Fx f) = Fx.ofRat rc σ512q) (k : RawKey) :
    expandC P f k = expandC { P with rc := rc } f k := by
  have e1 := fftC_rc_congr P rc f h 9 le_rfl
  have e2 := splitC_rc_congr P rc f h (L := 8) le_rfl
  have e3 := ldlC_rc_congr P rc f h hσ 8 le_rfl
  obtain ⟨rm, rc0, dm, root⟩ := P
  cases root <;> simp only [expandC, gramC, ldlStepC, d11C, e1, e2, e3]

/-- **Stored-constant rounding, the signer**: if the tables agree at `64` and at `64 + xn` bits
and the stored `σ` agrees, `C` and `C` with stored constants rounded by `rc` give the same output
on every key, message, salt source, hash and sampler family. -/
theorem signMsgX_rc (C : Choices) (rc : RMode) (h64 : tabEqB C.x.rc rc 64 = true)
    (hx : tabEqB C.x.rc rc (64 + C.xn) = true)
    (hσ : (Fx.ofRat C.x.rc σ512q : Fx (64 + C.xn)) = Fx.ofRat rc σ512q) {m : Type → Type*}
    [Monad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S)
    (hash : S → M → m ZPoly) (k : RawKey) (msg : M) :
    signMsgX C sampF salt hash k msg =
      signMsgX { C with x := { C.x with rc := rc } } sampF salt hash k msg := by
  refine signMsgX_congr sampF salt hash k msg rfl rfl (accX_congr rfl rfl k) ?_
  have e : storeC C.x C.xn k = storeC { C.x with rc := rc } C.xn k := by
    simp only [storeC]
    rw [expandC_rc_congr C.x rc (64 + C.xn) hx hσ k]
  rw [e]
  funext c
  exact signX_rc C rc h64 _ _ k c

/-! ## Stored trees -/

/-- Equality of stored trees, decided. -/
def CTree.eqB {f : ℕ} : {L : ℕ} → CTree f L → CTree f L → Bool
  | _, .leaf a, .leaf b => decide (a = b)
  | _, .node ℓ T0 T1, .node ℓ' T0' T1' =>
    allOut _ (fun o => decide (ℓ o = ℓ' o)) && eqB T0 T0' && eqB T1 T1'

theorem CTree.eq_of_eqB {f : ℕ} : {L : ℕ} → (T T' : CTree f L) → T.eqB T' = true → T = T'
  | _, .leaf a, .leaf b, h => by
    simp only [CTree.eqB, decide_eq_true_eq] at h
    rw [h]
  | _, .node ℓ T0 T1, .node ℓ' T0' T1', h => by
    simp only [CTree.eqB, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hℓ : ℓ = ℓ' := funext fun o => of_decide_eq_true ((allOut_iff _ _).1 h1 o)
    rw [hℓ, eq_of_eqB T0 T0' h2, eq_of_eqB T1 T1' h3]

/-- **Key expansion choices**: two choice points that differ only in key expansion (`dm`, `root`,
`xn`) give the same signer output on every message, salt source, hash and sampler family for a
key whose stored trees are equal (decided by `CTree.eqB`). -/
theorem signMsgX_store (C : Choices) (P : XChoices) (n : ℕ) (hrm : P.rm = C.x.rm)
    (hrc : P.rc = C.x.rc) (k : RawKey) (hT : (storeC C.x C.xn k).eqB (storeC P n k) = true)
    {m : Type → Type*} [Monad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ)
    (salt : m S) (hash : S → M → m ZPoly) (msg : M) :
    signMsgX C sampF salt hash k msg =
      signMsgX { C with x := P, xn := n } sampF salt hash k msg := by
  refine signMsgX_congr sampF salt hash k msg rfl rfl (accX_congr rfl rfl k) ?_
  rw [CTree.eq_of_eqB _ _ hT]
  funext c
  exact signX_congr (C1 := C) (C2 := { C with x := P, xn := n })
    (SameAttempt.of_eq _ _ hrm.symm rfl rfl rfl rfl hrc.symm) _ _ k c

/-! ## Restart loop and salt -/

/-- **Cap `N + j`**: the first `N` attempts, then, if none is accepted, `j` more. -/
theorem loopR_add {m : Type → Type*} [Monad m] [LawfulMonad m] {γ β : Type} (att : m γ)
    (acc : γ → Option β) (j : ℕ) : ∀ N, loopR att acc (N + j) =
      loopR att acc N >>= fun r => r.elim (loopR att acc j) fun b => pure (some b)
  | 0 => by simp [loopR]
  | N + 1 => by
    rw [Nat.add_right_comm]
    simp only [loopR, bind_assoc]
    refine congrArg (att >>= ·) (funext fun y => ?_)
    cases acc y with
    | some b => simp
    | none => exact loopR_add att acc j N

theorem signMsgX_with_cap (C : Choices) (a : ℕ) {m : Type → Type*} [Monad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (k : RawKey) (msg : M) :
    signMsgX { C with cap := a } sampF salt hash k msg =
      signLoopX C.salt salt hash (signX C (sampF C.samp) (storeC C.x C.xn k) k) (accX C k) msg
        a := by
  have e : signX { C with cap := a } (sampF C.samp) (storeC C.x C.xn k) k =
      signX C (sampF C.samp) (storeC C.x C.xn k) k :=
    funext fun c => signX_congr (C1 := { C with cap := a }) (C2 := C)
      (SameAttempt.of_eq _ _ rfl rfl rfl rfl rfl rfl) _ _ k c
  have ea : accX { C with cap := a } k = accX C k := accX_congr rfl rfl k
  simp only [signMsgX]
  rw [e, ea]

/-- **Restart cap**: with a fresh salt per attempt, the signer capped at `N + j` attempts is the
signer capped at `N`, followed, when it fails, by the signer capped at `j`. -/
theorem signMsgX_cap_add (C : Choices) (hs : C.salt = .perAttempt) {m : Type → Type*} [Monad m]
    [LawfulMonad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S)
    (hash : S → M → m ZPoly) (k : RawKey) (msg : M) (N j : ℕ) :
    signMsgX { C with cap := N + j } sampF salt hash k msg =
      signMsgX { C with cap := N } sampF salt hash k msg >>= fun r =>
        r.elim (signMsgX { C with cap := j } sampF salt hash k msg) fun b => pure (some b) := by
  rw [signMsgX_with_cap, signMsgX_with_cap, signMsgX_with_cap]
  rw [hs]
  simp only [signLoopX]
  exact loopR_add (m := m) _ _ j N

/-- **Salt per attempt or reused, one attempt**: with cap 1 they are equal, in every lawful
monad. -/
theorem signLoopX_one {m : Type → Type*} [Monad m] [LawfulMonad m] {S M β : Type} (salt : m S)
    (hash : S → M → m ZPoly) (att : ZPoly → m (Option (ZPoly × ZPoly)))
    (acc : ZPoly → Option (ZPoly × ZPoly) → Option β) (msg : M) :
    signLoopX .reused salt hash att acc msg 1 = signLoopX .perAttempt salt hash att acc msg 1 := by
  simp only [signLoopX, loopR, map_bind, bind_assoc, bind_map_left]
  refine congrArg (salt >>= ·) (funext fun s => congrArg (hash s msg >>= ·)
    (funext fun c => congrArg (att c >>= ·) (funext fun y => ?_)))
  cases acc c y <;> simp

/-! ## Fractional centre (ePrint 2026/2902 Alg. 17, p. 622) -/

/-- The residue of `x` modulo `q` in `[-q/2, q/2)`. -/
def modqC (x : ℤ) : ℤ := if 2 * (x % 12289) < 12289 then x % 12289 else x % 12289 - 12289

/-- `qt = (-c·F, c·f)` in `ℤ[x]/(x⁵¹² + 1)` (2026/2902 Def. A.13, p. 74). -/
def qtX (k : RawKey) (c : ZPoly) : ZPoly × ZPoly :=
  (fun i => -ncoef c k.F i, fun i => ncoef c k.f i)

/-- The integer part `t_int = (qt - qt_frac)/q` (Alg. 17 l. 5). -/
def tIntX (k : RawKey) (c : ZPoly) : ZPoly × ZPoly :=
  ((fun i => ((qtX k c).1 i - modqC ((qtX k c).1 i)) / 12289),
    fun i => ((qtX k c).2 i - modqC ((qtX k c).2 i)) / 12289)

/-- The fractional centre `FFT(qt_frac) ⊗ 1/q` (Alg. 17 l. 7, 12), each result reduced. -/
def targetFracX (C : Choices) (k : RawKey) (c : ZPoly) : (Out 9 → Cx 64) × (Out 9 → Cx 64) :=
  let w := wordFn C.word
  let f0 := fftW C 9 fun i => modqC ((qtX k c).1 i)
  let f1 := fftW C 9 fun i => modqC ((qtX k c).2 i)
  (memo 9 fun o => (divqX C.x.rm C.qinv (f0 o)).wr w,
    memo 9 fun o => (divqX C.x.rm C.qinv (f1 o)).wr w)

/-- **A signing attempt with the centre handling `C.samp.centre`**: `plain` is `signX`;
`fractional` samples `z'` at the fractional centre and returns `t_int + z'` exactly, unreduced
(2026/2902 Alg. 10 l. 5-7, 25-30, p. 28, reduces the sum mod `q`; the signature does not see that
reduction). -/
def signXc (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 9) (k : RawKey) (c : ZPoly) : m (Option (ZPoly × ZPoly)) :=
  match C.samp.centre with
  | .plain => signX C samp T k c
  | .fractional =>
    if ∀ i, |c i| < 12289 then
      (fun r => r.map fun s => (fun i => (tIntX k c).1 i + s.z0 i,
        fun i => (tIntX k c).2 i + s.z1 i)) <$>
        ffsX C samp T (targetFracX C k c).1 (targetFracX C k c).2
    else pure none

end FalconPrecision.Exec
