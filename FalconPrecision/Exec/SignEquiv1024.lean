/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.SignEquiv
public import FalconPrecision.Exec.SignWordHop1024

/-! # Equivalences of design-space points of the executable signer at Falcon-1024

`Exec.SignEquiv` at `n = 1024` (keys `RawKey 10`, stored trees `CTree 64 10`, leaves at
`σ1024q`), from its statements at every size (`SameAttemptN`, `signX_congrN`, `accX_congrP`,
`signMsgX_congrP`, `tabEqBN`, `signX_rcN`, `expandC_rc_congrP`, `signMsgX_rcP`, `signMsgX_storeP`,
`signMsgX_cap_addP`, `signLoopX_oneP`; `loopR_add` has no size).

* `signX_congr1024`, `signMsgX_congr1024`: the attempt reads `SameAttemptN 10` data (tables at
  levels `≤ 9`), the signer its attempts, norm bounds, salt mode and cap.
* `signMsgX_word1024`, `signMsgX_32_64_1024`: `signX_word1024`, `sign32_eq_sign64_1024`
  (`Exec.SignRange1024`, `27 ≤ i ≤ 64`) lifted to the signer `signMsgX … σ1024q`, for every
  sampler clamped to `⌊t̄⌋ ± W`; `signMsgZ_word1024`, `signMsgZ_32_64_1024`: with the executable
  SamplerZ at `falcon1024S` (`clampS_samplerZ1024`), unclamped.
* `signX_rc1024`, `fftC_rc_congr1024`, `splitC_rc_congr1024`, `ldlC_rc_congr1024`,
  `expandC_rc_congr1024`, `signMsgX_rc1024`: stored-constant rounding, decided by `tabEqBN 10`;
  `signMsgX_store1024`: key-expansion choices on keys with equal stored trees;
  `signMsgX_cap_add1024`: the restart cap. The other restart-loop and salt lemmas are stated at
  every size and need no copy: `loopR_add` (no size), `signMsgX_with_capP`, `signLoopX_oneP`.

Not proved here: equalities for pairs that differ (witnesses: `Exec.SignWitness1024`); that any
key passes `check1024` or `checkRange … σ1024q` (`#eval` evidence only); `i < 27` or `i > 64`;
samplers outside `⌊t̄⌋ ± W` other than SamplerZ; key expansion `storeC` on words (unbounded `Int`
in both signers); Compress and its restart (spec Alg. 10 l. 10-11), which `signMsgX` does not
model. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFSamp

/-- **The signing attempt at Falcon-1024 depends only on `SameAttemptN 10` data.** -/
theorem signX_congr1024 {C1 C2 : Choices} (h : SameAttemptN 10 C1 C2) {m : Type → Type*}
    [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 10) (k : RawKey 10) (c : ZPoly 10) :
    signX C1 samp T k c = signX C2 samp T k c :=
  signX_congrN h samp T le_rfl k c

theorem accX_congr1024 {C1 C2 : Choices} (hb : C1.beta2 = C2.beta2) (hi : C1.infB = C2.infB)
    (k : RawKey 10) : accX C1 k = accX C2 k :=
  accX_congrP hb hi k

/-- **The signer at Falcon-1024 depends only on its attempts, norm bounds, salt mode and cap.** -/
theorem signMsgX_congr1024 {C1 C2 : Choices} {m : Type → Type*} [Monad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m (ZPoly 10))
    (k : RawKey 10) (msg : M) (hs : C1.salt = C2.salt) (hcap : C1.cap = C2.cap)
    (hacc : accX C1 k = accX C2 k)
    (hatt : signX C1 (sampF C1.samp) (storeC C1.x C1.xn k σ1024q) k =
      signX C2 (sampF C2.samp) (storeC C2.x C2.xn k σ1024q) k) :
    signMsgX C1 sampF salt hash k msg σ1024q = signMsgX C2 sampF salt hash k msg σ1024q :=
  signMsgX_congrP sampF salt hash k msg σ1024q hs hcap hacc hatt

/-! ## Words: the signer -/

/-- **No reduction changes the signer's output at Falcon-1024**: `signX_word1024` for the signer
`signMsgX … σ1024q` (restart loop, salt, norm check; key expansion unbounded in both), every
sampler family clamped to `⌊t̄⌋ ± W`, every salt source, hash and message, every lawful monad, on a
key passing `check1024` and `checkRange C i W · σ1024q`, `27 ≤ i ≤ 64`. -/
theorem signMsgX_word1024 (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi27 : 27 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey 10) (hc : check1024 C.x C.xn δq k = true)
    (hk : checkRange C i W k σ1024q = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S)
    (hash : S → M → m (ZPoly 10)) (msg : M) :
    signMsgX { C with word := some i } (fun s => clampS W (sampF s)) salt hash k msg σ1024q =
      signMsgX { C with word := none } (fun s => clampS W (sampF s)) salt hash k msg σ1024q :=
  signMsgX_congr1024 _ salt hash k msg rfl rfl (accX_congr1024 rfl rfl k)
    (funext fun c => signX_word1024 C δq i W hi27 hi64 k hc hk (sampF C.samp) c)

/-- **32.64 = 64.64 for the signer at Falcon-1024**: on a key passing `check1024` and
`checkRange · σ1024q` at `i = 32` and `i = 64`, with every sampler family clamped to `⌊t̄⌋ ± W`,
the signers whose attempts run on 96-bit and 128-bit words give the same output on every message,
salt source and hash. Key expansion `storeC` runs in unbounded `Int` in both; Compress and its
restart are not modelled. -/
theorem signMsgX_32_64_1024 (C : Choices) (δq : ℕ → ℚ) (W : ℕ) (k : RawKey 10)
    (hc : check1024 C.x C.xn δq k = true) (h32 : checkRange C 32 W k σ1024q = true)
    (h64 : checkRange C 64 W k σ1024q = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S)
    (hash : S → M → m (ZPoly 10)) (msg : M) :
    signMsgX { C with word := some 32 } (fun s => clampS W (sampF s)) salt hash k msg σ1024q =
      signMsgX { C with word := some 64 } (fun s => clampS W (sampF s)) salt hash k msg
        σ1024q :=
  (signMsgX_word1024 C δq 32 W (by norm_num) (by norm_num) k hc h32 sampF salt hash msg).trans
    (signMsgX_word1024 C δq 64 W (by norm_num) le_rfl k hc h64 sampF salt hash msg).symm

/-- **The signer with the executable SamplerZ on words at Falcon-1024**: on a key passing
`check1024` and `checkRange C i 19 · σ1024q`, `27 ≤ i ≤ 64`, for every random-bit source `ub` in
every lawful monad, the signer with SamplerZ at `falcon1024S` whose attempts run on
`(i + 64)`-bit words is the unbounded one (key expansion unbounded in both). -/
theorem signMsgZ_word1024 (C : Choices) (δq : ℕ → ℚ) (i : ℕ) (hi27 : 27 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey 10) (hc : check1024 C.x C.xn δq k = true)
    (hk : checkRange C i 19 k σ1024q = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    {S M : Type} (ub : ℕ → m ℕ) (salt : m S) (hash : S → M → m (ZPoly 10)) (msg : M) :
    signMsgX { C with word := some i } (fun s => samplerZ falcon1024S s ub) salt hash k msg
        σ1024q =
      signMsgX { C with word := none } (fun s => samplerZ falcon1024S s ub) salt hash k msg
        σ1024q := by
  have e : (fun s => samplerZ falcon1024S s ub) =
      fun s => clampS 19 (samplerZ falcon1024S s ub) :=
    funext fun s => (clampS_samplerZ1024 s ub).symm
  rw [e]
  exact signMsgX_word1024 C δq i 19 hi27 hi64 k hc hk _ salt hash msg

/-- **32.64 = 64.64 for the signer with the executable SamplerZ at Falcon-1024**: on a key passing
`check1024` and `checkRange · σ1024q` at `i = 32` and `i = 64` (`W = 19`), bit-identical outputs
on every message, salt source, hash and random-bit source. -/
theorem signMsgZ_32_64_1024 (C : Choices) (δq : ℕ → ℚ) (k : RawKey 10)
    (hc : check1024 C.x C.xn δq k = true) (h32 : checkRange C 32 19 k σ1024q = true)
    (h64 : checkRange C 64 19 k σ1024q = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    {S M : Type} (ub : ℕ → m ℕ) (salt : m S) (hash : S → M → m (ZPoly 10)) (msg : M) :
    signMsgX { C with word := some 32 } (fun s => samplerZ falcon1024S s ub) salt hash k msg
        σ1024q =
      signMsgX { C with word := some 64 } (fun s => samplerZ falcon1024S s ub) salt hash k msg
        σ1024q :=
  (signMsgZ_word1024 C δq 32 (by norm_num) (by norm_num) k hc h32 ub salt hash msg).trans
    (signMsgZ_word1024 C δq 64 (by norm_num) le_rfl k hc h64 ub salt hash msg).symm

/-! ## Stored constants and stored trees -/

/-- **Stored-constant rounding, signing attempt at Falcon-1024**: if the tables at levels `≤ 9`
agree at 64 bits (`tabEqBN 10`), the attempts of `C` and of `C` with stored constants rounded by
`rc` are equal on every input. -/
theorem signX_rc1024 (C : Choices) (rc : RMode) (h : tabEqBN 10 C.x.rc rc 64 = true)
    {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 10) (k : RawKey 10)
    (c : ZPoly 10) :
    signX C samp T k c = signX { C with x := { C.x with rc := rc } } samp T k c :=
  signX_rcN C rc h samp T le_rfl k c

theorem fftC_rc_congr1024 (P : XChoices) (rc : RMode) (f : ℕ)
    (h : tabEqBN 10 P.rc rc f = true) :
    ∀ L, L ≤ 10 → ∀ a : Fin (2 ^ L) → ℤ, fftC P f L a = fftC { P with rc := rc } f L a :=
  fftC_rc_congrN P rc f h

theorem splitC_rc_congr1024 (P : XChoices) (rc : RMode) (f : ℕ)
    (h : tabEqBN 10 P.rc rc f = true) {L : ℕ} (hL : L ≤ 9) (t : Out (L + 1) → Cx f) :
    splitC P f L t = splitC { P with rc := rc } f L t :=
  splitC_rc_congrN P rc f h (by omega) t

theorem ldlC_rc_congr1024 (P : XChoices) (rc : RMode) (f : ℕ)
    (h : tabEqBN 10 P.rc rc f = true) (hσ : (Fx.ofRat P.rc σ1024q : Fx f) = Fx.ofRat rc σ1024q) :
    ∀ L, L ≤ 9 → ∀ g00 g10 g11 : Out L → Cx f,
      ldlC P f L g00 g10 g11 σ1024q = ldlC { P with rc := rc } f L g00 g10 g11 σ1024q :=
  fun L hL => ldlC_rc_congrP P rc f h σ1024q hσ L (by omega)

/-- Key expansion at Falcon-1024 reads `rc` only through the tables at levels `≤ 9` at `f` bits
and the stored `σ1024q`. -/
theorem expandC_rc_congr1024 (P : XChoices) (rc : RMode) (f : ℕ)
    (h : tabEqBN 10 P.rc rc f = true)
    (hσ : (Fx.ofRat P.rc σ1024q : Fx f) = Fx.ofRat rc σ1024q) (k : RawKey 10) :
    expandC P f k σ1024q = expandC { P with rc := rc } f k σ1024q :=
  expandC_rc_congrP P rc f h σ1024q hσ k

/-- **Stored-constant rounding, the signer at Falcon-1024**: if the tables at levels `≤ 9` agree at
`64` and at `64 + xn` bits and the stored `σ1024q` agrees, `C` and `C` with stored constants
rounded by `rc` give the same output on every key, message, salt source, hash and sampler
family. -/
theorem signMsgX_rc1024 (C : Choices) (rc : RMode) (h64 : tabEqBN 10 C.x.rc rc 64 = true)
    (hx : tabEqBN 10 C.x.rc rc (64 + C.xn) = true)
    (hσ : (Fx.ofRat C.x.rc σ1024q : Fx (64 + C.xn)) = Fx.ofRat rc σ1024q) {m : Type → Type*}
    [Monad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S)
    (hash : S → M → m (ZPoly 10)) (k : RawKey 10) (msg : M) :
    signMsgX C sampF salt hash k msg σ1024q =
      signMsgX { C with x := { C.x with rc := rc } } sampF salt hash k msg σ1024q :=
  signMsgX_rcP C rc h64 hx σ1024q hσ sampF salt hash k msg

/-- **Key expansion choices at Falcon-1024**: two choice points that differ only in key expansion
(`dm`, `root`, `xn`) give the same signer output on every message, salt source, hash and sampler
family for a key whose stored trees (`storeC … σ1024q`) are equal (decided by `CTree.eqB`). -/
theorem signMsgX_store1024 (C : Choices) (P : XChoices) (n : ℕ) (hrm : P.rm = C.x.rm)
    (hrc : P.rc = C.x.rc) (k : RawKey 10)
    (hT : (storeC C.x C.xn k σ1024q).eqB (storeC P n k σ1024q) = true)
    {m : Type → Type*} [Monad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ)
    (salt : m S) (hash : S → M → m (ZPoly 10)) (msg : M) :
    signMsgX C sampF salt hash k msg σ1024q =
      signMsgX { C with x := P, xn := n } sampF salt hash k msg σ1024q :=
  signMsgX_storeP C P n hrm hrc k σ1024q hT sampF salt hash msg

/-! ## Restart loop -/

/-- **Restart cap at Falcon-1024**: with a fresh salt per attempt, the signer capped at `N + j`
attempts is the signer capped at `N`, followed, when it fails, by the signer capped at `j`. -/
theorem signMsgX_cap_add1024 (C : Choices) (hs : C.salt = .perAttempt) {m : Type → Type*}
    [Monad m] [LawfulMonad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ)
    (salt : m S) (hash : S → M → m (ZPoly 10)) (k : RawKey 10) (msg : M) (N j : ℕ) :
    signMsgX { C with cap := N + j } sampF salt hash k msg σ1024q =
      signMsgX { C with cap := N } sampF salt hash k msg σ1024q >>= fun r =>
        r.elim (signMsgX { C with cap := j } sampF salt hash k msg σ1024q)
          fun b => pure (some b) :=
  signMsgX_cap_addP C hs sampF salt hash k msg σ1024q N j

end FalconPrecision.Exec
