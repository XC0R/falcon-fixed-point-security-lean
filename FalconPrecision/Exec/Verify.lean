/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Codec
public import VCVio.Algorithms.KeccakPrefix

/-! # HashToPoint and verification, parametric in the encoding choices

* `hashToPoint`: Falcon specification v1.2 Alg. 3 (p. 31) on the SHAKE-256 stream of VCVio's
  pure-Lean `shake256`: 16-bit big-endian chunks `t`, accepted if `t < kq` (`k = ⌊2¹⁶/q⌋`), value
  `t mod q`. The stream is squeezed to `L = 4n·2ʲ` bytes, `j < 12`, until `n` values are found.
* `hashInput`: the hashed string. Round 3 (Alg. 10 l. 2, Alg. 16 l. 1): `r ‖ m`. FN-DSA
  (provisional per NIST's Sep 2025 slides: BUFF, pure/prehash; layout not given there): the layout
  of VCVio's c-fn-dsa port (`Extern/Falcon/Sampling.lean`, text) `r ‖ tr ‖ 0x00 ‖ |ctx| ‖ ctx ‖ m`
  with `tr = SHAKE-256(pk)` over `trLen` bytes; prehash `r ‖ tr ‖ 0x01 ‖ |ctx| ‖ ctx ‖ oid ‖ m`;
  `|ctx| > 255` is rejected (`none`; one length byte, as FIPS 204), so verification fails.
* `verifyCore`: Alg. 16 l. 5-9 (p. 45) at `n = 2^logn` (default `n = 512`; `verifySig`, `openSm`:
  `logn = V.enc.logn`): `s₁ = c - s₂h mod q` centred, accept iff
  `‖(s₁, s₂)‖² ≤ ⌊β²⌋` and, if `infB = some B` (the slides' infinity-norm bound, value
  unpinned), `|s₁ᵢ|, |s₂ᵢ| ≤ B`.
* `verifySig` (detached signatures, §3.11.3) and `openSm` (NIST API, §3.11.6).

VCVio's `shake256` is trusted as tested in VCVio and here against Python `hashlib` (the 100
fingerprints of each round-3 KAT file, Falcon-512 and Falcon-1024, full values for entries 0 and 70
of each); it is not proved equal to FIPS 202. -/

@[expose] public section

namespace FalconPrecision.Exec.Codec

open VCVio.Algorithms.Keccak (shake256)
open Round3 (qN centre modq polyOf inttq)

/-! ## HashToPoint -/

/-- A byte list as a `ByteArray`. -/
def toBA (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- 16-bit big-endian chunks (§3.7, p. 31); a trailing odd byte is not used. -/
def chunks16 : List UInt8 → List ℕ
  | a :: b :: r => (256 * a.toNat + b.toNat) :: chunks16 r
  | _ => []

/-- Alg. 3 l. 1, 4-9 on a finite stream: the first `n` values `t mod q` of the chunks `t < kq`,
`k = ⌊2¹⁶/q⌋`; `none` if there are fewer than `n`. -/
def htpOf (n : ℕ) (xs : List UInt8) : Option (List ℕ) :=
  let vs := ((chunks16 xs).filter (· < 2 ^ 16 / qN * qN)).map (· % qN)
  if n ≤ vs.length then some (vs.take n) else none

/-- Alg. 3 on the first `L` bytes of `SHAKE-256(str)`. -/
def hashToPointL (n L : ℕ) (str : List UInt8) : Option (List ℕ) :=
  htpOf n (shake256 (toBA str) L).data.toList

/-- Alg. 3 `HashToPoint(str, q, n)`: the stream squeezed to `4n·2ʲ` bytes, `j < 12`; `none` if
`4n·2¹¹` bytes give fewer than `n` values (Alg. 3 would squeeze further). -/
def hashToPoint (n : ℕ) (str : List UInt8) : Option (List ℕ) :=
  ((List.range 12).map fun j => 4 * n * 2 ^ j).findSome? fun L => hashToPointL n L str

/-- Byte `j` of the SHAKE-256 output stream of `str` (FIPS 202: `SHAKE256(str, d)` is the first
`d` bytes of the stream). -/
def xof (str : List UInt8) (j : ℕ) : UInt8 := (shake256 (toBA str) (j + 1)).data.toList.getD j 0

/-! ## Hash input -/

/-- How the message enters the hash. -/
inductive MsgMode where
  /-- `m` (round 3). -/
  | raw
  /-- `0x00 ‖ |ctx| ‖ ctx ‖ m` (pure, provisional; `|ctx| ≤ 255`). -/
  | pure (ctx : List UInt8)
  /-- `0x01 ‖ |ctx| ‖ ctx ‖ oid ‖ m`, `m` the digest (prehash, provisional; `|ctx| ≤ 255`). -/
  | prehash (ctx oid : List UInt8)
  deriving DecidableEq, Repr

/-- The message part of the hash input; `none` if `|ctx| > 255` (one length byte, as FIPS 204). -/
def msgRep : MsgMode → List UInt8 → Option (List UInt8)
  | .raw, m => some m
  | .pure ctx, m =>
    if ctx.length ≤ 255 then some ([0, ctx.length.toUInt8] ++ ctx ++ m) else none
  | .prehash ctx oid, m =>
    if ctx.length ≤ 255 then some ([1, ctx.length.toUInt8] ++ ctx ++ oid ++ m) else none

/-- The verification choices. -/
structure VerChoices where
  enc : EncChoices
  /-- Hash `tr = SHAKE-256(pk)` (`enc.trLen` bytes) after the salt (BUFF). -/
  buff : Bool
  mode : MsgMode
  beta2 : ℕ
  infB : Option ℕ
  deriving DecidableEq, Repr

/-- Round 3, Falcon-512: `⌊β²⌋ = 34034726` (Table 3.3, p. 51), no BUFF, raw messages. -/
def round3V : VerChoices := ⟨round3, false, .raw, 34034726, none⟩

/-- FN-DSA provisional, Falcon-512, pure mode: BUFF with `trLen` bytes, infinity bound `infB`
(both unpinned); `⌊β²⌋` kept at the round-3 value, context empty (placeholders). -/
def fndsaProvV (trLen infB : ℕ) : VerChoices :=
  ⟨fndsaProv trLen, true, .pure [], 34034726, some infB⟩

/-- Round 3, Falcon-1024: `⌊β²⌋ = 70265242` (Table 3.3, p. 51), no BUFF, raw messages. -/
def round3V1024 : VerChoices := ⟨round3_1024, false, .raw, 70265242, none⟩

/-- `fndsaProvV` at Falcon-1024: `⌊β²⌋` kept at the round-3 value `70265242`, context empty
(placeholders). -/
def fndsaProvV1024 (trLen infB : ℕ) : VerChoices :=
  ⟨fndsaProv1024 trLen, true, .pure [], 70265242, some infB⟩

/-- The hashed string `r ‖ (tr) ‖ msgRep`; `none` if `msgRep` is. -/
def hashInput (V : VerChoices) (pk salt msg : List UInt8) : Option (List UInt8) :=
  (msgRep V.mode msg).map fun m =>
    salt ++ (if V.buff then (shake256 (toBA pk) V.enc.trLen).data.toList else []) ++ m

/-! ## Verification (`n = 2^logn`) -/

/-- `s₁ = c - s₂h mod q`, centred in `[-⌊q/2⌋, ⌊q/2⌋]` (Alg. 16 l. 5). -/
def s1Of (c : List ℕ) (s2 h : List ℤ) (logn : ℕ := 9) : Fin (2 ^ logn) → ℤ := fun i =>
  centre (modq ((c.getD i 0 : ℤ) - ncoef (polyOf s2.toArray logn) (polyOf h.toArray logn) i))

/-- The squared norm. -/
def normSq {logn : ℕ} (a : Fin (2 ^ logn) → ℤ) : ℤ := ∑ i, a i ^ 2

/-- The infinity-norm check (none: no check). -/
def infOk {logn : ℕ} (B : Option ℕ) (a : Fin (2 ^ logn) → ℤ) : Bool :=
  B.all fun B => decide (∀ i, |a i| ≤ B)

/-- The coefficients of `h` from the stored public key. -/
def hPoly (C : EncChoices) (hv : List ℕ) : List ℕ :=
  match C.pkForm with
  | .coeff => hv
  | .ntt => (inttq hv.toArray C.logn).toList

/-- Alg. 16 l. 5-9 at degree `2^logn`: accept iff `‖(s₁, s₂)‖² ≤ ⌊β²⌋` and the infinity-norm
check. -/
def verifyCore (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) (logn : ℕ := 9) : Bool :=
  let s1 := s1Of c s2 (h.map Int.ofNat) logn
  decide (normSq s1 + normSq (polyOf s2.toArray logn) ≤ V.beta2) && infOk V.infB s1 &&
    infOk V.infB (polyOf s2.toArray logn)

/-- `verifyCore` on inputs of exactly `2^logn` coefficients: `h`, `c` and `s₂` of any other length
are rejected (`verifyCore` reads missing coefficients as `0` and ignores extra ones). -/
def verifyCoreChecked (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) (logn : ℕ := 9) : Bool :=
  (h.length == 2 ^ logn && c.length == 2 ^ logn && s2.length == 2 ^ logn) &&
    verifyCore V h c s2 logn

/-- Alg. 16 on a detached signature (§3.11.3), at degree `2^V.enc.logn`; rejects if `hashInput`
is `none`. -/
def verifySig (V : VerChoices) (pk msg sig : List UInt8) : Bool :=
  match decodePk V.enc pk, decodeSig V.enc sig with
  | some hv, some σ =>
    match (hashInput V pk σ.salt msg).bind (hashToPoint V.enc.n) with
    | some c => verifyCore V (hPoly V.enc hv) c σ.s2 V.enc.logn
    | none => false
  | _, _ => false

/-- Alg. 16 on a NIST-API signed message (§3.11.6), at degree `2^V.enc.logn`: the message if
accepted. -/
def openSm (V : VerChoices) (pk sm : List UInt8) : Option (List UInt8) := do
  let hv ← decodePk V.enc pk
  let (salt, msg, s2) ← decodeSm V.enc sm
  let c ← (hashInput V pk salt msg).bind (hashToPoint V.enc.n)
  guard (verifyCore V (hPoly V.enc hv) c s2 V.enc.logn)
  pure msg

/-! ## Statements -/

theorem chunks16_append : ∀ (a t : List UInt8), ∃ u, chunks16 (a ++ t) = chunks16 a ++ u
  | x :: y :: r, t => by
    obtain ⟨u, hu⟩ := chunks16_append r t
    exact ⟨u, by simp only [List.cons_append, chunks16, hu]⟩
  | [x], t => ⟨chunks16 ([x] ++ t), rfl⟩
  | [], t => ⟨chunks16 t, rfl⟩

theorem htpOf_append {n : ℕ} {a : List UInt8} {c : List ℕ} (t : List UInt8)
    (h : htpOf n a = some c) : htpOf n (a ++ t) = some c := by
  obtain ⟨u, hu⟩ := chunks16_append a t
  simp only [htpOf] at h ⊢
  rw [hu, List.filter_append, List.map_append]
  split at h
  · rename_i h1
    cases h
    rw [ite_eq_left (by rw [List.length_append]; omega), List.take_append_of_le_length h1]
  · cases h

/-- **HashToPoint does not depend on the squeezed length**: once `L` bytes give `n` values,
every longer prefix of the stream gives the same values. -/
theorem hashToPointL_mono {n L L' : ℕ} {str : List UInt8} {c : List ℕ}
    (h : hashToPointL n L str = some c) (hL : L ≤ L') : hashToPointL n L' str = some c := by
  unfold hashToPointL at h ⊢
  rw [← List.take_append_drop L (shake256 (toBA str) L').data.toList,
    VCVio.Algorithms.Keccak.take_toList_shake256 (toBA str) hL]
  exact htpOf_append _ h

/-- **HashToPoint is Alg. 3 on the SHAKE-256 stream**: its output is the result of Alg. 3 l. 4-9
on every long enough prefix of the stream `xof str`. -/
theorem hashToPoint_spec {n : ℕ} {str : List UInt8} {c : List ℕ}
    (h : hashToPoint n str = some c) :
    ∃ L, ∀ L' ≥ L, htpOf n ((List.range L').map (xof str)) = some c := by
  obtain ⟨L, -, hc⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨L, fun L' hL' => ?_⟩
  have hx : (List.range L').map (xof str) = (shake256 (toBA str) L').data.toList := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, Array.length_toList, ByteArray.size_data,
        VCVio.Algorithms.Keccak.shake256_size]
    · intro j h1 h2
      rw [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range]
      rw [xof, List.getD_eq_getElem?_getD,
        ← VCVio.Algorithms.Keccak.take_toList_shake256 (toBA str) (show j + 1 ≤ L' by omega),
        List.getElem?_take_of_lt (Nat.lt_succ_self j), List.getElem?_eq_getElem h2]
      rfl
  rw [hx]
  exact hashToPointL_mono hc hL'

theorem centre_spec (d s : ℤ) :
    ((d - s) % (qN : ℤ) = 0 ∧ 2 * |s| < qN) ↔ s = centre (modq d) := by
  have hq : (qN : ℤ) = 12289 := rfl
  have hq2 : qN / 2 = 6144 := rfl
  simp only [centre, modq, hq, hq2]
  rcases abs_cases s with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] <;> split_ifs <;> constructor <;>
    intro h <;> omega

/-- **The verifier's equation is the spec's at degree `2^logn`** (Alg. 16 l. 5-9, p. 45): accept
iff some `s₁` with `s₁ ≡ c - s₂h (mod q)` in `ℤ[x]/(x^(2^logn) + 1)`, `|s₁ᵢ| ≤ ⌊q/2⌋`, has
`‖(s₁, s₂)‖² ≤ ⌊β²⌋` and passes the infinity-norm check. -/
theorem verifyCore_iffP (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) (logn : ℕ) :
    verifyCore V h c s2 logn = true ↔ ∃ s1 : Fin (2 ^ logn) → ℤ,
      (∀ i : Fin (2 ^ logn), ((c.getD i 0 : ℤ) - ncoef (polyOf s2.toArray logn)
          (polyOf (h.map Int.ofNat).toArray logn) i - s1 i) % (qN : ℤ) = 0 ∧ 2 * |s1 i| < qN) ∧
      normSq s1 + normSq (polyOf s2.toArray logn) ≤ V.beta2 ∧ infOk V.infB s1 = true ∧
      infOk V.infB (polyOf s2.toArray logn) = true := by
  have key : ∀ s1 : Fin (2 ^ logn) → ℤ, (∀ i : Fin (2 ^ logn), ((c.getD i 0 : ℤ) -
      ncoef (polyOf s2.toArray logn) (polyOf (h.map Int.ofNat).toArray logn) i - s1 i) %
        (qN : ℤ) = 0 ∧ 2 * |s1 i| < qN) ↔ s1 = s1Of c s2 (h.map Int.ofNat) logn := fun s1 =>
    (forall_congr' fun i => centre_spec _ _).trans funext_iff.symm
  constructor
  · intro hv
    simp only [verifyCore, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ⟨_, (key _).mpr rfl, hv.1.1, hv.1.2, hv.2⟩
  · rintro ⟨s1, hs, hn, h1, h2⟩
    rw [(key s1).mp hs] at hn h1
    simp only [verifyCore, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hn, h1⟩, h2⟩

/-- **The verifier's equation is the spec's** (Alg. 16 l. 5-9, p. 45): accept iff some `s₁` with
`s₁ ≡ c - s₂h (mod q)` in `ℤ[x]/(x⁵¹² + 1)`, `|s₁ᵢ| ≤ ⌊q/2⌋`, has `‖(s₁, s₂)‖² ≤ ⌊β²⌋` and
passes the infinity-norm check. -/
theorem verifyCore_iff (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) :
    verifyCore V h c s2 = true ↔ ∃ s1 : Fin (2 ^ 9) → ℤ,
      (∀ i : Fin (2 ^ 9), ((c.getD i 0 : ℤ) -
          ncoef (polyOf s2.toArray) (polyOf (h.map Int.ofNat).toArray) i - s1 i) % (qN : ℤ) = 0 ∧
        2 * |s1 i| < qN) ∧
      normSq s1 + normSq (polyOf s2.toArray) ≤ V.beta2 ∧ infOk V.infB s1 = true ∧
      infOk V.infB (polyOf s2.toArray) = true :=
  verifyCore_iffP V h c s2 9

/-- **The checked verifier**: it accepts iff `h`, `c` and `s₂` have exactly `2^logn` coefficients
and `verifyCore` accepts. -/
theorem verifyCoreChecked_iff (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) (logn : ℕ) :
    verifyCoreChecked V h c s2 logn = true ↔ h.length = 2 ^ logn ∧ c.length = 2 ^ logn ∧
      s2.length = 2 ^ logn ∧ verifyCore V h c s2 logn = true := by
  simp only [verifyCoreChecked, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- On inputs of exactly `2^logn` coefficients the checked verifier is `verifyCore`. -/
theorem verifyCoreChecked_eq (V : VerChoices) {h c : List ℕ} {s2 : List ℤ} {logn : ℕ}
    (hh : h.length = 2 ^ logn) (hc : c.length = 2 ^ logn) (hs : s2.length = 2 ^ logn) :
    verifyCoreChecked V h c s2 logn = verifyCore V h c s2 logn := by
  simp only [verifyCoreChecked, hh, hc, hs, beq_self_eq_true, Bool.and_self, Bool.true_and]

/-- **The checked verifier's equation is the spec's** (Alg. 16 l. 5-9, p. 45): it accepts iff
`h`, `c`, `s₂` have exactly `2^logn` coefficients and some `s₁ ≡ c - s₂h (mod q)` in
`ℤ[x]/(x^(2^logn) + 1)`, `|s₁ᵢ| ≤ ⌊q/2⌋`, has `‖(s₁, s₂)‖² ≤ ⌊β²⌋` and passes the infinity-norm
check. -/
theorem verifyCoreChecked_spec (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) (logn : ℕ) :
    verifyCoreChecked V h c s2 logn = true ↔ h.length = 2 ^ logn ∧ c.length = 2 ^ logn ∧
      s2.length = 2 ^ logn ∧ ∃ s1 : Fin (2 ^ logn) → ℤ,
      (∀ i : Fin (2 ^ logn), ((c.getD i 0 : ℤ) - ncoef (polyOf s2.toArray logn)
          (polyOf (h.map Int.ofNat).toArray logn) i - s1 i) % (qN : ℤ) = 0 ∧ 2 * |s1 i| < qN) ∧
      normSq s1 + normSq (polyOf s2.toArray logn) ≤ V.beta2 ∧ infOk V.infB s1 = true ∧
      infOk V.infB (polyOf s2.toArray logn) = true := by
  rw [verifyCoreChecked_iff, verifyCore_iffP]

end FalconPrecision.Exec.Codec
