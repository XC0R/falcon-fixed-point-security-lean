/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Round3Codec
public import LatticeCrypto.Falcon.Concrete.Encoding
import all LatticeCrypto.Falcon.Concrete.Encoding

/-! # Falcon encodings, parametric in the encoding choices

Key, signature and NIST-API encodings over bit streams `List Bool`, with the unpinned choices as
fields of `EncChoices`. References: Falcon specification v1.2 (round 3) §3.11, pp. 46-50; NIST,
"FIPS 206 Status Update" (Perlner, Sep 2025, marked provisional), slides "Our default encodings"
and "Comparison to FIPS 204, 205".

* Bits: `BitOrder` (§3.11.1: most significant bit first; the slides: little-endian encodings,
  taken here as least significant bit first in bytes and fields, as FIPS 204's `BitPack`).
* Public key (§3.11.4): optional header byte, then `n` values `< q` over 14 bits; `PkForm`
  (coefficients of `h`, or `ĥ = NTT(h)` per the slides).
* Private key (§3.11.5): optional header byte, `f, g` over `fgBits`, `F` over `capFBits`, two's
  complement, minimal value rejected; then `trLen` bytes `tr` (the slides' PK hash).
* `compress` / `decompress`: Alg. 17 (p. 47) and Alg. 18 (p. 48) on bit strings, coefficient code
  `coeffBits` of VCVio (sign, seven low bits, unary high part); `coeffMax` bounds `|sᵢ|` (`none`:
  the spec's algorithms; `some 2047`: VCVio's c-fn-dsa codec). `none` accepts
  `2047 < |sᵢ| ≤ 5833` (`5833² ≤ ⌊β²⌋`), which a codec bounding at 2047 rejects; the round-3 KATs
  do not tell them apart. Under `lsbFirst` the code keeps Alg. 17's bit sequence (the seven low
  bits most significant first); only the packing into bytes follows `order`.
* Signatures (§3.11.3): header, salt, then `s₂` compressed (padded to `sbytelen` or unpadded) or
  uncompressed (12-bit two's complement, `-2048` rejected).
* NIST API (§3.11.6): `sm = len₂ ‖ r ‖ m ‖ (0x20 + logn) ‖ compressed s₂`, unpadded.

Decoders enforce canonical form (exact lengths, zero padding bits, unique code of `0`), so that
`encode ∘ decode` is the identity where `decode` succeeds. -/

@[expose] public section

namespace FalconPrecision.Exec.Codec

open Falcon.Concrete (natBits natOfBits byteBits bytesToBits bitsToBytes coeffBits)
open Round3 (qN signedOf)

/-! ## Bits -/

/-- Bit order inside bytes and inside numerical fields. -/
inductive BitOrder where
  /-- Most significant bit first (round 3, §3.11.1, p. 46). -/
  | msbFirst
  /-- Least significant bit first (FN-DSA provisional: little-endian, as FIPS 204). -/
  | lsbFirst
  deriving DecidableEq, Repr

/-- `bs` followed by zeros up to a multiple of 8. -/
def pad8 (bs : List Bool) : List Bool := bs ++ List.replicate ((8 - bs.length % 8) % 8) false

/-- Each block of 8 bits reversed (the last block as it is if shorter). -/
def revChunks (bs : List Bool) : List Bool :=
  if bs.isEmpty then [] else (bs.take 8).reverse ++ revChunks (bs.drop 8)
termination_by bs.length
decreasing_by
  simp only [List.length_drop]
  have : bs.length ≠ 0 := by simpa [List.isEmpty_iff_length_eq_zero] using ‹¬bs.isEmpty›
  omega

/-- The bit stream of a byte string. -/
def bytesBits : BitOrder → List UInt8 → List Bool
  | .msbFirst, d => bytesToBits d
  | .lsbFirst, d => d.flatMap fun b => (byteBits b).reverse

/-- The bytes of a bit stream, the last byte padded with zero bits. -/
def bitsBytes : BitOrder → List Bool → List UInt8
  | .msbFirst, bs => bitsToBytes bs
  | .lsbFirst, bs => bitsToBytes (revChunks (pad8 bs))

/-- A `w`-bit field holding `v < 2ʷ`. -/
def natField : BitOrder → ℕ → ℕ → List Bool
  | .msbFirst, w, v => natBits w v
  | .lsbFirst, w, v => (natBits w v).reverse

/-- The value of a field. -/
def fieldNat : BitOrder → List Bool → ℕ
  | .msbFirst, bs => natOfBits bs
  | .lsbFirst, bs => natOfBits bs.reverse

/-- A `w`-bit two's-complement field. -/
def intField (o : BitOrder) (w : ℕ) (x : ℤ) : List Bool := natField o w (x % 2 ^ w).toNat

/-- `cnt` consecutive blocks of `w` bits. -/
def chunks (w : ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, bs => bs.take w :: chunks w k (bs.drop w)

/-- The bytes of a header (none, or one byte). -/
def hdrBytes : Option UInt8 → List UInt8
  | none => []
  | some h => [h]

/-- The bytes after the header, if the header matches. -/
def stripHdr : Option UInt8 → List UInt8 → Option (List UInt8)
  | none, b => some b
  | some h, b :: r => if b = h then some r else none
  | some _, [] => none

/-! ## Choices -/

/-- What the public key stores. -/
inductive PkForm where
  /-- The coefficients of `h` (round 3, §3.11.4). -/
  | coeff
  /-- `ĥ = NTT(h)` at the points `Round3.pts` in that order (slides; order unpinned, ours). -/
  | ntt
  deriving DecidableEq, Repr

/-- How `s₂` is stored in a signature. -/
inductive SigComp where
  /-- Alg. 17 (header bits `cc = 01`). -/
  | compressed
  /-- 12-bit two's complement per coefficient (`cc = 10`, §3.11.3, p. 48). -/
  | uncompressed
  deriving DecidableEq, Repr

/-- Length of a signature. -/
inductive SigPad where
  /-- Padded to exactly `sbytelen` bytes (§3.11.3; Alg. 10 l. 10, Alg. 16 l. 2; compressed form
  only). -/
  | fixed (sbytelen : ℕ)
  /-- Unpadded: the code ends in the last byte (fewer than 8 padding bits). -/
  | minimal
  deriving DecidableEq, Repr

/-- The encoding choices. -/
structure EncChoices where
  order : BitOrder
  logn : ℕ
  pkHdr : Option UInt8
  pkForm : PkForm
  skHdr : Option UInt8
  fgBits : ℕ
  capFBits : ℕ
  trLen : ℕ
  saltLen : ℕ
  sigHdr : Option UInt8
  sigComp : SigComp
  sigPad : SigPad
  coeffMax : Option ℕ
  deriving DecidableEq, Repr

/-- The degree `n = 2^logn`. -/
def EncChoices.n (C : EncChoices) : ℕ := 2 ^ C.logn

/-- Round 3 (v1.2), Falcon-512: §3.11.1-3.11.5, Table 3.3 (`sbytelen = 666`); detached
compressed signatures, header `0x39`. -/
def round3 : EncChoices :=
  { order := .msbFirst, logn := 9, pkHdr := some 0x09, pkForm := .coeff, skHdr := some 0x59,
    fgBits := 6, capFBits := 8, trLen := 0, saltLen := 40, sigHdr := some 0x39,
    sigComp := .compressed, sigPad := .fixed 666, coeffMax := none }

/-- FN-DSA as provisional in NIST's Sep 2025 slides, Falcon-512: little-endian bits, NTT-form
public key, `tr` (`trLen` bytes) in the private key, 40-byte salt. Not given by the slides and
kept at round-3 values here: header bytes, field widths, signature layout and padding. -/
def fndsaProv (trLen : ℕ) : EncChoices :=
  { round3 with order := .lsbFirst, pkForm := .ntt, trLen := trLen }

/-- Round 3 (v1.2), Falcon-1024: Table 3.3 (`sbytelen = 1280`), headers `0x0A`, `0x5A`, `0x3A`
(§3.11.3-3.11.5: `nnnn = 10`), `f`, `g` over 5 bits (§3.11.5). -/
def round3_1024 : EncChoices :=
  { round3 with
    logn := 10, pkHdr := some 0x0A, skHdr := some 0x5A, fgBits := 5, sigHdr := some 0x3A,
    sigPad := .fixed 1280 }

/-- `fndsaProv` at Falcon-1024: the same provisional choices on `round3_1024`. -/
def fndsaProv1024 (trLen : ℕ) : EncChoices :=
  { round3_1024 with order := .lsbFirst, pkForm := .ntt, trLen := trLen }

/-! ## Public keys -/

/-- Encode `n` values `< q` (§3.11.4). -/
def encodePk (C : EncChoices) (h : List ℕ) : List UInt8 :=
  hdrBytes C.pkHdr ++ bitsBytes C.order (h.flatMap (natField C.order 14))

/-- Decode a public key: exact length, zero padding bits, every value `< q`. -/
def decodePk (C : EncChoices) (b : List UInt8) : Option (List ℕ) := do
  let body ← stripHdr C.pkHdr b
  guard (body.length = (14 * C.n + 7) / 8)
  let bs := bytesBits C.order body
  guard ((bs.drop (14 * C.n)).all (· == false))
  let h := (chunks 14 C.n bs).map (fieldNat C.order)
  guard (h.all (· < qN))
  pure h

/-! ## Private keys -/

/-- A private key as stored: `f, g, F` and the public-key hash `tr` (empty in round 3). -/
structure SkData where
  f : List ℤ
  g : List ℤ
  capF : List ℤ
  tr : List UInt8
  deriving DecidableEq, Repr

/-- The bit length of the `f, g, F` part. -/
def EncChoices.skBits (C : EncChoices) : ℕ := (2 * C.fgBits + C.capFBits) * C.n

/-- Encode a private key (§3.11.5); `tr` follows `F` (position unpinned for FN-DSA; ours). -/
def encodeSk (C : EncChoices) (k : SkData) : List UInt8 :=
  hdrBytes C.skHdr ++ bitsBytes C.order (k.f.flatMap (intField C.order C.fgBits) ++
    k.g.flatMap (intField C.order C.fgBits) ++ k.capF.flatMap (intField C.order C.capFBits)) ++
    k.tr

/-- `cnt` signed `w`-bit fields from a bit stream. -/
def signedFields (o : BitOrder) (w cnt : ℕ) (bs : List Bool) : Option (List ℤ) :=
  (chunks w cnt bs).mapM fun c => signedOf w (fieldNat o c)

/-- Decode a private key: exact length, zero padding bits, minimal values rejected. -/
def decodeSk (C : EncChoices) (b : List UInt8) : Option SkData := do
  let body ← stripHdr C.skHdr b
  let L := (C.skBits + 7) / 8
  guard (body.length = L + C.trLen)
  let bs := bytesBits C.order (body.take L)
  guard ((bs.drop C.skBits).all (· == false))
  let f ← signedFields C.order C.fgBits C.n bs
  let g ← signedFields C.order C.fgBits C.n (bs.drop (C.fgBits * C.n))
  let capF ← signedFields C.order C.capFBits C.n (bs.drop (2 * C.fgBits * C.n))
  pure ⟨f, g, capF, body.drop L⟩

/-! ## Compress / Decompress -/

/-- Whether `|x|` is within the bound. -/
def inMax (cm : Option ℕ) (x : ℤ) : Bool := cm.all (x.natAbs ≤ ·)

/-- The code of `s` without padding (Alg. 17 l. 1-6), `none` if a coefficient exceeds `cm`. -/
def compressBits (cm : Option ℕ) (s : List ℤ) : Option (List Bool) :=
  if s.all (inMax cm) then some (s.flatMap coeffBits) else none

/-- Alg. 17 `Compress(s, slen)`: the code padded with zeros to `slen` bits, `none` if longer. -/
def compress (cm : Option ℕ) (s : List ℤ) (slen : ℕ) : Option (List Bool) := do
  let str ← compressBits cm s
  guard (str.length ≤ slen)
  pure (str ++ List.replicate (slen - str.length) false)

/-- The high part of `|sᵢ|` (Alg. 18 l. 5-10): each `0` adds `128`; a `1` ends; `-0` and
`|sᵢ| > cm` rejected. -/
def unary (cm : Option ℕ) (t : Bool) : ℕ → List Bool → Option (ℤ × List Bool)
  | m, true :: rest =>
    if m = 0 ∧ t ∨ cm.any (· < m) then none else some (if t then -(m : ℤ) else m, rest)
  | m, false :: rest => if cm.any (· < m + 128) then none else unary cm t (m + 128) rest
  | _, [] => none

/-- One coefficient (Alg. 18 l. 4-10). -/
def parseCoeff (cm : Option ℕ) : List Bool → Option (ℤ × List Bool)
  | t :: rest =>
    if 7 ≤ rest.length then unary cm t (natOfBits (rest.take 7)) (rest.drop 7) else none
  | [] => none

/-- `k` coefficients. -/
def parseCoeffs (cm : Option ℕ) : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
    let (x, rest) ← parseCoeff cm bs
    let (xs, rest') ← parseCoeffs cm k rest
    pure (x :: xs, rest')

/-- Alg. 18 `Decompress(str, slen)` for `n` coefficients. -/
def decompress (cm : Option ℕ) (n : ℕ) (str : List Bool) (slen : ℕ) : Option (List ℤ) := do
  guard (str.length = slen)
  let (s, rest) ← parseCoeffs cm n str
  guard (rest.all (· == false))
  pure s

/-- Unpadded decompression: as `decompress` at `slen = |str|`, and fewer than 8 padding bits. -/
def decompressMin (cm : Option ℕ) (n : ℕ) (str : List Bool) : Option (List ℤ) := do
  let (s, rest) ← parseCoeffs cm n str
  guard (rest.all (· == false) ∧ rest.length < 8)
  pure s

/-! ## Signatures -/

/-- A signature: the salt `r` and `s₂`. -/
structure Sig where
  salt : List UInt8
  s2 : List ℤ
  deriving DecidableEq, Repr

/-- The encoded `s₂` (after header and salt). -/
def encodeS2 (C : EncChoices) (s2 : List ℤ) : Option (List UInt8) :=
  match C.sigComp, C.sigPad with
  | .compressed, .fixed L =>
    (compress C.coeffMax s2 (8 * (L - (hdrBytes C.sigHdr).length - C.saltLen))).map
      (bitsBytes C.order)
  | .compressed, .minimal => (compressBits C.coeffMax s2).map (bitsBytes C.order)
  | .uncompressed, _ =>
    if s2.all (inMax (some 2047)) then
      some (bitsBytes C.order (s2.flatMap (intField C.order 12)))
    else none

/-- Decode `s₂` from the bytes after header and salt. -/
def decodeS2 (C : EncChoices) (b : List UInt8) : Option (List ℤ) :=
  match C.sigComp, C.sigPad with
  | .compressed, .fixed L =>
    decompress C.coeffMax C.n (bytesBits C.order b)
      (8 * (L - (hdrBytes C.sigHdr).length - C.saltLen))
  | .compressed, .minimal => decompressMin C.coeffMax C.n (bytesBits C.order b)
  | .uncompressed, _ => do
    guard (b.length = (12 * C.n + 7) / 8)
    let bs := bytesBits C.order b
    guard ((bs.drop (12 * C.n)).all (· == false))
    signedFields C.order 12 C.n bs

/-- Encode a signature: header, salt, `s₂` (§3.11.3). -/
def encodeSig (C : EncChoices) (σ : Sig) : Option (List UInt8) := do
  guard (σ.salt.length = C.saltLen)
  let body ← encodeS2 C σ.s2
  pure (hdrBytes C.sigHdr ++ σ.salt ++ body)

/-- Decode a signature. -/
def decodeSig (C : EncChoices) (b : List UInt8) : Option Sig := do
  let rest ← stripHdr C.sigHdr b
  guard (C.saltLen ≤ rest.length)
  let s2 ← decodeS2 C (rest.drop C.saltLen)
  pure ⟨rest.take C.saltLen, s2⟩

/-! ## NIST API (§3.11.6, p. 50) -/

/-- `sm = len₂ ‖ r ‖ m ‖ (0x20 + logn) ‖ compressed s₂` (unpadded; `len₂` big-endian, the byte
length of header and compressed `s₂`). -/
def encodeSm (C : EncChoices) (salt msg : List UInt8) (s2 : List ℤ) : Option (List UInt8) := do
  guard (salt.length = C.saltLen)
  let body ← (compressBits C.coeffMax s2).map (bitsBytes C.order)
  let sl := body.length + 1
  guard (sl < 2 ^ 16)
  pure ([(sl / 256).toUInt8, (sl % 256).toUInt8] ++ salt ++ msg ++
    ((0x20 + C.logn).toUInt8 :: body))

/-- Decode `sm` into salt, message and `s₂`. -/
def decodeSm (C : EncChoices) (sm : List UInt8) :
    Option (List UInt8 × List UInt8 × List ℤ) :=
  match sm with
  | a :: b :: _ => do
    let sl := 256 * a.toNat + b.toNat
    guard (1 ≤ sl ∧ 2 + C.saltLen + sl ≤ sm.length)
    let esig := sm.drop (sm.length - sl)
    guard (esig.head? = some (0x20 + C.logn).toUInt8)
    let s2 ← decompressMin C.coeffMax C.n (bytesBits C.order (esig.drop 1))
    pure ((sm.drop 2).take C.saltLen,
      (sm.take (sm.length - sl)).drop (2 + C.saltLen), s2)
  | _ => none

/-! ## Correctness statements -/

/-- Well-formed public-key values. -/
def PkOk (C : EncChoices) (h : List ℕ) : Prop := h.length = C.n ∧ ∀ x ∈ h, x < qN

/-- A coefficient fits a `w`-bit field with the minimal value excluded. -/
def FitsW (w : ℕ) (x : ℤ) : Prop := -(2 ^ (w - 1) : ℤ) < x ∧ x < 2 ^ (w - 1)

/-- Well-formed private keys. -/
def SkOk (C : EncChoices) (k : SkData) : Prop :=
  k.f.length = C.n ∧ k.g.length = C.n ∧ k.capF.length = C.n ∧ k.tr.length = C.trLen ∧
    (∀ x ∈ k.f, FitsW C.fgBits x) ∧ (∀ x ∈ k.g, FitsW C.fgBits x) ∧
    ∀ x ∈ k.capF, FitsW C.capFBits x

/-! ## Lemmas -/

section Lemmas

open Falcon.Concrete (natBits_length natOfBits_lt natBits_natOfBits natOfBits_natBits
  bytesToBits_bitsToBytes bitsToBytes_length)

/-! ### Option -/

theorem guard_bind_pos {p : Prop} [Decidable p] {β : Type} (hp : p) (f : Unit → Option β) :
    (guard p >>= f) = f () := by
  unfold guard; rw [ite_eq_left hp]; rfl

theorem guard_bind_neg {p : Prop} [Decidable p] {β : Type} (hp : ¬p) (f : Unit → Option β) :
    (guard p >>= f) = none := by
  unfold guard; rw [ite_eq_right hp]; rfl

theorem guard_bind_some {p : Prop} [Decidable p] {β : Type} {f : Unit → Option β} {b : β}
    (h : (guard p >>= f) = some b) : p ∧ f () = some b := by
  by_cases hp : p
  · exact ⟨hp, by rwa [guard_bind_pos hp] at h⟩
  · rw [guard_bind_neg hp] at h; cases h

theorem guard_bind_eq {p : Prop} [Decidable p] {β : Type} {f : Unit → Option β} {b : β}
    (hp : p) (h : f () = some b) : (guard p >>= f) = some b := by
  rw [guard_bind_pos hp]; exact h

theorem guard_bind_ite {p : Prop} [Decidable p] {β : Type} (b : β) :
    (guard p >>= fun _ => (pure b : Option β)) = if p then some b else none := by
  by_cases hp : p
  · rw [guard_bind_pos hp, ite_eq_left hp]; rfl
  · rw [guard_bind_neg hp, ite_eq_right hp]

theorem obind_eq_some {α β : Type} {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b :=
  Option.bind_eq_some_iff

/-! ### Bits and bytes -/

theorem length_pad8 (bs : List Bool) :
    (pad8 bs).length = bs.length + (8 - bs.length % 8) % 8 := by
  simp [pad8]

theorem pad8_of_mod {bs : List Bool} (h : bs.length % 8 = 0) : pad8 bs = bs := by
  simp [pad8, h]

theorem revChunks_nil : revChunks [] = [] := by
  rw [revChunks]; simp

theorem revChunks_append {a : List Bool} (b : List Bool) (ha : a.length = 8) :
    revChunks (a ++ b) = a.reverse ++ revChunks b := by
  have hne : ¬(a ++ b).isEmpty = true := by cases a <;> simp_all
  conv_lhs => rw [revChunks, ite_eq_right hne, List.take_left' ha, List.drop_left' ha]

theorem revChunks_of_le {bs : List Bool} (h : bs.length ≤ 8) : revChunks bs = bs.reverse := by
  rw [revChunks]
  split
  · simp_all
  · rw [List.take_of_length_le h, List.drop_of_length_le h, revChunks_nil, List.append_nil]

theorem length_revChunks (bs : List Bool) : (revChunks bs).length = bs.length := by
  fun_induction revChunks bs with
  | case1 bs h => simp_all
  | case2 bs h ih =>
    simp only [List.length_append, List.length_reverse, List.length_take, ih, List.length_drop]
    omega

theorem revChunks_revChunks (bs : List Bool) : revChunks (revChunks bs) = bs := by
  fun_induction revChunks bs with
  | case1 bs h =>
    rw [List.isEmpty_iff] at h
    subst h
    exact revChunks_nil
  | case2 bs h ih =>
    by_cases h8 : 8 ≤ bs.length
    · rw [revChunks_append _ (by simp only [List.length_reverse, List.length_take]; omega),
        List.reverse_reverse, ih, List.take_append_drop]
    · rw [List.drop_of_length_le (by omega), revChunks_nil, List.append_nil,
        revChunks_of_le (by simp only [List.length_reverse, List.length_take]; omega),
        List.reverse_reverse, List.take_of_length_le (by omega)]

theorem length_byteBits (b : UInt8) : (byteBits b).length = 8 := natBits_length 8 _

theorem bytesToBits_cons (b : UInt8) (d : List UInt8) :
    bytesToBits (b :: d) = byteBits b ++ bytesToBits d := by
  simp [bytesToBits]

theorem length_bytesToBits (d : List UInt8) : (bytesToBits d).length = 8 * d.length := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    rw [bytesToBits_cons, List.length_append, length_byteBits, ih, List.length_cons]; ring

theorem bytesBits_lsb (d : List UInt8) : bytesBits .lsbFirst d = revChunks (bytesToBits d) := by
  induction d with
  | nil => exact revChunks_nil.symm
  | cons b d ih =>
    simp only [bytesBits, List.flatMap_cons] at ih ⊢
    rw [ih, bytesToBits_cons, revChunks_append _ (length_byteBits b)]

theorem bitsToBytes_cons (b : UInt8) (y : List Bool) :
    bitsToBytes (byteBits b ++ y) = b :: bitsToBytes y := by
  have hne : ¬(byteBits b ++ y).isEmpty = true := by simp [byteBits, Falcon.Concrete.natBits]
  conv_lhs => rw [bitsToBytes, ite_eq_right hne, List.take_left' (length_byteBits b),
    List.drop_left' (length_byteBits b), length_byteBits, Nat.sub_self, List.replicate_zero,
    List.append_nil, byteBits, natOfBits_natBits (k := 8) (UInt8.toNat_lt_size b)]
  rw [Nat.toUInt8_eq, UInt8.ofNat_toNat]

theorem bitsToBytes_bytesToBits (d : List UInt8) : bitsToBytes (bytesToBits d) = d := by
  induction d with
  | nil => rw [bitsToBytes]; simp [bytesToBits]
  | cons b d ih => rw [bytesToBits_cons, bitsToBytes_cons, ih]

theorem bytesBits_bitsBytes (o : BitOrder) (bs : List Bool) :
    bytesBits o (bitsBytes o bs) = pad8 bs := by
  cases o
  · exact bytesToBits_bitsToBytes bs
  · simp only [bitsBytes]
    rw [bytesBits_lsb, bytesToBits_bitsToBytes, ← pad8,
      pad8_of_mod (by rw [length_revChunks, length_pad8]; omega), revChunks_revChunks]

theorem bitsBytes_bytesBits (o : BitOrder) (d : List UInt8) : bitsBytes o (bytesBits o d) = d := by
  cases o
  · exact bitsToBytes_bytesToBits d
  · simp only [bitsBytes]
    rw [bytesBits_lsb, pad8_of_mod (by rw [length_revChunks, length_bytesToBits]; omega),
      revChunks_revChunks, bitsToBytes_bytesToBits]

theorem length_bytesBits (o : BitOrder) (d : List UInt8) :
    (bytesBits o d).length = 8 * d.length := by
  cases o
  · exact length_bytesToBits d
  · rw [bytesBits_lsb, length_revChunks, length_bytesToBits]

theorem length_bitsBytes (o : BitOrder) (bs : List Bool) :
    (bitsBytes o bs).length = (bs.length + 7) / 8 := by
  cases o
  · exact bitsToBytes_length bs
  · simp only [bitsBytes]
    rw [bitsToBytes_length, length_revChunks, length_pad8]; omega

/-- `bitsBytes o` inverts `bytesBits o` up to the zero padding. -/
theorem bitsBytes_eq_of {o : BitOrder} {d : List UInt8} {x : List Bool}
    (h : bytesBits o d = pad8 x) : bitsBytes o x = d :=
  calc bitsBytes o x = bitsBytes o (bytesBits o (bitsBytes o x)) := (bitsBytes_bytesBits _ _).symm
    _ = d := by rw [bytesBits_bitsBytes, ← h, bitsBytes_bytesBits]

theorem eq_replicate_of_all {l : List Bool} (h : l.all (· == false) = true) :
    l = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, List.length_cons, List.replicate_succ]
    exact congrArg _ (ih h.2)

theorem eq_pad8_take {bs : List Bool} {m : ℕ} (hl : bs.length = 8 * ((m + 7) / 8))
    (hz : (bs.drop m).all (· == false) = true) : bs = pad8 (bs.take m) := by
  rw [pad8, List.length_take, Nat.min_eq_left (by omega)]
  conv_lhs => rw [← List.take_append_drop m bs]
  congr 1
  rw [eq_replicate_of_all hz, List.length_drop]
  congr 1
  omega

/-! ### Fields and chunks -/

theorem length_natField (o : BitOrder) (w v : ℕ) : (natField o w v).length = w := by
  cases o <;> simp [natField, natBits_length]

theorem length_intField (o : BitOrder) (w : ℕ) (x : ℤ) : (intField o w x).length = w :=
  length_natField o w _

theorem fieldNat_natField {o : BitOrder} {w v : ℕ} (h : v < 2 ^ w) :
    fieldNat o (natField o w v) = v := by
  cases o <;> simp [natField, fieldNat, natOfBits_natBits h]

theorem natField_fieldNat (o : BitOrder) (bs : List Bool) :
    natField o bs.length (fieldNat o bs) = bs := by
  cases o
  · exact natBits_natOfBits bs
  · simp only [natField, fieldNat]
    rw [← List.length_reverse, natBits_natOfBits, List.reverse_reverse]

theorem fieldNat_lt (o : BitOrder) (bs : List Bool) : fieldNat o bs < 2 ^ bs.length := by
  cases o
  · exact natOfBits_lt bs
  · simpa [fieldNat] using natOfBits_lt bs.reverse

theorem length_flatMap_of {α : Type} {f : α → List Bool} {w : ℕ} (hf : ∀ x, (f x).length = w) :
    ∀ xs : List α, (xs.flatMap f).length = w * xs.length
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_of hf xs, List.length_cons]
    ring

theorem chunks_flatMap {α : Type} (f : α → List Bool) {w : ℕ} (hf : ∀ x, (f x).length = w)
    (xs : List α) (tail : List Bool) : chunks w xs.length (xs.flatMap f ++ tail) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons, chunks, List.flatMap_cons, List.append_assoc, List.take_left' (hf x),
      List.drop_left' (hf x), ih, List.map_cons]

theorem flatten_chunks (w k : ℕ) (bs : List Bool) :
    (chunks w k bs).flatten = bs.take (w * k) := by
  induction k generalizing bs with
  | zero => simp [chunks]
  | succ k ih =>
    rw [chunks, List.flatten_cons, ih, show w * (k + 1) = w + w * k by ring, List.take_add]

theorem length_chunks (w k : ℕ) (bs : List Bool) : (chunks w k bs).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => rw [chunks, List.length_cons, ih]

theorem length_of_mem_chunks {w k : ℕ} {bs : List Bool} (h : w * k ≤ bs.length) :
    ∀ c ∈ chunks w k bs, c.length = w := by
  induction k generalizing bs with
  | zero => simp [chunks]
  | succ k ih =>
    intro c hc
    rw [mul_add_one] at h
    rw [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [List.length_take]; omega
    · exact ih (by rw [List.length_drop]; omega) c hc

theorem flatMap_natField_fieldNat {o : BitOrder} {w : ℕ} :
    ∀ {cs : List (List Bool)}, (∀ c ∈ cs, c.length = w) →
      (cs.map (fieldNat o)).flatMap (natField o w) = cs.flatten
  | [], _ => rfl
  | c :: cs, h => by
    have hc := natField_fieldNat o c
    rw [h c (by simp)] at hc
    rw [List.map_cons, List.flatMap_cons, hc,
      flatMap_natField_fieldNat fun c' hc' => h c' (by simp [hc']), List.flatten_cons]

theorem flatMap_natField_chunks {o : BitOrder} {w cnt : ℕ} {bs : List Bool}
    (hl : w * cnt ≤ bs.length) :
    ((chunks w cnt bs).map (fieldNat o)).flatMap (natField o w) = bs.take (w * cnt) := by
  rw [flatMap_natField_fieldNat (length_of_mem_chunks hl), flatten_chunks]

/-! ### Signed fields -/

theorem toNat_emod_lt (x : ℤ) (w : ℕ) : (x % 2 ^ w).toNat < 2 ^ w := by
  obtain ⟨Q, hQ, hQ'⟩ : ∃ Q : ℕ, (2 : ℤ) ^ w = Q ∧ 2 ^ w = Q := ⟨2 ^ w, by push_cast; rfl, rfl⟩
  have hQ0 : 0 < Q := by rw [← hQ']; positivity
  rw [hQ, hQ']
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < Q by omega)
  have h0 := Int.emod_nonneg x (show (Q : ℤ) ≠ 0 by omega)
  generalize x % (Q : ℤ) = r at h0 h1 ⊢
  omega

theorem signedOf_spec {w v : ℕ} {x : ℤ} (hv : v < 2 ^ w) :
    signedOf w v = some x ↔ FitsW w x ∧ (x % 2 ^ w).toNat = v := by
  rcases w with _ | k
  · have : v = 0 := by simpa using hv
    subst this
    simp only [signedOf, FitsW, Nat.zero_sub, pow_zero, Int.emod_one]
    constructor
    · intro h; cases h; simp
    · rintro ⟨⟨h1, h2⟩, -⟩
      rw [ite_eq_left (by norm_num)]
      congr 1; omega
  · obtain ⟨P, hN, hZ, hN2, hZ2⟩ : ∃ P : ℕ, 2 ^ k = P ∧ (2 : ℤ) ^ k = P ∧ 2 ^ (k + 1) = 2 * P ∧
        (2 : ℤ) ^ (k + 1) = 2 * P :=
      ⟨2 ^ k, rfl, by push_cast; rfl, by ring, by push_cast; ring⟩
    have hP : 0 < P := by rw [← hN]; positivity
    simp only [signedOf, FitsW, Nat.add_sub_cancel, hN, hZ, hN2, hZ2] at hv ⊢
    constructor
    · intro h
      by_cases h1 : v < P
      · rw [ite_eq_left h1] at h
        cases h
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        omega
      · rw [ite_eq_right h1] at h
        by_cases h2 : v = P
        · rw [ite_eq_left h2] at h; cases h
        · rw [ite_eq_right h2] at h
          cases h
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
          omega
    · rintro ⟨⟨h1, h2⟩, rfl⟩
      rcases le_or_gt 0 x with hx | hx
      · rw [Int.emod_eq_of_lt hx (by omega), ite_eq_left (by omega)]
        congr 1; omega
      · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega)]
        congr 1; omega

theorem signedOf_fieldNat_intField {o : BitOrder} {w : ℕ} {x : ℤ} (hx : FitsW w x) :
    signedOf w (fieldNat o (intField o w x)) = some x := by
  rw [intField, fieldNat_natField (toNat_emod_lt x w)]
  exact (signedOf_spec (toNat_emod_lt x w)).mpr ⟨hx, rfl⟩

theorem intField_of_signedOf {o : BitOrder} {w : ℕ} {c : List Bool} {x : ℤ} (hc : c.length = w)
    (h : signedOf w (fieldNat o c) = some x) : intField o w x = c ∧ FitsW w x := by
  have hv : fieldNat o c < 2 ^ w := by rw [← hc]; exact fieldNat_lt o c
  obtain ⟨hf, he⟩ := (signedOf_spec hv).mp h
  refine ⟨?_, hf⟩
  rw [intField, he, ← hc, natField_fieldNat]

theorem mapM_some_of {α β : Type} {φ : α → Option β} {g : β → α} :
    ∀ {l : List β}, (∀ x ∈ l, φ (g x) = some x) → (l.map g).mapM φ = some l
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, List.mapM_cons, h x (by simp),
      mapM_some_of fun y hy => h y (by simp [hy])]
    rfl

theorem signedFields_flatMap {o : BitOrder} {w : ℕ} {xs : List ℤ} (hx : ∀ x ∈ xs, FitsW w x)
    (tail : List Bool) :
    signedFields o w xs.length (xs.flatMap (intField o w) ++ tail) = some xs := by
  rw [signedFields, chunks_flatMap _ (length_intField o w)]
  exact mapM_some_of fun x hx' => signedOf_fieldNat_intField (hx x hx')

theorem signedFields_inv_aux {o : BitOrder} {w : ℕ} :
    ∀ {cs : List (List Bool)} {l : List ℤ}, (∀ c ∈ cs, c.length = w) →
      cs.mapM (fun c => signedOf w (fieldNat o c)) = some l →
      l.flatMap (intField o w) = cs.flatten ∧ (∀ x ∈ l, FitsW w x)
  | [], l, _, h => by
    rw [List.mapM_nil] at h
    cases h
    simp
  | c :: cs, l, hc, h => by
    rw [List.mapM_cons] at h
    obtain ⟨x, h1, h⟩ := obind_eq_some.mp h
    obtain ⟨xs, h2, h⟩ := obind_eq_some.mp h
    cases h
    obtain ⟨e1, e2⟩ := intField_of_signedOf (hc c (by simp)) h1
    obtain ⟨f1, f2⟩ := signedFields_inv_aux (fun c' hc' => hc c' (by simp [hc'])) h2
    refine ⟨by rw [List.flatMap_cons, e1, f1, List.flatten_cons], ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    exacts [e2, f2 y hy]

theorem signedFields_inv {o : BitOrder} {w cnt : ℕ} {bs : List Bool} {l : List ℤ}
    (hl : w * cnt ≤ bs.length) (h : signedFields o w cnt bs = some l) :
    l.flatMap (intField o w) = bs.take (w * cnt) ∧ ∀ x ∈ l, FitsW w x := by
  obtain ⟨e, hf⟩ := signedFields_inv_aux (length_of_mem_chunks hl) h
  exact ⟨by rw [e, flatten_chunks], hf⟩

/-! ### Headers -/

theorem stripHdr_hdrBytes (hd : Option UInt8) (b : List UInt8) :
    stripHdr hd (hdrBytes hd ++ b) = some b := by
  cases hd <;> simp [stripHdr, hdrBytes]

theorem eq_of_stripHdr {hd : Option UInt8} {b r : List UInt8} (h : stripHdr hd b = some r) :
    b = hdrBytes hd ++ r := by
  cases hd with
  | none => simp only [stripHdr, Option.some.injEq] at h; simp [hdrBytes, h]
  | some x =>
    cases b with
    | nil => simp [stripHdr] at h
    | cons y b =>
      simp only [stripHdr] at h
      by_cases hy : y = x
      · rw [ite_eq_left hy] at h; cases h; simp [hdrBytes, hy]
      · rw [ite_eq_right hy] at h; cases h

/-! ### Compress -/

theorem any_lt_false {cm : Option ℕ} {a : ℕ} (h : ∀ M, cm = some M → a ≤ M) :
    cm.any (· < a) = false := by
  cases cm with
  | none => rfl
  | some M => simpa using h M rfl

theorem unary_replicate (cm : Option ℕ) (t : Bool) (m q : ℕ) (rest : List Bool)
    (hle : ∀ M, cm = some M → m + 128 * q ≤ M) (hz : ¬(m + 128 * q = 0 ∧ t = true)) :
    unary cm t m (List.replicate q false ++ true :: rest) =
      some (if t then -((m + 128 * q : ℕ) : ℤ) else ((m + 128 * q : ℕ) : ℤ), rest) := by
  induction q generalizing m with
  | zero =>
    have h1 : ¬(m = 0 ∧ t = true ∨ cm.any (· < m) = true) := by
      rintro (h | h)
      · exact hz (by simpa using h)
      · rw [any_lt_false (fun M hM => by simpa using hle M hM)] at h; exact absurd h (by decide)
    rw [List.replicate_zero, List.nil_append, unary, ite_eq_right h1]
    simp
  | succ q ih =>
    have h1 : ¬(cm.any (· < m + 128) = true) := by
      rw [any_lt_false (fun M hM => by have := hle M hM; omega)]; decide
    rw [List.replicate_succ, List.cons_append, unary, ite_eq_right h1,
      ih (m + 128) (fun M hM => by have := hle M hM; omega) (fun h => hz ⟨by omega, h.2⟩),
      show m + 128 + 128 * q = m + 128 * (q + 1) by ring]

theorem parseCoeff_coeffBits (cm : Option ℕ) (x : ℤ) (hx : inMax cm x = true)
    (rest : List Bool) : parseCoeff cm (coeffBits x ++ rest) = some (x, rest) := by
  simp only [coeffBits, List.cons_append, parseCoeff, List.append_assoc]
  rw [ite_eq_left (by simp [natBits_length]),
    List.take_append_of_le_length (by simp [natBits_length]),
    List.take_of_length_le (by simp [natBits_length]),
    List.drop_append_of_le_length (by simp [natBits_length]),
    List.drop_of_length_le (by simp [natBits_length]), List.nil_append,
    natOfBits_natBits (k := 7)
      (by have := Nat.mod_lt x.natAbs (by norm_num : 0 < 128); simpa using this),
    List.nil_append,
    unary_replicate _ _ _ _ _ (fun M hM => by
      rw [Nat.mod_add_div]; simpa [inMax, hM] using hx)]
  · rw [Nat.mod_add_div]
    congr 2
    split_ifs with hneg <;> simp only [decide_eq_true_eq] at hneg <;> omega
  · rw [Nat.mod_add_div]
    rintro ⟨h0, ht⟩
    have : x < 0 := by simpa using ht
    omega

theorem parseCoeffs_flatMap (cm : Option ℕ) :
    ∀ (xs : List ℤ), (∀ x ∈ xs, inMax cm x = true) → ∀ tail : List Bool,
      parseCoeffs cm xs.length (xs.flatMap coeffBits ++ tail) = some (xs, tail)
  | [], _, _ => rfl
  | x :: xs, h, tail => by
    simp [List.flatMap_cons, parseCoeffs, parseCoeff_coeffBits cm x (h x (by simp)),
      parseCoeffs_flatMap cm xs (fun y hy => h y (by simp [hy])) tail]

theorem unary_inv (cm : Option ℕ) (t : Bool) :
    ∀ (bs : List Bool) (m : ℕ) (x : ℤ) (rest : List Bool), unary cm t m bs = some (x, rest) →
      ∃ q, bs = List.replicate q false ++ true :: rest ∧
        x = (if t then -((m + 128 * q : ℕ) : ℤ) else ((m + 128 * q : ℕ) : ℤ)) ∧
        ¬(m + 128 * q = 0 ∧ t = true) ∧ ∀ M, cm = some M → m + 128 * q ≤ M
  | [], m, x, rest, h => by simp [unary] at h
  | true :: bs, m, x, rest, h => by
    rw [unary] at h
    by_cases hc : (m = 0 ∧ t = true ∨ cm.any (· < m) = true)
    · rw [ite_eq_left hc] at h; cases h
    · rw [ite_eq_right hc] at h
      cases h
      refine ⟨0, by simp, by simp, fun hz => hc (Or.inl (by simpa using hz)), ?_⟩
      intro M hM
      have : ¬M < m := fun hlt => hc (Or.inr (by simp [hM, hlt]))
      omega
  | false :: bs, m, x, rest, h => by
    rw [unary] at h
    by_cases hc : cm.any (· < m + 128) = true
    · rw [ite_eq_left hc] at h; cases h
    · rw [ite_eq_right hc] at h
      obtain ⟨q, h1, h2, h3, h4⟩ := unary_inv cm t bs (m + 128) x rest h
      have e : m + 128 + 128 * q = m + 128 * (q + 1) := by ring
      refine ⟨q + 1, by rw [h1, List.replicate_succ, List.cons_append], by rw [h2, e],
        by rw [← e]; exact h3, fun M hM => by rw [← e]; exact h4 M hM⟩

theorem parseCoeff_inv {cm : Option ℕ} {bs : List Bool} {x : ℤ} {rest : List Bool}
    (h : parseCoeff cm bs = some (x, rest)) : bs = coeffBits x ++ rest ∧ inMax cm x = true := by
  match bs, h with
  | [], h => simp [parseCoeff] at h
  | t :: r, h =>
    rw [parseCoeff] at h
    by_cases hr : 7 ≤ r.length
    · rw [ite_eq_left hr] at h
      obtain ⟨m, hm⟩ : ∃ m, natOfBits (r.take 7) = m := ⟨_, rfl⟩
      rw [hm] at h
      have hm7 : m < 128 := by
        have := natOfBits_lt (r.take 7)
        rw [hm, List.length_take, Nat.min_eq_left hr] at this
        simpa using this
      have hnb : natBits 7 m = r.take 7 := by
        have := natBits_natOfBits (r.take 7)
        rw [List.length_take, Nat.min_eq_left hr] at this
        rw [← hm]; exact this
      obtain ⟨q, h1, h2, h3, h4⟩ := unary_inv cm t _ _ x rest h
      have habs : x.natAbs = m + 128 * q := by rw [h2]; cases t <;> simp <;> omega
      have hneg : decide (x < 0) = t := by
        cases t
        · simp at h2
          exact decide_eq_false (by omega)
        · have : m + 128 * q ≠ 0 := fun h0 => h3 ⟨h0, rfl⟩
          simp at h2
          exact decide_eq_true (by omega)
      constructor
      · rw [coeffBits, habs, show (m + 128 * q) % 128 = m by omega,
          show (m + 128 * q) / 128 = q by omega, hneg, hnb]
        conv_lhs => rw [← List.take_append_drop 7 r, h1]
        simp
      · rw [inMax, habs]
        cases cm with
        | none => rfl
        | some M => simpa using h4 M rfl
    · rw [ite_eq_right hr] at h; cases h

theorem parseCoeffs_inv (cm : Option ℕ) :
    ∀ (n : ℕ) (bs : List Bool) (s : List ℤ) (rest : List Bool),
      parseCoeffs cm n bs = some (s, rest) →
      bs = s.flatMap coeffBits ++ rest ∧ (∀ x ∈ s, inMax cm x = true) ∧ s.length = n
  | 0, bs, s, rest, h => by
    simp only [parseCoeffs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, bs, s, rest, h => by
    simp only [parseCoeffs] at h
    obtain ⟨⟨x, r1⟩, h1, h⟩ := obind_eq_some.mp h
    obtain ⟨⟨xs, r2⟩, h2, h⟩ := obind_eq_some.mp h
    cases h
    obtain ⟨e1, i1⟩ := parseCoeff_inv h1
    obtain ⟨e2, i2, l2⟩ := parseCoeffs_inv cm n r1 xs r2 h2
    refine ⟨by rw [e1, e2]; simp, ?_, by simp [l2]⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    exacts [i1, i2 y hy]

theorem compressBits_eq_some {cm : Option ℕ} {s : List ℤ} {code : List Bool} :
    compressBits cm s = some code ↔
      (∀ x ∈ s, inMax cm x = true) ∧ s.flatMap coeffBits = code := by
  unfold compressBits
  by_cases hs : s.all (inMax cm) = true
  · rw [ite_eq_left hs, Option.some.injEq]
    exact ⟨fun h => ⟨List.all_eq_true.mp hs, h⟩, fun h => h.2⟩
  · rw [ite_eq_right hs]
    exact ⟨(fun h => nomatch h), fun h => absurd (List.all_eq_true.mpr h.1) hs⟩

theorem compress_eq_some {cm : Option ℕ} {s : List ℤ} {slen : ℕ} {str : List Bool} :
    compress cm s slen = some str ↔ (∀ x ∈ s, inMax cm x = true) ∧
      (s.flatMap coeffBits).length ≤ slen ∧
      str = s.flatMap coeffBits ++ List.replicate (slen - (s.flatMap coeffBits).length) false := by
  constructor
  · intro h
    simp only [compress] at h
    obtain ⟨code, hc, h⟩ := obind_eq_some.mp h
    obtain ⟨hl, h⟩ := guard_bind_some h
    obtain ⟨hin, rfl⟩ := compressBits_eq_some.mp hc
    exact ⟨hin, hl, (Option.some.inj h).symm⟩
  · rintro ⟨hin, hl, rfl⟩
    simp only [compress]
    exact obind_eq_some.mpr ⟨_, compressBits_eq_some.mpr ⟨hin, rfl⟩, guard_bind_eq hl rfl⟩

theorem length_of_compress {cm : Option ℕ} {s : List ℤ} {slen : ℕ} {str : List Bool}
    (h : compress cm s slen = some str) : str.length = slen := by
  obtain ⟨-, hl, rfl⟩ := compress_eq_some.mp h
  rw [List.length_append, List.length_replicate]
  omega

theorem decompressMin_pad8 {cm : Option ℕ} {s : List ℤ} (hs : ∀ x ∈ s, inMax cm x = true) :
    decompressMin cm s.length (pad8 (s.flatMap coeffBits)) = some s := by
  simp only [decompressMin, pad8]
  refine obind_eq_some.mpr ⟨_, parseCoeffs_flatMap cm s hs _, ?_⟩
  exact guard_bind_eq ⟨by simp, by simp only [List.length_replicate]; omega⟩ rfl

theorem bitsBytes_of_decompressMin {o : BitOrder} {cm : Option ℕ} {n : ℕ} {d : List UInt8}
    {s : List ℤ} (h : decompressMin cm n (bytesBits o d) = some s) :
    (∀ x ∈ s, inMax cm x = true) ∧ bitsBytes o (s.flatMap coeffBits) = d ∧ s.length = n := by
  simp only [decompressMin] at h
  obtain ⟨⟨s', rest⟩, hp, h⟩ := obind_eq_some.mp h
  obtain ⟨hzh, h⟩ := guard_bind_some h
  have hz : rest.all (· == false) = true := hzh.1
  have h8 : rest.length < 8 := hzh.2
  have hs : s' = s := Option.some.inj h
  subst hs
  obtain ⟨e, hin, hl⟩ := parseCoeffs_inv cm n _ _ _ hp
  refine ⟨hin, bitsBytes_eq_of ?_, hl⟩
  have hlen := length_bytesBits o d
  rw [e, List.length_append] at hlen
  rw [e, pad8, eq_replicate_of_all hz]
  congr 2
  omega

theorem obind_some {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

theorem decodePk_body (C : EncChoices) (body : List UInt8)
    (hl : body.length = (14 * C.n + 7) / 8)
    (hz : ((bytesBits C.order body).drop (14 * C.n)).all (· == false) = true) :
    decodePk C (hdrBytes C.pkHdr ++ body) =
      if ((chunks 14 C.n (bytesBits C.order body)).map (fieldNat C.order)).all (· < qN) then
        some ((chunks 14 C.n (bytesBits C.order body)).map (fieldNat C.order)) else none := by
  simp only [decodePk, stripHdr_hdrBytes, obind_some, guard_bind_pos hl, guard_bind_pos hz,
    guard_bind_ite]

end Lemmas

/-- **Public keys decode as encoded** (§3.11.4), for every bit order and header. -/
theorem decodePk_encodePk (C : EncChoices) (h : List ℕ) (hh : PkOk C h) :
    decodePk C (encodePk C h) = some h := by
  obtain ⟨hn, hq⟩ := hh
  have hX : (h.flatMap (natField C.order 14)).length = 14 * C.n := by
    rw [length_flatMap_of (length_natField C.order 14), hn]
  have hbs := bytesBits_bitsBytes C.order (h.flatMap (natField C.order 14))
  rw [pad8, hX] at hbs
  have h3 : (chunks 14 C.n (bytesBits C.order (bitsBytes C.order
      (h.flatMap (natField C.order 14))))).map (fieldNat C.order) = h := by
    rw [hbs, ← hn, chunks_flatMap _ (length_natField C.order 14), List.map_map]
    exact (List.map_congr_left fun x hx => fieldNat_natField (lt_trans (hq x hx) (by decide))).trans
      (List.map_id _)
  rw [encodePk, decodePk_body C _ (by rw [length_bitsBytes, hX])
    (by rw [hbs, List.drop_left' hX]; simp), h3,
    ite_eq_left (List.all_eq_true.mpr fun x hx => decide_eq_true (hq x hx))]

/-- **Public-key encodings are unique**: a decoded key re-encodes to the same bytes. -/
theorem encodePk_of_decodePk (C : EncChoices) (b : List UInt8) (h : List ℕ)
    (hd : decodePk C b = some h) : encodePk C h = b := by
  simp only [decodePk] at hd
  obtain ⟨body, hs, hd⟩ := obind_eq_some.mp hd
  obtain ⟨h1, hd⟩ := guard_bind_some hd
  obtain ⟨h2, hd⟩ := guard_bind_some hd
  obtain ⟨-, hd⟩ := guard_bind_some hd
  cases hd
  have hl : (bytesBits C.order body).length = 8 * ((14 * C.n + 7) / 8) := by
    rw [length_bytesBits, h1]
  rw [eq_of_stripHdr hs, encodePk, flatMap_natField_chunks (by rw [hl]; omega),
    bitsBytes_eq_of (eq_pad8_take hl h2)]

/-- **Private keys decode as encoded** (§3.11.5), for every field width (width `0` holds `0`). -/
theorem decodeSk_encodeSk (C : EncChoices) (k : SkData) (hk : SkOk C k) :
    decodeSk C (encodeSk C k) = some k := by
  obtain ⟨hf, hg, hF, htr, hfw, hgw, hFw⟩ := hk
  have l1 := length_flatMap_of (length_intField C.order C.fgBits) k.f
  have l2 := length_flatMap_of (length_intField C.order C.fgBits) k.g
  have l3 := length_flatMap_of (length_intField C.order C.capFBits) k.capF
  rw [hf] at l1
  rw [hg] at l2
  rw [hF] at l3
  have hX : (k.f.flatMap (intField C.order C.fgBits) ++ k.g.flatMap (intField C.order C.fgBits) ++
      k.capF.flatMap (intField C.order C.capFBits)).length = C.skBits := by
    rw [List.length_append, List.length_append, l1, l2, l3, EncChoices.skBits]; ring
  have hB := length_bitsBytes C.order (k.f.flatMap (intField C.order C.fgBits) ++
    k.g.flatMap (intField C.order C.fgBits) ++ k.capF.flatMap (intField C.order C.capFBits))
  have hbs := bytesBits_bitsBytes C.order (k.f.flatMap (intField C.order C.fgBits) ++
    k.g.flatMap (intField C.order C.fgBits) ++ k.capF.flatMap (intField C.order C.capFBits))
  rw [hX] at hB
  rw [pad8, hX] at hbs
  have g1 : (bitsBytes C.order (k.f.flatMap (intField C.order C.fgBits) ++
      k.g.flatMap (intField C.order C.fgBits) ++ k.capF.flatMap (intField C.order C.capFBits)) ++
      k.tr).length = (C.skBits + 7) / 8 + C.trLen := by
    rw [List.length_append, hB, htr]
  have g2 : ((k.f.flatMap (intField C.order C.fgBits) ++ k.g.flatMap (intField C.order C.fgBits) ++
      k.capF.flatMap (intField C.order C.capFBits) ++
      List.replicate ((8 - C.skBits % 8) % 8) false).drop C.skBits).all (· == false) = true := by
    rw [List.drop_left' hX]; simp
  have s1 : signedFields C.order C.fgBits C.n (k.f.flatMap (intField C.order C.fgBits) ++
      k.g.flatMap (intField C.order C.fgBits) ++ k.capF.flatMap (intField C.order C.capFBits) ++
      List.replicate ((8 - C.skBits % 8) % 8) false) = some k.f := by
    simp only [List.append_assoc]
    rw [← hf]; exact signedFields_flatMap hfw _
  have s2 : signedFields C.order C.fgBits C.n ((k.f.flatMap (intField C.order C.fgBits) ++
      k.g.flatMap (intField C.order C.fgBits) ++ k.capF.flatMap (intField C.order C.capFBits) ++
      List.replicate ((8 - C.skBits % 8) % 8) false).drop (C.fgBits * C.n)) = some k.g := by
    simp only [List.append_assoc]
    rw [List.drop_left' l1, ← hg]; exact signedFields_flatMap hgw _
  have s3 : signedFields C.order C.capFBits C.n ((k.f.flatMap (intField C.order C.fgBits) ++
      k.g.flatMap (intField C.order C.fgBits) ++ k.capF.flatMap (intField C.order C.capFBits) ++
      List.replicate ((8 - C.skBits % 8) % 8) false).drop (2 * C.fgBits * C.n)) =
      some k.capF := by
    rw [List.append_assoc (_ ++ _),
      List.drop_left' (by rw [List.length_append, l1, l2]; ring), ← hF]
    exact signedFields_flatMap hFw _
  simp only [decodeSk, encodeSk, List.append_assoc (hdrBytes C.skHdr), stripHdr_hdrBytes,
    obind_some, guard_bind_pos g1, List.take_left' hB, List.drop_left' hB, hbs,
    guard_bind_pos g2, s1, s2, s3]
  rfl

/-- **Private-key encodings are unique**. -/
theorem encodeSk_of_decodeSk (C : EncChoices) (b : List UInt8) (k : SkData)
    (hd : decodeSk C b = some k) : encodeSk C k = b := by
  simp only [decodeSk] at hd
  obtain ⟨body, hs, hd⟩ := obind_eq_some.mp hd
  obtain ⟨h1, hd⟩ := guard_bind_some hd
  obtain ⟨h2, hd⟩ := guard_bind_some hd
  obtain ⟨f, hf, hd⟩ := obind_eq_some.mp hd
  obtain ⟨g, hg, hd⟩ := obind_eq_some.mp hd
  obtain ⟨F, hF, hd⟩ := obind_eq_some.mp hd
  cases hd
  have hsk : C.skBits = C.fgBits * C.n + C.fgBits * C.n + C.capFBits * C.n := by
    rw [EncChoices.skBits]; ring
  have h2n : 2 * C.fgBits * C.n = C.fgBits * C.n + C.fgBits * C.n := by ring
  have hl : (bytesBits C.order (body.take ((C.skBits + 7) / 8))).length =
      8 * ((C.skBits + 7) / 8) := by
    rw [length_bytesBits, List.length_take, Nat.min_eq_left (by omega)]
  obtain ⟨ef, -⟩ := signedFields_inv (by rw [hl]; omega) hf
  obtain ⟨eg, -⟩ := signedFields_inv (by rw [List.length_drop, hl]; omega) hg
  obtain ⟨eF, -⟩ := signedFields_inv (by rw [List.length_drop, hl]; omega) hF
  rw [h2n] at eF
  rw [eq_of_stripHdr hs, encodeSk, List.append_assoc (hdrBytes C.skHdr)]
  congr 1
  dsimp only
  rw [ef, eg, eF, ← List.take_add, ← List.take_add, ← hsk,
    bitsBytes_eq_of (eq_pad8_take hl h2), List.take_append_drop]

/-- **Decompress inverts Compress** (§3.11.2, p. 47: "for any polynomial `s` such that
`Compress(s, slen) ≠ ⊥`, `Decompress(Compress(s, slen), slen) = s`"), for every bound `cm`. -/
theorem decompress_compress (cm : Option ℕ) (s : List ℤ) (slen : ℕ) (str : List Bool)
    (h : compress cm s slen = some str) : decompress cm s.length str slen = some s := by
  obtain ⟨hin, hl, rfl⟩ := compress_eq_some.mp h
  simp only [decompress]
  refine guard_bind_eq (by rw [List.length_append, List.length_replicate]; omega) ?_
  exact obind_eq_some.mpr ⟨_, parseCoeffs_flatMap cm s hin _,
    guard_bind_eq (by simp) rfl⟩

/-- **Unique encoding** (§3.11.2, p. 47, the three checks of Alg. 18): a string that decompresses
to `s` is `Compress(s, slen)`. -/
theorem compress_of_decompress (cm : Option ℕ) (n : ℕ) (s : List ℤ) (slen : ℕ) (str : List Bool)
    (h : decompress cm n str slen = some s) : compress cm s slen = some str := by
  simp only [decompress] at h
  obtain ⟨hl, h⟩ := guard_bind_some h
  obtain ⟨⟨s', rest⟩, hp, h⟩ := obind_eq_some.mp h
  obtain ⟨hz', h⟩ := guard_bind_some h
  have hz : rest.all (· == false) = true := hz'
  have hs : s' = s := Option.some.inj h
  subst hs
  obtain ⟨e, hin, -⟩ := parseCoeffs_inv cm n _ _ _ hp
  refine compress_eq_some.mpr ⟨hin, by rw [← hl, e, List.length_append]; omega, ?_⟩
  conv_lhs => rw [e, eq_replicate_of_all hz]
  congr 2
  rw [← hl, e, List.length_append]
  omega

/-! ### Signature helpers -/

theorem fitsW12_of_inMax {x : ℤ} (h : inMax (some 2047) x = true) : FitsW 12 x := by
  simp [inMax] at h
  unfold FitsW
  norm_num
  omega

theorem inMax_of_fitsW12 {x : ℤ} (h : FitsW 12 x) : inMax (some 2047) x = true := by
  unfold FitsW at h
  norm_num at h
  simp [inMax]
  omega

theorem decodeS2_encodeS2 (C : EncChoices) {s2 : List ℤ} {d : List UInt8} (hn : s2.length = C.n)
    (h : encodeS2 C s2 = some d) : decodeS2 C d = some s2 := by
  unfold encodeS2 at h
  unfold decodeS2
  cases hc : C.sigComp <;> cases hp : C.sigPad <;> simp only [hc, hp] at h ⊢
  · obtain ⟨str, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [bytesBits_bitsBytes, pad8_of_mod (by rw [length_of_compress hs]; omega), ← hn]
    exact decompress_compress _ _ _ _ hs
  · obtain ⟨code, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hin, rfl⟩ := compressBits_eq_some.mp hcb
    rw [bytesBits_bitsBytes, ← hn]
    exact decompressMin_pad8 hin
  all_goals
    by_cases hs : s2.all (inMax (some 2047)) = true
    · rw [ite_eq_left hs] at h
      cases h
      have hX := length_flatMap_of (length_intField C.order 12) s2
      rw [hn] at hX
      have hbs := bytesBits_bitsBytes C.order (s2.flatMap (intField C.order 12))
      rw [pad8, hX] at hbs
      refine guard_bind_eq (by rw [length_bitsBytes, hX]) (guard_bind_eq ?_ ?_)
      · rw [hbs, List.drop_left' hX]; simp
      · rw [hbs, ← hn]
        exact signedFields_flatMap (fun x hx => fitsW12_of_inMax (List.all_eq_true.mp hs x hx)) _
    · rw [ite_eq_right hs] at h; cases h

theorem encodeS2_decodeS2 (C : EncChoices) {s2 : List ℤ} {d : List UInt8}
    (h : decodeS2 C d = some s2) : encodeS2 C s2 = some d := by
  unfold decodeS2 at h
  unfold encodeS2
  cases hc : C.sigComp <;> cases hp : C.sigPad <;> simp only [hc, hp] at h ⊢
  · rw [compress_of_decompress _ _ _ _ _ h]
    exact congrArg some (bitsBytes_bytesBits _ _)
  · obtain ⟨hin, he, -⟩ := bitsBytes_of_decompressMin h
    rw [compressBits_eq_some.mpr ⟨hin, rfl⟩]
    exact congrArg some he
  all_goals
    obtain ⟨h1, h⟩ := guard_bind_some h
    obtain ⟨h2, h⟩ := guard_bind_some h
    have hl : (bytesBits C.order d).length = 8 * ((12 * C.n + 7) / 8) := by
      rw [length_bytesBits, h1]
    obtain ⟨e, hfit⟩ := signedFields_inv (by rw [hl]; omega) h
    rw [ite_eq_left (List.all_eq_true.mpr fun x hx => inMax_of_fitsW12 (hfit x hx)), e,
      bitsBytes_eq_of (eq_pad8_take hl h2)]

theorem toNat_hi_lo {sl : ℕ} (h : sl < 2 ^ 16) :
    256 * (sl / 256).toUInt8.toNat + (sl % 256).toUInt8.toNat = sl := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow] at h ⊢
  omega

theorem sm_drop (a b x : UInt8) (P Q : List UInt8) :
    (a :: b :: (P ++ x :: Q)).drop ((a :: b :: (P ++ x :: Q)).length - (Q.length + 1)) =
      x :: Q := by
  rw [show (a :: b :: (P ++ x :: Q)).length - (Q.length + 1) = P.length + 1 + 1 by
    simp only [List.length_cons, List.length_append]; omega]
  simp

theorem sm_salt (a b : UInt8) (salt msg Q : List UInt8) :
    ((a :: b :: (salt ++ msg ++ Q)).drop 2).take salt.length = salt := by
  simp

theorem sm_msg (a b x : UInt8) (salt msg Q : List UInt8) :
    ((a :: b :: (salt ++ msg ++ x :: Q)).take ((a :: b :: (salt ++ msg ++ x :: Q)).length -
      (Q.length + 1))).drop (2 + salt.length) = msg := by
  rw [show (a :: b :: (salt ++ msg ++ x :: Q)).length - (Q.length + 1) =
      (salt ++ msg).length + 1 + 1 by simp only [List.length_cons, List.length_append]; omega,
    show 2 + salt.length = salt.length + 1 + 1 by omega, List.take_succ_cons,
    List.take_succ_cons, List.take_left' rfl, List.drop_succ_cons, List.drop_succ_cons,
    List.drop_left' rfl]

/-- **Signatures decode as encoded** (§3.11.3), for every encoding choice. -/
theorem decodeSig_encodeSig (C : EncChoices) (σ : Sig) (b : List UInt8)
    (hn : σ.s2.length = C.n) (h : encodeSig C σ = some b) : decodeSig C b = some σ := by
  simp only [encodeSig] at h
  obtain ⟨hsl, h⟩ := guard_bind_some h
  obtain ⟨body, hb, h⟩ := obind_eq_some.mp h
  cases h
  simp only [decodeSig, List.append_assoc, stripHdr_hdrBytes, obind_some]
  refine guard_bind_eq (by rw [List.length_append]; omega) ?_
  rw [List.drop_left' hsl, decodeS2_encodeS2 C hn hb, List.take_left' hsl]
  rfl

/-- **Signature encodings are unique**. -/
theorem encodeSig_of_decodeSig (C : EncChoices) (σ : Sig) (b : List UInt8)
    (h : decodeSig C b = some σ) : encodeSig C σ = some b := by
  simp only [decodeSig] at h
  obtain ⟨rest, hs, h⟩ := obind_eq_some.mp h
  obtain ⟨hl, h⟩ := guard_bind_some h
  obtain ⟨s2, h2, h⟩ := obind_eq_some.mp h
  cases h
  simp only [encodeSig]
  refine guard_bind_eq (by rw [List.length_take]; omega) ?_
  rw [encodeS2_decodeS2 C h2, eq_of_stripHdr hs]
  change some (hdrBytes C.sigHdr ++ rest.take C.saltLen ++ rest.drop C.saltLen) =
    some (hdrBytes C.sigHdr ++ rest)
  rw [List.append_assoc, List.take_append_drop]

/-- **NIST-API messages decode as encoded** (§3.11.6). -/
theorem decodeSm_encodeSm (C : EncChoices) (salt msg : List UInt8) (s2 : List ℤ)
    (sm : List UInt8) (hn : s2.length = C.n) (h : encodeSm C salt msg s2 = some sm) :
    decodeSm C sm = some (salt, msg, s2) := by
  simp only [encodeSm] at h
  obtain ⟨hsl, h⟩ := guard_bind_some h
  obtain ⟨body, hb, h⟩ := obind_eq_some.mp h
  obtain ⟨hlt, h⟩ := guard_bind_some h
  cases h
  obtain ⟨code, hcb, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨hin, rfl⟩ := compressBits_eq_some.mp hcb
  have hB : decompressMin C.coeffMax C.n
      (bytesBits C.order (bitsBytes C.order (s2.flatMap coeffBits))) = some s2 := by
    rw [bytesBits_bitsBytes, ← hn]; exact decompressMin_pad8 hin
  generalize bitsBytes C.order (s2.flatMap coeffBits) = B at hB hlt ⊢
  simp only [List.cons_append, List.nil_append, decodeSm]
  rw [toNat_hi_lo hlt]
  refine guard_bind_eq ⟨by omega, by simp only [List.length_cons, List.length_append]; omega⟩ ?_
  refine guard_bind_eq (by rw [sm_drop]; rfl)
    (obind_eq_some.mpr ⟨s2, by rw [sm_drop]; exact hB, ?_⟩)
  exact congrArg some (by rw [← hsl, sm_salt, sm_msg])

/-- **NIST-API encodings are unique**. -/
theorem encodeSm_of_decodeSm (C : EncChoices) (sm salt msg : List UInt8) (s2 : List ℤ)
    (h : decodeSm C sm = some (salt, msg, s2)) : encodeSm C salt msg s2 = some sm := by
  match sm, h with
  | [], h => simp [decodeSm] at h
  | [_], h => simp [decodeSm] at h
  | a :: b :: t, h =>
    simp only [decodeSm] at h
    obtain ⟨⟨hs1, hs2⟩, h⟩ := guard_bind_some h
    obtain ⟨hg2, h⟩ := guard_bind_some h
    obtain ⟨s2', hdm, h⟩ := obind_eq_some.mp h
    cases h
    obtain ⟨hin, he, -⟩ := bitsBytes_of_decompressMin hdm
    have ha : a.toNat < 256 := UInt8.toNat_lt_size a
    have hb : b.toNat < 256 := UInt8.toNat_lt_size b
    generalize hsl : 256 * a.toNat + b.toNat = sl at hs1 hs2 hg2 he ⊢
    simp only [List.length_cons] at hs2 hg2 he ⊢
    obtain ⟨M, hM⟩ : ∃ M, t.length + 1 + 1 - sl = M + 2 := ⟨t.length - sl, by omega⟩
    rw [hM] at hg2 he
    rw [hM, Nat.add_comm 2 C.saltLen]
    simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons] at hg2 he ⊢
    obtain ⟨E', hE⟩ : ∃ E', t.drop M = (0x20 + C.logn).toUInt8 :: E' := by
      cases hT : t.drop M with
      | nil => rw [hT] at hg2; cases hg2
      | cons x E' => rw [hT] at hg2; cases hg2; exact ⟨E', rfl⟩
    rw [hE] at he
    have hEl : E'.length + 1 = sl := by
      have := congrArg List.length hE
      simp only [List.length_drop, List.length_cons] at this
      omega
    simp only [List.drop_succ_cons, List.drop_zero] at he
    simp only [encodeSm]
    refine guard_bind_eq (by rw [List.length_take]; omega) ?_
    rw [compressBits_eq_some.mpr ⟨hin, rfl⟩]
    simp only [Option.map_some, obind_some, he]
    refine guard_bind_eq (by change E'.length + 1 < 65536; omega) ?_
    have h1 : (sl / 256).toUInt8 = a := by
      rw [← hsl, show (256 * a.toNat + b.toNat) / 256 = a.toNat by omega, Nat.toUInt8_eq,
        UInt8.ofNat_toNat]
    have h2 : (sl % 256).toUInt8 = b := by
      rw [← hsl, show (256 * a.toNat + b.toNat) % 256 = b.toNat by omega, Nat.toUInt8_eq,
        UInt8.ofNat_toNat]
    change some _ = some _
    rw [hEl, h1, h2, ← hE, show t.take C.saltLen = (t.take M).take C.saltLen by
      rw [List.take_take, Nat.min_eq_left (by omega)]]
    simp only [List.cons_append, List.nil_append, List.take_append_drop]

/-! ### Round 3 -/

theorem length_data (b : ByteArray) : b.data.toList.length = b.size := by
  rw [Array.length_toList, ByteArray.size_data]

theorem byteArray_getElem! (b : ByteArray) (i : ℕ) : b[i]! = b.data.toList.getD i 0 := by
  by_cases hi : i < b.size
  · rw [getElem!_pos b i hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [length_data]; exact hi)]
    simp [ByteArray.getElem_eq_getElem_data]
  · rw [getElem!_neg b i hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [length_data]; omega)]
    rfl

theorem natBits_getD : ∀ {n i : ℕ} (v : ℕ), i < n → (natBits n v).getD i false =
    v.testBit (n - 1 - i)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, v, _ => by simp [Falcon.Concrete.natBits]
  | n + 1, i + 1, v, h => by
    rw [Falcon.Concrete.natBits, List.getD_cons_succ, natBits_getD v (by omega)]
    congr 1
    omega

theorem bytesToBits_getD : ∀ (l : List UInt8) (k : ℕ), k < 8 * l.length →
    (bytesToBits l).getD k false = (l.getD (k / 8) 0).toNat.testBit (7 - k % 8)
  | [], k, h => by simp at h
  | x :: l, k, h => by
    rw [bytesToBits_cons]
    by_cases hk : k < 8
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_byteBits]; omega),
        ← List.getD_eq_getElem?_getD, byteBits, natBits_getD _ hk, Nat.div_eq_of_lt hk,
        Nat.mod_eq_of_lt hk, List.getD_cons_zero]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_byteBits]; omega),
        ← List.getD_eq_getElem?_getD, length_byteBits,
        bytesToBits_getD l (k - 8) (by simp only [List.length_cons] at h; omega),
        show k / 8 = (k - 8) / 8 + 1 by omega, List.getD_cons_succ]
      congr 2
      omega

theorem bit_eq (b : ByteArray) (k : ℕ) (hk : k < 8 * b.size) :
    Round3.bit b k = if (bytesToBits b.data.toList).getD k false then 1 else 0 := by
  rw [bytesToBits_getD _ _ (by rw [length_data]; exact hk), Round3.bit, byteArray_getElem!,
    Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one
    ((b.data.toList.getD (k / 8) 0).toNat / 2 ^ (7 - k % 8)) with h | h <;> rw [h] <;> rfl

theorem natOfBits_append_single (l : List Bool) (x : Bool) :
    natOfBits (l ++ [x]) = 2 * natOfBits l + (if x then 1 else 0) := by
  induction l with
  | nil => cases x <;> rfl
  | cons y l ih =>
    simp only [List.cons_append, Falcon.Concrete.natOfBits, ih, List.length_append,
      List.length_singleton, pow_succ]
    cases y
    · simp
    · simp; ring

theorem bitsAt_succ (b : ByteArray) (p w : ℕ) :
    Round3.bitsAt b p (w + 1) = 2 * Round3.bitsAt b p w + Round3.bit b (p + w) := by
  unfold Round3.bitsAt
  rw [show w + 1 = Nat.succ w from rfl, List.range_succ, List.foldl_append]
  rfl

theorem bitsAt_eq (b : ByteArray) (p : ℕ) :
    ∀ w, p + w ≤ 8 * b.size →
      Round3.bitsAt b p w = natOfBits (((bytesToBits b.data.toList).drop p).take w)
  | 0, _ => by simp [Round3.bitsAt, Falcon.Concrete.natOfBits]
  | w + 1, h => by
    have hlen : (bytesToBits b.data.toList).length = 8 * b.size := by
      rw [length_bytesToBits, length_data]
    rw [bitsAt_succ, bitsAt_eq b p w (by omega), List.take_add_one, List.getElem?_drop,
      List.getElem?_eq_getElem (by omega), Option.toList_some, natOfBits_append_single,
      bit_eq b _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem chunks_eq_map_range (w : ℕ) : ∀ (k : ℕ) (bs : List Bool),
    chunks w k bs = (List.range k).map fun i => (bs.drop (w * i)).take w
  | 0, _ => rfl
  | k + 1, bs => by
    rw [chunks, chunks_eq_map_range w k, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.drop_drop]
    congr 2
    rw [Nat.mul_succ]
    omega

theorem map_toList_toArray {α : Type} (x : Option (List α)) :
    (List.toArray <$> x).map (·.toList) = x := by
  cases x <;> rfl

theorem mapM_bitsAt {β : Type} (φ : ℕ → Option β) (b : ByteArray) {p w cnt : ℕ}
    (hb : p + w * cnt ≤ 8 * b.size) :
    ((Array.range cnt).mapM fun i => φ (Round3.bitsAt b (p + w * i) w)).map (·.toList) =
      (chunks w cnt ((bytesToBits b.data.toList).drop p)).mapM fun c => φ (natOfBits c) := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_range, map_toList_toArray]
  refine (List.mapM_map (f := fun i => Round3.bitsAt b (p + w * i) w)).symm.trans
    (.trans ?_ (List.mapM_map (f := natOfBits)))
  rw [chunks_eq_map_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := Nat.mul_le_mul_left w (show i + 1 ≤ cnt from hi)
  rw [mul_add_one] at this
  simp only [Function.comp_apply, List.drop_drop]
  exact bitsAt_eq b _ _ (by omega)

theorem mapM_ite {α : Type} (f : α → ℕ) (q : ℕ) : ∀ l : List α,
    l.mapM (fun c => if f c < q then some (f c) else none) =
      if (l.map f).all (· < q) then some (l.map f) else none
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, mapM_ite f q l]
    by_cases ha : f a < q <;> by_cases hl : (l.map f).all (· < q) = true <;> simp [ha, hl]

theorem map_bind3 (X Y Z : Option (Array ℤ)) :
    (do let f ← X; let g ← Y; let F ← Z; pure (f, g, F)).map
        (fun k : Array ℤ × Array ℤ × Array ℤ =>
          (⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩ : SkData)) =
      (do let f ← X.map (·.toList); let g ← Y.map (·.toList); let F ← Z.map (·.toList)
          pure ⟨f, g, F, []⟩) := by
  cases X <;> cases Y <;> cases Z <;> rfl

theorem data_cons {b : ByteArray} {n : ℕ} (hs : b.size = n + 1) :
    ∃ x body, b.data.toList = x :: body ∧ b[0]! = x ∧ body.length = n := by
  cases hL : b.data.toList with
  | nil => have := length_data b; rw [hL] at this; simp at this; omega
  | cons x body =>
    refine ⟨x, body, rfl, by rw [byteArray_getElem!, hL]; rfl, ?_⟩
    have := length_data b
    rw [hL, List.length_cons] at this
    omega

/-- **At round 3 the public-key decoder is `Round3.decodePk`**. -/
theorem decodePk_round3 (b : ByteArray) :
    decodePk round3 b.data.toList = (Round3.decodePk b).map (·.toList) := by
  rw [Round3.decodePk, guard_bind_pos (show 1 ≤ 9 ∧ 9 ≤ 10 by decide)]
  simp only [show (2 : ℕ) ^ 9 = 512 from rfl, show 1 + (14 * 512 + 7) / 8 = 897 from rfl,
    show Nat.toUInt8 9 = 0x09 from rfl]
  by_cases hg : b.size = 897 ∧ b[0]! = 0x09
  · have hs : b.size = 897 := hg.1
    rw [guard_bind_pos hg]
    obtain ⟨x, body, hL, hx, hbl⟩ := data_cons hs
    rw [hg.2] at hx
    subst hx
    rw [mapM_bitsAt (fun v => if v < qN then some v else none) b (p := 8) (w := 14) (cnt := 512)
        (by omega), hL, bytesToBits_cons, List.drop_left' (length_byteBits _),
      mapM_ite natOfBits qN,
      show (0x09 :: body : List UInt8) = hdrBytes round3.pkHdr ++ body from rfl,
      decodePk_body round3 body (by rw [hbl]; rfl)
        (by rw [List.drop_of_length_le (by rw [length_bytesBits, hbl]; decide)]; rfl)]
    rfl
  · rw [guard_bind_neg hg]
    cases hd : decodePk round3 b.data.toList with
    | none => rfl
    | some H =>
      exfalso
      apply hg
      simp only [decodePk] at hd
      obtain ⟨body, hs, hd⟩ := obind_eq_some.mp hd
      obtain ⟨h1, -⟩ := guard_bind_some hd
      have e := eq_of_stripHdr hs
      have hsz := length_data b
      rw [e] at hsz
      refine ⟨?_, ?_⟩
      · rw [← hsz]; simp only [List.length_append]; rw [h1]; rfl
      · rw [byteArray_getElem!, e]; rfl

/-- **At round 3 the private-key decoder is `Round3.decodeSk`** (`tr` empty). -/
theorem decodeSk_round3 (b : ByteArray) :
    decodeSk round3 b.data.toList =
      (Round3.decodeSk b).map fun k => ⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩ := by
  rw [Round3.decodeSk, guard_bind_pos (show 1 ≤ 9 ∧ 9 ≤ 10 by decide)]
  simp only [show Round3.fgBitsOf 9 = 6 from rfl, show (2 : ℕ) ^ 9 = 512 from rfl,
    show 1 + (2 * 6 + 8) * 512 / 8 = 1281 from rfl,
    show Nat.toUInt8 (0x50 + 9) = 0x59 from rfl, show 2 * 6 * 512 = 12 * 512 from rfl]
  by_cases hg : b.size = 1281 ∧ b[0]! = 0x59
  · have hs : b.size = 1281 := hg.1
    rw [guard_bind_pos hg]
    rw [map_bind3]
    obtain ⟨x, body, hL, hx, hbl⟩ := data_cons hs
    rw [hg.2] at hx
    subst hx
    have e1 : (Round3.signedPoly b 8 6 512).map (·.toList) =
        signedFields .msbFirst 6 512 (bytesToBits body) := by
      rw [Round3.signedPoly, mapM_bitsAt (Round3.signedOf 6) b (by omega), hL, bytesToBits_cons,
        List.drop_left' (length_byteBits _)]
      rfl
    have e2 : (Round3.signedPoly b (8 + 6 * 512) 6 512).map (·.toList) =
        signedFields .msbFirst 6 512 ((bytesToBits body).drop (6 * 512)) := by
      rw [Round3.signedPoly, mapM_bitsAt (Round3.signedOf 6) b (by omega), hL, bytesToBits_cons,
        ← List.drop_drop, List.drop_left' (length_byteBits _)]
      rfl
    have e3 : (Round3.signedPoly b (8 + 12 * 512) 8 512).map (·.toList) =
        signedFields .msbFirst 8 512 ((bytesToBits body).drop (12 * 512)) := by
      rw [Round3.signedPoly, mapM_bitsAt (Round3.signedOf 8) b (by omega), hL, bytesToBits_cons,
        ← List.drop_drop, List.drop_left' (length_byteBits _)]
      rfl
    rw [e1, e2, e3, hL]
    have hz : ((bytesBits round3.order body).drop round3.skBits).all (· == false) = true := by
      rw [List.drop_of_length_le (by rw [length_bytesBits, hbl]; decide)]; rfl
    rw [show (0x59 :: body : List UInt8) = hdrBytes round3.skHdr ++ body from rfl]
    simp only [decodeSk, stripHdr_hdrBytes, obind_some,
      guard_bind_pos (show body.length = (round3.skBits + 7) / 8 + round3.trLen by rw [hbl]; rfl),
      guard_bind_pos hz, List.take_of_length_le (show body.length ≤ (round3.skBits + 7) / 8 by
        rw [hbl]; decide),
      List.drop_of_length_le (show body.length ≤ (round3.skBits + 7) / 8 by rw [hbl]; decide)]
    rfl
  · rw [guard_bind_neg hg]
    cases hd : decodeSk round3 b.data.toList with
    | none => rfl
    | some H =>
      exfalso
      apply hg
      simp only [decodeSk] at hd
      obtain ⟨body, hs, hd⟩ := obind_eq_some.mp hd
      obtain ⟨h1, -⟩ := guard_bind_some hd
      have e := eq_of_stripHdr hs
      have hsz := length_data b
      rw [e] at hsz
      refine ⟨?_, ?_⟩
      · rw [← hsz]; simp only [List.length_append]; rw [h1]; rfl
      · rw [byteArray_getElem!, e]; rfl

end FalconPrecision.Exec.Codec
