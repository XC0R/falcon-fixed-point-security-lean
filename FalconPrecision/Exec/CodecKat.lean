/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Verify

/-! # The checks run on each round-3 KAT entry

An entry of `falcon512-KAT.rsp` (round 3) as hexadecimal strings, and `EntryOk`: at the round-3
instance its `pk`, `sk`, `sm` decode and re-encode byte for byte, the decoders agree with
`Round3.decodePk`/`Round3.decodeSk`, the message in `sm` is `msg`, the fingerprint `fp` of
`HashToPoint(r ‖ m)` equals the one computed outside Lean (Python `hashlib`), `s₂` re-encoded as a
detached signature (§3.11.3) verifies, `openSm` accepts `sm` with message `msg`, and rejects `sm`
with one bit flipped in the salt, in the message, or in the first byte of the compressed `s₂`.
`entryOkB` decides it; `entryOk_of` turns `entryOkB e = true` into `EntryOk e`. -/

@[expose] public section

namespace FalconPrecision.Exec.Codec

/-- A KAT entry: hex strings, and the Python fingerprint of the hashed point. -/
structure KatEntry where
  count : ℕ
  msg : String
  pk : String
  sk : String
  sm : String
  fpC : ℕ

/-- The bytes of a hex string (empty if malformed). -/
def hexL (s : String) : List UInt8 := ((Round3.ofHex s).map (·.data.toList)).getD []

/-- `Σ cᵢ·2^(16i) mod (2⁶¹ - 1)`: a linear checksum, not a hash (`+d` at `i` and `-d` at `i + 61`
cancel). -/
def fp (c : List ℕ) : ℕ := c.foldr (fun x a => (a * 65536 + x) % (2 ^ 61 - 1)) 0

/-- Byte `i` with its lowest bit flipped. -/
def flip (l : List UInt8) (i : ℕ) : List UInt8 := l.set i (l.getD i 0 ^^^ 1)

/-- The index of the first byte of the compressed `s₂` in `sm` (after the header byte). -/
def sPos (sm : List UInt8) : ℕ := sm.length - (256 * (sm.getD 0 0).toNat + (sm.getD 1 0).toNat) + 1

/-- The checks on one entry. -/
structure EntryOk (e : KatEntry) : Prop where
  pk : (decodePk round3 (hexL e.pk)).map (encodePk round3) = some (hexL e.pk)
  sk : (decodeSk round3 (hexL e.sk)).map (encodeSk round3) = some (hexL e.sk)
  pkR3 : decodePk round3 (hexL e.pk) =
    ((Round3.ofHex e.pk).bind Round3.decodePk).map (·.toList)
  skR3 : decodeSk round3 (hexL e.sk) = ((Round3.ofHex e.sk).bind Round3.decodeSk).map
    fun k => ⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩
  sm : (decodeSm round3 (hexL e.sm)).bind (fun x => encodeSm round3 x.1 x.2.1 x.2.2) =
    some (hexL e.sm)
  msg : (decodeSm round3 (hexL e.sm)).map (·.2.1) = some (hexL e.msg)
  htp : ((decodeSm round3 (hexL e.sm)).bind fun x => hashToPoint 512 (x.1 ++ x.2.1)).map fp =
    some e.fpC
  detached : ((decodeSm round3 (hexL e.sm)).bind fun x => encodeSig round3 ⟨x.1, x.2.2⟩).map
    (verifySig round3V (hexL e.pk) (hexL e.msg)) = some true
  accept : openSm round3V (hexL e.pk) (hexL e.sm) = some (hexL e.msg)
  rejSalt : openSm round3V (hexL e.pk) (flip (hexL e.sm) 2) = none
  rejMsg : openSm round3V (hexL e.pk) (flip (hexL e.sm) 42) = none
  rejS : openSm round3V (hexL e.pk) (flip (hexL e.sm) (sPos (hexL e.sm))) = none

/-- `EntryOk`, decided. -/
def entryOkB (e : KatEntry) : Bool :=
  let pk := hexL e.pk
  let sk := hexL e.sk
  let sm := hexL e.sm
  let msg := hexL e.msg
  let d := decodeSm round3 sm
  decide ((decodePk round3 pk).map (encodePk round3) = some pk) &&
  decide ((decodeSk round3 sk).map (encodeSk round3) = some sk) &&
  decide (decodePk round3 pk = ((Round3.ofHex e.pk).bind Round3.decodePk).map (·.toList)) &&
  decide (decodeSk round3 sk = ((Round3.ofHex e.sk).bind Round3.decodeSk).map
    fun k => ⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩) &&
  decide (d.bind (fun x => encodeSm round3 x.1 x.2.1 x.2.2) = some sm) &&
  decide (d.map (·.2.1) = some msg) &&
  decide ((d.bind fun x => hashToPoint 512 (x.1 ++ x.2.1)).map fp = some e.fpC) &&
  decide ((d.bind fun x => encodeSig round3 ⟨x.1, x.2.2⟩).map (verifySig round3V pk msg) =
    some true) &&
  decide (openSm round3V pk sm = some msg) &&
  decide (openSm round3V pk (flip sm 2) = none) &&
  decide (openSm round3V pk (flip sm 42) = none) &&
  decide (openSm round3V pk (flip sm (sPos sm)) = none)

/-- `entryOkB e = true` gives `EntryOk e`. -/
theorem entryOk_of {e : KatEntry} (h : entryOkB e = true) : EntryOk e := by
  simp only [entryOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- All entries of a list pass, if `l.all entryOkB` (true by `#eval` in the slices). -/
theorem entriesOk_of {l : List KatEntry} (h : l.all entryOkB = true) : ∀ e ∈ l, EntryOk e :=
  fun e he => entryOk_of (List.all_eq_true.mp h e he)

end FalconPrecision.Exec.Codec
