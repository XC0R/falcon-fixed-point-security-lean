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
`entryOkB` decides it; `entryOk_of` turns `entryOkB e = true` into `EntryOk e`.

`EntryOkP V`, `entryOkBP V`, `entryOkP_of`: the same checks at any `VerChoices` `V` (degree
`2^V.enc.logn`, the decoders compared with `Round3`'s at `logn = V.enc.logn`, the message flipped
at its first byte `2 + V.enc.saltLen`); `EntryOk`, `entryOkB` are the instance `round3V`
(`entryOkB_eq`), `round3V1024` is the Falcon-1024 instance for the entries of
`falcon1024-KAT.rsp`. `entryOkBU V`: the checks at `V.unpadded` and no detached encoding at `V`,
for an entry whose compressed `s₂` does not fit the padded signature. -/

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

/-- The checks on one entry at the verification choices `V`. -/
structure EntryOkP (V : VerChoices) (e : KatEntry) : Prop where
  pk : (decodePk V.enc (hexL e.pk)).map (encodePk V.enc) = some (hexL e.pk)
  sk : (decodeSk V.enc (hexL e.sk)).map (encodeSk V.enc) = some (hexL e.sk)
  pkR3 : decodePk V.enc (hexL e.pk) =
    ((Round3.ofHex e.pk).bind (Round3.decodePk · V.enc.logn)).map (·.toList)
  skR3 : decodeSk V.enc (hexL e.sk) = ((Round3.ofHex e.sk).bind (Round3.decodeSk · V.enc.logn)).map
    fun k => ⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩
  sm : (decodeSm V.enc (hexL e.sm)).bind (fun x => encodeSm V.enc x.1 x.2.1 x.2.2) =
    some (hexL e.sm)
  msg : (decodeSm V.enc (hexL e.sm)).map (·.2.1) = some (hexL e.msg)
  htp : ((decodeSm V.enc (hexL e.sm)).bind fun x => hashToPoint V.enc.n (x.1 ++ x.2.1)).map fp =
    some e.fpC
  detached : ((decodeSm V.enc (hexL e.sm)).bind fun x => encodeSig V.enc ⟨x.1, x.2.2⟩).map
    (verifySig V (hexL e.pk) (hexL e.msg)) = some true
  accept : openSm V (hexL e.pk) (hexL e.sm) = some (hexL e.msg)
  rejSalt : openSm V (hexL e.pk) (flip (hexL e.sm) 2) = none
  rejMsg : openSm V (hexL e.pk) (flip (hexL e.sm) (2 + V.enc.saltLen)) = none
  rejS : openSm V (hexL e.pk) (flip (hexL e.sm) (sPos (hexL e.sm))) = none

/-- `EntryOkP V`, decided. -/
def entryOkBP (V : VerChoices) (e : KatEntry) : Bool :=
  let pk := hexL e.pk
  let sk := hexL e.sk
  let sm := hexL e.sm
  let msg := hexL e.msg
  let d := decodeSm V.enc sm
  decide ((decodePk V.enc pk).map (encodePk V.enc) = some pk) &&
  decide ((decodeSk V.enc sk).map (encodeSk V.enc) = some sk) &&
  decide (decodePk V.enc pk =
    ((Round3.ofHex e.pk).bind (Round3.decodePk · V.enc.logn)).map (·.toList)) &&
  decide (decodeSk V.enc sk = ((Round3.ofHex e.sk).bind (Round3.decodeSk · V.enc.logn)).map
    fun k => ⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩) &&
  decide (d.bind (fun x => encodeSm V.enc x.1 x.2.1 x.2.2) = some sm) &&
  decide (d.map (·.2.1) = some msg) &&
  decide ((d.bind fun x => hashToPoint V.enc.n (x.1 ++ x.2.1)).map fp = some e.fpC) &&
  decide ((d.bind fun x => encodeSig V.enc ⟨x.1, x.2.2⟩).map (verifySig V pk msg) =
    some true) &&
  decide (openSm V pk sm = some msg) &&
  decide (openSm V pk (flip sm 2) = none) &&
  decide (openSm V pk (flip sm (2 + V.enc.saltLen)) = none) &&
  decide (openSm V pk (flip sm (sPos sm)) = none)

/-- `entryOkBP V e = true` gives `EntryOkP V e`. -/
theorem entryOkP_of {V : VerChoices} {e : KatEntry} (h : entryOkBP V e = true) : EntryOkP V e := by
  simp only [entryOkBP, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- All entries of a list pass at `V`, if `l.all (entryOkBP V)` (true by `#eval` in the
slices). -/
theorem entriesOkP_of {V : VerChoices} {l : List KatEntry} (h : l.all (entryOkBP V) = true) :
    ∀ e ∈ l, EntryOkP V e :=
  fun e he => entryOkP_of (List.all_eq_true.mp h e he)

/-- `V` with unpadded detached signatures (`sigPad := .minimal`); the other checks of `EntryOkP`
do not depend on `sigPad`. -/
def VerChoices.unpadded (V : VerChoices) : VerChoices :=
  { V with enc := { V.enc with sigPad := .minimal } }

/-- The salt and `s₂` of the entry's `sm` have no detached encoding at `V.enc` (at `.fixed L`: the
compressed `s₂` does not fit, where Alg. 10 l. 10-11 restarts). -/
def NoSigEnc (V : VerChoices) (e : KatEntry) : Prop :=
  ((decodeSm V.enc (hexL e.sm)).bind fun x => encodeSig V.enc ⟨x.1, x.2.2⟩) = none

/-- `EntryOkP V.unpadded e ∧ NoSigEnc V e`, decided. -/
def entryOkBU (V : VerChoices) (e : KatEntry) : Bool :=
  entryOkBP V.unpadded e &&
    decide (((decodeSm V.enc (hexL e.sm)).bind fun x => encodeSig V.enc ⟨x.1, x.2.2⟩) = none)

/-- `entryOkBU V e = true` gives `EntryOkP V.unpadded e` and `NoSigEnc V e`. -/
theorem entryOkU_of {V : VerChoices} {e : KatEntry} (h : entryOkBU V e = true) :
    EntryOkP V.unpadded e ∧ NoSigEnc V e := by
  simp only [entryOkBU, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨entryOkP_of h.1, h.2⟩

/-- `entryOkB` is `entryOkBP` at `round3V`. -/
theorem entryOkB_eq (e : KatEntry) : entryOkB e = entryOkBP round3V e := rfl

end FalconPrecision.Exec.Codec
