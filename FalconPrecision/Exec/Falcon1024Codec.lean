/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Codec

/-! # The round-3 decoders at Falcon-1024

At `round3_1024` (round 3, v1.2, `n = 1024`) the decoders of `Codec` agree with
`Round3.decodePk`/`Round3.decodeSk` at `logn = 10` (§3.11.4-5: public key 1793 bytes, header
`0x0A`; private key 2305 bytes, header `0x5A`, `f`, `g` over 5 bits). -/

@[expose] public section

namespace FalconPrecision.Exec.Codec

open Falcon.Concrete (natOfBits bytesToBits)
open Round3 (qN)

/-- **At round 3, Falcon-1024, the public-key decoder is `Round3.decodePk` at `logn = 10`**. -/
theorem decodePk_round3_1024 (b : ByteArray) :
    decodePk round3_1024 b.data.toList = (Round3.decodePk b 10).map (·.toList) := by
  rw [Round3.decodePk, guard_bind_pos (show 1 ≤ 10 ∧ 10 ≤ 10 by decide)]
  simp only [show (2 : ℕ) ^ 10 = 1024 from rfl, show 1 + (14 * 1024 + 7) / 8 = 1793 from rfl,
    show Nat.toUInt8 10 = 0x0A from rfl]
  by_cases hg : b.size = 1793 ∧ b[0]! = 0x0A
  · have hs : b.size = 1793 := hg.1
    rw [guard_bind_pos hg]
    obtain ⟨x, body, hL, hx, hbl⟩ := data_cons hs
    rw [hg.2] at hx
    subst hx
    rw [mapM_bitsAt (fun v => if v < qN then some v else none) b (p := 8) (w := 14) (cnt := 1024)
        (by omega), hL, bytesToBits_cons, List.drop_left' (length_byteBits _),
      mapM_ite natOfBits qN,
      show (0x0A :: body : List UInt8) = hdrBytes round3_1024.pkHdr ++ body from rfl,
      decodePk_body round3_1024 body (by rw [hbl]; rfl)
        (by rw [List.drop_of_length_le (by rw [length_bytesBits, hbl]; decide)]; rfl)]
    rfl
  · rw [guard_bind_neg hg]
    cases hd : decodePk round3_1024 b.data.toList with
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

/-- **At round 3, Falcon-1024, the private-key decoder is `Round3.decodeSk` at `logn = 10`**
(`tr` empty). -/
theorem decodeSk_round3_1024 (b : ByteArray) :
    decodeSk round3_1024 b.data.toList =
      (Round3.decodeSk b 10).map fun k => ⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩ := by
  rw [Round3.decodeSk, guard_bind_pos (show 1 ≤ 10 ∧ 10 ≤ 10 by decide)]
  simp only [show Round3.fgBitsOf 10 = 5 from rfl, show (2 : ℕ) ^ 10 = 1024 from rfl,
    show 1 + (2 * 5 + 8) * 1024 / 8 = 2305 from rfl,
    show Nat.toUInt8 (0x50 + 10) = 0x5A from rfl, show 2 * 5 * 1024 = 10 * 1024 from rfl]
  by_cases hg : b.size = 2305 ∧ b[0]! = 0x5A
  · have hs : b.size = 2305 := hg.1
    rw [guard_bind_pos hg]
    rw [map_bind3]
    obtain ⟨x, body, hL, hx, hbl⟩ := data_cons hs
    rw [hg.2] at hx
    subst hx
    have e1 : (Round3.signedPoly b 8 5 1024).map (·.toList) =
        signedFields .msbFirst 5 1024 (bytesToBits body) := by
      rw [Round3.signedPoly, mapM_bitsAt (Round3.signedOf 5) b (by omega), hL, bytesToBits_cons,
        List.drop_left' (length_byteBits _)]
      rfl
    have e2 : (Round3.signedPoly b (8 + 5 * 1024) 5 1024).map (·.toList) =
        signedFields .msbFirst 5 1024 ((bytesToBits body).drop (5 * 1024)) := by
      rw [Round3.signedPoly, mapM_bitsAt (Round3.signedOf 5) b (by omega), hL, bytesToBits_cons,
        ← List.drop_drop, List.drop_left' (length_byteBits _)]
      rfl
    have e3 : (Round3.signedPoly b (8 + 10 * 1024) 8 1024).map (·.toList) =
        signedFields .msbFirst 8 1024 ((bytesToBits body).drop (10 * 1024)) := by
      rw [Round3.signedPoly, mapM_bitsAt (Round3.signedOf 8) b (by omega), hL, bytesToBits_cons,
        ← List.drop_drop, List.drop_left' (length_byteBits _)]
      rfl
    rw [e1, e2, e3, hL]
    have hz : ((bytesBits round3_1024.order body).drop round3_1024.skBits).all (· == false) =
        true := by
      rw [List.drop_of_length_le (by rw [length_bytesBits, hbl]; decide)]; rfl
    rw [show (0x5A :: body : List UInt8) = hdrBytes round3_1024.skHdr ++ body from rfl]
    simp only [decodeSk, stripHdr_hdrBytes, obind_some,
      guard_bind_pos (show body.length = (round3_1024.skBits + 7) / 8 + round3_1024.trLen by
        rw [hbl]; rfl),
      guard_bind_pos hz, List.take_of_length_le (show body.length ≤ (round3_1024.skBits + 7) / 8 by
        rw [hbl]; decide),
      List.drop_of_length_le (show body.length ≤ (round3_1024.skBits + 7) / 8 by rw [hbl]; decide)]
    rfl
  · rw [guard_bind_neg hg]
    cases hd : decodeSk round3_1024 b.data.toList with
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
