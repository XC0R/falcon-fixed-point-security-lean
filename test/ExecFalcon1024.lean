import FalconPrecision.Exec.CodecKat
import FalconPrecision.Exec.Falcon1024Codec

/-! `FalconPrecision.Exec.Codec`, `.Verify` at Falcon-1024 (`round3_1024`, `round3V1024`) on
inputs built here: sizes and header bytes of the round-3 encodings (spec v1.2 §3.11.3-3.11.6,
Table 3.3), round trips and agreement with `Round3`'s decoders at `logn = 10`, the bound
`⌊β²⌋ = 70265242` on all 1024 coefficients, `verifyCoreChecked` on inputs of other lengths,
the decoders' range `1 ≤ logn ≤ 10`; the theorems added for Falcon-1024 depend only on the
standard axioms. -/

open FalconPrecision.Exec FalconPrecision.Exec.Codec

/-- A public key of degree 1024 with every coefficient in `[0, q)` used. -/
def h1024 : List ℕ := (List.range 1024).map fun i => i * 12 % 12289

/-- A private key of degree 1024: `f`, `g` in `[-15, 15]` (5 bits), `F` in `[-127, 127]`. -/
def k1024 : SkData :=
  ⟨(List.range 1024).map fun i => (i % 31 : ℤ) - 15,
    (List.range 1024).map fun i => (i * 7 % 31 : ℤ) - 15,
    (List.range 1024).map fun i => (i % 255 : ℤ) - 127, []⟩

/-- A signature value of degree 1024. -/
def s1024 : List ℤ := (List.range 1024).map fun i => (i % 41 : ℤ) - 20

-- sizes and headers: public key 1793 bytes (`0x0A`), private key 2305 (`0x5A`), signature 1280
-- (`0x3A`), signed-message header `0x2A`
/-- info: true -/
#guard_msgs in
#eval (encodePk round3_1024 h1024).length = 1793 &&
  (encodePk round3_1024 h1024).head? = some 0x0A &&
  (encodeSk round3_1024 k1024).length = 2305 && (encodeSk round3_1024 k1024).head? = some 0x5A &&
  (encodeSig round3_1024 ⟨List.replicate 40 7, s1024⟩).map List.length = some 1280 &&
  ((encodeSig round3_1024 ⟨List.replicate 40 7, s1024⟩).bind List.head?) = some 0x3A &&
  ((encodeSm round3_1024 (List.replicate 40 7) [1, 2] s1024).map fun sm => sm.getD 44 0) =
    some 0x2A

-- round trips, and the decoders agree with `Round3.decodePk`, `Round3.decodeSk` at `logn = 10`
/-- info: true -/
#guard_msgs in
#eval decodePk round3_1024 (encodePk round3_1024 h1024) = some h1024 &&
  (Round3.decodePk (toBA (encodePk round3_1024 h1024)) 10).map (·.toList) = some h1024 &&
  decodeSk round3_1024 (encodeSk round3_1024 k1024) = some k1024 &&
  (Round3.decodeSk (toBA (encodeSk round3_1024 k1024)) 10).map
    (fun k => (⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩ : SkData)) = some k1024 &&
  (encodeSig round3_1024 ⟨List.replicate 40 7, s1024⟩).bind (decodeSig round3_1024) =
    some ⟨List.replicate 40 7, s1024⟩ &&
  (encodeSm round3_1024 (List.replicate 40 7) [1, 2] s1024).bind (decodeSm round3_1024) =
    some (List.replicate 40 7, [1, 2], s1024)

-- `⌊β²⌋ = 70265242` over 1024 coefficients (`h = 0`, `s₂ = 0`, so `s₁ = c` centred): one value
-- `6144` is accepted at `round3V1024` and rejected at `round3V` (`6144² > 34034726`); `6144` at
-- coefficients 600 and 1000 is rejected (`2·6144² > 70265242`), `6144` and `1000` accepted
/-- info: true -/
#guard_msgs in
#eval
  let z := List.replicate 1024 0
  let c1 := (List.range 1024).map fun i => if i = 1000 then 6144 else 0
  let c2 := (List.range 1024).map fun i => if i = 600 ∨ i = 1000 then 6144 else 0
  let c3 := (List.range 1024).map fun i => if i = 600 then 1000 else if i = 1000 then 6144 else 0
  verifyCore round3V1024 z c1 (z.map Int.ofNat) 10 &&
    !verifyCore round3V (z.take 512) (6144 :: List.replicate 511 0) ((z.take 512).map Int.ofNat) &&
    !verifyCore round3V1024 z c2 (z.map Int.ofNat) 10 &&
    verifyCore round3V1024 z c3 (z.map Int.ofNat) 10

-- `verifyCoreChecked` accepts the accepted input above and rejects it with `c` padded or
-- truncated, `h` truncated or `s₂` padded, which `verifyCore` accepts
/-- info: true -/
#guard_msgs in
#eval
  let z := List.replicate 1024 0
  let c1 := (List.range 1024).map fun i => if i = 1000 then 6144 else 0
  let s := z.map Int.ofNat
  let V := round3V1024
  verifyCoreChecked V z c1 s 10 &&
    !verifyCoreChecked V z (c1 ++ [0]) s 10 && verifyCore V z (c1 ++ [0]) s 10 &&
    !verifyCoreChecked V z (c1.take 1001) s 10 && verifyCore V z (c1.take 1001) s 10 &&
    !verifyCoreChecked V (z.take 3) c1 s 10 && verifyCore V (z.take 3) c1 s 10 &&
    !verifyCoreChecked V z c1 (s ++ [5]) 10 && verifyCore V z c1 (s ++ [5]) 10

-- the round-3 decoders return `none` outside `1 ≤ logn ≤ 10` (correct lengths and headers for
-- `logn = 0` and `logn = 11`)
/-- info: true -/
#guard_msgs in
#eval (Round3.decodePk (toBA ([0x00] ++ List.replicate 2 0)) 0).isNone &&
  (Round3.decodePk (toBA ([0x0B] ++ List.replicate 3584 0)) 11).isNone &&
  (Round3.decodeSk (toBA ([0x50] ++ List.replicate 3 0)) 0).isNone &&
  (Round3.decodeSk (toBA ([0x5B] ++ List.replicate 4608 0)) 11).isNone &&
  (Round3.decodePk (toBA ([0x0A] ++ List.replicate 1792 0)) 10).isSome

-- the theorems added for Falcon-1024 use only the standard axioms
/--
info: 'FalconPrecision.Exec.Codec.decodePk_round3_1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodePk_round3_1024
/--
info: 'FalconPrecision.Exec.Codec.decodeSk_round3_1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeSk_round3_1024
/--
info: 'FalconPrecision.Exec.Codec.verifyCore_iffP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms verifyCore_iffP
/--
info: 'FalconPrecision.Exec.Codec.entryOkP_of' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms entryOkP_of
/--
info: 'FalconPrecision.Exec.Codec.entriesOkP_of' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms entriesOkP_of
/--
info: 'FalconPrecision.Exec.Codec.entryOkB_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms entryOkB_eq
/--
info: 'FalconPrecision.Exec.Codec.entryOkU_of' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms entryOkU_of
