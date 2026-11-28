import FalconPrecision.Exec.SignEquiv1024
import FalconPrecision.Exec.SignWitness1024
import FalconPrecision.Exec.CodecKat

/-! `FalconPrecision.Exec.SignEquiv1024`, `WitnessData1024`, `SignWitness1024` at Falcon-1024: the
inputs of the witnesses, table and tree comparisons, the sampler witnesses; axioms. The premises
`wit*B1024` cost 12 s to 3 min each when interpreted; they are evaluated in
`test/ExecEquivEval1024.lean` and `test/ExecEquivEval1024Sig.lean` (not `Axioms` roots), not
here. -/

open FalconPrecision.Exec FalconPrecision.Exec.Witness Round3

-- KAT entries 0 and 2: the keys decode, are NTRU keys; entries 0, 2, 70: `|c i| < q`
/-- info: true -/
#guard_msgs in
#eval ((ofHex wSk0_1024).bind (decodeKey · 10)).isSome &&
  ((ofHex wSk2_1024).bind (decodeKey · 10)).isSome && ntruB key0_1024 && ntruB key2_1024 &&
  wC0_1024.length == 1024 && wC2_1024.length == 1024 && wC70_1024.length == 1024 &&
  (wC0_1024 ++ wC2_1024 ++ wC70_1024).all fun x => decide (0 ≤ x ∧ x < 12289)

-- the stored hashed messages are `hashToPoint 1024` of the stored `nonce ‖ msg`
/-- info: true -/
#guard_msgs in
#eval (Codec.hashToPoint 1024 (Codec.hexL wHin0_1024)).map (·.map Int.ofNat) == some wC0_1024 &&
  (Codec.hashToPoint 1024 (Codec.hexL wHin2_1024)).map (·.map Int.ofNat) == some wC2_1024 &&
  (Codec.hashToPoint 1024 (Codec.hexL wHin70_1024)).map (·.map Int.ofNat) == some wC70_1024

-- stored constants at 64 bits, levels `≤ 9`: ties to even, half up and half away give the same
-- tables; floor does not; the stored `σ1024q` is the same under all four
/-- info: (true, true, false) -/
#guard_msgs in
#eval (tabEqBAN 10 .halfEven .halfUp 64, tabEqBAN 10 .halfEven .halfAway 64,
  tabEqBAN 10 .halfEven .floor 64)

/-- info: (true, true, true) -/
#guard_msgs in
#eval (decide ((Fx.ofRat .halfEven σ1024q : Fx 64) = Fx.ofRat .halfUp σ1024q),
  decide ((Fx.ofRat .halfEven σ1024q : Fx 64) = Fx.ofRat .halfAway σ1024q),
  decide ((Fx.ofRat .halfEven σ1024q : Fx 64) = Fx.ofRat .floor σ1024q))

-- stored trees of key 0 at `xn = 32`: `dm` and `root` do not change them (`signMsgX_store1024`)
/-- info: (true, true) -/
#guard_msgs in
#eval ((storeCA { cW1024 with xn := 32 } key0_1024 σ1024q).eqB
    (storeCA { cW1024 with xn := 32, x := { cW1024.x with dm := .invMul } } key0_1024 σ1024q),
  (storeCA { cW1024 with xn := 32 } key0_1024 σ1024q).eqB
    (storeCA { cW1024 with xn := 32, x := { cW1024.x with root := .ntru } } key0_1024 σ1024q))

-- the sampler witnesses at `falcon1024S`: outputs
/-- info: (-16, -17, -18, 0) -/
#guard_msgs in
#eval (Id.run ((sampDP falcon1024S [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
    ⟨33582297586188238716⟩ ⟨0⟩).run' {}),
  Id.run ((sampDP falcon1024S [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b79⟩
    ⟨33582297586188238716⟩ ⟨0⟩).run' {}),
  Id.run ((sampDP falcon1024S [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
    ⟨23949045057228157292⟩ ⟨0⟩).run' {}),
  Id.run ((sampDP falcon1024S [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, true, .b72⟩
    ⟨23949045057228157292⟩ ⟨0⟩).run' {}))

-- `σ̄` of the sampler witnesses lies in `[σmin, σmax]` at Falcon-1024; `σ̄ - 2⁻⁶⁴` of
-- `samp_shift1024` does not
/-- info: (true, true, false) -/
#guard_msgs in
#eval (inRangeB falcon1024S ⟨33582297586188238716⟩, inRangeB falcon1024S ⟨23949045057228157292⟩,
  inRangeB falcon1024S ⟨23949045057228157291⟩)

/-! ## Axioms -/

/--
info: 'FalconPrecision.Exec.signX_congrN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_congrN

/--
info: 'FalconPrecision.Exec.accX_congrP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accX_congrP

/--
info: 'FalconPrecision.Exec.signMsgX_congrP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_congrP

/--
info: 'FalconPrecision.Exec.signX_rcN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_rcN

/--
info: 'FalconPrecision.Exec.fftC_rc_congrN' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fftC_rc_congrN

/--
info: 'FalconPrecision.Exec.splitC_rc_congrN' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms splitC_rc_congrN

/--
info: 'FalconPrecision.Exec.ldlC_rc_congrP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ldlC_rc_congrP

/--
info: 'FalconPrecision.Exec.expandC_rc_congrP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandC_rc_congrP

/--
info: 'FalconPrecision.Exec.signMsgX_rcP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_rcP

/--
info: 'FalconPrecision.Exec.signMsgX_storeP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_storeP

/--
info: 'FalconPrecision.Exec.signMsgX_with_capP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_with_capP

/--
info: 'FalconPrecision.Exec.signMsgX_cap_addP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_cap_addP

/--
info: 'FalconPrecision.Exec.signLoopX_oneP' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signLoopX_oneP

/--
info: 'FalconPrecision.Exec.signXA_eqP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signXA_eqP

/--
info: 'FalconPrecision.Exec.signX_congr1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_congr1024

/--
info: 'FalconPrecision.Exec.accX_congr1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accX_congr1024

/--
info: 'FalconPrecision.Exec.signMsgX_congr1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_congr1024

/--
info: 'FalconPrecision.Exec.signMsgX_word1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_word1024

/--
info: 'FalconPrecision.Exec.signMsgX_32_64_1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_32_64_1024

/--
info: 'FalconPrecision.Exec.signMsgZ_word1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgZ_word1024

/--
info: 'FalconPrecision.Exec.signMsgZ_32_64_1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgZ_32_64_1024

/--
info: 'FalconPrecision.Exec.signX_rc1024' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_rc1024

/--
info: 'FalconPrecision.Exec.fftC_rc_congr1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fftC_rc_congr1024

/--
info: 'FalconPrecision.Exec.splitC_rc_congr1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms splitC_rc_congr1024

/--
info: 'FalconPrecision.Exec.ldlC_rc_congr1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ldlC_rc_congr1024

/--
info: 'FalconPrecision.Exec.expandC_rc_congr1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandC_rc_congr1024

/--
info: 'FalconPrecision.Exec.signMsgX_rc1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_rc1024

/--
info: 'FalconPrecision.Exec.signMsgX_store1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_store1024

/--
info: 'FalconPrecision.Exec.signMsgX_cap_add1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_cap_add1024

/--
info: 'FalconPrecision.Exec.Witness.attDAP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms attDAP_eq

/--
info: 'FalconPrecision.Exec.Witness.attDcAP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms attDcAP_eq

/--
info: 'FalconPrecision.Exec.Witness.msgDAP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms msgDAP_eq

/--
info: 'FalconPrecision.Exec.Witness.accXAP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accXAP_eq

/--
info: 'FalconPrecision.Exec.Witness.tabEqBAN_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tabEqBAN_eq

/--
info: 'FalconPrecision.Exec.Witness.samp_base1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samp_base1024

/--
info: 'FalconPrecision.Exec.Witness.samp_shift1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samp_shift1024

/--
info: 'FalconPrecision.Exec.Witness.wit_word_mf1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_word_mf1024

/--
info: 'FalconPrecision.Exec.Witness.wit_target1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_target1024

/--
info: 'FalconPrecision.Exec.Witness.wit_dm1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_dm1024

/--
info: 'FalconPrecision.Exec.Witness.wit_root1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_root1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_up1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_up1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_away1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_away1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_floor1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_floor1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rc_floor1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rc_floor1024

/--
info: 'FalconPrecision.Exec.Witness.wit_qinv1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_qinv1024

/--
info: 'FalconPrecision.Exec.Witness.wit_centre1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_centre1024

/--
info: 'FalconPrecision.Exec.Witness.wit_salt1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_salt1024

/--
info: 'FalconPrecision.Exec.Witness.wit_cap1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_cap1024

/--
info: 'FalconPrecision.Exec.Witness.wit_word_mf_none1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_word_mf_none1024

/--
info: 'FalconPrecision.Exec.Witness.wit_word_mf_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_word_mf_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_target_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_target_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_dm_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_dm_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_root_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_root_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_up_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_up_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_away_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_away_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_floor_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_floor_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_rc_floor_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rc_floor_sig1024

/--
info: 'FalconPrecision.Exec.Witness.wit_qinv_sig1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_qinv_sig1024
