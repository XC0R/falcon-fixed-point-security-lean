import FalconPrecision.Exec.SignEquiv
import FalconPrecision.Exec.SignWordHop
import FalconPrecision.Exec.SignWitness

/-! `FalconPrecision.Exec.SignEquiv`, `SignWordHop`, `WitnessData`, `SignWitness`: the inputs of the
witnesses, table and tree comparisons, the sampler witnesses; axioms. The premises `wit*B` of the
attempt and signer witnesses (`wit_*`) cost seconds each when interpreted; they are evaluated in
`test/ExecEquivEval.lean` (not an `Axioms` root), not here. -/

open FalconPrecision.Exec FalconPrecision.Exec.Witness Round3

-- KAT entries 0 and 70: the keys decode, are NTRU keys, `|c i| < q`
/-- info: true -/
#guard_msgs in
#eval ((ofHex wSk0).bind decodeKey).isSome && ((ofHex wSk70).bind decodeKey).isSome &&
  ntruB key0 && ntruB key70 && wC0.length == 512 && wC70.length == 512 &&
  (wC0 ++ wC70).all fun x => decide (0 ≤ x ∧ x < 12289)

-- stored constants at 64 bits: ties to even, half up and half away give the same tables and the
-- same `σ`; floor does not
/-- info: (true, true, false) -/
#guard_msgs in
#eval (tabEqBA .halfEven .halfUp 64, tabEqBA .halfEven .halfAway 64, tabEqBA .halfEven .floor 64)

/-- info: (true, true, false) -/
#guard_msgs in
#eval (decide ((Fx.ofRat .halfEven σ512q : Fx 64) = Fx.ofRat .halfUp σ512q),
  decide ((Fx.ofRat .halfEven σ512q : Fx 64) = Fx.ofRat .halfAway σ512q),
  decide ((Fx.ofRat .halfEven σ512q : Fx 64) = Fx.ofRat .floor σ512q))

-- stored trees of key 0 at `xn = 32`: `dm` and `root` do not change them (`signMsgX_store`)
/-- info: (true, true) -/
#guard_msgs in
#eval ((storeCA { cW with xn := 32 } key0).eqB
    (storeCA { cW with xn := 32, x := { cW.x with dm := .invMul } } key0),
  (storeCA { cW with xn := 32 } key0).eqB
    (storeCA { cW with xn := 32, x := { cW.x with root := .ntru } } key0))

-- the sampler witnesses: outputs
/-- info: (-16, -17, -18, 0) -/
#guard_msgs in
#eval (Id.run ((sampD [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
    ⟨33582297586188238716⟩ ⟨0⟩).run' {}),
  Id.run ((sampD [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b79⟩
    ⟨33582297586188238716⟩ ⟨0⟩).run' {}),
  Id.run ((sampD [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
    ⟨23571871177321116846⟩ ⟨0⟩).run' {}),
  Id.run ((sampD [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, true, .b72⟩
    ⟨23571871177321116846⟩ ⟨0⟩).run' {}))

-- `σ̄` of the sampler witnesses lies in SamplerZ's range `[σmin, σmax]`
/-- info: (true, true) -/
#guard_msgs in
#eval (inRangeB falcon512S ⟨33582297586188238716⟩, inRangeB falcon512S ⟨23571871177321116846⟩)

/-! ## Axioms -/

/--
info: 'FalconPrecision.Exec.signX_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_congr

/--
info: 'FalconPrecision.Exec.signMsgX_congr' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_congr

/--
info: 'FalconPrecision.Exec.signMsgX_word' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_word

/--
info: 'FalconPrecision.Exec.signMsgX_32_64' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_32_64

/--
info: 'FalconPrecision.Exec.clampS_samplerZ' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms clampS_samplerZ

/--
info: 'FalconPrecision.Exec.signMsgZ_word' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgZ_word

/--
info: 'FalconPrecision.Exec.signMsgZ_32_64' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgZ_32_64

/--
info: 'FalconPrecision.Exec.falcon512_exec_word_sampler_vs_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_exec_word_sampler_vs_true

/--
info: 'FalconPrecision.Exec.signX_rc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_rc

/--
info: 'FalconPrecision.Exec.expandC_rc_congr' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandC_rc_congr

/--
info: 'FalconPrecision.Exec.signMsgX_rc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_rc

/--
info: 'FalconPrecision.Exec.signMsgX_store' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_store

/--
info: 'FalconPrecision.Exec.loopR_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms loopR_add

/--
info: 'FalconPrecision.Exec.signMsgX_cap_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signMsgX_cap_add

/--
info: 'FalconPrecision.Exec.signLoopX_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signLoopX_one

/--
info: 'FalconPrecision.Exec.Witness.attDA_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms attDA_eq

/--
info: 'FalconPrecision.Exec.Witness.attDcA_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms attDcA_eq

/--
info: 'FalconPrecision.Exec.Witness.msgDA_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms msgDA_eq

/--
info: 'FalconPrecision.Exec.Witness.tabEqBA_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tabEqBA_eq

/--
info: 'FalconPrecision.Exec.Witness.samp_base' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samp_base

/--
info: 'FalconPrecision.Exec.Witness.samp_shift' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samp_shift

/--
info: 'FalconPrecision.Exec.Witness.wit_word_mf' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_word_mf

/--
info: 'FalconPrecision.Exec.Witness.wit_target' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_target

/--
info: 'FalconPrecision.Exec.Witness.wit_dm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_dm

/--
info: 'FalconPrecision.Exec.Witness.wit_root' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_root

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_up' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_up

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_away' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_away

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_floor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_floor

/--
info: 'FalconPrecision.Exec.Witness.wit_rc_floor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rc_floor

/--
info: 'FalconPrecision.Exec.Witness.wit_qinv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_qinv

/--
info: 'FalconPrecision.Exec.Witness.wit_centre' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_centre

/--
info: 'FalconPrecision.Exec.Witness.wit_salt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_salt

/--
info: 'FalconPrecision.Exec.Witness.wit_cap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_cap

/--
info: 'FalconPrecision.Exec.Witness.wit_word_mf_none' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_word_mf_none

/--
info: 'FalconPrecision.Exec.Witness.wit_word_mf_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_word_mf_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_target_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_target_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_dm_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_dm_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_root_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_root_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_up_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_up_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_away_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_away_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_rm_floor_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rm_floor_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_rc_floor_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_rc_floor_sig

/--
info: 'FalconPrecision.Exec.Witness.wit_qinv_sig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wit_qinv_sig
