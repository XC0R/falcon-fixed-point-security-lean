import FalconPrecision.Exec.SignWitness1024

/-! Evaluation evidence for the premises of the signer witnesses `wit_*_sig1024`,
`wit_word_mf_none1024` of `FalconPrecision.Exec.SignWitness1024`: each `wit*SigB1024` is `true` by
`#eval` (Lean's interpreter), not by a kernel proof. Not an `Axioms` root (about 23 s per signer
pair, 3 min for `witWordMfSigB1024`, whose 32.64 signer makes 27 attempts); run with
`lake env lean test/ExecEquivEval1024Sig.lean`. -/

open FalconPrecision.Exec.Witness

/-- info: true -/
#guard_msgs in
#eval witWordMfSigB1024

/-- info: true -/
#guard_msgs in
#eval witTargetSigB1024

/-- info: true -/
#guard_msgs in
#eval witDmSigB1024

/-- info: true -/
#guard_msgs in
#eval witRootSigB1024

/-- info: true -/
#guard_msgs in
#eval witRmUpSigB1024

/-- info: true -/
#guard_msgs in
#eval witRmAwaySigB1024

/-- info: true -/
#guard_msgs in
#eval witRmFloorSigB1024

/-- info: true -/
#guard_msgs in
#eval witRcFloorSigB1024

/-- info: true -/
#guard_msgs in
#eval witQinvSigB1024
