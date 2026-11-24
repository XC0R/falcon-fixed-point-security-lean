import FalconPrecision.Exec.SignWitness

/-! Evaluation evidence for the premises of the attempt and signer witnesses `wit_*` of
`FalconPrecision.Exec.SignWitness`: each `wit*B` is `true` by `#eval` (the compiler's code, run by
Lean's interpreter), not by a kernel proof. Not an `Axioms` root (seconds per attempt pair); run
with `lake env lean test/ExecEquivEval.lean`. -/

open FalconPrecision.Exec.Witness

/-- info: true -/
#guard_msgs in
#eval witWordMfB

/-- info: true -/
#guard_msgs in
#eval witTargetB

/-- info: true -/
#guard_msgs in
#eval witDmB

/-- info: true -/
#guard_msgs in
#eval witRootB

/-- info: true -/
#guard_msgs in
#eval witRmUpB

/-- info: true -/
#guard_msgs in
#eval witRmAwayB

/-- info: true -/
#guard_msgs in
#eval witRmFloorB

/-- info: true -/
#guard_msgs in
#eval witRcFloorB

/-- info: true -/
#guard_msgs in
#eval witQinvB

/-- info: true -/
#guard_msgs in
#eval witCentreB

/-- info: true -/
#guard_msgs in
#eval witSaltB

/-- info: true -/
#guard_msgs in
#eval witCapB

/-- info: true -/
#guard_msgs in
#eval witWordMfSigB

/-- info: true -/
#guard_msgs in
#eval witTargetSigB

/-- info: true -/
#guard_msgs in
#eval witDmSigB

/-- info: true -/
#guard_msgs in
#eval witRootSigB

/-- info: true -/
#guard_msgs in
#eval witRmUpSigB

/-- info: true -/
#guard_msgs in
#eval witRmAwaySigB

/-- info: true -/
#guard_msgs in
#eval witRmFloorSigB

/-- info: true -/
#guard_msgs in
#eval witRcFloorSigB

/-- info: true -/
#guard_msgs in
#eval witQinvSigB
