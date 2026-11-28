import FalconPrecision.Exec.SignWitness1024

/-! Evaluation evidence for the premises of the attempt witnesses `wit_*1024` (and `wit_salt1024`,
`wit_cap1024`) of `FalconPrecision.Exec.SignWitness1024`: each `wit*B1024` is `true` by `#eval` (the
compiler's code, run by Lean's interpreter), not by a kernel proof. Not an `Axioms` root (about
12 s per attempt pair at Falcon-1024); run with `lake env lean test/ExecEquivEval1024.lean`. The
signer premises are in `test/ExecEquivEval1024Sig.lean` (about 6 min; the two files are run
separately). -/

open FalconPrecision.Exec.Witness

/-- info: true -/
#guard_msgs in
#eval witWordMfB1024

/-- info: true -/
#guard_msgs in
#eval witTargetB1024

/-- info: true -/
#guard_msgs in
#eval witDmB1024

/-- info: true -/
#guard_msgs in
#eval witRootB1024

/-- info: true -/
#guard_msgs in
#eval witRmUpB1024

/-- info: true -/
#guard_msgs in
#eval witRmAwayB1024

/-- info: true -/
#guard_msgs in
#eval witRmFloorB1024

/-- info: true -/
#guard_msgs in
#eval witRcFloorB1024

/-- info: true -/
#guard_msgs in
#eval witQinvB1024

/-- info: true -/
#guard_msgs in
#eval witCentreB1024

/-- info: true -/
#guard_msgs in
#eval witSaltB1024

/-- info: true -/
#guard_msgs in
#eval witCapB1024
