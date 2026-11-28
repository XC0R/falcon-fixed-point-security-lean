import FalconPrecision.Exec.SampKeyCheck

/-! `FalconPrecision.Exec.SampKeyCheck`: keys passing `check` resp. `check1024` are `SampKey`s
resp. `SampKey1024`s, and the composed theorems on experiments over checked keys; the theorems
depend only on the standard axioms. -/

open FalconPrecision.Exec

/--
info: 'FalconPrecision.Exec.CTree.leavesB_of_okB' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CTree.leavesB_of_okB

/--
info: 'FalconPrecision.Exec.CheckedKey.leavesB_inRange' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CheckedKey.leavesB_inRange

/--
info: 'FalconPrecision.Exec.CheckedKey1024.leavesB_inRange' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CheckedKey1024.leavesB_inRange

/--
info: 'FalconPrecision.Exec.sampKeyEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampKeyEquiv

/--
info: 'FalconPrecision.Exec.sampKey1024Equiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampKey1024Equiv

/--
info: 'FalconPrecision.Exec.embedS_toSamp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embedS_toSamp

/--
info: 'FalconPrecision.Exec.pathSum_toSamp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_toSamp

/--
info: 'FalconPrecision.Exec.exec_toSamp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_toSamp

/--
info: 'FalconPrecision.Exec.embedS_toSamp1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embedS_toSamp1024

/--
info: 'FalconPrecision.Exec.pathSum_toSamp1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_toSamp1024

/--
info: 'FalconPrecision.Exec.exec_toSamp1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_toSamp1024

/--
info: 'FalconPrecision.Exec.falcon512_exec_sampler_vs_true_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_exec_sampler_vs_true_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true43_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true43_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true127_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true127_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true256_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true256_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true256_43_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true256_43_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true256_127_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true256_127_checked

/--
info: 'FalconPrecision.Exec.rKeyEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rKeyEquiv

/--
info: 'FalconPrecision.Exec.embedR_toR' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embedR_toR

/--
info: 'FalconPrecision.Exec.pathSum_toR' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_toR

/--
info: 'FalconPrecision.Exec.exec_toR' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_toR

/--
info: 'FalconPrecision.Exec.rKey1024Equiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rKey1024Equiv

/--
info: 'FalconPrecision.Exec.embedR_toR1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embedR_toR1024

/--
info: 'FalconPrecision.Exec.pathSum_toR1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_toR1024

/--
info: 'FalconPrecision.Exec.exec_toR1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_toR1024

/--
info: 'FalconPrecision.Exec.falcon512_exec_word_sampler_vs_true_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_exec_word_sampler_vs_true_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_word_sampler_vs_true_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_word_sampler_vs_true_checked

/--
info: 'FalconPrecision.Exec.falcon1024_exec_word_sampler_vs_true256_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_word_sampler_vs_true256_checked
