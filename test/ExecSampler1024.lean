import FalconPrecision.Exec.SamplerHop1024
import FalconPrecision.Exec.SignWordHop1024

/-! `FalconPrecision.Exec.SamplerHop1024`, `SignWordHop1024`: the executable signer with the
executable SamplerZ at Falcon-1024 against exact Falcon; the theorems depend only on the standard
axioms. -/

open FalconPrecision.Exec

/--
info: 'FalconPrecision.Exec.exec_factor1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_factor1024

/--
info: 'FalconPrecision.Exec.embedS_exec1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embedS_exec1024

/--
info: 'FalconPrecision.Exec.pathSum_embedS1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_embedS1024

/--
info: 'FalconPrecision.Exec.pathSum_execZ1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_execZ1024

/--
info: 'FalconPrecision.Exec.exec_sampler_step1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_sampler_step1024

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true43' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true43

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true127' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true127

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true256' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true256

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true256_43' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true256_43

/--
info: 'FalconPrecision.Exec.falcon1024_exec_sampler_vs_true256_127' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_sampler_vs_true256_127

/--
info: 'FalconPrecision.Exec.exec_sampler_worlds_exist1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_sampler_worlds_exist1024

/--
info: 'FalconPrecision.Exec.clamp_samplerLoop1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms clamp_samplerLoop1024

/--
info: 'FalconPrecision.Exec.clampS_samplerZ1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms clampS_samplerZ1024

/--
info: 'FalconPrecision.Exec.execR_word1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms execR_word1024

/--
info: 'FalconPrecision.Exec.pathSum_embedR1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_embedR1024

/--
info: 'FalconPrecision.Exec.falcon1024_exec_word_sampler_vs_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_word_sampler_vs_true

/--
info: 'FalconPrecision.Exec.falcon1024_exec_word_sampler_vs_true256' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_exec_word_sampler_vs_true256
