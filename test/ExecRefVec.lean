import FalconPrecision.Exec.RefVec1024

/-! `Exec.RefRun`, `.RefBall`, `.RefVec`, `.RefVecOut`, `.RefVec1024`: tape order (also depth 10),
slot exponents, a ball FFT of size 2, hull and widening on small balls, the tables of `opsBN 10`;
the generic lemmas, the soundness theorems at both sizes, the bridges to `signX`, `katIn_spec`,
`katIn1024_spec`, `opsE_fft` and `pt_angle` depend only on the standard axioms. -/

open FalconPrecision.Exec

-- answers at depth 1 in call order: `T1` (`z1`) before `T0` (`z0`)
/-- info: true -/
#guard_msgs in
#eval tapeOf 1 (fun i => [10, 11].getD i.1 0) (fun i => [20, 21].getD i.1 0) = [20, 21, 10, 11]

-- slots at level 2: `exp(iπ/4)`, `exp(-3iπ/4)`, `exp(-iπ/4)`, `exp(3iπ/4)`
/-- info: true -/
#guard_msgs in
#eval (List.range 4).map (fun j => slotK 2 (Out.ofIdx 2 j)) = [1, -3, -1, 3]

-- the ball FFT of `1 + 2x` at `x = i`: centre within `2⁻⁶³` of `1 + 2i`, radius below `2⁻⁶⁰`
/-- info: true -/
#guard_msgs in
#eval
  let b := opsB.fft 1 (fun i => [1, 2].getD i.1 0) (Out.ofIdx 1 0)
  decide (|b.b.c.re.m - 2 ^ 64| ≤ 2 ∧ |b.b.c.im.m - 2 ^ 65| ≤ 2) &&
    (b.b.r.map fun r => decide (r < 1 / 2 ^ 60)) == some true

-- `hull` of the exact balls `0` and `3` has centre `0` and a radius `≥ 3`; `widen` adds
/-- info: true -/
#guard_msgs in
#eval
  let z : CB 64 := CB.ofInt 0
  let t : CB 64 := CB.ofInt 3
  ((z.hull t).r.map fun r => decide (3 ≤ r)) == some true && (z.widen 1).r == some 1 &&
    (t.coarse).r == some 0

-- `opsBN 10` has tables at levels 0-9, level `L` with `2^L` balls
/-- info: true -/
#guard_msgs in
#eval (twTAN 10).size == 10 && ((twTAN 10).toList.map Array.size == (List.range 10).map (2 ^ ·)) &&
  (twsTAN 10).size == 10 && ((twsTAN 10).getD 9 #[]).size == 512

-- the tape at depth 10: 2048 distinct answers, the 1024 of `z1` (`T1`) before those of `z0`
/-- info: true -/
#guard_msgs in
#eval
  let t := tapeOf 10 (fun i => (i.1 : ℤ)) (fun i => 10000 + (i.1 : ℤ))
  t.length == 2048 && t.eraseDups.length == 2048 && (t.take 1024).all (10000 ≤ ·) &&
    (t.drop 1024).all (· < 1024)

/--
info: 'FalconPrecision.Exec.signT_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms signT_sim

/--
info: 'FalconPrecision.Exec.refRaw_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refRaw_rel

/--
info: 'FalconPrecision.Exec.refVecB_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refVecB_spec

/--
info: 'FalconPrecision.Exec.zOfSig_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms zOfSig_spec

/--
info: 'FalconPrecision.Exec.refRawA_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refRawA_eq

/--
info: 'FalconPrecision.Exec.refVec_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refVec_sound

/--
info: 'FalconPrecision.Exec.refVec_word' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refVec_word

/--
info: 'FalconPrecision.Exec.refVec_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refVec_exact

/--
info: 'FalconPrecision.Exec.refVec_adm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refVec_adm

/--
info: 'FalconPrecision.Exec.signX_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms signX_log

/--
info: 'FalconPrecision.Exec.katIn_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms katIn_spec

/--
info: 'FalconPrecision.Exec.opsE_fft' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms opsE_fft

/--
info: 'FalconPrecision.Exec.pt_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pt_angle

/--
info: 'FalconPrecision.Exec.signT_simN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms signT_simN

/--
info: 'FalconPrecision.Exec.refRawT_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refRawT_rel

/--
info: 'FalconPrecision.Exec.refRawAT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refRawAT_eq

/--
info: 'FalconPrecision.Exec.refVecBT_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVecBT_spec

/--
info: 'FalconPrecision.Exec.refVecBT_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVecBT_sound

/--
info: 'FalconPrecision.Exec.refVecBT_word' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVecBT_word

/--
info: 'FalconPrecision.Exec.refVecBT_exact' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVecBT_exact

/--
info: 'FalconPrecision.Exec.signX_logP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms signX_logP

/--
info: 'FalconPrecision.Exec.zOfSigP_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms zOfSigP_spec

/--
info: 'FalconPrecision.Exec.simXN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms simXN

/--
info: 'FalconPrecision.Exec.simWN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms simWN

/--
info: 'FalconPrecision.Exec.simEN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms simEN

/--
info: 'FalconPrecision.Exec.treeX1024' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms treeX1024

/--
info: 'FalconPrecision.Exec.treeE1024' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms treeE1024

/--
info: 'FalconPrecision.Exec.refVec_sound1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVec_sound1024

/--
info: 'FalconPrecision.Exec.refVec_adm1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVec_adm1024

/--
info: 'FalconPrecision.Exec.refVec_word1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVec_word1024

/--
info: 'FalconPrecision.Exec.refVec_exact1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refVec_exact1024

/--
info: 'FalconPrecision.Exec.signX_log1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_log1024

/--
info: 'FalconPrecision.Exec.katIn1024_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms katIn1024_spec
