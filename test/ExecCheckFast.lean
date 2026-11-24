import FalconPrecision.Exec.CheckFast

/-! `FalconPrecision.Exec.CheckFast`: array vectors, the twiddle tables of Falcon-512; axioms. -/

open FalconPrecision.Exec FalconPrecision.Errors.FFTRec

-- position `o` of `toArr` is entry `Out.idx o`
/-- info: true -/
#guard_msgs in
#eval decide (toArr 2 (Out.idx 2) = #[0, 1, 2, 3] ∧
  ofArr 2 #[5, 6, 7, 8] (Out.ofIdx 2 2) = 7)

-- the tables of all 9 levels within `0.7072·2⁻⁶⁴` (round to nearest), not with `floor`
/-- info: true -/
#guard_msgs in
#eval decide (twOkFast .halfEven = true ∧ twOkFast .halfUp = true ∧ twOkFast .halfAway = true ∧
  twOkFast .floor = false)

-- the FFT of `3 + 5x` at `±i`, centres
/-- info: true -/
#guard_msgs in
#eval decide ((fftBA ⟨.halfEven, .halfEven, .direct, .plain⟩ 4 1
  (fun i => if i.1 = 0 then 3 else 5)).map (fun b => (b.c.re.m, b.c.im.m)) =
  #[(48, 80), (48, -80)])

/--
info: 'FalconPrecision.Exec.ofArr_twHiA' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ofArr_twHiA

/--
info: 'FalconPrecision.Exec.ofArr_twBA' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ofArr_twBA

/--
info: 'FalconPrecision.Exec.ofArr_twsBA' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ofArr_twsBA

/--
info: 'FalconPrecision.Exec.twOkFast_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twOkFast_eq

/--
info: 'FalconPrecision.Exec.ofArr_fftBA' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ofArr_fftBA

/--
info: 'FalconPrecision.Exec.expandBA_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandBA_eq

/--
info: 'FalconPrecision.Exec.checkFast_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkFast_eq
