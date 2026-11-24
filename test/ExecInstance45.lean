import FalconPrecision.Exec.Instance45

/-! `FalconPrecision.Exec.Instance45`: `δ45q` at the root and below; axioms. -/

open FalconPrecision.Exec

/-- info: true -/
#guard_msgs in
#eval decide (δ45q 8 = 1 / 35184372088832 ∧ δ45q 0 = δ45q 8)

/--
info: 'FalconPrecision.Exec.δ45q_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms δ45q_eq

/--
info: 'FalconPrecision.Exec.s2B_falcon45' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms s2B_falcon45

/--
info: 'FalconPrecision.Exec.falcon512_fixed_vs_true45_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_fixed_vs_true45_checked
