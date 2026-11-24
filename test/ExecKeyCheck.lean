import FalconPrecision.Exec.KeyCheck

/-! `FalconPrecision.Exec.KeyCheck`: the negacyclic product, storage rounding; axioms. -/

open FalconPrecision.Exec

/-- The monomial `xⁱ` of size `2⁹`. -/
def mono (i : ℕ) : Fin (2 ^ 9) → ℤ := fun j => if j.1 = i then 1 else 0

-- x·x⁵¹¹ = x⁵¹² = -1
/-- info: true -/
#guard_msgs in
#eval decide (ncoef (mono 1) (mono 511) 0 = -1 ∧ ncoef (mono 1) (mono 511) 1 = 0)
-- x²·x³ = x⁵
/-- info: true -/
#guard_msgs in
#eval decide (ncoef (mono 2) (mono 3) 5 = 1 ∧ ncoef (mono 2) (mono 3) 4 = 0)

-- storage rounding: 5·2⁻³ to 2⁻² is 2.5·2⁻², ties to even give 2·2⁻²; at 0 extra bits unchanged
/-- info: true -/
#guard_msgs in
#eval decide ((Fx.lower (f := 2) RMode.halfEven 1 ⟨5⟩).m = 2 ∧
  (Fx.lower (f := 2) RMode.halfEven 0 ⟨5⟩).m = 5)

/--
info: 'FalconPrecision.Exec.check_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms check_sound

/--
info: 'FalconPrecision.Exec.falcon512_fixed_vs_true_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_fixed_vs_true_checked

/--
info: 'FalconPrecision.Exec.falcon512_fixed_vs_true127_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_fixed_vs_true127_checked

/--
info: 'FalconPrecision.Exec.sqrt_le_sqrtUB' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sqrt_le_sqrtUB

/--
info: 'FalconPrecision.Exec.sqrtLB_le_sqrt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sqrtLB_le_sqrt

/--
info: 'FalconPrecision.Exec.Cx.norm_le_nUB' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cx.norm_le_nUB

/--
info: 'FalconPrecision.Exec.Cx.nLB_le_norm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cx.nLB_le_norm

/--
info: 'FalconPrecision.Exec.CB.Holds.mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.mul

/--
info: 'FalconPrecision.Exec.CB.Holds.half' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.half

/--
info: 'FalconPrecision.Exec.CB.Holds.normSq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.normSq

/--
info: 'FalconPrecision.Exec.CB.Holds.divR' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.divR

/--
info: 'FalconPrecision.Exec.CB.Holds.leaf' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.leaf

/--
info: 'FalconPrecision.Exec.CB.Holds.sqrtU' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.sqrtU

/--
info: 'FalconPrecision.Exec.CB.Holds.lower' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.lower

/--
info: 'FalconPrecision.Exec.CB.Holds.lowerConjHalf' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CB.Holds.lowerConjHalf

/--
info: 'FalconPrecision.Exec.expandB_centre' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandB_centre

/--
info: 'FalconPrecision.Exec.fftB_holds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fftB_holds

/--
info: 'FalconPrecision.Exec.ntru_det' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ntru_det

/--
info: 'FalconPrecision.Exec.ntru_root' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ntru_root

/--
info: 'FalconPrecision.Exec.expandB_holdsT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandB_holdsT

/--
info: 'FalconPrecision.Exec.BTree.close_of' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BTree.close_of

/--
info: 'FalconPrecision.Exec.CTree.real_toFTree' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CTree.real_toFTree

/--
info: 'FalconPrecision.Exec.pathSum_embed' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_embed

/--
info: 'FalconPrecision.Exec.CTree.lower_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CTree.lower_zero

/--
info: 'FalconPrecision.Exec.BTree.centre_lower' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BTree.centre_lower

/--
info: 'FalconPrecision.Exec.storeB_holdsT' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms storeB_holdsT
