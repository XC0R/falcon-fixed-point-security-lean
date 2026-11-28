import FalconPrecision.Exec.KeyCheck
import FalconPrecision.Exec.KeyCheck1024

/-! `FalconPrecision.Exec.KeyCheck`, `FalconPrecision.Exec.KeyCheck1024`: the negacyclic product,
storage rounding; axioms. -/

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

/-- The monomial `xⁱ` of size `2¹⁰`. -/
def mono10 (i : ℕ) : Fin (2 ^ 10) → ℤ := fun j => if j.1 = i then 1 else 0

-- x·x¹⁰²³ = x¹⁰²⁴ = -1
/-- info: true -/
#guard_msgs in
#eval decide (ncoef (mono10 1) (mono10 1023) 0 = -1 ∧ ncoef (mono10 1) (mono10 1023) 1 = 0)

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

/--
info: 'FalconPrecision.Exec.Cx.norm_le_of_nsq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cx.norm_le_of_nsq

/--
info: 'FalconPrecision.Exec.CTree.ok_of_okB' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CTree.ok_of_okB

/--
info: 'FalconPrecision.Exec.CTree.toFTreeP_congr' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CTree.toFTreeP_congr

/--
info: 'FalconPrecision.Exec.CTree.real_toFTreeP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CTree.real_toFTreeP

/--
info: 'FalconPrecision.Exec.BTree.close_ofP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BTree.close_ofP

/--
info: 'FalconPrecision.Exec.ldlB_centreP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ldlB_centreP

/--
info: 'FalconPrecision.Exec.expandB_centreP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandB_centreP

/--
info: 'FalconPrecision.Exec.storeB_centreP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms storeB_centreP

/--
info: 'FalconPrecision.Exec.evalAt_ncoef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalAt_ncoef

/--
info: 'FalconPrecision.Exec.gramB_holds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gramB_holds

/--
info: 'FalconPrecision.Exec.rootB_holds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rootB_holds

/--
info: 'FalconPrecision.Exec.ldlStepB_holdsTP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ldlStepB_holdsTP

/--
info: 'FalconPrecision.Exec.ldlB_holdsTP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ldlB_holdsTP

/--
info: 'FalconPrecision.Exec.expandB_holdsTP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expandB_holdsTP

/--
info: 'FalconPrecision.Exec.storeB_holdsTP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms storeB_holdsTP

/--
info: 'FalconPrecision.Exec.check_ok' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms check_ok

/--
info: 'FalconPrecision.Exec.check_soundP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms check_soundP

/--
info: 'FalconPrecision.Exec.pathSum_embedP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_embedP

/--
info: 'FalconPrecision.Exec.lam1024q_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lam1024q_eq

/--
info: 'FalconPrecision.Exec.σ1024_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms σ1024_eq

/--
info: 'FalconPrecision.Exec.checkFast_eq1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkFast_eq1024

/--
info: 'FalconPrecision.Exec.check1024_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms check1024_sound

/--
info: 'FalconPrecision.Exec.pathSum_embed1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_embed1024

/--
info: 'FalconPrecision.Exec.δ43q_1024_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms δ43q_1024_eq

/--
info: 'FalconPrecision.Exec.δ127q_1024_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms δ127q_1024_eq

/--
info: 'FalconPrecision.Exec.falcon1024_fixed_vs_true_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_fixed_vs_true_checked

/--
info: 'FalconPrecision.Exec.falcon1024_fixed_vs_true43_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_fixed_vs_true43_checked

/--
info: 'FalconPrecision.Exec.falcon1024_fixed_vs_true127_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_fixed_vs_true127_checked

/--
info: 'FalconPrecision.Exec.falcon1024_fixed_vs_true256_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_fixed_vs_true256_checked

/--
info: 'FalconPrecision.Exec.falcon1024_fixed_vs_true256_43_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_fixed_vs_true256_43_checked

/--
info: 'FalconPrecision.Exec.falcon1024_fixed_vs_true256_127_checked' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024_fixed_vs_true256_127_checked
