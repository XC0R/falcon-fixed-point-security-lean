import FalconPrecision.Exec.SignRefine
import FalconPrecision.Exec.SignFast
import FalconPrecision.Exec.SignRange

/-! `FalconPrecision.Exec.Sign`, `SignRefine`, `SignFast`, `SignRange`: words, products, FFT,
checks, ffSampling, the restart loop, ranges, tables, array versions; axioms. -/

open FalconPrecision.Exec FalconPrecision.Errors.FFTRec

/-- A choice point: ties to even, scale-first, 32.64, no range checks, reused salt, cap 27. -/
def cEx : Choices :=
  { x := ⟨.halfEven, .halfEven, .direct, .plain⟩, xn := 0, target := .scaleFirst, qinv := .w77,
    word := some 32, rchk := none, salt := .reused, cap := 27, beta2 := 34034726, infB := none,
    samp := ⟨.plain, true, .b79⟩ }

-- 96-bit words: 2⁹⁵ wraps to -2⁹⁵, 2⁹⁵ - 1 stays
/-- info: true -/
#guard_msgs in
#eval decide (wordFn (some 32) (2 ^ 95) = -2 ^ 95 ∧ wordFn (some 32) (2 ^ 95 - 1) = 2 ^ 95 - 1 ∧
  wordFn none 5 = 5)

-- with no reduction the product is `Cx.mul`
/-- info: true -/
#guard_msgs in
#eval decide (Cx.mulW id .halfEven (⟨⟨3 * 2 ^ 63⟩, ⟨-5⟩⟩ : Cx 64) ⟨⟨7⟩, ⟨2 ^ 64 + 1⟩⟩ =
  Cx.mul .halfEven ⟨⟨3 * 2 ^ 63⟩, ⟨-5⟩⟩ ⟨⟨7⟩, ⟨2 ^ 64 + 1⟩⟩)

-- FFT of 3 + 5x at ±i: 3 ± 5i
/-- info: true -/
#guard_msgs in
#eval decide (fftW cEx 1 (fun i => if i.1 = 0 then 3 else 5) (((), false) : Out 1) =
    ⟨⟨3 * 2 ^ 64⟩, ⟨5 * 2 ^ 64⟩⟩ ∧
  fftW cEx 1 (fun i => if i.1 = 0 then 3 else 5) (((), true) : Out 1) =
    ⟨⟨3 * 2 ^ 64⟩, ⟨-5 * 2 ^ 64⟩⟩)

-- the range check `‖·‖ ≤ R - 1` at R = 2
/-- info: true -/
#guard_msgs in
#eval decide (chkX (some 2) 0 (fun _ => Cx.ofInt 1) = true ∧
  chkX (some 2) 0 (fun _ => Cx.ofInt 2) = false ∧ chkX none 0 (fun _ => Cx.ofInt 9) = true)

-- clamping into 5 ± 2
/-- info: true -/
#guard_msgs in
#eval decide (clampZ 5 2 10 = 7 ∧ clampZ 5 2 0 = 3 ∧ clampZ 5 2 6 = 6)

/-- A deterministic sampler: the centre rounded to nearest, ties to even. -/
def sampR (_ t : Fx 64) : Id ℤ := pure (t.toInt .halfEven)

-- a leaf: centres 2.5, 1.75 give 2, 2
/-- info: true -/
#guard_msgs in
#eval decide ((Id.run (ffsX cEx sampR (.leaf ⟨3 * 2 ^ 63⟩) (fun _ => ⟨⟨5 * 2 ^ 63⟩, ⟨0⟩⟩)
  (fun _ => ⟨⟨7 * 2 ^ 62⟩, ⟨0⟩⟩))).map (fun s => (s.z0 ⟨0, by norm_num⟩,
    s.z1 ⟨0, by norm_num⟩)) = some (2, 2))

/-- A depth-1 tree with `ℓ̂ = 0`, leaves `1.5`. -/
def tree1 : CTree 64 1 := .node (fun _ => ⟨⟨0⟩, ⟨0⟩⟩) (.leaf ⟨3 * 2 ^ 63⟩) (.leaf ⟨3 * 2 ^ 63⟩)

-- zero inputs pass the checks at R = 1; a nonzero `t1` fails them (⊥)
/-- info: true -/
#guard_msgs in
#eval decide ((Id.run (ffsX { cEx with rchk := some 1 } sampR tree1 (fun _ => ⟨⟨0⟩, ⟨0⟩⟩)
    (fun _ => ⟨⟨0⟩, ⟨0⟩⟩))).isSome = true ∧
  (Id.run (ffsX { cEx with rchk := some 1 } sampR tree1 (fun _ => ⟨⟨0⟩, ⟨0⟩⟩)
    (fun _ => Cx.ofInt 1))).isSome = false)

/-- Salts `0, 1, 2, …` from a counter; an attempt succeeds when the salt is `≥ 2`. -/
def loopEx (mode : SaltMode) (N : ℕ) : Option (ℕ × ZPoly) × ℕ :=
  (signLoopX (m := StateM ℕ) mode (modifyGet fun n => (n, n + 1)) (fun s _ => pure fun _ => s)
    (fun c => pure (if 2 ≤ c ⟨0, by norm_num⟩ then some (c, c) else none))
    (fun _ y => y.map Prod.fst) () N).run 0

-- per attempt: success at the third salt; cap 2: failure after two salts; reused: one salt
/-- info: true -/
#guard_msgs in
#eval decide ((loopEx .perAttempt 5).1.map Prod.fst = some 2 ∧ (loopEx .perAttempt 5).2 = 3 ∧
  (loopEx .perAttempt 2).1 = none ∧ (loopEx .perAttempt 2).2 = 2 ∧
  (loopEx .reused 5).1 = none ∧ (loopEx .reused 5).2 = 1)

-- the norm bound: 0 passes; 300 in every coefficient of s1 fails (512·300² > 34034726)
/-- info: true -/
#guard_msgs in
#eval decide (normOk cEx (fun _ => 0, fun _ => 0) = true ∧
  normOk cEx (fun _ => 300, fun _ => 0) = false)

-- deviation bounds (leaf `W + 1 + E`; `ℓ̂ = 0`: `λ = 2⁻⁶⁴`), the leaf range check, `imE 32`
/-- info: true -/
#guard_msgs in
#eval decide (devT 30 0 (.leaf ⟨3 * 2 ^ 63⟩) = 31 ∧ devT 30 (1 / 2) tree1 = 66 + 65 / 2 ^ 64 ∧
  rangeT 32 30 0 (.leaf ⟨3 * 2 ^ 63⟩) 100 = true ∧
  rangeT 8 30 0 (.leaf ⟨3 * 2 ^ 63⟩) 100 = false ∧ imE 32 = 1 / 2)

-- the array FFT, split and ffSampling agree with the originals; merge at `±i`: `2 + i·1`
/-- info: true -/
#guard_msgs in
#eval decide (ofArr 1 (fftWA cEx 1 fun i => if i.1 = 0 then 3 else 5) (((), true) : Out 1) =
    fftW cEx 1 (fun i => if i.1 = 0 then 3 else 5) (((), true) : Out 1) ∧
  ofArr 0 (splitWA cEx 0 fun x => Cx.ofInt (if (x : Unit × Bool).2 then 7 else 3)).2 () =
    (splitW cEx 0 fun x => Cx.ofInt (if (x : Unit × Bool).2 then 7 else 3)).2 () ∧
  ofArr 1 (mergeWA cEx 0 (fun _ => Cx.ofInt 2) fun _ => Cx.ofInt 1) (((), false) : Out 1) =
    ⟨⟨2 * 2 ^ 64⟩, ⟨2 ^ 64⟩⟩ ∧
  (Id.run (ffsXA cEx sampR tree1 (fun _ => Cx.ofInt 4) fun _ => Cx.ofInt 6)).map
      (fun s => (s.z0, s.z1)) =
    (Id.run (ffsX cEx sampR tree1 (fun _ => Cx.ofInt 4) fun _ => Cx.ofInt 6)).map
      (fun s => (s.z0, s.z1)))

-- the computed tables at levels `< 3` meet `0.7072·2⁻⁶⁴` for nearest rounding, not for floor
/-- info: true -/
#guard_msgs in
#eval decide (twOkN .halfEven 3 = true ∧ twOkN .halfUp 3 = true ∧ twOkN .floor 3 = false)

/--
info: 'FalconPrecision.Exec.signXA_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signXA_eq

/--
info: 'FalconPrecision.Exec.checkRangeA_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkRangeA_eq

/--
info: 'FalconPrecision.Exec.signX_refines' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_refines

/--
info: 'FalconPrecision.Exec.falcon512_exec_vs_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_exec_vs_true

/--
info: 'FalconPrecision.Exec.sign32_eq_sign64' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sign32_eq_sign64

/--
info: 'FalconPrecision.Exec.arithX' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms arithX

/--
info: 'FalconPrecision.Exec.twX_err64' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twX_err64

/--
info: 'FalconPrecision.Exec.twsX_err64' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twsX_err64

/--
info: 'FalconPrecision.Exec.chkX_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chkX_iff

/--
info: 'FalconPrecision.Exec.fftW_toC' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fftW_toC

/--
info: 'FalconPrecision.Exec.targetX_toC' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms targetX_toC

/--
info: 'FalconPrecision.Exec.ffsX_refines' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ffsX_refines

/--
info: 'FalconPrecision.Exec.world_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms world_eq

/--
info: 'FalconPrecision.Exec.pathSum_signLoopX' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_signLoopX

/--
info: 'FalconPrecision.Exec.signX_word' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signX_word

/--
info: 'FalconPrecision.Exec.leafX_im' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leafX_im

/--
info: 'FalconPrecision.Exec.ffsX_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ffsX_sound

/--
info: 'FalconPrecision.Exec.ffsX_word' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ffsX_word
