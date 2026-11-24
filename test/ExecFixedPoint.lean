import FalconPrecision.Exec.FixedPoint

/-! Concrete values of `FalconPrecision.Exec`: `f = 4` (ulp `1/16`) and `f = 64`. -/

open FalconPrecision.Exec

/-- `m` of the product of `⟨a⟩ ⟨b⟩ : Fx 4` under each rule (floor, even, up, away). -/
def mul4 (a b : ℤ) : List ℤ :=
  [.floor, .halfEven, .halfUp, .halfAway].map fun r => ((⟨a⟩ : Fx 4).mul r ⟨b⟩).m

/-- `m` of the quotient of `⟨a⟩ ⟨b⟩ : Fx 4` under each rule. -/
def div4 (a b : ℤ) : List ℤ :=
  [.floor, .halfEven, .halfUp, .halfAway].map fun r => ((⟨a⟩ : Fx 4).div r ⟨b⟩).m

-- 3·8/16 = 1.5
/-- info: true -/
#guard_msgs in
#eval decide (mul4 3 8 = [1, 2, 2, 2])
-- 5·8/16 = 2.5
/-- info: true -/
#guard_msgs in
#eval decide (mul4 5 8 = [2, 2, 3, 3])
-- -5·8/16 = -2.5
/-- info: true -/
#guard_msgs in
#eval decide (mul4 (-5) 8 = [-3, -2, -2, -3])
-- -3·8/16 = -1.5
/-- info: true -/
#guard_msgs in
#eval decide (mul4 (-3) 8 = [-2, -2, -1, -2])
-- 49/16 = 3.0625
/-- info: true -/
#guard_msgs in
#eval decide (mul4 7 7 = [3, 3, 3, 3])
-- -49/16 = -3.0625
/-- info: true -/
#guard_msgs in
#eval decide (mul4 (-7) 7 = [-4, -3, -3, -3])
-- 16·16/48 = 5.33
/-- info: true -/
#guard_msgs in
#eval decide (div4 16 48 = [5, 5, 5, 5])
-- -256/48 = -5.33
/-- info: true -/
#guard_msgs in
#eval decide (div4 (-16) 48 = [-6, -5, -5, -5])
-- 256/(-48) = -5.33
/-- info: true -/
#guard_msgs in
#eval decide (div4 16 (-48) = [-6, -5, -5, -5])
-- 16/32 = 0.5
/-- info: true -/
#guard_msgs in
#eval decide (div4 1 32 = [0, 0, 1, 1])
-- -16/32 = -0.5
/-- info: true -/
#guard_msgs in
#eval decide (div4 (-1) 32 = [-1, 0, 0, -1])
-- √2·16 = 22.63: Nat.sqrt 512 = 22, 512 > 22·22 + 22 = 506
/-- info: true -/
#guard_msgs in
#eval decide (((⟨32⟩ : Fx 4).sqrt .floor).m = 22)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨32⟩ : Fx 4).sqrt .halfEven).m = 23)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨16⟩ : Fx 4).sqrt .halfUp).m = 16)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨-16⟩ : Fx 4).sqrt .halfUp).m = 0)
-- 40/16 = 2.5
/-- info: true -/
#guard_msgs in
#eval decide ([RMode.floor, .halfEven, .halfUp, .halfAway].map (fun r => (⟨40⟩ : Fx 4).toInt r) =
  [2, 2, 3, 3])
/-- info: true -/
#guard_msgs in
#eval decide ((Fx.ofInt 3 : Fx 4).m = 48)
-- 1/3·16 = 5.33; -1/3·16 = -5.33
/-- info: true -/
#guard_msgs in
#eval decide ((Fx.ofRat .halfEven (1 / 3) : Fx 4).m = 5)
/-- info: true -/
#guard_msgs in
#eval decide ((Fx.ofRat .halfEven (-1 / 3) : Fx 4).m = -5)
/-- info: true -/
#guard_msgs in
#eval decide ((Fx.ofRat .floor (-1 / 3) : Fx 4).m = -6)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨3⟩ : Fx 4).add ⟨-5⟩).m = -2)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨3⟩ : Fx 4).sub ⟨-5⟩).m = 8)
/-- info: true -/
#guard_msgs in
#eval decide ((⟨3⟩ : Fx 4).toRat = 3 / 16)
-- (8 + 4i)(12 - 8i)/16: re 6 - (-2) = 8, im -4 + 3 = -1
/-- info: true -/
#guard_msgs in
#eval decide (((⟨⟨8⟩, ⟨4⟩⟩ : Cx 4).mul .halfEven ⟨⟨12⟩, ⟨-8⟩⟩) = ⟨⟨8⟩, ⟨-1⟩⟩)
-- (1 + i)(8 + 8i)/16: re 0.5 - 0.5, im 0.5 + 0.5 (two ties)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨⟨1⟩, ⟨1⟩⟩ : Cx 4).mul .halfEven ⟨⟨8⟩, ⟨8⟩⟩) = ⟨⟨0⟩, ⟨0⟩⟩)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨⟨1⟩, ⟨1⟩⟩ : Cx 4).mul .halfUp ⟨⟨8⟩, ⟨8⟩⟩) = ⟨⟨0⟩, ⟨2⟩⟩)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨⟨3⟩, ⟨-3⟩⟩ : Cx 4).half .halfEven) = ⟨⟨2⟩, ⟨-2⟩⟩)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨⟨3⟩, ⟨-3⟩⟩ : Cx 4).half .halfAway) = ⟨⟨2⟩, ⟨-2⟩⟩)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨⟨3⟩, ⟨-3⟩⟩ : Cx 4).half .halfUp) = ⟨⟨2⟩, ⟨-1⟩⟩)
-- range [-1, 1) at i = 1: m ∈ [-16, 16)
/-- info: true -/
#guard_msgs in
#eval decide ([15, 16, -16, -17].map (fun m => decide ((⟨m⟩ : Fx 4).InRange 1)) =
  [true, false, true, false])
-- 4-bit words
/-- info: true -/
#guard_msgs in
#eval decide ([8, 7, -9, -8].map (Fx.wrap 3) = [-8, 7, 7, -8])
-- f = 64: 1·2⁶³/2⁶⁴ = 0.5, -0.5, 1.5
/-- info: true -/
#guard_msgs in
#eval decide ([RMode.floor, .halfEven, .halfUp, .halfAway].map
  (fun r => ((⟨1⟩ : Fx 64).mul r ⟨2 ^ 63⟩).m) = [0, 0, 1, 1])
/-- info: true -/
#guard_msgs in
#eval decide ([RMode.floor, .halfEven, .halfUp, .halfAway].map
  (fun r => ((⟨-1⟩ : Fx 64).mul r ⟨2 ^ 63⟩).m) = [-1, 0, 0, -1])
/-- info: true -/
#guard_msgs in
#eval decide ([RMode.floor, .halfEven, .halfUp, .halfAway].map
  (fun r => ((⟨3⟩ : Fx 64).mul r ⟨2 ^ 63⟩).m) = [1, 2, 2, 2])
-- 1.5·1.5 = 2.25
/-- info: true -/
#guard_msgs in
#eval decide (((⟨3 * 2 ^ 63⟩ : Fx 64).mul .halfEven ⟨3 * 2 ^ 63⟩).m = 9 * 2 ^ 62)
-- √2·2⁶⁴ = 26087635650665564424.70
/-- info: true -/
#guard_msgs in
#eval decide (((⟨2 ^ 65⟩ : Fx 64).sqrt .floor).m = 26087635650665564424)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨2 ^ 65⟩ : Fx 64).sqrt .halfEven).m = 26087635650665564425)
-- 2⁷⁷/12289 = 12296828663994519231 rem 8513, 2·8513 > 12289
/-- info: true -/
#guard_msgs in
#eval decide ((Cx.qinv .halfEven).m = 12296828663994519232)
/-- info: true -/
#guard_msgs in
#eval decide ((Cx.qinv .floor).m = 12296828663994519231)
/-- info: true -/
#guard_msgs in
#eval decide (2 ^ 63 < (Cx.qinv .halfEven).m ∧ (Cx.qinv .halfEven).m < 2 ^ 64)
-- 12289·2⁶⁴/q: (12289·2⁶⁴)·qinv/2⁷⁷ rounds to 2⁶⁴ (value 1)
/-- info: true -/
#guard_msgs in
#eval decide (((⟨⟨12289 * 2 ^ 64⟩, ⟨0⟩⟩ : Cx 64).divq .halfEven) = ⟨⟨2 ^ 64⟩, ⟨0⟩⟩)
-- 32.64 and 64.64: same bits in a 96-bit and a 128-bit word when in range 32
/-- info: true -/
#guard_msgs in
#eval decide (decide ((⟨3 * 2 ^ 63⟩ : Fx 64).InRange 32))
/-- info: true -/
#guard_msgs in
#eval decide (Fx.wrap 95 (3 * 2 ^ 63) = Fx.wrap 127 (3 * 2 ^ 63))
/-- info: true -/
#guard_msgs in
#eval decide (Fx.wrap 95 (2 ^ 95) ≠ Fx.wrap 127 (2 ^ 95))
