/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.Sign

/-! # An executable SamplerZ parametric in the base table and the shift handling

Falcon round 3 (v1.2) §3.9.3, pp. 40-44: `baseZ` is BaseSampler (Alg. 12) on a table `BaseTable`,
`approxExp` is ApproxExp (Alg. 13) verbatim on naturals, `accW` is `2⁶⁴` times the acceptance
probability of BerExp (Alg. 14 l. 1-4), `berExp` its byte comparison (l. 5-10), `samplerZ` is
SamplerZ (Alg. 15) with uniform bits `ub k` on `[0, 2ᵏ)`. The SamplerZ choices `SampChoices`
pick the table (`base`: 72 bits, spec Table 3.1; 79 bits, `rcdt79`) and the handling of a shift
`≥ 64` (`shiftRej`: reject the candidate, ePrint 2026/2902 Alg. 9 l. 14-15, p. 27; else
saturate at 63 as the spec). `centre` is not read here (it is how the signer forms its target).

Departures from the spec, all explicit: `x = (z - r)²/(2σ̄²) - z0²/(2σmax²)`, `ccs = σmin/σ̄`
and `r = t̄ - ⌊t̄⌋` are exact in `ℚ` from the `Fx 64` inputs; `ln 2` is the stored `ln2`; the
loop stops after `fuel` rejected rounds with output `⌊t̄⌋`; the 79-bit draw is `u72·2⁷` plus
the 7 high bits of the sign byte. `rcdt79` is ours: the rule that gives spec Table 3.1 at 72 bits
(`pdt[i] = ⌊2ʷ·D_{ℤ⁺,σmax}(i)⌋` for `i ≥ 1`) applied at 79 bits; NIST's 79-bit table is
unpublished. -/

@[expose] public section

namespace FalconPrecision.Exec

/-- A BaseSampler table: `w`-bit draws `u`, `z0 = #{i | u < rcdt[i]}` (spec Alg. 12). -/
structure BaseTable where
  w : ℕ
  rcdt : List ℕ
  deriving DecidableEq, Repr

/-- Spec Table 3.1, `RCDT` (72 bits). -/
def rcdt72 : List ℕ :=
  [3024686241123004913666, 1564742784480091954050, 636254429462080897535,
    199560484645026482916, 47667343854657281903, 8595902006365044063, 1163297957344668388,
    117656387352093658, 8867391802663976, 496969357462633, 20680885154299, 638331848991,
    14602316184, 247426747, 3104126, 28824, 198, 1]

/-- A 79-bit `RCDT` by the rule of spec Table 3.1 (ours; NIST's table is unpublished). -/
def rcdt79 : List ℕ :=
  [387159838863744628950290, 200287076413451770119407, 81440566971146354885372,
    25543742034563389814034, 6101420013396132084367, 1100275456814725640756,
    148902138540117554346, 15060017581067988855, 1135026150740989486, 63612077755217481,
    2647153299750712, 81706476671178, 1869096471765, 31670623791, 397328250, 3689577, 25352,
    128]

/-- The 72-bit table. -/
def tab72 : BaseTable := ⟨72, rcdt72⟩

/-- The 79-bit table. -/
def tab79 : BaseTable := ⟨79, rcdt79⟩

/-- `z0` of a draw `u` (spec Alg. 12 l. 2-5). -/
def baseZ (T : BaseTable) (u : ℕ) : ℕ := (T.rcdt.filter (u < ·)).length

/-- The candidate `z = b + (2b - 1)·z0` (spec Alg. 15 l. 6). -/
def zOf (z0 : ℕ) (b : Bool) : ℤ := if b then 1 + z0 else -z0

/-- `C[1..12]` of ApproxExp (spec p. 42; `C[0] = 0x00000004741183A3`). -/
def facct : List ℕ :=
  [0x00000036548CFC06, 0x0000024FDCBF140A, 0x0000171D939DE045, 0x0000D00CF58F6F84,
    0x000680681CF796E3, 0x002D82D8305B0FEA, 0x011111110E066FD0, 0x0555555555070F00,
    0x155555555581FF00, 0x400000000002B400, 0x7FFFFFFFFFFF4800, 0x8000000000000000]

/-- ApproxExp (spec Alg. 13): an integral approximation of `2⁶³·ccs·exp(-x)`. -/
def approxExp (x ccs : ℚ) : ℕ :=
  let z := ⌊x * 2 ^ 63⌋.toNat
  ⌊ccs * 2 ^ 63⌋.toNat * facct.foldl (fun y c => c - z * y / 2 ^ 63) 0x00000004741183A3 / 2 ^ 63

/-- SamplerZ constants. -/
structure SampParams where
  σmin : ℚ
  σmax : ℚ
  /-- The stored `ln 2`. -/
  ln2 : ℚ
  /-- Rejected rounds before the output `⌊t̄⌋`. -/
  fuel : ℕ
  tab : BaseBits → BaseTable

/-- `2⁶⁴·Pr[BerExp(x, ccs) = 1]` (spec Alg. 14 l. 1-4, at most `2⁶⁴ - 1`); `0` at a shift
`≥ 64` when `rej` (ePrint 2026/2902 Alg. 9 l. 14-15). -/
def accW (P : SampParams) (rej : Bool) (x ccs : ℚ) : ℕ :=
  let s := ⌊x / P.ln2⌋
  if rej && decide (64 ≤ s) then 0
  else min ((2 * approxExp (x - s * P.ln2) ccs - 1) / 2 ^ (min s 63).toNat) (2 ^ 64 - 1)

/-- BerExp's comparison (spec Alg. 14 l. 5-10): uniform bytes against the bytes of `za`, from
byte `i - 1` down. -/
def berExp {m : Type → Type*} [Monad m] (ub : ℕ → m ℕ) (za : ℕ) : ℕ → m Bool
  | 0 => pure false
  | i + 1 => ub 8 >>= fun u =>
    if u < za / 2 ^ (8 * i) % 256 then pure true
    else if za / 2 ^ (8 * i) % 256 < u then pure false
    else berExp ub za i

/-- `x` of spec Alg. 15 l. 7 for the candidate `(z0, b)`, exactly. -/
def xOf (P : SampParams) (σ r : ℚ) (z0 : ℕ) (b : Bool) : ℚ :=
  (zOf z0 b - r) ^ 2 / (2 * σ ^ 2) - (z0 : ℚ) ^ 2 / (2 * P.σmax ^ 2)

/-- `z0` of the draws `u` (72 bits) and `c` (the sign byte). -/
def z0Of (T : BaseTable) (u c : ℕ) : ℕ := baseZ T (u * 2 ^ (T.w - 72) + c / 2 % 2 ^ (T.w - 72))

/-- The rejection loop of SamplerZ (spec Alg. 15 l. 3-9) at `σ̄`, `r`, `⌊μ⌋ = s`. -/
def samplerLoop {m : Type → Type*} [Monad m] (P : SampParams) (S : SampChoices)
    (ub : ℕ → m ℕ) (σ r : ℚ) (s : ℤ) : ℕ → m ℤ
  | 0 => pure s
  | n + 1 => ub 72 >>= fun u => ub 8 >>= fun c =>
    berExp ub (accW P S.shiftRej (xOf P σ r (z0Of (P.tab S.base) u c) (c % 2 = 1))
      (P.σmin / σ)) 8 >>= fun a =>
    if a then pure (s + zOf (z0Of (P.tab S.base) u c) (c % 2 = 1))
    else samplerLoop P S ub σ r s n

/-- **SamplerZ** (spec Alg. 15) at the leaf `σ̄` and centre `t̄`. -/
def samplerZ {m : Type → Type*} [Monad m] (P : SampParams) (S : SampChoices) (ub : ℕ → m ℕ)
    (σ t : Fx 64) : m ℤ :=
  samplerLoop P S ub σ.toRat (t.toRat - t.toInt .floor) (t.toInt .floor) P.fuel

/-- Falcon-512: `σmin = 1.277833697`, `σmax = 1.8205` (spec Table 3.3, p. 51), `ln 2` to
`2⁻⁶⁴`, `128` rounds, the tables `tab72`, `tab79`. -/
def falcon512S : SampParams where
  σmin := 1277833697 / 1000000000
  σmax := 18205 / 10000
  ln2 := 12786308645202655660 / 2 ^ 64
  fuel := 128
  tab
    | .b72 => tab72
    | .b79 => tab79

/-- `σ̄` in SamplerZ's range `[σmin, σmax]` (spec Alg. 11 l. 2, p. 40). -/
def inRangeB (P : SampParams) (σ : Fx 64) : Bool :=
  decide (P.σmin ≤ σ.toRat) && decide (σ.toRat ≤ P.σmax)

end FalconPrecision.Exec
