/-! SamplerZ at Falcon-1024 on the round-3 reference trace (run file fragment, not part of the
package): each SamplerZ call of the trace, `samplerZ falcon1024S` (72-bit table) at
`σ̄ = Fx.ofRat .halfEven (1 / isig)` and `t̄ = Fx.ofRat .halfEven mu` (`mu`, `isig` the trace's
binary64 `mu` and `1/sigma`, exact), on the call's recorded random bytes (BaseSampler `u` as 9
bytes big-endian, the sign byte, the BerExp bytes, round after round), with saturated shifts
(`sat`) and with shift rejection (`rej`): `1` when the output is the trace's accepted `z` and
every byte is used. `range`: `σ̄` is in `falcon1024S`'s range. `#eval` only. -/

open FalconPrecision.Exec

/-- Uniform bits from a byte list, big-endian. -/
def ubL (k : ℕ) : StateM (List ℕ) ℕ := modifyGet fun l =>
  ((l.take ((k + 7) / 8)).foldl (fun a b => 256 * a + b) 0 % 2 ^ k, l.drop ((k + 7) / 8))

/-- A hex string as bytes. -/
def hexB (s : String) : List ℕ :=
  let d (c : Char) : ℕ := if c.isDigit then c.toNat - 48 else c.toNat - 87
  ((s.toList.zip s.toList.tail).zipIdx.filter (·.2 % 2 = 0)).map fun ((a, b), _) => 16 * d a + d b

/-- One call: `(mu, isig, bytes, z)`. -/
abbrev Call := ℚ × ℚ × String × ℤ

def sigmaOf (v : Call) : Fx 64 := Fx.ofRat .halfEven (1 / v.2.1)

/-- The output equals the trace's `z` and every byte is used. -/
def okC (rej : Bool) (v : Call) : Bool :=
  Id.run ((samplerZ falcon1024S ⟨.plain, rej, .b72⟩ ubL (sigmaOf v)
    (Fx.ofRat .halfEven v.1)).run (hexB v.2.2.1)) == (v.2.2.2, [])

def b2 (b : Bool) : String := if b then "1" else "0"

def runCalls (i0 : ℕ) (l : List Call) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut ns := 0
  let mut nr := 0
  for (v, i) in l.zipIdx do
    let s := okC false v
    let r := okC true v
    ns := ns + (if s then 1 else 0)
    nr := nr + (if r then 1 else 0)
    let g := inRangeB falcon1024S (sigmaOf v)
    IO.println s!"call={i0 + i} sat={b2 s} rej={b2 r} range={b2 g} bytes={(hexB v.2.2.1).length}"
  IO.println s!"calls={i0}-{i0 + l.length - 1} sat={ns} rej={nr} ms={(← IO.monoMsNow) - t0}"
