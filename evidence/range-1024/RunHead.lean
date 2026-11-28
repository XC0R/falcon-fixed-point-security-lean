
/-! Integer-range survey at Falcon-1024 (run file fragment, not part of the package): the 100
Falcon-1024 round-3 KAT keys through `checkRangeA` (`= checkRange … σ1024q` by `checkRangeA_eqP`)
at `i = 32` and `i = 64`, `W = 19`, ties to even (operations and tables), `xn = 0`, in one target
order, and the parts of it that do not read the stored tree. `#eval` only. -/

open FalconPrecision.Exec FalconPrecision.Exec.Round3

/-- The choice point of the survey (`checkRange` reads `x`, `xn`, `target`, `qinv`). -/
def cfg (tg : Target) : Choices :=
  { x := ⟨.halfEven, .halfEven, .direct, .plain⟩, xn := 0, target := tg, qinv := .w77,
    word := none, rchk := none, salt := .reused, cap := 27, beta2 := 70265242, infB := none,
    samp := ⟨.plain, true, .b79⟩ }

def log2Q (x : ℚ) : Float :=
  let a := x.num.natAbs
  let b := x.den
  let sa := a.log2 - 52
  let sb := b.log2 - 52
  Float.log2 (a >>> sa).toFloat + sa.toFloat - Float.log2 (b >>> sb).toFloat - sb.toFloat

def b2 (b : Bool) : String := if b then "1" else "0"

def tgName : Target → String
  | .scaleFirst => "scaleFirst"
  | .multiplyFirst => "multiplyFirst"

/-- The values of `checkRangeA C i W k σ1024q` before `rangeT`: the tables, the bounds that must be
`< 2^(i - 1)` (`bc`, `‖f‖₁`, `‖F‖₁`, the target list) and the root bound `tgt.2`. -/
def parts (C : Choices) (k : RawKey 10) : Bool × List ℚ × ℚ :=
  let C0 := { C with word := none }
  let bc : ℚ := 2 * (2 ^ 10 * 12288) + 1
  let mf := nmaxA 10 (fftWA C0 10 k.f) + 1
  let mF := nmaxA 10 (fftWA C0 10 k.F) + 1
  let tgt : List ℚ × ℚ := match C.target with
    | .scaleFirst =>
      let cq := 2 * bc / 12289 + 1
      ([cq, cq * mF + 1, cq * mf + 1], max (cq * mF + 1) (cq * mf + 1))
    | .multiplyFirst =>
      let p := bc * max mF mf + 1
      ([p, 2 * p / 12289 + 1], 2 * p / 12289 + 1)
  (twOkFastN C.x.rc 10, [bc, 2 * l1Q k.f + 1, 2 * l1Q k.F + 1] ++ tgt.1, tgt.2)

def runRange (tg : Target) (lo hi : ℕ) : IO Unit := do
  for j in [lo:hi] do
    match (ofHex katSk[j]!).bind (decodeKey · 10) with
    | none => IO.println s!"target={tgName tg} key={j} decode=0"
    | some k =>
      let p ← IO.lazyPure fun _ => parts (cfg tg) k
      let fmax := p.2.1.foldl max 0
      for i in [32, 64] do
        let t0 ← IO.monoMsNow
        let c ← IO.lazyPure fun _ => checkRangeA (cfg tg) i 19 k σ1024q
        let t1 ← IO.monoMsNow
        IO.println (s!"target={tgName tg} i={i} key={j} checkRangeA={b2 c} tw={b2 p.1} " ++
          s!"fit={b2 (p.2.1.all (fitsQ i))} fitMax={log2Q fmax} root={log2Q p.2.2} " ++
          s!"ms={t1 - t0}")
