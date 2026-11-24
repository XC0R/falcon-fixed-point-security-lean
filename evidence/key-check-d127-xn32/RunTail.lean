open FalconPrecision.Exec FalconPrecision.Exec.Round3

def runD127 : IO Unit := do
  for i in [0:100] do
    match (ofHex katSk[i]!).bind decodeKey with
    | none => IO.println s!"d127 key={i} decode=0"
    | some k =>
      let t0 ← IO.monoMsNow
      let c ← IO.lazyPure fun _ => checkFast ⟨.halfEven, .halfEven, .direct, .plain⟩ 32 δ127q k
      let t1 ← IO.monoMsNow
      IO.println s!"d127 key={i} checkFast_halfEven_xn32_delta127q={c} ms={t1 - t0}"

#eval runD127
