
/-! Key-check survey at `δ127q_1024` (run file fragment, not part of the package): the 100
Falcon-1024 round-3 KAT keys through `checkFast` at the Falcon-1024 thresholds (= `check1024`,
`checkFast_eq1024`) and a breakdown of its parts. -/

open FalconPrecision.Exec FalconPrecision.Exec.Round3 FalconPrecision.Errors.FFTRec

def maxO (a b : Option ℚ) : Option ℚ :=
  match a, b with
  | some x, some y => some (max x y)
  | _, _ => none

/-- The entries of a vector over `Out L`. -/
def entries {X : Type} (L : ℕ) (v : Out L → X) : List X :=
  (List.range (2 ^ L)).map fun i => v (Out.ofIdx L i)

/-- Per level `L` (factor `ℓ : Out (L + 1) → CB`): the maximum radius (`none`: unknown). -/
def nodeRad {f : ℕ} : {L : ℕ} → BTree f L → Array (Option ℚ) → Array (Option ℚ)
  | _, .leaf _, acc => acc
  | _, @BTree.node _ L ℓ T0 T1, acc =>
    let m := (entries (L + 1) ℓ).foldl (fun a b => maxO a b.r) (some 0)
    nodeRad T1 (nodeRad T0 (acc.modify L (maxO m)))

/-- Leaves: maximum radius, all `leafOkB`. -/
def leafInfo {f : ℕ} : {L : ℕ} → BTree f L → Option ℚ × Bool
  | _, .leaf s => (s.r, s.leafOkB)
  | _, .node _ T0 T1 =>
    let a := leafInfo T0
    let b := leafInfo T1
    (maxO a.1 b.1, a.2 && b.2)

/-- All node radii `≤ δq L`. -/
def nodeOk {f : ℕ} (δq : ℕ → ℚ) : {L : ℕ} → BTree f L → Bool
  | _, .leaf _ => true
  | _, @BTree.node _ L ℓ T0 T1 =>
    allOut (L + 1) (fun o => (ℓ o).radLeB (δq L)) && nodeOk δq T0 && nodeOk δq T1

def log2Q (x : ℚ) : Float :=
  let a := x.num.natAbs
  let b := x.den
  let sa := a.log2 - 52
  let sb := b.log2 - 52
  Float.log2 (a >>> sa).toFloat + sa.toFloat - Float.log2 (b >>> sb).toFloat - sb.toFloat

def showO (x : Option ℚ) : String :=
  match x with
  | some r => if r = 0 then "zero" else toString (log2Q r)
  | none => "unknown"

def b2 (b : Bool) : String := if b then "1" else "0"

/-- The parts of `checkFast P n δ127q_1024 k` at the Falcon-1024 thresholds (without `ntruB`), from
one tree. -/
def diag (P : XChoices) (n : ℕ) (k : RawKey 10) : String :=
  let T := (expandBA P (64 + n) k σ1024q).lower P.rm n
  let C := T.centre
  let fb := fftBA P (64 + n) 10 k.f
  let Fb := fftBA P (64 + n) 10 k.F
  let hf := allOut 10 (fun o => (ofArr 10 fb o).normLeB 256)
  let hF := allOut 10 (fun o => (ofArr 10 Fb o).normLeB 7365)
  let ok := C.okB (1298280334 / 10 ^ 9) lam1024q
  let re := C.realB
  let li := leafInfo T
  let no := nodeOk δ127q_1024 T
  let ro := T.radOkB δ127q_1024
  let rads := nodeRad T (Array.replicate 10 (some 0))
  s!"fft256={b2 hf} fft7365={b2 hF} okB={b2 ok} realB={b2 re} leafOk={b2 li.2} " ++
    s!"nodeOk127={b2 no} radOkB127={b2 ro} leafR={showO li.1} " ++
    s!"rad=[{",".intercalate ((rads.toList.reverse).map showO)}]"

def runDecode (lo hi : ℕ) : IO Unit := do
  for i in [lo:hi] do
    let t0 ← IO.monoMsNow
    let r ← IO.lazyPure fun _ =>
      match (ofHex katSk[i]!).bind (decodeKey · 10),
          (ofHex katPk[i]!).bind (decodePk · 10) with
      | some k, some h => s!"decode=1 ntru={b2 (ntruB k)} pk={b2 (pkMatchB h k)}"
      | some _, none => "decode=1 pkdecode=0"
      | none, _ => "decode=0"
    let t1 ← IO.monoMsNow
    IO.println s!"key={i} {r} ms={t1 - t0}"

def runCfg (rm : RMode) (n lo hi : ℕ) : IO Unit := do
  let P : XChoices := ⟨rm, rm, .direct, .plain⟩
  for i in [lo:hi] do
    match (ofHex katSk[i]!).bind (decodeKey · 10) with
    | none => IO.println s!"cfg={repr rm} xn={n} key={i} decode=0"
    | some k =>
      let t0 ← IO.monoMsNow
      let c ← IO.lazyPure fun _ =>
        checkFast P n δ127q_1024 k 256 7365 (1298280334 / 10 ^ 9) lam1024q σ1024q
      let t1 ← IO.monoMsNow
      let r ← IO.lazyPure fun _ => diag P n k
      let t2 ← IO.monoMsNow
      IO.println (s!"cfg={repr rm} xn={n} key={i} checkFast127={b2 c} {r} " ++
        s!"msCheck={t1 - t0} msDiag={t2 - t1}")
