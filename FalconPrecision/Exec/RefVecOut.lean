/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.RefVec
public import FalconPrecision.Exec.CodecKat
public import FalconPrecision.Exec.Instance45

/-! # Reference vectors of round-3 KAT entries, and their JSON form

`katIn e`: the key of `sk`, the hashed point `c = HashToPoint(r ‖ m)` of `sm` (`Exec.Verify`,
Lean), the signature `(s1, s2)` (`s1 = c - s2·h mod q`, `s1Of`), and `(z0, z1)`: the unique `z` with
`s = (c, 0) - z·B` (`zOfSig`, checked: `zOfSig_spec`); equal to the reference signer's SamplerZ
outputs by round-3 Alg. 10 (`s = (t - z)·B`), not proved. `katIn_spec`: what `katIn` computes.
`genVecAt δq e`: `refVecB δq` on them, printed as JSON (`vecJson`; format
`falcon-precision-refvec/1`) with its scope (hypotheses, `checkFast` evaluated for this key at
ties to even, `xn = 0` and `xn = 32`, what is not covered), each line prefixed by
`@@VEC <file> `; `genVec` at `δ45q`. The printer is not proved; it prints the integers of the
vector. `zOfSigP`, `vecJsonN`, `scopeJsonN`: the same at every size, the text naming the KAT file
and the theorems through `VecNames` (`names512`; Falcon-1024: `Exec.RefVec1024`). -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec

/-! ## The SamplerZ outputs of a signature -/

/-- `zOfSig` at every size `2^logn`. -/
def zOfSigP {logn : ℕ} (k : RawKey logn) (c s1 s2 : ZPoly logn) :
    Option (ZPoly logn × ZPoly logn) :=
  let a := Round3.polyOf (Array.ofFn fun i => c i - s1 i) logn
  let z0 := Round3.polyOf (Array.ofFn fun i => -((ncoef a k.F i - ncoef s2 k.G i) / 12289)) logn
  let z1 := Round3.polyOf (Array.ofFn fun i => -((ncoef s2 k.g i - ncoef a k.f i) / 12289)) logn
  if (List.finRange (2 ^ logn)).all fun i =>
      decide ((sOf k c z0 z1).1 i = s1 i ∧ (sOf k c z0 z1).2 i = s2 i) then some (z0, z1)
  else none

theorem zOfSigP_spec {logn : ℕ} {k : RawKey logn} {c s1 s2 z0 z1 : ZPoly logn}
    (h : zOfSigP k c s1 s2 = some (z0, z1)) : sOf k c z0 z1 = (s1, s2) := by
  revert h
  simp only [zOfSigP]
  split_ifs with hb
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [List.all_eq_true] at hb
    have hb' := fun i => of_decide_eq_true (hb i (List.mem_finRange i))
    exact Prod.ext (funext fun i => (hb' i).1) (funext fun i => (hb' i).2)
  · intro h
    cases h

/-- `(z0, z1)` with `s = (c, 0) - z·B`, `B = [[g, -f], [G, -F]]`:
`z·[[g, f], [G, F]] = (c - s1, s2)`, `det = gF - fG = -q`; `none` unless
`sOf k c z0 z1 = (s1, s2)` exactly. -/
def zOfSig (k : RawKey) (c s1 s2 : ZPoly) : Option (ZPoly × ZPoly) :=
  let a := Round3.polyOf (Array.ofFn fun i => c i - s1 i)
  let z0 := Round3.polyOf (Array.ofFn fun i => -((ncoef a k.F i - ncoef s2 k.G i) / 12289))
  let z1 := Round3.polyOf (Array.ofFn fun i => -((ncoef s2 k.g i - ncoef a k.f i) / 12289))
  if (List.finRange (2 ^ 9)).all fun i =>
      decide ((sOf k c z0 z1).1 i = s1 i ∧ (sOf k c z0 z1).2 i = s2 i) then some (z0, z1)
  else none

theorem zOfSig_eq (k : RawKey) (c s1 s2 : ZPoly) : zOfSig k c s1 s2 = zOfSigP k c s1 s2 := rfl

theorem zOfSig_spec {k : RawKey} {c s1 s2 z0 z1 : ZPoly} (h : zOfSig k c s1 s2 = some (z0, z1)) :
    sOf k c z0 z1 = (s1, s2) :=
  zOfSigP_spec h

/-- The inputs of the vector of a KAT entry: key, `c`, `s1`, `s2`, `z0`, `z1`. -/
def katIn (e : Codec.KatEntry) : Option (RawKey × ZPoly × ZPoly × ZPoly × ZPoly × ZPoly) :=
  ((Round3.ofHex e.sk).bind Round3.decodeKey).bind fun k =>
  (Codec.decodeSm Codec.round3 (Codec.hexL e.sm)).bind fun x =>
  (Codec.hashToPoint 512 (x.1 ++ x.2.1)).bind fun cl =>
  (Codec.decodePk Codec.round3 (Codec.hexL e.pk)).bind fun hv =>
    let c := Round3.polyOf (cl.map Int.ofNat).toArray
    let s2 := Round3.polyOf x.2.2.toArray
    let s1 := Round3.polyOf (Array.ofFn (Codec.s1Of cl x.2.2 (hv.map Int.ofNat)))
    (zOfSig k c s1 s2).map fun z => (k, c, s1, s2, z.1, z.2)

theorem polyOf_ofFn (f : Fin (2 ^ 9) → ℤ) : Round3.polyOf (Array.ofFn f) = f := by
  funext i
  simp [Round3.polyOf]

/-- What `katIn` computes. -/
theorem katIn_spec {e : Codec.KatEntry} {k : RawKey} {c s1 s2 z0 z1 : ZPoly}
    (h : katIn e = some (k, c, s1, s2, z0, z1)) :
    (Round3.ofHex e.sk).bind Round3.decodeKey = some k ∧
      (∃ salt msg s2l cl hv, Codec.decodeSm Codec.round3 (Codec.hexL e.sm) = some (salt, msg, s2l) ∧
        Codec.hashToPoint 512 (salt ++ msg) = some cl ∧
        Codec.decodePk Codec.round3 (Codec.hexL e.pk) = some hv ∧
        c = Round3.polyOf (cl.map Int.ofNat).toArray ∧ s2 = Round3.polyOf s2l.toArray ∧
        s1 = Codec.s1Of cl s2l (hv.map Int.ofNat)) ∧
      sOf k c z0 z1 = (s1, s2) := by
  unfold katIn at h
  generalize (Round3.ofHex e.sk).bind Round3.decodeKey = oK at h
  generalize Codec.decodeSm Codec.round3 (Codec.hexL e.sm) = oS at h
  generalize Codec.decodePk Codec.round3 (Codec.hexL e.pk) = oP at h
  obtain _ | k' := oK <;> dsimp only [Option.bind] at h
  · cases h
  obtain _ | ⟨salt, msg, s2l⟩ := oS <;> dsimp only [Option.bind] at h
  · cases h
  generalize hH : Codec.hashToPoint 512 (salt ++ msg) = oH at h
  obtain _ | cl := oH <;> dsimp only [Option.bind] at h
  · cases h
  obtain _ | hv := oP <;> dsimp only [Option.bind] at h
  · cases h
  obtain ⟨⟨z0', z1'⟩, hz, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
  exact ⟨rfl, ⟨salt, msg, s2l, cl, hv, rfl, hH, rfl, rfl, rfl, polyOf_ofFn _⟩, zOfSig_spec hz⟩

/-! ## JSON -/

/-- A JSON list. -/
def jL (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

/-- A JSON object. -/
def jO (l : List String) : String := "{" ++ ",".intercalate l ++ "}"

/-- A JSON string (no escaping needed for the keys and values used here). -/
def jS (s : String) : String := "\"" ++ s ++ "\""

/-- A JSON field. -/
def jF (k v : String) : String := jS k ++ ":" ++ v

/-- A radius `r` as `⌈r·2⁹⁶⌉` (exact: radii are on the grid `2⁻⁹⁶`). -/
def jRad (b : CB 64) : String := match b.r with
  | some r => toString ⌈r * 2 ^ 96⌉
  | none => "null"

/-- A ball `[re, im, r]`: centre `(re + i·im)/2⁶⁴`, radius `r/2⁹⁶`. -/
def jB (b : MB) : String := jL [toString b.b.c.re.m, toString b.b.c.im.m, jRad b.b]

/-- A vector over `Out L` in slot order `Out.ofIdx`. -/
def jV (L : ℕ) (v : Out L → MB) : String :=
  jL ((List.range (2 ^ L)).map fun j => jB (v (Out.ofIdx L j)))

/-- An integer polynomial. -/
def jZ (a : ZPoly) : String := jL ((List.finRange (2 ^ 9)).map fun i => toString (a i))

/-- An integer polynomial of size `2^logn`. -/
def jZP {logn : ℕ} (a : ZPoly logn) : String :=
  jL ((List.finRange (2 ^ logn)).map fun i => toString (a i))

/-- The nodes of a trace in run order, with the path of child choices (`1` = `T1`). -/
def RunT.jNodes : {L : ℕ} → RunT MB L → String → List String
  | _, .leaf _ _ _ _ _, _ => []
  | _, @RunT.node _ L t0 t1 ℓ r1 zh1 t0u r0 zh0, p =>
    jO [jF "path" (jS p), jF "L" (toString (L + 1)), jF "t0" (jV (L + 1) t0),
      jF "t1" (jV (L + 1) t1), jF "l" (jV (L + 1) ℓ), jF "z1hat" (jV (L + 1) zh1),
      jF "t0new" (jV (L + 1) t0u), jF "z0hat" (jV (L + 1) zh0)] ::
      (r1.jNodes (p ++ "1") ++ r0.jNodes (p ++ "0"))

/-- The fields of the leaves of a trace in run order. -/
def RunT.jLeaves : {L : ℕ} → RunT MB L → String → List (List String)
  | _, .leaf σ t0 t1 z0 z1, p =>
    [[jF "path" (jS p), jF "sigma" (jB σ), jF "t0" (jB t0), jF "t1" (jB t1),
      jF "z0" (toString z0), jF "z1" (toString z1)]]
  | _, .node _ _ _ r1 _ _ r0 _, p => r1.jLeaves (p ++ "1") ++ r0.jLeaves (p ++ "0")

/-- Every entry of a trace. -/
def RunT.entries {V : Type} : {L : ℕ} → RunT V L → List V
  | _, .leaf σ t0 t1 _ _ => [σ, t0, t1]
  | _, @RunT.node _ L t0 t1 ℓ r1 zh1 t0u r0 zh0 =>
    ((List.range (2 ^ (L + 1))).flatMap fun j =>
      let o := Out.ofIdx (L + 1) j
      [t0 o, t1 o, ℓ o, zh1 o, t0u o, zh0 o]) ++ r1.entries ++ r0.entries

/-- Every entry of a trace. -/
def SignT.entries {V : Type} (A : SignT V) : List V :=
  ((List.range (2 ^ 9)).flatMap fun j =>
    let o := Out.ofIdx 9 j
    [A.ch o, A.fh o, A.Fh o, A.t0 o, A.t1 o]) ++ A.run.entries

/-- Every entry of a trace of size `2^logn`. -/
def SignT.entriesP {V : Type} {logn : ℕ} (A : SignT V logn) : List V :=
  ((List.range (2 ^ logn)).flatMap fun j =>
    let o := Out.ofIdx logn j
    [A.ch o, A.fh o, A.Fh o, A.t0 o, A.t1 o]) ++ A.run.entries

/-- The largest value of a list (`0` if empty). -/
def maxQ (l : List ℚ) : ℚ := l.foldl max 0

/-- What the text of a vector names: the KAT file and its sha256, the suffix of the soundness
theorems, the table condition, the check, the word condition, the stored tree and the solver of
`z`. -/
structure VecNames where
  kat : String
  sha : String
  sfx : String
  tw : String
  chk : String
  mag : String
  tree : String
  zs : String

/-- The names of the Falcon-512 vectors. -/
def names512 : VecNames :=
  ⟨"falcon512-KAT.rsp", "dd75c946fdedef4ec46a2bee7e10c65c9126f1a839b9ced6921fd45f7354b5cd", "",
    "twOk C.x.rc", "check", "magOkB", "storeC C.x C.xn k", "zOfSig"⟩

/-- The scope of a vector named by `nm`: conditioning, hypotheses at `δq` (named `dq`), the
evaluated check values `chk` (point, value), control flag (no evaluated point passes), what is
not covered. -/
def scopeJsonN (nm : VecNames) (dq : String) (chk : List (String × Bool)) : String :=
  let ctl := !(chk.any (·.2))
  jO [jF "conditioning" (jS ("SamplerZ replaced by the tape: call j answered by tape[j]; z is " ++
      "the unique solution of s = (c,0) - zB (" ++ nm.zs ++ ", checked exactly)")),
    jF "hypothesis" (jS ("refVec_sound" ++ nm.sfx ++ ": every point C with " ++ nm.tw ++ " and " ++
      nm.chk ++ " C.x C.xn " ++ dq ++ " k = true at that point (rm, rc, dm, root, xn all enter " ++
      nm.chk ++ "), unbounded words; " ++ "refVec_word" ++ nm.sfx ++
      ": the same at (i+64)-bit words, 1 <= i, when " ++ nm.mag ++ " C.target i; " ++
      "refVec_exact" ++ nm.sfx ++ ": the exact values (fG - gF = q)")),
    jF "check" (jO (chk.map fun x => jF x.1 (toString x.2))),
    jF "control" (toString ctl),
    jF "controlNote" (jS (if ctl then nm.chk ++ " fails at every evaluated point: refVec_sound" ++
      nm.sfx ++ " and refVec_word" ++ nm.sfx ++ " are not available for this key as stated; " ++
      "refVec_exact" ++ nm.sfx ++ " is"
      else nm.chk ++ " holds at the evaluated points marked true")),
    jF "notCovered" (jS ("binary64 (floating-point) implementations; operation orders other " ++
      "than the Choices order (fftW, splitW, mergeW, updW, targetX; only the target has two " ++
      "orders), e.g. another association order or a half-spectrum FFT; key expansion on words " ++
      "(the tree is the unbounded " ++ nm.tree ++ ", also in refVec_word" ++ nm.sfx ++ "); " ++
      "the printer is not proved")),
    jF "reading" (jS ("necessary, not sufficient: a value outside its disc is not produced by " ++
      "any point satisfying the hypothesis; a value inside shows nothing more (one key, one " ++
      "message, one tape)"))]

/-- The scope of a vector: conditioning, hypotheses at `δq` (named `dq`), the evaluated `check`
values `chk` (point, value), control flag (no evaluated point passes), what is not covered. -/
def scopeJson (dq : String) (chk : List (String × Bool)) : String := scopeJsonN names512 dq chk

/-- The JSON form of a vector of size `2^logn` named by `nm`, at `δq` (named `dq`, described by
`desc`), with the evaluated check values `chk`. -/
def vecJsonN {logn : ℕ} (nm : VecNames) (count : ℕ) (dq desc : String)
    (chk : List (String × Bool)) (k : RawKey logn) (c s1 s2 z0 z1 : ZPoly logn)
    (V : SignT MB logn) : List String :=
  let es := V.entriesP
  let rad := maxQ (es.map fun b => (b.b.r.getD 0))
  let nrm := ((List.finRange (2 ^ logn)).map fun i => s1 i ^ 2 + s2 i ^ 2).sum
  let leaves := V.run.jLeaves ""
  let calls := (List.range leaves.length).zip leaves
  ["{" ++ jF "format" (jS "falcon-precision-refvec/1") ++ ",",
    jF "source" (jO [jF "kat" (jS nm.kat), jF "sha256" (jS nm.sha),
      jF "count" (toString count)]) ++ ",",
    jF "params" (jO [jF "dq" (jS (dq ++ ": " ++ desc)),
      jF "refPoint" (jS "rm=rc=halfEven, dm=direct, root=plain, xn=32"),
      jF "ball" (jS "[re,im,r]: |x - (re + i*im)/2^64| <= r/2^96"),
      jF "slot" (jS "slot j of a level-L vector: value at exp(i*pi*k_j/2^L), k = slots[L][j]"),
      jF "tape" (jS "SamplerZ outputs in call order: node T1 then T0, leaf z0 then z1")]) ++ ",",
    jF "scope" (scopeJsonN nm dq chk) ++ ",",
    jF "f" (jZP k.f) ++ ",", jF "g" (jZP k.g) ++ ",", jF "F" (jZP k.F) ++ ",",
    jF "G" (jZP k.G) ++ ",", jF "c" (jZP c) ++ ",", jF "s1" (jZP s1) ++ ",",
    jF "s2" (jZP s2) ++ ",", jF "norm2" (toString nrm) ++ ",", jF "z0" (jZP z0) ++ ",",
    jF "z1" (jZP z1) ++ ",",
    jF "tape" (jL ((tapeOf logn z0 z1).map toString)) ++ ",",
    jF "mag" (jO [jF "scaleFirst" (toString ⌈maxQ (es.map (·.mS))⌉),
      jF "multiplyFirst" (toString ⌈maxQ (es.map (·.mM))⌉),
      jF "fits32_scaleFirst" (toString (V.magOkBP .scaleFirst 32)),
      jF "fits64_scaleFirst" (toString (V.magOkBP .scaleFirst 64)),
      jF "fits32_multiplyFirst" (toString (V.magOkBP .multiplyFirst 32)),
      jF "fits64_multiplyFirst" (toString (V.magOkBP .multiplyFirst 64)),
      jF "maxRadius" (toString ⌈rad * 2 ^ 96⌉)]) ++ ",",
    jF "slots" (jO ((List.range (logn + 1)).map fun L =>
      jF (toString L) (jL ((List.range (2 ^ L)).map fun j => toString (slotK L (Out.ofIdx L j))))))
      ++ ",",
    jF "fft_c" (jV logn V.ch) ++ ",", jF "fft_f" (jV logn V.fh) ++ ",",
    jF "fft_F" (jV logn V.Fh) ++ ",", jF "t0" (jV logn V.t0) ++ ",", jF "t1" (jV logn V.t1) ++ ",",
    jS "nodes" ++ ":["] ++
  (V.run.jNodes "").intersperse "," ++ ["],", jS "leaves" ++ ":["] ++
  (calls.map fun x => jO (jF "call" (toString (2 * x.1)) :: x.2)).intersperse "," ++
  ["]}"]

/-- The JSON form of a vector at `δq` (named `dq`, described by `desc`), with the evaluated
`check` values `chk`. -/
def vecJson (count : ℕ) (dq desc : String) (chk : List (String × Bool)) (k : RawKey)
    (c s1 s2 z0 z1 : ZPoly) (V : SignT MB) : List String :=
  vecJsonN names512 count dq desc chk k c s1 s2 z0 z1 V

/-- The vector of a KAT entry at `δq` (named `dq`, described by `desc`), as lines
`@@VEC e<count>.json <json line>`, followed by a summary line; `check` (as `checkFast`,
`checkFast_eq`) evaluated at `P0` with `xn = 0` and `xn = 32`. -/
def genVecAt (δq : ℕ → ℚ) (dq desc : String) (e : Codec.KatEntry) : String :=
  match katIn e with
  | none => "entry " ++ toString e.count ++ ": katIn none"
  | some (k, c, s1, s2, z0, z1) =>
    match refVecB δq k c z0 z1 with
    | none => "entry " ++ toString e.count ++ ": refVecB none"
    | some V =>
      let chk := [("rm=rc=halfEven, dm=direct, root=plain, xn=0", checkFast P0 0 δq k),
        ("rm=rc=halfEven, dm=direct, root=plain, xn=32", checkFast P0 32 δq k)]
      let pre := "@@VEC e" ++ toString e.count ++ ".json "
      "\n".intercalate ((vecJson e.count dq desc chk k c s1 s2 z0 z1 V).map (pre ++ ·)) ++
        "\nentry " ++ toString e.count ++ " " ++ dq ++ ": refVecB some; magOkB sf32 " ++
        toString (V.magOkB .scaleFirst 32) ++ " sf64 " ++ toString (V.magOkB .scaleFirst 64) ++
        " mf32 " ++ toString (V.magOkB .multiplyFirst 32) ++ " mf64 " ++
        toString (V.magOkB .multiplyFirst 64) ++ "; checkFast xn0 " ++ toString chk[0]!.2 ++
        " xn32 " ++ toString chk[1]!.2

/-- The vector of a KAT entry at `δ45q`. -/
def genVec (e : Codec.KatEntry) : String := genVecAt δ45q "delta45q" "2^-45 at every level" e

end FalconPrecision.Exec
