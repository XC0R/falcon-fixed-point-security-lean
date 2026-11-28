/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.RefVecOut
public import FalconPrecision.Exec.KeyCheck1024
public import FalconPrecision.Exec.Falcon1024Codec

/-! # Certified interval reference vectors at Falcon-1024

The Falcon-1024 instances of `Exec.RefBall`, `Exec.RefVec` and `Exec.RefVecOut` (size `2^10`,
tables at levels `< 10`, `σ1024q`).

`refTree1024 δq k : GTree MB 10`: the balls `storeB P0 32 k σ1024q` (ties to even, `xn = 32`),
node balls widened by `δq`, leaf balls by `σtol = 1.825·2⁻⁴²`: what `check1024`'s leaf test
`CB.leafOkB` allows (`s + r ≤ 1.825` and `2⁴²·r ≤ s - r` give `r ≤ 1.825·2⁻⁴²`; the same test as
at Falcon-512). `refVecB1024 δq k c z0 z1`: the ball trace of one signing attempt conditioned on
the SamplerZ outputs `(z0, z1)` (in call order `tapeOf 10 z0 z1`, 2048 values).

* `refVec_sound1024`: every design point `C` with unbounded words, `twOkN C.x.rc 10` and a key
  passing `check1024 C.x C.xn δq`: every intermediate of the attempt at `C` (`traceX1024`) lies
  in its ball. `refVec_adm1024`: the `AdmN 10` points.
* `refVec_word1024`: the same at `(i + 64)`-bit words, `1 ≤ i`, when `magOkBP C.target i`.
* `refVec_exact1024`: the exact attempt on the true tree at `σ1024` (`traceE1024`).
* `signX_log1024`: the trace's leaf values are the queries SamplerZ receives in `signX` when it
  answers by the tape.
* `katIn1024 e`: key, `c = HashToPoint(r ‖ m)` (`n = 1024`), `(s1, s2)` and `(z0, z1)` of a
  Falcon-1024 round-3 KAT entry (`zOfSigP`, checked: `katIn1024_spec`); `genVecAt1024`: the vector
  as JSON (`falcon-precision-refvec/1`) with `checkFast` at the `check1024` thresholds at `P0`,
  `xn = 0` and `xn = 32`.

Not proved here: that `refVecB1024 … = some V` (by `#eval` in the generation runs), that a key
passes `check1024`, that `twOkN C.x.rc 10` holds for a given rounding (`#eval` only), what holds
for sampler answers other than the tape, that `(z0, z1)` equals the reference signer's SamplerZ
outputs; the printer. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.HopB

/-! ## The reference tree -/

/-- **The Falcon-1024 reference tree**: `storeB P0 32 k σ1024q` (array version) widened for
`check1024` at `δq`. -/
def refTree1024 (δq : ℕ → ℚ) (k : RawKey 10) : GTree MB 10 :=
  ((expandBA P0 (64 + 32) k σ1024q).lower P0.rm 32).toGW δq

/-- The stored tree of every point passing `check1024` at `δq` lies in the reference tree. -/
theorem treeX1024 (C : Choices) (δq : ℕ → ℚ) (k : RawKey 10)
    (hk : check1024 C.x C.xn δq k = true) :
    (refTree1024 δq k).Rel RX (storeC C.x C.xn k σ1024q).toG := by
  have hc := check_ok C.x C.xn hk
  rw [← storeB_centreP, refTree1024, expandBA_eqP]
  exact BTree.toGW_relX δq _ _ _
    (storeB_holdsTP P0 32 σ1024 σ1024q σ1024_eq (by norm_num [σ1024q]) k hc.ntru)
    (storeB_holdsTP C.x C.xn σ1024 σ1024q σ1024_eq (by norm_num [σ1024q]) k hc.ntru) hc.rad

/-- The true tree at `σ1024` lies in the reference tree. -/
theorem treeE1024 (δq : ℕ → ℚ) (hδ : ∀ L, 0 ≤ δq L) (k : RawKey 10) (hn : ntruB k = true) :
    (refTree1024 δq k).Rel RE (k.trueTree σ1024).toG := by
  rw [refTree1024, expandBA_eqP]
  exact BTree.toGW_relE δq hδ _ _
    (storeB_holdsTP P0 32 σ1024 σ1024q σ1024_eq (by norm_num [σ1024q]) k hn)

/-! ## Vectors -/

/-- The conditioned attempt of the signer at `C` on its stored Falcon-1024 tree. -/
def traceX1024 (C : Choices) (k : RawKey 10) (c z0 z1 : ZPoly 10) : SignT (Cx 64) 10 :=
  (opsX C).sign C.target (storeC C.x C.xn k σ1024q).toG k.f k.F c z0 z1

/-- The exact conditioned attempt on the Falcon-1024 true tree. -/
noncomputable def traceE1024 (k : RawKey 10) (c z0 z1 : ZPoly 10) : SignT ℂ 10 :=
  opsE.sign .scaleFirst (k.trueTree σ1024).toG k.f k.F c z0 z1

/-- **The Falcon-1024 reference vector**: `none` unless every radius is known and
`fG - gF = q`. -/
def refVecB1024 (δq : ℕ → ℚ) (k : RawKey 10) (c z0 z1 : ZPoly 10) : Option (SignT MB 10) :=
  refVecBT 10 (refTree1024 δq k) k c z0 z1

/-- **Reference vectors at Falcon-1024, every unbounded design point with `twOkN C.x.rc 10`**: on
a key passing `check1024 C.x C.xn δq`, every intermediate of the attempt at `C` conditioned on
`(z0, z1)` lies in its ball. `refVecB1024 … = some V`, `check1024 … = true` and
`twOkN C.x.rc 10 = true` are hypotheses (`#eval` evidence only). -/
theorem refVec_sound1024 (C : Choices) (hw : C.word = none) (htw : twOkN C.x.rc 10 = true)
    (δq : ℕ → ℚ) (k : RawKey 10) (hk : check1024 C.x C.xn δq k = true) (c z0 z1 : ZPoly 10)
    (V : SignT MB 10) (hV : refVecB1024 δq k c z0 z1 = some V) :
    V.Rel RX (traceX1024 C k c z0 z1) :=
  refVecBT_sound 10 C hw htw (refTree1024 δq k) _ (treeX1024 C δq k hk) k c z0 z1 V hV

/-- The points `AdmN 10 C` (`Exec.SignRefine`). -/
theorem refVec_adm1024 (C : Choices) (hC : AdmN 10 C) (δq : ℕ → ℚ) (k : RawKey 10)
    (hk : check1024 C.x C.xn δq k = true) (c z0 z1 : ZPoly 10) (V : SignT MB 10)
    (hV : refVecB1024 δq k c z0 z1 = some V) : V.Rel RX (traceX1024 C k c z0 z1) :=
  refVec_sound1024 C hC.word hC.tw δq k hk c z0 z1 V hV

/-- **Reference vectors at Falcon-1024, words**: at `(i + 64)`-bit words, `1 ≤ i`, when every
operation magnitude of the order `C.target` in the vector is below `2^(i-1)` (`magOkBP`), every
intermediate lies in its ball. Key expansion is unbounded (`storeC`). -/
theorem refVec_word1024 (C : Choices) {i : ℕ} (hi : 1 ≤ i) (hw : C.word = some i)
    (htw : twOkN C.x.rc 10 = true) (δq : ℕ → ℚ) (k : RawKey 10)
    (hk : check1024 C.x C.xn δq k = true) (c z0 z1 : ZPoly 10) (V : SignT MB 10)
    (hV : refVecB1024 δq k c z0 z1 = some V) (hm : V.magOkBP C.target i = true) :
    V.Rel RX (traceX1024 C k c z0 z1) :=
  refVecBT_word 10 C hi hw htw (refTree1024 δq k) _ (treeX1024 C δq k hk) k c z0 z1 V hV hm

/-- **The exact Falcon-1024 attempt** lies in the same balls (no key check needed). -/
theorem refVec_exact1024 (δq : ℕ → ℚ) (hδ : ∀ L, 0 ≤ δq L) (k : RawKey 10) (c z0 z1 : ZPoly 10)
    (V : SignT MB 10) (hV : refVecB1024 δq k c z0 z1 = some V) :
    V.Rel RE (traceE1024 k c z0 z1) :=
  refVecBT_exact 10 (refTree1024 δq k) (k.trueTree σ1024) k (treeE1024 δq hδ k) c z0 z1 V hV

/-- **The Falcon-1024 signer's SamplerZ queries**: with a sampler answering by the tape of
`(z0, z1)` and no range checks, the attempt `signX` on the stored tree returns `(z0, z1)` and its
queries are the trace's leaf values. -/
theorem signX_log1024 (C : Choices) (hr : C.rchk = none) (k : RawKey 10) (c z0 z1 : ZPoly 10)
    (hc : ∀ i, |c i| < 12289) (g : ℕ → ℤ)
    (hg : ∀ i, i < (tapeOf 10 z0 z1).length → g i = (tapeOf 10 z0 z1).getD i 0) :
    ((signX C (logS g) (storeC C.x C.xn k σ1024q) k c).run (0, [])).run =
      (some (z0, z1), ((tapeOf 10 z0 z1).length, (traceX1024 C k c z0 z1).run.queries)) :=
  signX_logP C hr _ k c z0 z1 hc g hg

/-! ## KAT entries and JSON -/

/-- The inputs of the vector of a Falcon-1024 KAT entry: key, `c`, `s1`, `s2`, `z0`, `z1`. -/
def katIn1024 (e : Codec.KatEntry) :
    Option (RawKey 10 × ZPoly 10 × ZPoly 10 × ZPoly 10 × ZPoly 10 × ZPoly 10) :=
  ((Round3.ofHex e.sk).bind (Round3.decodeKey · 10)).bind fun k =>
  (Codec.decodeSm Codec.round3_1024 (Codec.hexL e.sm)).bind fun x =>
  (Codec.hashToPoint 1024 (x.1 ++ x.2.1)).bind fun cl =>
  (Codec.decodePk Codec.round3_1024 (Codec.hexL e.pk)).bind fun hv =>
    let c := Round3.polyOf (cl.map Int.ofNat).toArray 10
    let s2 := Round3.polyOf x.2.2.toArray 10
    let s1 := Round3.polyOf (Array.ofFn (Codec.s1Of cl x.2.2 (hv.map Int.ofNat) 10)) 10
    (zOfSigP k c s1 s2).map fun z => (k, c, s1, s2, z.1, z.2)

theorem polyOf_ofFn1024 (f : Fin (2 ^ 10) → ℤ) : Round3.polyOf (Array.ofFn f) 10 = f := by
  funext i
  simp [Round3.polyOf]

/-- What `katIn1024` computes. -/
theorem katIn1024_spec {e : Codec.KatEntry} {k : RawKey 10} {c s1 s2 z0 z1 : ZPoly 10}
    (h : katIn1024 e = some (k, c, s1, s2, z0, z1)) :
    (Round3.ofHex e.sk).bind (Round3.decodeKey · 10) = some k ∧
      (∃ salt msg s2l cl hv,
        Codec.decodeSm Codec.round3_1024 (Codec.hexL e.sm) = some (salt, msg, s2l) ∧
        Codec.hashToPoint 1024 (salt ++ msg) = some cl ∧
        Codec.decodePk Codec.round3_1024 (Codec.hexL e.pk) = some hv ∧
        c = Round3.polyOf (cl.map Int.ofNat).toArray 10 ∧
        s2 = Round3.polyOf s2l.toArray 10 ∧ s1 = Codec.s1Of cl s2l (hv.map Int.ofNat) 10) ∧
      sOf k c z0 z1 = (s1, s2) := by
  unfold katIn1024 at h
  generalize (Round3.ofHex e.sk).bind (Round3.decodeKey · 10) = oK at h
  generalize Codec.decodeSm Codec.round3_1024 (Codec.hexL e.sm) = oS at h
  generalize Codec.decodePk Codec.round3_1024 (Codec.hexL e.pk) = oP at h
  obtain _ | k' := oK <;> dsimp only [Option.bind] at h
  · cases h
  obtain _ | ⟨salt, msg, s2l⟩ := oS <;> dsimp only [Option.bind] at h
  · cases h
  generalize hH : Codec.hashToPoint 1024 (salt ++ msg) = oH at h
  obtain _ | cl := oH <;> dsimp only [Option.bind] at h
  · cases h
  obtain _ | hv := oP <;> dsimp only [Option.bind] at h
  · cases h
  obtain ⟨⟨z0', z1'⟩, hz, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
  exact ⟨rfl, ⟨salt, msg, s2l, cl, hv, rfl, hH, rfl, rfl, rfl, polyOf_ofFn1024 _⟩,
    zOfSigP_spec hz⟩

/-- The names of the Falcon-1024 vectors. -/
def names1024 : VecNames :=
  ⟨"falcon1024-KAT.rsp", "036a0bf5260573cec44977284dfef756cd1143db9961b981bd1fb55828acb20d",
    "1024", "twOkN C.x.rc 10", "check1024", "magOkBP", "storeC C.x C.xn k sigma1024q", "zOfSigP"⟩

/-- The vector of a Falcon-1024 KAT entry at `δq` (named `dq`, described by `desc`), as lines
`@@VEC e<count>.json <json line>`, followed by a summary line; `check1024` (as `checkFast` at its
thresholds, `checkFast_eq1024`) evaluated at `P0` with `xn = 0` and `xn = 32`. -/
def genVecAt1024 (δq : ℕ → ℚ) (dq desc : String) (e : Codec.KatEntry) : String :=
  match katIn1024 e with
  | none => "entry " ++ toString e.count ++ ": katIn1024 none"
  | some (k, c, s1, s2, z0, z1) =>
    match refVecB1024 δq k c z0 z1 with
    | none => "entry " ++ toString e.count ++ ": refVecB1024 none"
    | some V =>
      let ck := fun n => checkFast P0 n δq k 256 7365 (1298280334 / 10 ^ 9) lam1024q σ1024q
      let chk := [("rm=rc=halfEven, dm=direct, root=plain, xn=0", ck 0),
        ("rm=rc=halfEven, dm=direct, root=plain, xn=32", ck 32)]
      let pre := "@@VEC e" ++ toString e.count ++ ".json "
      "\n".intercalate ((vecJsonN names1024 e.count dq desc chk k c s1 s2 z0 z1 V).map
          (pre ++ ·)) ++
        "\nentry " ++ toString e.count ++ " " ++ dq ++ ": refVecB1024 some; magOkBP sf32 " ++
        toString (V.magOkBP .scaleFirst 32) ++ " sf64 " ++ toString (V.magOkBP .scaleFirst 64) ++
        " mf32 " ++ toString (V.magOkBP .multiplyFirst 32) ++ " mf64 " ++
        toString (V.magOkBP .multiplyFirst 64) ++ "; checkFast1024 xn0 " ++ toString chk[0]!.2 ++
        " xn32 " ++ toString chk[1]!.2

end FalconPrecision.Exec
