/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.RefBall

/-! # Certified interval reference vectors of a signing attempt

A vector is the ball trace `refVecB δq k c z0 z1 : Option (SignT MB)` of one signing attempt on
the key `k`, the hashed point `c`, conditioned on the SamplerZ outputs `(z0, z1)` (in call order
`tapeOf 9 z0 z1`): FFTs, target (hull of both orders), and every node and leaf value of
ffSampling (`Exec.RefRun`), radii on the grid `2⁻⁹⁶`.

* `refVec_sound`: for every design point `C` with unbounded words, tables passing `twOk` and a key
  passing `check C.x C.xn δq`, every intermediate of the attempt at `C` (`traceX`) lies in its
  ball. It holds at every point with `twOk C.x.rc` and `check C.x C.xn δq k` at that point (rm,
  rc, dm, root, xn all enter `check`; `twOk .floor` is `false` by `#eval`); both target orders
  and both stored `1/q` are free; `rchk`, `salt`, `cap`, `beta2`, `infB`, `samp` do not enter
  the conditioned attempt. `refVec_adm`: the `Adm` points (`Exec.SignRefine`).
* `refVec_word`: the same at `(i + 64)`-bit words, `1 ≤ i`, when `magOkB C.target i` (every
  operation of the order `C.target` below `2^(i-1)`).
* `refVec_exact`: the exact attempt (exact FFT, true tree `k.trueTree`, exact operations,
  `traceE`) lies in the same balls.
* `signX_log`: the trace's leaf values are the queries SamplerZ receives in `signX` when it
  answers by the tape.
* `opsE_fft`: the exact FFT is evaluation at `pt L o`; `pt_angle`: `pt L o = exp(iπ·k/2^L)`,
  `k = slotK L o`.

At every size `2^N`, on a ball tree `T` given as a parameter: `refVecBT N T`, `refVecBT_sound`
(`twOkN C.x.rc N`, `T` holding the stored tree at its centres), `refVecBT_word` (`magOkBP`),
`refVecBT_exact`, `signX_logP`; the Falcon-512 statements are their instances at `N = 9` on
`refTree δq k`, the Falcon-1024 ones (`Exec.RefVec1024`) at `N = 10`.

Not proved here: that `refVecB … = some V` (by `#eval` in the generation runs) or that a key passes
`check`; what holds for sampler answers other than the tape. -/

@[expose] public section

namespace FalconPrecision.Exec

open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.Fixed
  FalconPrecision.Errors.HopB

/-! ## Traces -/

/-- The conditioned attempt of the signer at `C` on its stored tree. -/
def traceX (C : Choices) (k : RawKey) (c z0 z1 : ZPoly) : SignT (Cx 64) :=
  (opsX C).sign C.target (storeC C.x C.xn k).toG k.f k.F c z0 z1

/-- The exact conditioned attempt on the true tree. -/
noncomputable def traceE (k : RawKey) (c z0 z1 : ZPoly) : SignT ℂ :=
  opsE.sign .scaleFirst k.trueTree.toG k.f k.F c z0 z1

/-! ## The evaluator -/

/-- The hull of the two target orders: magnitude of each order from its own ball. -/
def hullM (a b : MB) : MB := ⟨a.b.hull b.b, a.mS, b.mM⟩

/-- The radius rounded up to `2⁻⁹⁶`. -/
def coarseM (a : MB) : MB := ⟨a.b.coarse, a.mS, a.mM⟩

/-- The ball trace before rounding the radii. -/
def refRaw (δq : ℕ → ℚ) (k : RawKey) (c z0 z1 : ZPoly) : SignT MB :=
  let ch := opsB.fft 9 c
  let fh := opsB.fft 9 k.f
  let Fh := opsB.fft 9 k.F
  let tS := opsB.target .scaleFirst ch fh Fh
  let tM := opsB.target .multiplyFirst ch fh Fh
  let t0 := fun o => hullM (tS.1 o) (tM.1 o)
  let t1 := fun o => hullM (tS.2 o) (tM.2 o)
  ⟨ch, fh, Fh, t0, t1, opsB.run (refTree δq k) t0 t1 z0 z1⟩

/-- `refRaw` on arrays. -/
def refRawA (δq : ℕ → ℚ) (k : RawKey) (c z0 z1 : ZPoly) : SignT MB :=
  let O := opsBT twTA twsTA
  let ch := ofArr 9 (O.fftA 9 c)
  let fh := ofArr 9 (O.fftA 9 k.f)
  let Fh := ofArr 9 (O.fftA 9 k.F)
  let tS := O.targetA .scaleFirst ch fh Fh
  let tM := O.targetA .multiplyFirst ch fh Fh
  let t0 := ofArr 9 (toArr 9 fun o => hullM (ofArr 9 tS.1 o) (ofArr 9 tM.1 o))
  let t1 := ofArr 9 (toArr 9 fun o => hullM (ofArr 9 tS.2 o) (ofArr 9 tM.2 o))
  ⟨ch, fh, Fh, t0, t1, O.runA (refTree δq k) t0 t1 z0 z1⟩

/-- The ball trace on the tree `T` at size `2^N` (tables `opsBN N`) before rounding the radii. -/
def refRawT (N : ℕ) (T : GTree MB N) (k : RawKey N) (c z0 z1 : ZPoly N) : SignT MB N :=
  let O := opsBN N
  let ch := O.fft N c
  let fh := O.fft N k.f
  let Fh := O.fft N k.F
  let tS := O.target .scaleFirst ch fh Fh
  let tM := O.target .multiplyFirst ch fh Fh
  let t0 := fun o => hullM (tS.1 o) (tM.1 o)
  let t1 := fun o => hullM (tS.2 o) (tM.2 o)
  ⟨ch, fh, Fh, t0, t1, O.run T t0 t1 z0 z1⟩

/-- `refRawT` on arrays. -/
def refRawAT (N : ℕ) (T : GTree MB N) (k : RawKey N) (c z0 z1 : ZPoly N) : SignT MB N :=
  let O := opsBN N
  let ch := ofArr N (O.fftA N c)
  let fh := ofArr N (O.fftA N k.f)
  let Fh := ofArr N (O.fftA N k.F)
  let tS := O.targetA .scaleFirst ch fh Fh
  let tM := O.targetA .multiplyFirst ch fh Fh
  let t0 := ofArr N (toArr N fun o => hullM (ofArr N tS.1 o) (ofArr N tM.1 o))
  let t1 := ofArr N (toArr N fun o => hullM (ofArr N tS.2 o) (ofArr N tM.2 o))
  ⟨ch, fh, Fh, t0, t1, O.runA T t0 t1 z0 z1⟩

theorem refRawAT_eq (N : ℕ) (T : GTree MB N) (k : RawKey N) (c z0 z1 : ZPoly N) :
    refRawAT N T k c z0 z1 = refRawT N T k c z0 z1 := by
  have e := fun τ ch fh Fh => VOps.ofArr_targetAP (opsBN N) (logn := N) τ ch fh Fh
  simp only [refRawAT, refRawT] at e ⊢
  simp only [VOps.ofArr_fftA, e, ofArr_toArr, VOps.runA_eq]

theorem refRawA_eq (δq : ℕ → ℚ) (k : RawKey) (c z0 z1 : ZPoly) :
    refRawA δq k c z0 z1 = refRaw δq k c z0 z1 :=
  refRawAT_eq 9 (refTree δq k) k c z0 z1

/-- **The reference vector on the tree `T`** at size `2^N`: `none` unless every radius is known
and `fG - gF = q`. -/
def refVecBT (N : ℕ) (T : GTree MB N) (k : RawKey N) (c z0 z1 : ZPoly N) :
    Option (SignT MB N) :=
  let V := (refRawAT N T k c z0 z1).map coarseM
  if V.allB (fun b => b.b.r.isSome) && ntruB k then some V else none

/-- **The reference vector**: `none` unless every radius is known and `fG - gF = q`. -/
def refVecB (δq : ℕ → ℚ) (k : RawKey) (c z0 z1 : ZPoly) : Option (SignT MB) :=
  let V := (refRawA δq k c z0 z1).map coarseM
  if V.allB (fun b => b.b.r.isSome) && ntruB k then some V else none

theorem refVecB_eq (δq : ℕ → ℚ) (k : RawKey) (c z0 z1 : ZPoly) :
    refVecB δq k c z0 z1 = refVecBT 9 (refTree δq k) k c z0 z1 := rfl

/-- `magOkB` at every size. -/
def SignT.magOkBP {logn : ℕ} (τ : Target) (i : ℕ) (V : SignT MB logn) : Bool :=
  V.allB fun b => b.b.r.isSome && decide (MB.m τ b < 2 ^ (i - 1))

/-- Every radius known and every operation magnitude of the order `τ` below `2^(i-1)`. -/
def SignT.magOkB (τ : Target) (i : ℕ) (V : SignT MB) : Bool :=
  V.allB fun b => b.b.r.isSome && decide (MB.m τ b < 2 ^ (i - 1))

theorem MB.m_coarseM (τ : Target) (a : MB) : MB.m τ (coarseM a) = MB.m τ a := by
  cases τ <;> rfl

theorem refVecBT_spec {N : ℕ} {T : GTree MB N} {k : RawKey N} {c z0 z1 : ZPoly N}
    {V : SignT MB N} (h : refVecBT N T k c z0 z1 = some V) :
    V = (refRawT N T k c z0 z1).map coarseM ∧ V.allB (fun b => b.b.r.isSome) = true ∧
      ntruB k = true := by
  revert h
  simp only [refVecBT]
  split_ifs with hb
  · intro h
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true] at hb
    rw [refRawAT_eq] at hb ⊢
    exact ⟨rfl, hb.1, hb.2⟩
  · intro h
    cases h

theorem refVecB_spec {δq : ℕ → ℚ} {k : RawKey} {c z0 z1 : ZPoly} {V : SignT MB}
    (h : refVecB δq k c z0 z1 = some V) :
    V = (refRaw δq k c z0 z1).map coarseM ∧ V.allB (fun b => b.b.r.isSome) = true ∧
      ntruB k = true :=
  refVecBT_spec h

theorem CB.hull_isSome {f : ℕ} {a b : CB f} (h : (a.hull b).r.isSome = true) :
    a.r.isSome = true ∧ b.r.isSome = true := by
  cases ha : a.r <;> cases hb : b.r <;> simp_all [CB.hull]

/-- The ball trace on `T` relates to every run of `P` whose operations (tables at levels `< N`)
and tree it simulates; the target hull needs only the lemma of the order `τ`. -/
theorem refRawT_rel {W : Type} [Inhabited W] {P : VOps W} {R : MB → W → Prop} (N : ℕ)
    (h : VSimN N (opsBN N) P R) (τ : Target)
    (hS : τ = .scaleFirst → ∀ a b x, R a x → R (hullM a b) x)
    (hM : τ = .multiplyFirst → ∀ a b x, R b x → R (hullM a b) x) (T : GTree MB N)
    (k : RawKey N) (c z0 z1 : ZPoly N) (T' : GTree W N) (hT : T.Rel R T') :
    (refRawT N T k c z0 z1).Rel R (P.sign τ T' k.f k.F c z0 z1) := by
  have hc := fft_simN h N le_rfl c
  have hf := fft_simN h N le_rfl k.f
  have hF := fft_simN h N le_rfl k.F
  have tS := target_simN h .scaleFirst _ _ _ _ _ _ hc hf hF
  have tM := target_simN h .multiplyFirst _ _ _ _ _ _ hc hf hF
  have ht : ∀ o, R (hullM (((opsBN N).target .scaleFirst ((opsBN N).fft N c)
        ((opsBN N).fft N k.f) ((opsBN N).fft N k.F)).1 o) (((opsBN N).target .multiplyFirst
        ((opsBN N).fft N c) ((opsBN N).fft N k.f) ((opsBN N).fft N k.F)).1 o))
        ((P.target τ (P.fft N c) (P.fft N k.f) (P.fft N k.F)).1 o) ∧
      R (hullM (((opsBN N).target .scaleFirst ((opsBN N).fft N c)
        ((opsBN N).fft N k.f) ((opsBN N).fft N k.F)).2 o) (((opsBN N).target .multiplyFirst
        ((opsBN N).fft N c) ((opsBN N).fft N k.f) ((opsBN N).fft N k.F)).2 o))
        ((P.target τ (P.fft N c) (P.fft N k.f) (P.fft N k.F)).2 o) := by
    intro o
    cases τ
    · exact ⟨hS rfl _ _ _ (tS o).1, hS rfl _ _ _ (tS o).2⟩
    · exact ⟨hM rfl _ _ _ (tM o).1, hM rfl _ _ _ (tM o).2⟩
  unfold SignT.Rel refRawT VOps.sign
  dsimp only
  exact ⟨fun o => ⟨hc o, hf o, hF o, (ht o).1, (ht o).2⟩,
    run_simN h T T' le_rfl hT _ _ _ _ ht z0 z1⟩

/-- The ball trace relates to every run of `P` whose operations and tree it simulates; the target
hull needs only the lemma of the order `τ`. -/
theorem refRaw_rel {W : Type} [Inhabited W] {P : VOps W} {R : MB → W → Prop}
    (h : VSim opsB P R) (τ : Target)
    (hS : τ = .scaleFirst → ∀ a b x, R a x → R (hullM a b) x)
    (hM : τ = .multiplyFirst → ∀ a b x, R b x → R (hullM a b) x) (δq : ℕ → ℚ) (k : RawKey)
    (c z0 z1 : ZPoly) (T' : GTree W 9) (hT : (refTree δq k).Rel R T') :
    (refRaw δq k c z0 z1).Rel R (P.sign τ T' k.f k.F c z0 z1) :=
  refRawT_rel 9 h.toN τ hS hM (refTree δq k) k c z0 z1 T' hT

/-! ## Soundness -/

/-- **Reference vectors on a ball tree, every unbounded design point with `twOkN C.x.rc N`**: if
the ball tree `T` holds the stored tree `S` at its centres, every intermediate of the attempt at
`C` on `S` conditioned on `(z0, z1)` lies in its ball. -/
theorem refVecBT_sound (N : ℕ) (C : Choices) (hw : C.word = none) (htw : twOkN C.x.rc N = true)
    (T : GTree MB N) (S : CTree 64 N) (hT : T.Rel RX S.toG) (k : RawKey N) (c z0 z1 : ZPoly N)
    (V : SignT MB N) (hV : refVecBT N T k c z0 z1 = some V) :
    V.Rel RX ((opsX C).sign C.target S.toG k.f k.F c z0 z1) := by
  obtain ⟨rfl, -, -⟩ := refVecBT_spec hV
  exact SignT.Rel.map_leftP coarseM (fun _ _ h => CB.Holds.coarse h) _ _
    (refRawT_rel N (simXN N C hw htw) C.target (fun _ _ b _ h => CB.Holds.hull_left b.b h)
      (fun _ a _ _ h => CB.Holds.hull_right a.b h) T k c z0 z1 _ hT)

/-- **Reference vectors on a ball tree, words**: at `(i + 64)`-bit words, when every operation
magnitude of the order `C.target` in the vector is below `2^(i-1)`, every intermediate lies in its
ball. -/
theorem refVecBT_word (N : ℕ) (C : Choices) {i : ℕ} (hi : 1 ≤ i) (hw : C.word = some i)
    (htw : twOkN C.x.rc N = true) (T : GTree MB N) (S : CTree 64 N) (hT : T.Rel RX S.toG)
    (k : RawKey N) (c z0 z1 : ZPoly N) (V : SignT MB N) (hV : refVecBT N T k c z0 z1 = some V)
    (hm : V.magOkBP C.target i = true) :
    V.Rel RX ((opsX C).sign C.target S.toG k.f k.F c z0 z1) := by
  obtain ⟨rfl, -, -⟩ := refVecBT_spec hV
  have hT' : T.Rel (RW C.target i) (S.toG.map fun x => (x, x)) :=
    GTree.Rel.map_right _ (fun _ _ h => ⟨h, fun _ _ => rfl⟩) _ _ hT
  have h1 := refRawT_rel N (simWN N C hi hw htw) C.target
    (fun hτ _ b _ h => ⟨h.1.hull_left b.b, fun hs hl =>
      h.2 (CB.hull_isSome hs).1 (by rw [hτ] at hl ⊢; exact hl)⟩)
    (fun hτ a _ _ h => ⟨h.1.hull_right a.b, fun hs hl =>
      h.2 (CB.hull_isSome hs).2 (by rw [hτ] at hl ⊢; exact hl)⟩) T k c z0 z1 _ hT'
  have h2 := SignT.Rel.map_leftP coarseM (R := RW C.target i)
    (fun _ _ h => ⟨h.1.coarse, fun hs hl => h.2 (by simpa [coarseM, CB.coarse] using hs)
      (by rwa [MB.m_coarseM] at hl)⟩) _ _ h1
  have h3 := SignT.Rel.impP (R' := fun b p => RX b p.1)
    (fun b => b.b.r.isSome && decide (MB.m C.target b < 2 ^ (i - 1))) (fun _ p hP h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
    change CB.Holds _ p.1.toC
    rw [h.2 hP.1 hP.2]
    exact h.1) _ _ hm h2
  have h4 := signT_simN (simP1N N C { C with word := none }) C.target _ _
    (GTree.Rel.map_self (fun x => (x, x)) (fun _ => rfl) S.toG) k.f k.F c z0 z1
  exact SignT.Rel.monoP (fun _ _ ⟨_, hp, e⟩ => e ▸ hp) _ _ (SignT.Rel.compP _ _ _ h3 h4)

/-- **The exact attempt on a tree `U`** lies in the balls of a vector on a ball tree holding `U`
(when `fG - gF = q`). -/
theorem refVecBT_exact (N : ℕ) (T : GTree MB N) (U : LTree N) (k : RawKey N)
    (hT : ntruB k = true → T.Rel RE U.toG) (c z0 z1 : ZPoly N) (V : SignT MB N)
    (hV : refVecBT N T k c z0 z1 = some V) :
    V.Rel RE (opsE.sign .scaleFirst U.toG k.f k.F c z0 z1) := by
  obtain ⟨rfl, -, hn⟩ := refVecBT_spec hV
  exact SignT.Rel.map_leftP coarseM (fun _ _ h => CB.Holds.coarse h) _ _
    (refRawT_rel N (simEN N) .scaleFirst (fun _ _ b _ h => CB.Holds.hull_left b.b h)
      (fun h => absurd h (by decide)) T k c z0 z1 _ (hT hn))

/-- **Reference vectors, every unbounded design point with `twOk C.x.rc`**: on a key passing
`check C.x C.xn δq`, every intermediate of the attempt at `C` conditioned on `(z0, z1)` lies in
its ball. -/
theorem refVec_sound (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true)
    (δq : ℕ → ℚ) (k : RawKey) (hk : check C.x C.xn δq k = true) (c z0 z1 : ZPoly)
    (V : SignT MB) (hV : refVecB δq k c z0 z1 = some V) : V.Rel RX (traceX C k c z0 z1) :=
  refVecBT_sound 9 C hw htw (refTree δq k) _ (treeX C δq k hk) k c z0 z1 V hV

/-- The admissible points `Adm C` (`Exec.SignRefine`). -/
theorem refVec_adm (C : Choices) (hC : Adm C) (δq : ℕ → ℚ) (k : RawKey)
    (hk : check C.x C.xn δq k = true) (c z0 z1 : ZPoly) (V : SignT MB)
    (hV : refVecB δq k c z0 z1 = some V) : V.Rel RX (traceX C k c z0 z1) :=
  refVec_sound C hC.word hC.tw δq k hk c z0 z1 V hV

/-- **Reference vectors, words**: at `(i + 64)`-bit words, when every operation magnitude of the
order `C.target` in the vector is below `2^(i-1)`, every intermediate lies in its ball. -/
theorem refVec_word (C : Choices) {i : ℕ} (hi : 1 ≤ i) (hw : C.word = some i)
    (htw : twOk C.x.rc = true) (δq : ℕ → ℚ) (k : RawKey) (hk : check C.x C.xn δq k = true)
    (c z0 z1 : ZPoly) (V : SignT MB) (hV : refVecB δq k c z0 z1 = some V)
    (hm : V.magOkB C.target i = true) : V.Rel RX (traceX C k c z0 z1) :=
  refVecBT_word 9 C hi hw htw (refTree δq k) _ (treeX C δq k hk) k c z0 z1 V hV hm

/-- **The exact attempt** lies in the same balls. -/
theorem refVec_exact (δq : ℕ → ℚ) (hδ : ∀ L, 0 ≤ δq L) (k : RawKey) (c z0 z1 : ZPoly)
    (V : SignT MB) (hV : refVecB δq k c z0 z1 = some V) : V.Rel RE (traceE k c z0 z1) :=
  refVecBT_exact 9 (refTree δq k) k.trueTree k (treeE δq hδ k) c z0 z1 V hV

/-! ## The trace is the signer's computation -/

/-- A sampler answering call `j` by `g j` and logging its queries `(σ̄, t̄)`. -/
def logS (g : ℕ → ℤ) (σ t : Fx 64) : StateM (ℕ × List (Fx 64 × Fx 64)) ℤ :=
  modifyGet fun s => (g s.1, (s.1 + 1, s.2 ++ [(σ, t)]))

/-- The SamplerZ queries `(σ̄, Re t̄)` of a trace in call order. -/
def RunT.queries : {L : ℕ} → RunT (Cx 64) L → List (Fx 64 × Fx 64)
  | _, .leaf σ t0 t1 _ _ => [(σ.re, t0.re), (σ.re, t1.re)]
  | _, .node _ _ _ r1 _ _ r0 _ => r1.queries ++ r0.queries

theorem run_bind_of {σ α β : Type} {x : StateM σ α} {f : α → StateM σ β} {s : σ} {v : α × σ}
    (h : (x.run s).run = v) : ((x >>= f).run s).run = ((f v.1).run v.2).run := by
  subst h; rw [StateT.run_bind]; rfl

theorem ilv_evensZ_oddsZ {L : ℕ} (z : Fin (2 ^ (L + 1)) → ℤ) :
    Errors.FFSamp.ilv (evensZ z) (oddsZ z) = z := by
  funext i
  simp only [Errors.FFSamp.ilv, evensZ, oddsZ]
  split_ifs with h <;>
    exact congrArg z (Fin.ext (by dsimp only; omega))

/-- `ffsX` with a tape sampler is the conditioned run of `opsX C` (no range checks). -/
theorem ffsX_log (C : Choices) (hr : C.rchk = none) : ∀ {L : ℕ} (T : CTree 64 L)
    (t0 t1 : Out L → Cx 64) (z0 z1 : Fin (2 ^ L) → ℤ) (g : ℕ → ℤ) (j : ℕ)
    (q : List (Fx 64 × Fx 64)),
    (∀ i, i < (tapeOf L z0 z1).length → g (j + i) = (tapeOf L z0 z1).getD i 0) →
    ((ffsX C (logS g) T t0 t1).run (j, q)).run =
      (some ⟨z0, z1, (((opsX C).run T.toG t0 t1 z0 z1).outs (opsX C)).1,
        (((opsX C).run T.toG t0 t1 z0 z1).outs (opsX C)).2⟩,
        (j + (tapeOf L z0 z1).length, q ++ ((opsX C).run T.toG t0 t1 z0 z1).queries))
  | _, .leaf σ, t0, t1, z0, z1, g, j, q, hg => by
    have h0 : g j = z0 ⟨0, by norm_num⟩ := by simpa [tapeOf] using hg 0 (by simp [tapeOf])
    have h1 : g (j + 1) = z1 ⟨0, by norm_num⟩ := by
      simpa [tapeOf] using hg 1 (by simp [tapeOf])
    have e : ∀ z : Fin (2 ^ 0) → ℤ, (fun _ => z ⟨0, by norm_num⟩) = z := fun z =>
      funext fun i => congrArg z (Fin.ext (by have h : i.1 < 1 := i.2; change 0 = i.1; omega))
    change (some (⟨fun _ => g j, fun _ => g (j + 1), fun _ => Cx.ofInt (g j),
      fun _ => Cx.ofInt (g (j + 1))⟩ : SampX 0),
      (j + 1 + 1, q ++ [(σ, (t0 ()).re)] ++ [(σ, (t1 ()).re)])) = _
    rw [h0, h1, e z0, e z1, List.append_assoc]
    rfl
  | _, @CTree.node _ L ℓ T0 T1, t0, t1, z0, z1, g, j, q, hg => by
    have hT : tapeOf (L + 1) z0 z1 =
        tapeOf L (evensZ z1) (oddsZ z1) ++ tapeOf L (evensZ z0) (oddsZ z0) := rfl
    rw [hT] at hg ⊢
    have hg1 : ∀ i, i < (tapeOf L (evensZ z1) (oddsZ z1)).length →
        g (j + i) = (tapeOf L (evensZ z1) (oddsZ z1)).getD i 0 := fun i hi => by
      rw [hg i (by rw [List.length_append]; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have hg0 : ∀ i, i < (tapeOf L (evensZ z0) (oddsZ z0)).length →
        g (j + (tapeOf L (evensZ z1) (oddsZ z1)).length + i) =
          (tapeOf L (evensZ z0) (oddsZ z0)).getD i 0 := fun i hi => by
      rw [Nat.add_assoc, hg _ (by rw [List.length_append]; omega)]
      simp only [List.getD_eq_getElem?_getD, Nat.add_sub_cancel_left,
        List.getElem?_append_right (l₁ := tapeOf L (evensZ z1) (oddsZ z1)) (Nat.le_add_right _ i)]
    have ih1 := ffsX_log C hr T1 (splitW C L t1).1 (splitW C L t1).2 (evensZ z1) (oddsZ z1) g j q
      hg1
    have ih0 := fun t0' t1' q' => ffsX_log C hr T0 t0' t1' (evensZ z0) (oddsZ z0) g _ q' hg0
    simp only [ffsX, hr, chkX, Bool.and_self, ↓reduceIte]
    refine (run_bind_of ih1).trans ?_
    dsimp only
    refine (run_bind_of (ih0 _ _ _)).trans ?_
    dsimp only
    rw [ilv_evensZ_oddsZ, ilv_evensZ_oddsZ, List.length_append, ← Nat.add_assoc,
      List.append_assoc]
    rfl

theorem opsX_fft (C : Choices) : ∀ (L : ℕ) (a : Fin (2 ^ L) → ℤ), (opsX C).fft L a = fftW C L a
  | 0, _ => rfl
  | L + 1, a => by
    simp only [VOps.fft, fftW, opsX_fft C L]
    rfl

/-- The target of `opsX C` is `targetX`, at every size. -/
theorem opsX_targetP (C : Choices) {logn : ℕ} (f F c : ZPoly logn) :
    (opsX C).target C.target ((opsX C).fft logn c) ((opsX C).fft logn f)
      ((opsX C).fft logn F) = targetX C f F c := by
  rw [opsX_fft, opsX_fft, opsX_fft]
  obtain ⟨x, xn, τ, qi, w, rchk, salt, cap, beta2, infB, samp⟩ := C
  cases τ <;> rfl

/-- The target of `opsX C` is `targetX`. -/
theorem opsX_target (C : Choices) (f F c : ZPoly) :
    (opsX C).target C.target ((opsX C).fft 9 c) ((opsX C).fft 9 f) ((opsX C).fft 9 F) =
      targetX C f F c :=
  opsX_targetP C f F c

/-- The run of the conditioned attempt of `opsX C` on a stored tree `T`, at every size. -/
theorem sign_run_opsX (C : Choices) {logn : ℕ} (T : CTree 64 logn) (k : RawKey logn)
    (c z0 z1 : ZPoly logn) :
    ((opsX C).sign C.target T.toG k.f k.F c z0 z1).run = (opsX C).run T.toG
      (targetX C k.f k.F c).1 (targetX C k.f k.F c).2 z0 z1 := by
  unfold VOps.sign
  dsimp only
  rw [opsX_targetP]

theorem traceX_run (C : Choices) (k : RawKey) (c z0 z1 : ZPoly) :
    (traceX C k c z0 z1).run = (opsX C).run (storeC C.x C.xn k).toG
      (targetX C k.f k.F c).1 (targetX C k.f k.F c).2 z0 z1 :=
  sign_run_opsX C _ k c z0 z1

/-- `signX_eq_map` at every size. -/
theorem signX_eq_mapP (C : Choices) {m : Type → Type*} [Monad m] {logn : ℕ}
    (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 logn) (k : RawKey logn) (c : ZPoly logn)
    (hc : ∀ i, |c i| < 12289) :
    signX C samp T k c = (fun r => r.map fun s => (s.z0, s.z1)) <$>
      ffsX C samp T (targetX C k.f k.F c).1 (targetX C k.f k.F c).2 := by
  unfold signX
  exact ite_eq_left_of_eq_true _ _ (eq_true hc)

theorem signX_eq_map (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 9) (k : RawKey) (c : ZPoly) (hc : ∀ i, |c i| < 12289) :
    signX C samp T k c = (fun r => r.map fun s => (s.z0, s.z1)) <$>
      ffsX C samp T (targetX C k.f k.F c).1 (targetX C k.f k.F c).2 :=
  signX_eq_mapP C samp T k c hc

/-- **The signer's SamplerZ queries on a stored tree `T`**, at every size: with a sampler
answering by the tape of `(z0, z1)`, the attempt `signX` returns `(z0, z1)` and its queries are
the leaf values of the conditioned attempt of `opsX C` on `T`. -/
theorem signX_logP (C : Choices) (hr : C.rchk = none) {logn : ℕ} (T : CTree 64 logn)
    (k : RawKey logn) (c z0 z1 : ZPoly logn) (hc : ∀ i, |c i| < 12289) (g : ℕ → ℤ)
    (hg : ∀ i, i < (tapeOf logn z0 z1).length → g i = (tapeOf logn z0 z1).getD i 0) :
    ((signX C (logS g) T k c).run (0, [])).run =
      (some (z0, z1), ((tapeOf logn z0 z1).length,
        ((opsX C).sign C.target T.toG k.f k.F c z0 z1).run.queries)) := by
  have h : (ffsX C (logS g) T (targetX C k.f k.F c).1 (targetX C k.f k.F c).2).run (0, []) = _ :=
    ffsX_log C hr _ _ _ z0 z1 g 0 [] fun i hi => by rw [zero_add]; exact hg i hi
  rw [sign_run_opsX, signX_eq_mapP C _ _ k c hc, StateT.run_map, h]
  change (Option.map (fun s : SampX logn => (s.z0, s.z1)) _, _) = _
  exact Prod.ext rfl (Prod.ext (Nat.zero_add _) (List.nil_append _))

/-- **The signer's SamplerZ queries**: with a sampler answering by the tape of `(z0, z1)`, the
attempt `signX` returns `(z0, z1)` and its queries are the trace's leaf values. -/
theorem signX_log (C : Choices) (hr : C.rchk = none) (k : RawKey) (c z0 z1 : ZPoly)
    (hc : ∀ i, |c i| < 12289) (g : ℕ → ℤ)
    (hg : ∀ i, i < (tapeOf 9 z0 z1).length → g i = (tapeOf 9 z0 z1).getD i 0) :
    ((signX C (logS g) (storeC C.x C.xn k) k c).run (0, [])).run =
      (some (z0, z1), ((tapeOf 9 z0 z1).length, (traceX C k c z0 z1).run.queries)) :=
  signX_logP C hr _ k c z0 z1 hc g hg

/-! ## Meaning of the exact values and of the slots -/

/-- The exact FFT is the evaluation at the roots `pt L o`. -/
theorem opsE_fft : ∀ (L : ℕ) (a : Fin (2 ^ L) → ℤ) (o : Out L),
    opsE.fft L a o = evalAt (fun j => (a j : ℂ)) (pt L o)
  | 0, a, _ => by
    change ((a ⟨0, by norm_num⟩ : ℤ) : ℂ) = _
    simp [evalAt]
  | L + 1, a, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    have hs := evalAt_split (castC fun i => (a i : ℂ))
    simp only [evalAt_castC] at hs
    have he := opsE_fft L (evensZ a) o
    have ho := opsE_fft L (oddsZ a) o
    simp only [VOps.fft]; erw [memo_eq]
    cases b
    · change opsE.fft L (evensZ a) o + zeta L o * opsE.fft L (oddsZ a) o = _
      rw [he, ho, pt_succ]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hs, zeta_sq]
      rfl
    · change opsE.fft L (evensZ a) o - zeta L o * opsE.fft L (oddsZ a) o = _
      rw [he, ho, pt_succ]
      simp only [↓reduceIte]
      rw [hs, neg_sq, zeta_sq, neg_mul, ← sub_eq_add_neg]
      rfl

/-- The exponent `k` of a slot: `pt L o = exp(iπ·k/2^L)`, `k` odd in `(-2^L, 2^L]`. -/
def slotK : (L : ℕ) → Out L → ℤ
  | 0, _ => 1
  | L + 1, x =>
    let k := slotK L (x : Out L × Bool).1
    if (x : Out L × Bool).2 then (if 0 < k then k - 2 ^ (L + 1) else k + 2 ^ (L + 1)) else k

theorem slotK_range : ∀ (L : ℕ) (o : Out L), -(2 : ℤ) ^ L < slotK L o ∧ slotK L o ≤ 2 ^ L
  | 0, _ => by norm_num [slotK]
  | L + 1, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    have ih := slotK_range L o
    have hp : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L := by ring
    cases b
    · change -(2 : ℤ) ^ (L + 1) < slotK L o ∧ slotK L o ≤ 2 ^ (L + 1)
      constructor <;> linarith
    · change -(2 : ℤ) ^ (L + 1) < (if 0 < slotK L o then slotK L o - 2 ^ (L + 1)
        else slotK L o + 2 ^ (L + 1)) ∧ (if 0 < slotK L o then slotK L o - 2 ^ (L + 1)
        else slotK L o + 2 ^ (L + 1)) ≤ 2 ^ (L + 1)
      split_ifs with h <;> constructor <;> linarith

theorem cpow_inv_two_exp {θ : ℝ} (h1 : -Real.pi < θ) (h2 : θ ≤ Real.pi) :
    Complex.exp (θ * Complex.I) ^ (2⁻¹ : ℂ) = Complex.exp (θ / 2 * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp (by simpa using h1)
    (by simpa using h2)]
  congr 1
  ring

/-- The slot of a position is its evaluation point. -/
theorem pt_angle : ∀ (L : ℕ) (o : Out L),
    pt L o = Complex.exp (Real.pi * Complex.I * (slotK L o : ℂ) / 2 ^ L)
  | 0, _ => by
    change (-1 : ℂ) = Complex.exp (Real.pi * Complex.I * ((1 : ℤ) : ℂ) / 2 ^ 0)
    rw [Int.cast_one, pow_zero, mul_one, div_one, Complex.exp_pi_mul_I]
  | L + 1, x => by
    obtain ⟨o, b⟩ := (x : Out L × Bool)
    have hk := slotK_range L o
    have hk1 : -(2 : ℝ) ^ L < (slotK L o : ℝ) := by exact_mod_cast hk.1
    have hk2 : (slotK L o : ℝ) ≤ 2 ^ L := by exact_mod_cast hk.2
    have hpos : (0 : ℝ) < 2 ^ L := by positivity
    have e1 : Real.pi * Complex.I * (slotK L o : ℂ) / 2 ^ L =
        ((Real.pi * slotK L o / 2 ^ L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have hz : zeta L o = Complex.exp (Real.pi * Complex.I * (slotK L o : ℂ) / 2 ^ (L + 1)) := by
      rw [zeta, pt_angle L o, e1, cpow_inv_two_exp]
      · congr 1; push_cast; ring
      · rw [lt_div_iff₀ hpos]; nlinarith [mul_lt_mul_of_pos_left hk1 Real.pi_pos]
      · rw [div_le_iff₀ hpos]; exact mul_le_mul_of_nonneg_left hk2 Real.pi_pos.le
    cases b
    · change zeta L o = Complex.exp (Real.pi * Complex.I * (slotK L o : ℂ) / 2 ^ (L + 1))
      exact hz
    · change -zeta L o = Complex.exp (Real.pi * Complex.I * ((if 0 < slotK L o then
        slotK L o - 2 ^ (L + 1) else slotK L o + 2 ^ (L + 1) : ℤ) : ℂ) / 2 ^ (L + 1))
      split_ifs
      · rw [hz, show Real.pi * Complex.I * (((slotK L o - 2 ^ (L + 1) : ℤ)) : ℂ) / 2 ^ (L + 1) =
          Real.pi * Complex.I * (slotK L o : ℂ) / 2 ^ (L + 1) - Real.pi * Complex.I by
            push_cast; field_simp, Complex.exp_sub, Complex.exp_pi_mul_I]
        ring
      · rw [hz, show Real.pi * Complex.I * (((slotK L o + 2 ^ (L + 1) : ℤ)) : ℂ) / 2 ^ (L + 1) =
          Real.pi * Complex.I * (slotK L o : ℂ) / 2 ^ (L + 1) + Real.pi * Complex.I by
            push_cast; field_simp, Complex.exp_add, Complex.exp_pi_mul_I]
        ring

end FalconPrecision.Exec
