import FalconPrecision.Exec.SignFast
import FalconPrecision.Exec.SignEquiv
import FalconPrecision.Exec.RefRun
import FalconPrecision.Exec.Verify
import FalconPrecision.Exec.Round3Codec
import FalconPrecision.Exec.SignRange

/-! The definitions of release 0.5.0 that now take the size `2^logn` (and the per-size constants) as
parameters, frozen: each 0.5.0 body is copied into a namespace `V050` and followed by a theorem that
it equals the current definition at its defaults (Falcon-512). The bodies are verbatim, except that
a reference to another generalised definition points to its frozen copy (dot calls of those are
written as qualified calls). Non-recursive definitions are equal by `rfl` (`signImpl` by cases on
the query); `ldlC`, `ldlB`, `ldlBA`, `CTree.Ok`, `CTree.okB`, `gainA`, `devB` and `cB` by induction
(every depth), and the definitions that call them by rewriting with those. The structures `RawKey`,
`SignT` and `CheckOk` are compared field by field. The verifier definitions take the degree from
`V.enc.logn` and are compared for `V.enc.logn = 9`. Also checked: the 0.5.0 constructor names
`FTree.leaf`, `FTree.node`, `Key.mk`, `KeyB.mk` resolve, and so do `KeyB.Good.mk`, `.real`,
`.close`. `twX`, `twsX` (now `twXN 9`, `twsXN 9`) equal their 0.5.0 bodies, and they are the
tables of `arithX`. -/

/-! ## Model: names and the stored-leaf call -/

section
namespace FalconPrecision.Errors.FFSamp
open FalconPrecision.Errors.FFTRec

example (σ : ℝ) (h : 1277833697 / 10 ^ 9 ≤ σ ∧ σ ≤ 18205 / 10000) : FTree 0 := FTree.leaf σ h

example {L : ℕ} (ℓ : Out (L + 1) → ℂ) (h : ∀ o, ‖ℓ o‖ ≤ lam512 L) (T0 T1 : FTree L) :
    FTree (L + 1) :=
  FTree.node ℓ h T0 T1

example (f F : Fin (2 ^ 9) → ℤ) (hf : ∀ o, ‖fftE (fun i => (f i : ℂ)) o‖ ≤ 255)
    (hF : ∀ o, ‖fftE (fun i => (F i : ℂ)) o‖ ≤ 3500) (tree : FTree 9) : Key :=
  Key.mk f F hf hF tree

end FalconPrecision.Errors.FFSamp
end

section
namespace FalconPrecision.Errors.HopB
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFSamp

example (k : Key) (g G : Fin (2 ^ 9) → ℤ) : KeyB := KeyB.mk k g G

namespace V050

/-- 0.5.0 `callB`. -/
def callB (σ σb t tb : ℝ) (hb : 1277833697 / 10 ^ 9 ≤ σb ∧ σb ≤ 18205 / 10000)
    (h : (12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000) ∧ |σb / σ - 1| ≤ 1 / 2 ^ 42) : Falcon.CallP :=
  ⟨σ, σb, t, tb, h.1, by linarith [hb.1], h.2⟩

theorem callB_eq (σ σb t tb : ℝ) (hb : 1277833697 / 10 ^ 9 ≤ σb ∧ σb ≤ 18205 / 10000)
    (h : (12778 / 10000 ≤ σ ∧ σ ≤ 1825 / 1000) ∧ |σb / σ - 1| ≤ 1 / 2 ^ 42) :
    callB σ σb t tb hb h = HopB.callB σ σb t tb hb h :=
  rfl

/-- 0.5.0 `Sig`. -/
abbrev Sig : Type := Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))

theorem sig_eq : Sig = HopB.Sig := rfl

end V050
end FalconPrecision.Errors.HopB
end

/-! ## Hop B: key condition, signers and budgets -/

section
namespace FalconPrecision.Errors.HopB
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      ComplexConjugate MeasureTheory LatticeCrypto

example {δ : ℕ → ℝ} {k : KeyB} (hr : k.tree.Real) (hc : Close δ k.tree k.trueTree) : k.Good δ :=
  KeyB.Good.mk hr hc

example {δ : ℕ → ℝ} {k : KeyB} (h : k.Good δ) : k.tree.Real ∧ Close δ k.tree k.trueTree :=
  ⟨h.real, h.close⟩

namespace V050

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

open Classical in
/-- 0.5.0 `signB`. -/
noncomputable def signB (δ : ℕ → ℝ) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    OracleComp (FalconGame.spec aux Falcon.CallP) Sig :=
  if ∀ i, |c i| < 12289 then
    (fun s => some (s.z0, s.z1)) <$> ffsB δ k.1.tree k.1.trueTree k.2.close
      (t0E k.1.toKey c) (t1E k.1.toKey c) (t0E k.1.toKey c) (t1E k.1.toKey c)
  else pure none

theorem signB_eq (δ : ℕ → ℝ) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    signB (aux := aux) δ k c = HopB.signB δ k c :=
  rfl

open Classical in
/-- 0.5.0 `signT`. -/
noncomputable def signT (δ : ℕ → ℝ) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    OracleComp (FalconGame.spec aux Falcon.CallP) Sig :=
  if ∀ i, |c i| < 12289 then
    (fun s => some (s.z0, s.z1)) <$> ffsT k.1.trueTree k.2.close.inRange (t0E k.1.toKey c)
        (t1E k.1.toKey c)
  else pure none

theorem signT_eq (δ : ℕ → ℝ) (k : GoodKey δ) (c : Fin (2 ^ 9) → ℤ) :
    signT (aux := aux) δ k c = HopB.signT δ k c :=
  rfl

/-- 0.5.0 `specS`. -/
@[reducible] def specS (aux : OracleSpec.{0, 0} ιA) (δ : ℕ → ℝ) :
    OracleSpec (ιA ⊕ (GoodKey δ × (Fin (2 ^ 9) → ℤ))) :=
  Sum.elim aux fun _ => Sig

theorem specS_eq (aux : OracleSpec.{0, 0} ιA) (δ : ℕ → ℝ) : specS aux δ = HopB.specS aux δ :=
  rfl

/-- 0.5.0 `signImpl`. -/
noncomputable def signImpl {δ : ℕ → ℝ}
    (sg : GoodKey δ → (Fin (2 ^ 9) → ℤ) → OracleComp (FalconGame.spec aux Falcon.CallP) Sig) :
    QueryImpl (specS aux δ) (OracleComp (FalconGame.spec aux Falcon.CallP))
  | .inl x => liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl x))
  | .inr kc => sg kc.1 kc.2

theorem signImpl_eq {δ : ℕ → ℝ}
    (sg : GoodKey δ → (Fin (2 ^ 9) → ℤ) → OracleComp (FalconGame.spec aux Falcon.CallP) Sig) :
    signImpl sg = HopB.signImpl sg := by
  funext t
  rcases t with x | kc <;> rfl

/-- 0.5.0 `gainA`. -/
noncomputable def gainA : ℕ → ℝ
  | 0 => 1
  | L + 1 => gainA L * (lam512 L + √(lam512 L ^ 2 + 4)) / (2 * √2)

theorem gainA_eq : ∀ L : ℕ, gainA L = HopB.gainA L
  | 0 => rfl
  | L + 1 => by
    have ih : gainA L = gainAP lam512 L := gainA_eq L
    rw [gainA, HopB.gainA, gainAP, ih]

theorem gainA_fun : gainA = HopB.gainA := funext gainA_eq

/-- 0.5.0 `devB`. -/
noncomputable def devB (y : ℝ) (δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => √2 * y
  | L + 1 => √(2 * ((1 + lam512 L + δ L) ^ 2 + 1)) * devB y δ L

theorem devB_eq (y : ℝ) (δ : ℕ → ℝ) : ∀ L : ℕ, devB y δ L = HopB.devB y δ L
  | 0 => rfl
  | L + 1 => by
    have ih : devB y δ L = devBP lam512 y δ L := devB_eq y δ L
    rw [devB, HopB.devB, devBP, ih]

theorem devB_fun (y : ℝ) (δ : ℕ → ℝ) : devB y δ = HopB.devB y δ := funext (devB_eq y δ)

/-- 0.5.0 `s2B`. -/
noncomputable def s2B (y : ℝ) (δ : ℕ → ℝ) : ℝ :=
  (∑ L ∈ Finset.range 9, gainA L * δ L * √(2 ^ (8 - L)) * devB y δ L) ^ 2

theorem s2B_eq (y : ℝ) (δ : ℕ → ℝ) : s2B y δ = HopB.s2B y δ := by
  rw [s2B, gainA_fun, devB_fun]
  rfl

/-- 0.5.0 `cB`. -/
noncomputable def cB (y : ℝ) (δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | L + 1 => √2 * cB y δ L + gainA L * δ L * devB y δ L

theorem cB_eq (y : ℝ) (δ : ℕ → ℝ) : ∀ L : ℕ, cB y δ L = HopB.cB y δ L
  | 0 => rfl
  | L + 1 => by
    have ih : cB y δ L = cBP lam512 y δ L := cB_eq y δ L
    have hg : gainA L = gainAP lam512 L := gainA_eq L
    have hd : devB y δ L = devBP lam512 y δ L := devB_eq y δ L
    rw [cB, HopB.cB, cBP, ih, hg, hd]

/-- 0.5.0 `GoodB`. -/
def GoodB (y : ℝ) (δ : ℕ → ℝ) {L : ℕ} (t0 t1 : Out L → ℂ) (s : Samp L) : Prop :=
  IsFFT s ∧ l2 (pairF (t0 - s.e0) (t1 - s.e1)) ≤ devB y δ L

theorem GoodB_eq (y : ℝ) (δ : ℕ → ℝ) {L : ℕ} (t0 t1 : Out L → ℂ) (s : Samp L) :
    GoodB y δ t0 t1 s = HopB.GoodB y δ t0 t1 s := by
  rw [GoodB, devB_fun]
  rfl

end V050
end FalconPrecision.Errors.HopB
end

/-! ## Key expansion -/

section
namespace FalconPrecision.Exec.V050
open FalconPrecision.Errors.FFTRec ComplexConjugate

namespace Types

/-- 0.5.0 `RawKey`. -/
structure RawKey where
  f : Fin (2 ^ 9) → ℤ
  g : Fin (2 ^ 9) → ℤ
  F : Fin (2 ^ 9) → ℤ
  G : Fin (2 ^ 9) → ℤ

/-- The 0.5.0 `RawKey` and the current one at the default size: the same fields. -/
def rawKeyEquiv : RawKey ≃ Exec.RawKey :=
  ⟨fun k => ⟨k.f, k.g, k.F, k.G⟩, fun k => ⟨k.f, k.g, k.F, k.G⟩, fun _ => rfl, fun _ => rfl⟩

end Types

variable (P : XChoices) (f : ℕ)

/-- 0.5.0 `ldlC`. -/
def ldlC : (L : ℕ) → (g00 g10 g11 : Out L → Cx f) → CTree f L
  | 0, g00, _, _ => .leaf (Cx.leafR P.rm P.rc σ512q (g00 ()).re).re
  | L + 1, g00, g10, g11 => ldlStepC P f L g00 g10 (d11C P f (L + 1) g00 g10 g11) (ldlC L)

theorem ldlC_eq : ∀ (L : ℕ) (g00 g10 g11 : Out L → Cx f),
    ldlC P f L g00 g10 g11 = Exec.ldlC P f L g00 g10 g11
  | 0, _, _, _ => rfl
  | L + 1, g00, g10, g11 => by
    have ih : ldlC P f L = fun a b c => Exec.ldlC P f L a b c :=
      funext fun a => funext fun b => funext fun c => ldlC_eq L a b c
    rw [ldlC, Exec.ldlC, ih]

theorem ldlC_fun (L : ℕ) : ldlC P f L = fun a b c => Exec.ldlC P f L a b c :=
  funext fun a => funext fun b => funext fun c => ldlC_eq P f L a b c

/-- 0.5.0 `gramC`. -/
def gramC (k : RawKey) : (Out 9 → Cx f) × (Out 9 → Cx f) × (Out 9 → Cx f) :=
  let fb := fftC P f 9 k.f
  let gb := fftC P f 9 k.g
  let Fb := fftC P f 9 k.F
  let Gb := fftC P f 9 k.G
  (memo 9 fun o => ((gb o).normSqR P.rm).add ((fb o).normSqR P.rm),
    memo 9 fun o => ((Gb o).mul P.rm (gb o).conjg).add ((Fb o).mul P.rm (fb o).conjg),
    memo 9 fun o => ((Gb o).normSqR P.rm).add ((Fb o).normSqR P.rm))

theorem gramC_eq (k : RawKey) : gramC P f k = Exec.gramC P f k := rfl

/-- 0.5.0 `expandC`. -/
def expandC (k : RawKey) : CTree f 9 :=
  let gr := gramC P f k
  let d11 := match P.root with
    | .plain => d11C P f 9 gr.1 gr.2.1 gr.2.2
    | .ntru => memo 9 fun o => (Cx.ofInt (12289 ^ 2)).divR P.rm P.dm (gr.1 o).re
  ldlStepC P f 8 gr.1 gr.2.1 d11 (ldlC P f 8)

theorem expandC_eq (k : RawKey) : expandC P f k = Exec.expandC P f k := by
  rw [expandC, ldlC_fun]
  rfl

/-- 0.5.0 `ldlB`. -/
def ldlB : (L : ℕ) → (g00 g10 g11 : Out L → CB f) → BTree f L
  | 0, g00, _, _ => .leaf (CB.leaf P.rm P.rc σ512q (g00 ()))
  | L + 1, g00, g10, g11 => ldlStepB P f L g00 g10 (d11B P f (L + 1) g00 g10 g11) (ldlB L)

theorem ldlB_eq : ∀ (L : ℕ) (g00 g10 g11 : Out L → CB f),
    ldlB P f L g00 g10 g11 = Exec.ldlB P f L g00 g10 g11
  | 0, _, _, _ => rfl
  | L + 1, g00, g10, g11 => by
    have ih : ldlB P f L = fun a b c => Exec.ldlB P f L a b c :=
      funext fun a => funext fun b => funext fun c => ldlB_eq L a b c
    rw [ldlB, Exec.ldlB, ih]

theorem ldlB_fun (L : ℕ) : ldlB P f L = fun a b c => Exec.ldlB P f L a b c :=
  funext fun a => funext fun b => funext fun c => ldlB_eq P f L a b c

/-- 0.5.0 `gramB`. -/
def gramB (k : RawKey) : (Out 9 → CB f) × (Out 9 → CB f) × (Out 9 → CB f) :=
  let fb := fftB P f 9 k.f
  let gb := fftB P f 9 k.g
  let Fb := fftB P f 9 k.F
  let Gb := fftB P f 9 k.G
  (memo 9 fun o => ((gb o).normSq P.rm).add ((fb o).normSq P.rm),
    memo 9 fun o => (CB.mul P.rm (Gb o) (gb o).conjg).add (CB.mul P.rm (Fb o) (fb o).conjg),
    memo 9 fun o => ((Gb o).normSq P.rm).add ((Fb o).normSq P.rm))

theorem gramB_eq (k : RawKey) : gramB P f k = Exec.gramB P f k := rfl

/-- 0.5.0 `rootB`. -/
def rootB (gr : (Out 9 → CB f) × (Out 9 → CB f) × (Out 9 → CB f)) : Out 9 → CB f :=
  match P.root with
  | .plain => d11B P f 9 gr.1 gr.2.1 gr.2.2
  | .ntru => memo 9 fun o => CB.divR P.rm P.dm (CB.ofInt (12289 ^ 2)) (gr.1 o)

theorem rootB_eq (gr : (Out 9 → CB f) × (Out 9 → CB f) × (Out 9 → CB f)) :
    rootB P f gr = Exec.rootB P f gr :=
  rfl

/-- 0.5.0 `expandB`. -/
def expandB (k : RawKey) : BTree f 9 :=
  let gr := gramB P f k
  ldlStepB P f 8 gr.1 gr.2.1 (rootB P f gr) (ldlB P f 8)

theorem expandB_eq (k : RawKey) : expandB P f k = Exec.expandB P f k := by
  rw [expandB, ldlB_fun]
  rfl

/-- 0.5.0 `ldlBA`. -/
def ldlBA : (L : ℕ) → (g00 g10 g11 : Array (CB f)) → BTree f L
  | 0, g00, _, _ => .leaf (CB.leaf P.rm P.rc σ512q (ofArr 0 g00 ()))
  | L + 1, g00, g10, g11 => ldlStepBA P f L g00 g10 (d11BA P f (L + 1) g00 g10 g11) (ldlBA L)

theorem ldlBA_eq : ∀ (L : ℕ) (g00 g10 g11 : Array (CB f)),
    ldlBA P f L g00 g10 g11 = Exec.ldlBA P f L g00 g10 g11
  | 0, _, _, _ => rfl
  | L + 1, g00, g10, g11 => by
    have ih : ldlBA P f L = fun a b c => Exec.ldlBA P f L a b c :=
      funext fun a => funext fun b => funext fun c => ldlBA_eq L a b c
    rw [ldlBA, Exec.ldlBA, ih]

theorem ldlBA_fun (L : ℕ) : ldlBA P f L = fun a b c => Exec.ldlBA P f L a b c :=
  funext fun a => funext fun b => funext fun c => ldlBA_eq P f L a b c

/-- 0.5.0 `gramBA`. -/
def gramBA (k : RawKey) : Array (CB f) × Array (CB f) × Array (CB f) :=
  let fb := fftBA P f 9 k.f
  let gb := fftBA P f 9 k.g
  let Fb := fftBA P f 9 k.F
  let Gb := fftBA P f 9 k.G
  (toArr 9 fun o => ((ofArr 9 gb o).normSq P.rm).add ((ofArr 9 fb o).normSq P.rm),
    toArr 9 fun o => (CB.mul P.rm (ofArr 9 Gb o) (ofArr 9 gb o).conjg).add
      (CB.mul P.rm (ofArr 9 Fb o) (ofArr 9 fb o).conjg),
    toArr 9 fun o => ((ofArr 9 Gb o).normSq P.rm).add ((ofArr 9 Fb o).normSq P.rm))

theorem gramBA_eq (k : RawKey) : gramBA P f k = Exec.gramBA P f k := rfl

/-- 0.5.0 `rootBA`. -/
def rootBA (gr : Array (CB f) × Array (CB f) × Array (CB f)) : Array (CB f) :=
  match P.root with
  | .plain => d11BA P f 9 gr.1 gr.2.1 gr.2.2
  | .ntru => toArr 9 fun o => CB.divR P.rm P.dm (CB.ofInt (12289 ^ 2)) (ofArr 9 gr.1 o)

theorem rootBA_eq (gr : Array (CB f) × Array (CB f) × Array (CB f)) :
    rootBA P f gr = Exec.rootBA P f gr :=
  rfl

/-- 0.5.0 `expandBA`. -/
def expandBA (k : RawKey) : BTree f 9 :=
  let gr := gramBA P f k
  ldlStepBA P f 8 gr.1 gr.2.1 (rootBA P f gr) (ldlBA P f 8)

theorem expandBA_eq (k : RawKey) : expandBA P f k = Exec.expandBA P f k := by
  rw [expandBA, ldlBA_fun]
  rfl

variable (n : ℕ)

/-- 0.5.0 `storeC`. -/
def storeC (k : RawKey) : CTree 64 9 := (expandC P (64 + n) k).lower P.rm n

theorem storeC_eq (k : RawKey) : storeC P n k = Exec.storeC P n k :=
  congrArg (fun T => T.lower P.rm n) (expandC_eq P (64 + n) k)

/-- 0.5.0 `storeB`. -/
def storeB (k : RawKey) : BTree 64 9 := (expandB P (64 + n) k).lower P.rm n

theorem storeB_eq (k : RawKey) : storeB P n k = Exec.storeB P n k :=
  congrArg (fun T => T.lower P.rm n) (expandB_eq P (64 + n) k)

end FalconPrecision.Exec.V050
end

/-! ## The key check -/

section
namespace FalconPrecision.Exec.V050
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.HopB ComplexConjugate

/-- 0.5.0 `CTree.Ok`. -/
def CTree.Ok {f : ℕ} : {L : ℕ} → CTree f L → Prop
  | _, .leaf σ => 1277833697 / 10 ^ 9 ≤ σ.toRat ∧ σ.toRat ≤ 18205 / 10000
  | _, @CTree.node _ L ℓ T0 T1 => (∀ o, (ℓ o).nsq ≤ lam512q L ^ 2) ∧ Ok T0 ∧ Ok T1

theorem CTree.Ok_eq {f : ℕ} : ∀ {L : ℕ} (T : CTree f L), CTree.Ok T = T.Ok
  | _, .leaf _ => rfl
  | _, .node _ T0 T1 => by rw [CTree.Ok, Exec.CTree.Ok, Ok_eq T0, Ok_eq T1]

/-- 0.5.0 `CTree.okB`. -/
def CTree.okB {f : ℕ} : {L : ℕ} → CTree f L → Bool
  | _, .leaf σ => decide (1277833697 / 10 ^ 9 ≤ σ.toRat) && decide (σ.toRat ≤ 18205 / 10000)
  | _, @CTree.node _ L ℓ T0 T1 =>
    allOut (L + 1) (fun o => decide ((ℓ o).nsq ≤ lam512q L ^ 2)) && okB T0 && okB T1

theorem CTree.okB_eq {f : ℕ} : ∀ {L : ℕ} (T : CTree f L), CTree.okB T = T.okB
  | _, .leaf _ => rfl
  | _, .node _ T0 T1 => by rw [CTree.okB, Exec.CTree.okB, okB_eq T0, okB_eq T1]

theorem CTree.okB_fun {f L : ℕ} : (CTree.okB : CTree f L → Bool) = fun T => T.okB :=
  funext fun T => CTree.okB_eq T

/-- 0.5.0 `RawKey.g00`. -/
noncomputable def RawKey.g00 (k : RawKey) (o : Out 9) : ℂ :=
  fftZ k.g o * conj (fftZ k.g o) + fftZ k.f o * conj (fftZ k.f o)

theorem RawKey.g00_eq (k : RawKey) (o : Out 9) : RawKey.g00 k o = Exec.RawKey.g00 k o := rfl

/-- 0.5.0 `RawKey.g10`. -/
noncomputable def RawKey.g10 (k : RawKey) (o : Out 9) : ℂ :=
  fftZ k.G o * conj (fftZ k.g o) + fftZ k.F o * conj (fftZ k.f o)

theorem RawKey.g10_eq (k : RawKey) (o : Out 9) : RawKey.g10 k o = Exec.RawKey.g10 k o := rfl

/-- 0.5.0 `RawKey.g11`. -/
noncomputable def RawKey.g11 (k : RawKey) (o : Out 9) : ℂ :=
  fftZ k.G o * conj (fftZ k.G o) + fftZ k.F o * conj (fftZ k.F o)

theorem RawKey.g11_eq (k : RawKey) (o : Out 9) : RawKey.g11 k o = Exec.RawKey.g11 k o := rfl

/-- 0.5.0 `RawKey.trueTree`. -/
noncomputable def RawKey.trueTree (k : RawKey) : LTree 9 :=
  ffldl σ512 9 (RawKey.g00 k) (RawKey.g10 k) (RawKey.g11 k)

theorem RawKey.trueTree_eq (k : RawKey) : RawKey.trueTree k = Exec.RawKey.trueTree k := rfl

/-- 0.5.0 `ncoef`. -/
def ncoef (a b : Fin (2 ^ 9) → ℤ) (i : Fin (2 ^ 9)) : ℤ :=
  ∑ j : Fin (2 ^ 9), if h : j.1 ≤ i.1 then a j * b ⟨i.1 - j.1, by have := i.2; omega⟩
    else -(a j * b ⟨2 ^ 9 + i.1 - j.1, by omega⟩)

theorem ncoef_eq (a b : Fin (2 ^ 9) → ℤ) (i : Fin (2 ^ 9)) : ncoef a b i = Exec.ncoef a b i := rfl

theorem ncoef_fun :
    (ncoef : (Fin (2 ^ 9) → ℤ) → (Fin (2 ^ 9) → ℤ) → Fin (2 ^ 9) → ℤ) = Exec.ncoef :=
  rfl

/-- 0.5.0 `ntruB`. -/
def ntruB (k : RawKey) : Bool :=
  decide (∀ i : Fin (2 ^ 9), ncoef k.f k.G i - ncoef k.g k.F i = if i.1 = 0 then 12289 else 0)

theorem ntruB_eq (k : RawKey) : ntruB k = Exec.ntruB k := by
  unfold ntruB Exec.ntruB
  rw [ncoef_fun]

theorem ntruB_fun : (ntruB : RawKey → Bool) = Exec.ntruB := funext ntruB_eq

variable (P : XChoices) (n : ℕ)

/-- 0.5.0 `check`. -/
def check (δq : ℕ → ℚ) (k : RawKey) : Bool :=
  let T := storeB P n k
  let C := T.centre
  allOut 9 (fun o => (fftB P (64 + n) 9 k.f o).normLeB 255) &&
    allOut 9 (fun o => (fftB P (64 + n) 9 k.F o).normLeB 3500) && CTree.okB C && C.realB &&
    T.radOkB δq && ntruB k

theorem check_eq (δq : ℕ → ℚ) (k : RawKey) : check P n δq k = Exec.check P n δq k := by
  rw [check, storeB_eq, CTree.okB_fun, ntruB_fun]
  rfl

/-- 0.5.0 `CheckOk`. -/
structure CheckOk (δq : ℕ → ℚ) (k : RawKey) : Prop where
  hf : ∀ o, (fftB P (64 + n) 9 k.f o).normLeB 255 = true
  hF : ∀ o, (fftB P (64 + n) 9 k.F o).normLeB 3500 = true
  ok : CTree.okB (storeB P n k).centre = true
  real : (storeB P n k).centre.realB = true
  rad : (storeB P n k).radOkB δq = true
  ntru : ntruB k = true

theorem checkOk_iff (δq : ℕ → ℚ) (k : RawKey) : CheckOk P n δq k ↔ Exec.CheckOk P n δq k := by
  have e1 := storeB_eq P n k
  have e2 := CTree.okB_eq (Exec.storeB P n k).centre
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [e1, e2] at h3
    rw [e1] at h4 h5
    rw [ntruB_eq] at h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [← e2, ← e1] at h3
    rw [← e1] at h4 h5
    rw [← ntruB_eq] at h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- 0.5.0 `checkFast`. -/
def checkFast (δq : ℕ → ℚ) (k : RawKey) : Bool :=
  let T := (expandBA P (64 + n) k).lower P.rm n
  let C := T.centre
  let fb := fftBA P (64 + n) 9 k.f
  let Fb := fftBA P (64 + n) 9 k.F
  allOut 9 (fun o => (ofArr 9 fb o).normLeB 255) &&
    allOut 9 (fun o => (ofArr 9 Fb o).normLeB 3500) && CTree.okB C && C.realB &&
    T.radOkB δq && ntruB k

theorem checkFast_eq (δq : ℕ → ℚ) (k : RawKey) :
    checkFast P n δq k = Exec.checkFast P n δq k := by
  rw [checkFast, expandBA_eq, CTree.okB_fun, ntruB_fun]
  rfl

end FalconPrecision.Exec.V050
end

/-! ## Signing -/

section
namespace FalconPrecision.Exec.V050
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFSamp

/-- 0.5.0 `ZPoly`. -/
abbrev ZPoly : Type := Fin (2 ^ 9) → ℤ

theorem zPoly_eq : ZPoly = Exec.ZPoly := rfl

variable (C : Choices)

/-- 0.5.0 `targetX`. -/
def targetX (f F c : ZPoly) : (Out 9 → Cx 64) × (Out 9 → Cx 64) :=
  let w := wordFn C.word
  let rm := C.x.rm
  let ch := fftW C 9 c
  let fh := fftW C 9 f
  let Fh := fftW C 9 F
  match C.target with
  | .scaleFirst =>
    let cq := memo 9 fun o => (divqX rm C.qinv (ch o)).wr w
    (memo 9 fun o => ((cq o).neg.wr w).mulW w rm (Fh o), memo 9 fun o => (cq o).mulW w rm (fh o))
  | .multiplyFirst =>
    (memo 9 fun o => (divqX rm C.qinv (((ch o).mulW w rm (Fh o)).neg.wr w)).wr w,
      memo 9 fun o => (divqX rm C.qinv ((ch o).mulW w rm (fh o))).wr w)

theorem targetX_eq (f F c : ZPoly) : targetX C f F c = Exec.targetX C f F c := rfl

/-- 0.5.0 `signX`. -/
def signX {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9)
    (k : RawKey) (c : ZPoly) : m (Option (ZPoly × ZPoly)) :=
  if ∀ i, |c i| < 12289 then
    (fun r => r.map fun s => (s.z0, s.z1)) <$>
      ffsX C samp T (targetX C k.f k.F c).1 (targetX C k.f k.F c).2
  else pure none

theorem signX_eq {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9)
    (k : RawKey) (c : ZPoly) : signX C samp T k c = Exec.signX C samp T k c :=
  rfl

/-- 0.5.0 `sOf`. -/
def sOf (k : RawKey) (c z0 z1 : ZPoly) : ZPoly × ZPoly :=
  (fun i => c i - ncoef z0 k.g i - ncoef z1 k.G i, fun i => ncoef z0 k.f i + ncoef z1 k.F i)

theorem sOf_eq (k : RawKey) (c z0 z1 : ZPoly) : sOf k c z0 z1 = Exec.sOf k c z0 z1 := rfl

/-- 0.5.0 `normOk`. -/
def normOk (s : ZPoly × ZPoly) : Bool :=
  decide (((List.finRange (2 ^ 9)).map fun i => s.1 i ^ 2 + s.2 i ^ 2).sum ≤ (C.beta2 : ℤ)) &&
    (match C.infB with
      | none => true
      | some B => (List.finRange (2 ^ 9)).all fun i =>
        decide (|s.1 i| ≤ (B : ℤ) ∧ |s.2 i| ≤ (B : ℤ)))

theorem normOk_eq (s : ZPoly × ZPoly) : normOk C s = Exec.normOk C s := rfl

/-- 0.5.0 `accX`. -/
def accX (k : RawKey) (c : ZPoly) (y : Option (ZPoly × ZPoly)) : Option (ZPoly × ZPoly) :=
  y.bind fun z => if normOk C (sOf k c z.1 z.2) then some (sOf k c z.1 z.2) else none

theorem accX_eq (k : RawKey) (c : ZPoly) (y : Option (ZPoly × ZPoly)) :
    accX C k c y = Exec.accX C k c y :=
  rfl

/-- 0.5.0 `signLoopX`. -/
def signLoopX {m : Type → Type*} [Monad m] {S M β : Type} (mode : SaltMode) (salt : m S)
    (hash : S → M → m ZPoly) (att : ZPoly → m (Option (ZPoly × ZPoly)))
    (acc : ZPoly → Option (ZPoly × ZPoly) → Option β) (msg : M) (N : ℕ) : m (Option (S × β)) :=
  match mode with
  | .reused => salt >>= fun s => hash s msg >>= fun c =>
    (Option.map fun b => (s, b)) <$> loopR (att c) (acc c) N
  | .perAttempt =>
    loopR (salt >>= fun s => hash s msg >>= fun c => (fun y => (s, c, y)) <$> att c)
      (fun x => (acc x.2.1 x.2.2).map fun b => (x.1, b)) N

theorem signLoopX_eq {m : Type → Type*} [Monad m] {S M β : Type} (mode : SaltMode) (salt : m S)
    (hash : S → M → m ZPoly) (att : ZPoly → m (Option (ZPoly × ZPoly)))
    (acc : ZPoly → Option (ZPoly × ZPoly) → Option β) (msg : M) (N : ℕ) :
    signLoopX mode salt hash att acc msg N = Exec.signLoopX mode salt hash att acc msg N :=
  rfl

/-- 0.5.0 `signMsgX`. -/
def signMsgX {m : Type → Type*} [Monad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (k : RawKey) (msg : M) : m (Option (S × (ZPoly × ZPoly))) :=
  let T := storeC C.x C.xn k
  signLoopX C.salt salt hash (signX C (sampF C.samp) T k) (accX C k) msg C.cap

theorem signMsgX_eq {m : Type → Type*} [Monad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (k : RawKey) (msg : M) :
    signMsgX C sampF salt hash k msg = Exec.signMsgX C sampF salt hash k msg := by
  rw [signMsgX, storeC_eq]
  rfl

/-- 0.5.0 `l1Q`. -/
def l1Q (a : ZPoly) : ℚ := (((List.finRange (2 ^ 9)).map fun j => |a j|).sum : ℤ)

theorem l1Q_eq (a : ZPoly) : l1Q a = Exec.l1Q a := rfl

/-- 0.5.0 `checkRange`. -/
def checkRange (i W : ℕ) (k : RawKey) : Bool :=
  let C0 := { C with word := none }
  let bc : ℚ := 2 * (512 * 12288) + 1
  let mf := nmax 9 (fftW C0 9 k.f) + 1
  let mF := nmax 9 (fftW C0 9 k.F) + 1
  let tgt : List ℚ × ℚ := match C.target with
    | .scaleFirst =>
      let cq := 2 * bc / 12289 + 1
      ([cq, cq * mF + 1, cq * mf + 1], max (cq * mF + 1) (cq * mf + 1))
    | .multiplyFirst =>
      let p := bc * max mF mf + 1
      ([p, 2 * p / 12289 + 1], 2 * p / 12289 + 1)
  twOk C.x.rc && ([bc, 2 * l1Q k.f + 1, 2 * l1Q k.F + 1] ++ tgt.1).all (fitsQ i) &&
    rangeT i W (imE i) (storeC C.x C.xn k) tgt.2

theorem checkRange_eq (i W : ℕ) (k : RawKey) : checkRange C i W k = Exec.checkRange C i W k := by
  rw [checkRange, storeC_eq, Exec.checkRange, show (2 : ℚ) ^ (8 + 1) = 512 by norm_num]
  rfl

/-- 0.5.0 `qtX`. -/
def qtX (k : RawKey) (c : ZPoly) : ZPoly × ZPoly :=
  (fun i => -ncoef c k.F i, fun i => ncoef c k.f i)

theorem qtX_eq (k : RawKey) (c : ZPoly) : qtX k c = Exec.qtX k c := rfl

/-- 0.5.0 `tIntX`. -/
def tIntX (k : RawKey) (c : ZPoly) : ZPoly × ZPoly :=
  ((fun i => ((qtX k c).1 i - modqC ((qtX k c).1 i)) / 12289),
    fun i => ((qtX k c).2 i - modqC ((qtX k c).2 i)) / 12289)

theorem tIntX_eq (k : RawKey) (c : ZPoly) : tIntX k c = Exec.tIntX k c := rfl

/-- 0.5.0 `targetFracX`. -/
def targetFracX (C : Choices) (k : RawKey) (c : ZPoly) : (Out 9 → Cx 64) × (Out 9 → Cx 64) :=
  let w := wordFn C.word
  let f0 := fftW C 9 fun i => modqC ((qtX k c).1 i)
  let f1 := fftW C 9 fun i => modqC ((qtX k c).2 i)
  (memo 9 fun o => (divqX C.x.rm C.qinv (f0 o)).wr w,
    memo 9 fun o => (divqX C.x.rm C.qinv (f1 o)).wr w)

theorem targetFracX_eq (C : Choices) (k : RawKey) (c : ZPoly) :
    targetFracX C k c = Exec.targetFracX C k c :=
  rfl

/-- 0.5.0 `signXc`. -/
def signXc (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 9) (k : RawKey) (c : ZPoly) : m (Option (ZPoly × ZPoly)) :=
  match C.samp.centre with
  | .plain => signX C samp T k c
  | .fractional =>
    if ∀ i, |c i| < 12289 then
      (fun r => r.map fun s => (fun i => (tIntX k c).1 i + s.z0 i,
        fun i => (tIntX k c).2 i + s.z1 i)) <$>
        ffsX C samp T (targetFracX C k c).1 (targetFracX C k c).2
    else pure none

theorem signXc_eq (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 9) (k : RawKey) (c : ZPoly) : signXc C samp T k c = Exec.signXc C samp T k c :=
  rfl

/-- 0.5.0 `targetXA`. -/
def targetXA (f F c : ZPoly) : Array (Cx 64) × Array (Cx 64) :=
  let w := wordFn C.word
  let rm := C.x.rm
  let ch := ofArr 9 (fftWA C 9 c)
  let fh := ofArr 9 (fftWA C 9 f)
  let Fh := ofArr 9 (fftWA C 9 F)
  match C.target with
  | .scaleFirst =>
    let cq := ofArr 9 (toArr 9 fun o => (divqX rm C.qinv (ch o)).wr w)
    (toArr 9 fun o => ((cq o).neg.wr w).mulW w rm (Fh o), toArr 9 fun o => (cq o).mulW w rm (fh o))
  | .multiplyFirst =>
    (toArr 9 fun o => (divqX rm C.qinv (((ch o).mulW w rm (Fh o)).neg.wr w)).wr w,
      toArr 9 fun o => (divqX rm C.qinv ((ch o).mulW w rm (fh o))).wr w)

theorem targetXA_eq (f F c : ZPoly) : targetXA C f F c = Exec.targetXA C f F c := rfl

/-- 0.5.0 `signXA`. -/
def signXA {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9)
    (k : RawKey) (c : ZPoly) : m (Option (ZPoly × ZPoly)) :=
  if ∀ i, |c i| < 12289 then
    let tg := targetXA C k.f k.F c
    (fun r => r.map fun s => (s.z0, s.z1)) <$> ffsXA C samp T (ofArr 9 tg.1) (ofArr 9 tg.2)
  else pure none

theorem signXA_eq {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9)
    (k : RawKey) (c : ZPoly) : signXA C samp T k c = Exec.signXA C samp T k c :=
  rfl

/-- 0.5.0 `storeCA`. -/
def storeCA (k : RawKey) : CTree 64 9 :=
  ((expandBA C.x (64 + C.xn) k).lower C.x.rm C.xn).centre

theorem storeCA_eq (k : RawKey) : storeCA C k = Exec.storeCA C k :=
  congrArg (fun T => (T.lower C.x.rm C.xn).centre) (expandBA_eq C.x (64 + C.xn) k)

/-- 0.5.0 `checkRangeA`. -/
def checkRangeA (i W : ℕ) (k : RawKey) : Bool :=
  let C0 := { C with word := none }
  let bc : ℚ := 2 * (512 * 12288) + 1
  let mf := nmaxA 9 (fftWA C0 9 k.f) + 1
  let mF := nmaxA 9 (fftWA C0 9 k.F) + 1
  let tgt : List ℚ × ℚ := match C.target with
    | .scaleFirst =>
      let cq := 2 * bc / 12289 + 1
      ([cq, cq * mF + 1, cq * mf + 1], max (cq * mF + 1) (cq * mf + 1))
    | .multiplyFirst =>
      let p := bc * max mF mf + 1
      ([p, 2 * p / 12289 + 1], 2 * p / 12289 + 1)
  twOkFast C.x.rc && ([bc, 2 * l1Q k.f + 1, 2 * l1Q k.F + 1] ++ tgt.1).all (fitsQ i) &&
    rangeT i W (imE i) (storeCA C k) tgt.2

theorem checkRangeA_eq (i W : ℕ) (k : RawKey) :
    checkRangeA C i W k = Exec.checkRangeA C i W k := by
  rw [checkRangeA, storeCA_eq, Exec.checkRangeA, show (2 : ℚ) ^ (8 + 1) = 512 by norm_num]
  rfl

end FalconPrecision.Exec.V050
end

/-! ## The reference run -/

section
namespace FalconPrecision.Exec.V050
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.Fixed

namespace Types

/-- 0.5.0 `SignT`. -/
structure SignT (V : Type) where
  ch : Out 9 → V
  fh : Out 9 → V
  Fh : Out 9 → V
  t0 : Out 9 → V
  t1 : Out 9 → V
  run : RunT V 9

/-- The 0.5.0 `SignT` and the current one at the default size: the same fields. -/
def signTEquiv (V : Type) : SignT V ≃ Exec.SignT V :=
  ⟨fun A => ⟨A.ch, A.fh, A.Fh, A.t0, A.t1, A.run⟩, fun A => ⟨A.ch, A.fh, A.Fh, A.t0, A.t1, A.run⟩,
    fun _ => rfl, fun _ => rfl⟩

end Types

variable {V W : Type}

namespace VOps

variable [Inhabited V] (O : VOps V)

/-- 0.5.0 `VOps.target`. -/
def target (τ : Target) (ch fh Fh : Out 9 → V) : (Out 9 → V) × (Out 9 → V) :=
  match τ with
  | .scaleFirst =>
    let cq := memo 9 fun o => O.divq (ch o)
    (memo 9 fun o => O.mul (O.neg (cq o)) (Fh o), memo 9 fun o => O.mul (cq o) (fh o))
  | .multiplyFirst =>
    (memo 9 fun o => O.divq (O.neg (O.mul (ch o) (Fh o))),
      memo 9 fun o => O.divq (O.mul (ch o) (fh o)))

theorem target_eq (τ : Target) (ch fh Fh : Out 9 → V) :
    target O τ ch fh Fh = O.target τ ch fh Fh :=
  rfl

/-- 0.5.0 `VOps.sign`. -/
def sign (τ : Target) (T : GTree V 9) (f F c z0 z1 : ZPoly) : SignT V :=
  let ch := O.fft 9 c
  let fh := O.fft 9 f
  let Fh := O.fft 9 F
  let t := target O τ ch fh Fh
  ⟨ch, fh, Fh, t.1, t.2, O.run T t.1 t.2 z0 z1⟩

theorem sign_eq (τ : Target) (T : GTree V 9) (f F c z0 z1 : ZPoly) :
    sign O τ T f F c z0 z1 = O.sign τ T f F c z0 z1 :=
  rfl

/-- 0.5.0 `VOps.targetA`. -/
def targetA (τ : Target) (ch fh Fh : Out 9 → V) : Array V × Array V :=
  match τ with
  | .scaleFirst =>
    let cq := ofArr 9 (toArr 9 fun o => O.divq (ch o))
    (toArr 9 fun o => O.mul (O.neg (cq o)) (Fh o), toArr 9 fun o => O.mul (cq o) (fh o))
  | .multiplyFirst =>
    (toArr 9 fun o => O.divq (O.neg (O.mul (ch o) (Fh o))),
      toArr 9 fun o => O.divq (O.mul (ch o) (fh o)))

theorem targetA_eq (τ : Target) (ch fh Fh : Out 9 → V) :
    targetA O τ ch fh Fh = O.targetA τ ch fh Fh :=
  rfl

end VOps

/-- 0.5.0 `SignT.Rel`. -/
def SignT.Rel (R : V → W → Prop) (A : SignT V) (B : SignT W) : Prop :=
  (∀ o, R (A.ch o) (B.ch o) ∧ R (A.fh o) (B.fh o) ∧ R (A.Fh o) (B.Fh o) ∧ R (A.t0 o) (B.t0 o) ∧
    R (A.t1 o) (B.t1 o)) ∧ A.run.Rel R B.run

theorem SignT.Rel_eq (R : V → W → Prop) (A : SignT V) (B : SignT W) :
    SignT.Rel R A B = Exec.SignT.Rel R A B :=
  rfl

/-- 0.5.0 `SignT.allB`. -/
def SignT.allB (p : V → Bool) (A : SignT V) : Bool :=
  allOut 9 (fun o => p (A.ch o) && p (A.fh o) && p (A.Fh o) && p (A.t0 o) && p (A.t1 o)) &&
    A.run.allB p

theorem SignT.allB_eq (p : V → Bool) (A : SignT V) : SignT.allB p A = Exec.SignT.allB p A := rfl

/-- 0.5.0 `SignT.map`. -/
def SignT.map (g : V → W) (A : SignT V) : SignT W :=
  ⟨fun o => g (A.ch o), fun o => g (A.fh o), fun o => g (A.Fh o), fun o => g (A.t0 o),
    fun o => g (A.t1 o), A.run.map g⟩

theorem SignT.map_eq (g : V → W) (A : SignT V) : SignT.map g A = Exec.SignT.map g A := rfl

/-- 0.5.0 `tRef`. -/
noncomputable def tRef (f F c : ZPoly) : (Out 9 → ℂ) × (Out 9 → ℂ) :=
  (fun o => -(evalAt (fun j => (c j : ℂ)) (pt 9 o) * evalAt (fun j => (F j : ℂ)) (pt 9 o)) / 12289,
    fun o => evalAt (fun j => (c j : ℂ)) (pt 9 o) * evalAt (fun j => (f j : ℂ)) (pt 9 o) / 12289)

theorem tRef_eq (f F c : ZPoly) : tRef f F c = Exec.tRef f F c := rfl

end FalconPrecision.Exec.V050
end

/-! ## Round-3 key decoding -/

section
namespace FalconPrecision.Exec.Round3.V050

theorem fgBitsOf_nine : fgBitsOf 9 = 6 := rfl

/-- 0.5.0 `decodeSk`. -/
def decodeSk (b : ByteArray) : Option (Array ℤ × Array ℤ × Array ℤ) := do
  guard (b.size = 1281 ∧ b[0]! = 0x59)
  let f ← signedPoly b 8 6 512
  let g ← signedPoly b (8 + 6 * 512) 6 512
  let F ← signedPoly b (8 + 12 * 512) 8 512
  pure (f, g, F)

theorem decodeSk_eq (b : ByteArray) : decodeSk b = Round3.decodeSk b := rfl

/-- 0.5.0 `decodePk`. -/
def decodePk (b : ByteArray) : Option (Array ℕ) := do
  guard (b.size = 897 ∧ b[0]! = 0x09)
  (Array.range 512).mapM fun i =>
    let v := bitsAt b (8 + 14 * i) 14
    if v < qN then some v else none

theorem decodePk_eq (b : ByteArray) : decodePk b = Round3.decodePk b := rfl

/-- 0.5.0 `ω`. -/
def ω : ℕ := powq 7 2

theorem ω_eq : ω = Round3.ω := rfl

/-- 0.5.0 `pts`. -/
def pts : Array ℕ := (Array.range 512).map fun i => powq ω (2 * i + 1)

theorem pts_eq : pts = Round3.pts := rfl

/-- 0.5.0 `nttq`. -/
def nttq (a : Array ℤ) : Array ℕ := pts.map (evalq (a.map modq))

theorem nttq_eq (a : Array ℤ) : nttq a = Round3.nttq a := rfl

/-- 0.5.0 `inttq`. -/
def inttq (A : Array ℕ) : Array ℕ := Id.run do
  let ninv := powq 512 (qN - 2)
  let ys := pts.map fun x => powq x (qN - 2)
  let mut p := Array.replicate 512 1
  let mut out := Array.mkEmpty 512
  for _ in [0:512] do
    let s := (List.range 512).foldl (fun s i => (s + A[i]! * p[i]!) % qN) 0
    out := out.push (s * ninv % qN)
    p := (Array.range 512).map fun i => p[i]! * ys[i]! % qN
  return out

theorem inttq_eq (A : Array ℕ) : inttq A = Round3.inttq A := rfl

/-- 0.5.0 `solveG`. -/
def solveG (f g F : Array ℤ) : Option (Array ℤ) := do
  let fh := nttq f
  let gh := nttq g
  let Fh := nttq F
  guard (fh.all (· ≠ 0))
  let Gh := (Array.range 512).map fun i => gh[i]! * Fh[i]! % qN * powq fh[i]! (qN - 2) % qN
  pure ((inttq Gh).map centre)

theorem solveG_eq (f g F : Array ℤ) : solveG f g F = Round3.solveG f g F := rfl

/-- 0.5.0 `polyOf`. -/
def polyOf (a : Array ℤ) : Fin (2 ^ 9) → ℤ := fun i => a.getD i.1 0

theorem polyOf_eq (a : Array ℤ) : polyOf a = Round3.polyOf a := rfl

theorem polyOf_fun : polyOf = fun a => Round3.polyOf a := rfl

/-- 0.5.0 `decodeKey`. -/
def decodeKey (sk : ByteArray) : Option RawKey := do
  let (f, g, F) ← decodeSk sk
  let G ← solveG f g F
  pure ⟨polyOf f, polyOf g, polyOf F, polyOf G⟩

theorem decodeKey_eq (sk : ByteArray) : decodeKey sk = Round3.decodeKey sk := rfl

/-- 0.5.0 `pkMatchB`. -/
def pkMatchB (h : Array ℕ) (k : RawKey) : Bool :=
  decide (∀ i : Fin (2 ^ 9),
    (V050.ncoef (polyOf (h.map (Int.ofNat ·))) k.f i - k.g i) % (qN : ℤ) = 0)

theorem pkMatchB_eq (h : Array ℕ) (k : RawKey) : pkMatchB h k = Round3.pkMatchB h k := by
  unfold pkMatchB Round3.pkMatchB
  rw [V050.ncoef_fun, polyOf_eq]

end FalconPrecision.Exec.Round3.V050
end

/-! ## Verification -/

section
namespace FalconPrecision.Exec.Codec.V050
open Round3 (qN centre modq)
open Round3.V050 (polyOf inttq)

/-- 0.5.0 `s1Of`. -/
def s1Of (c : List ℕ) (s2 h : List ℤ) : Fin (2 ^ 9) → ℤ := fun i =>
  centre (modq ((c.getD i 0 : ℤ) - V050.ncoef (polyOf s2.toArray) (polyOf h.toArray) i))

theorem s1Of_eq (c : List ℕ) (s2 h : List ℤ) : s1Of c s2 h = Codec.s1Of c s2 h := rfl

theorem s1Of_fun : s1Of = fun c s2 h => Codec.s1Of c s2 h := rfl

/-- 0.5.0 `normSq`. -/
def normSq (a : Fin (2 ^ 9) → ℤ) : ℤ := ∑ i, a i ^ 2

theorem normSq_eq (a : Fin (2 ^ 9) → ℤ) : normSq a = Codec.normSq a := rfl

theorem normSq_fun : (normSq : (Fin (2 ^ 9) → ℤ) → ℤ) = Codec.normSq := rfl

/-- 0.5.0 `infOk`. -/
def infOk (B : Option ℕ) (a : Fin (2 ^ 9) → ℤ) : Bool := B.all fun B => decide (∀ i, |a i| ≤ B)

theorem infOk_eq (B : Option ℕ) (a : Fin (2 ^ 9) → ℤ) : infOk B a = Codec.infOk B a := rfl

theorem infOk_fun : (infOk : Option ℕ → (Fin (2 ^ 9) → ℤ) → Bool) = Codec.infOk := rfl

/-- 0.5.0 `hPoly`. -/
def hPoly (C : EncChoices) (hv : List ℕ) : List ℕ :=
  match C.pkForm with
  | .coeff => hv
  | .ntt => (inttq hv.toArray).toList

theorem hPoly_eq (C : EncChoices) (hC : C.logn = 9) (hv : List ℕ) :
    hPoly C hv = Codec.hPoly C hv := by
  obtain ⟨_, logn, _, _, _, _, _, _, _, _, _, _, _⟩ := C
  dsimp only at hC
  subst hC
  rfl

theorem hPoly_fun (C : EncChoices) (hC : C.logn = 9) : hPoly C = Codec.hPoly C :=
  funext (hPoly_eq C hC)

/-- 0.5.0 `verifyCore`. -/
def verifyCore (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) : Bool :=
  let s1 := s1Of c s2 (h.map Int.ofNat)
  decide (normSq s1 + normSq (polyOf s2.toArray) ≤ V.beta2) && infOk V.infB s1 &&
    infOk V.infB (polyOf s2.toArray)

theorem verifyCore_eq (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) :
    verifyCore V h c s2 = Codec.verifyCore V h c s2 := by
  rw [verifyCore, s1Of_fun, normSq_fun, infOk_fun, Round3.V050.polyOf_fun]
  rfl

theorem verifyCore_fun (V : VerChoices) (hV : V.enc.logn = 9) :
    verifyCore V = fun h c s2 => Codec.verifyCore V h c s2 V.enc.logn := by
  rw [hV]
  exact funext fun h => funext fun c => funext fun s2 => verifyCore_eq V h c s2

/-- 0.5.0 `verifySig`. -/
def verifySig (V : VerChoices) (pk msg sig : List UInt8) : Bool :=
  match decodePk V.enc pk, decodeSig V.enc sig with
  | some hv, some σ =>
    match (hashInput V pk σ.salt msg).bind (hashToPoint V.enc.n) with
    | some c => verifyCore V (hPoly V.enc hv) c σ.s2
    | none => false
  | _, _ => false

theorem verifySig_eq (V : VerChoices) (hV : V.enc.logn = 9) (pk msg sig : List UInt8) :
    verifySig V pk msg sig = Codec.verifySig V pk msg sig := by
  rw [verifySig, verifyCore_fun V hV, hPoly_fun V.enc hV]
  rfl

/-- 0.5.0 `openSm`. -/
def openSm (V : VerChoices) (pk sm : List UInt8) : Option (List UInt8) := do
  let hv ← decodePk V.enc pk
  let (salt, msg, s2) ← decodeSm V.enc sm
  let c ← (hashInput V pk salt msg).bind (hashToPoint V.enc.n)
  guard (verifyCore V (hPoly V.enc hv) c s2)
  pure msg

theorem openSm_eq (V : VerChoices) (hV : V.enc.logn = 9) (pk sm : List UInt8) :
    openSm V pk sm = Codec.openSm V pk sm := by
  rw [openSm, verifyCore_fun V hV, hPoly_fun V.enc hV]
  rfl

/-- The 512 instances of the verifier choices have `logn = 9`. -/
theorem round3V_logn : round3V.enc.logn = 9 := rfl

theorem fndsaProvV_logn (trLen infB : ℕ) : (fndsaProvV trLen infB).enc.logn = 9 := rfl

end FalconPrecision.Exec.Codec.V050
end

/-! ## Tables of the refinement (cutoff `N = 9`) -/

section
namespace FalconPrecision.Exec.V050
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.Fixed

/-- 0.5.0 `twX`. -/
noncomputable def twX (rc : RMode) (L : ℕ) (o : Out L) : ℂ :=
  if L ≤ 8 then (twB rc 64 L o).c.toC else zeta L o

/-- 0.5.0 `twsX`. -/
noncomputable def twsX (rc : RMode) (L : ℕ) (o : Out L) : ℂ :=
  if L ≤ 8 then (twsB rc 64 L o).c.toC else starRingEnd ℂ (zeta L o) / 2

theorem twX_fun (rc : RMode) : twX rc = Exec.twX rc := by
  funext L o
  simp only [twX, Exec.twX, twXN]
  split_ifs <;> first | rfl | omega

theorem twsX_fun (rc : RMode) : twsX rc = Exec.twsX rc := by
  funext L o
  simp only [twsX, Exec.twsX, twsXN]
  split_ifs <;> first | rfl | omega

/-- The tables of `arithX` are the 0.5.0 `twX`, `twsX`. -/
theorem arithX_tables (C : Choices) (h : Adm C) :
    (arithX C h).tw = twX C.x.rc ∧ (arithX C h).tws = twsX C.x.rc :=
  ⟨(twX_fun C.x.rc).symm, (twsX_fun C.x.rc).symm⟩

end FalconPrecision.Exec.V050
end
