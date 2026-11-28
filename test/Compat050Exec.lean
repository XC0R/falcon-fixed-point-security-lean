import FalconPrecision.Exec.CheckFast
import FalconPrecision.Exec.Codec
import FalconPrecision.Exec.CodecKat
import FalconPrecision.Exec.FixedPoint
import FalconPrecision.Exec.FixedPointArith64
import FalconPrecision.Exec.Instance45
import FalconPrecision.Exec.KeyCheck
import FalconPrecision.Exec.RefVec
import FalconPrecision.Exec.RefVecOut
import FalconPrecision.Exec.SamplerClose
import FalconPrecision.Exec.SamplerHop
import FalconPrecision.Exec.SamplerLaw
import FalconPrecision.Exec.SignEquiv
import FalconPrecision.Exec.SignRange
import FalconPrecision.Exec.SignRefine
import FalconPrecision.Exec.SignWitness
import FalconPrecision.Exec.SignWordHop
import FalconPrecision.Exec.Verify

/-! The statements of release 0.5.0, verbatim in their scopes, of every theorem of
`FalconPrecision.Exec` that README.md or LIMITS.md names: each theorem, applied to the binders by
name, has the 0.5.0 type. -/

section
namespace FalconPrecision.Exec
open FalconPrecision.Errors.FFTRec
variable (P : XChoices) (f : ℕ)
variable (n : ℕ)
example (δq : ℕ → ℚ) (k : RawKey) : checkFast P n δq k = check P n δq k :=
  _root_.FalconPrecision.Exec.checkFast_eq (P := P) (n := n) (δq := δq) (k := k)
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec.Codec
open Falcon.Concrete (natBits natOfBits byteBits bytesToBits bitsToBytes coeffBits)
open Round3 (qN signedOf)
example (C : EncChoices) (h : List ℕ) (hh : PkOk C h) :
    decodePk C (encodePk C h) = some h :=
  _root_.FalconPrecision.Exec.Codec.decodePk_encodePk (C := C) (h := h) (hh := hh)

example (C : EncChoices) (b : List UInt8) (h : List ℕ)
    (hd : decodePk C b = some h) : encodePk C h = b :=
  _root_.FalconPrecision.Exec.Codec.encodePk_of_decodePk (C := C) (b := b) (h := h) (hd := hd)

example (C : EncChoices) (k : SkData) (hk : SkOk C k) :
    decodeSk C (encodeSk C k) = some k :=
  _root_.FalconPrecision.Exec.Codec.decodeSk_encodeSk (C := C) (k := k) (hk := hk)

example (C : EncChoices) (b : List UInt8) (k : SkData)
    (hd : decodeSk C b = some k) : encodeSk C k = b :=
  _root_.FalconPrecision.Exec.Codec.encodeSk_of_decodeSk (C := C) (b := b) (k := k) (hd := hd)

example (cm : Option ℕ) (s : List ℤ) (slen : ℕ) (str : List Bool)
    (h : compress cm s slen = some str) : decompress cm s.length str slen = some s :=
  _root_.FalconPrecision.Exec.Codec.decompress_compress (cm := cm) (s := s) (slen := slen)
    (str := str) (h := h)

example (cm : Option ℕ) (n : ℕ) (s : List ℤ) (slen : ℕ) (str : List Bool)
    (h : decompress cm n str slen = some s) : compress cm s slen = some str :=
  _root_.FalconPrecision.Exec.Codec.compress_of_decompress (cm := cm) (n := n) (s := s)
    (slen := slen) (str := str) (h := h)

example (C : EncChoices) (σ : Sig) (b : List UInt8)
    (hn : σ.s2.length = C.n) (h : encodeSig C σ = some b) : decodeSig C b = some σ :=
  _root_.FalconPrecision.Exec.Codec.decodeSig_encodeSig (C := C) (σ := σ) (b := b) (hn := hn)
    (h := h)

example (C : EncChoices) (σ : Sig) (b : List UInt8)
    (h : decodeSig C b = some σ) : encodeSig C σ = some b :=
  _root_.FalconPrecision.Exec.Codec.encodeSig_of_decodeSig (C := C) (σ := σ) (b := b) (h := h)

example (C : EncChoices) (salt msg : List UInt8) (s2 : List ℤ)
    (sm : List UInt8) (hn : s2.length = C.n) (h : encodeSm C salt msg s2 = some sm) :
    decodeSm C sm = some (salt, msg, s2) :=
  _root_.FalconPrecision.Exec.Codec.decodeSm_encodeSm (C := C) (salt := salt) (msg := msg)
    (s2 := s2) (sm := sm) (hn := hn) (h := h)

example (C : EncChoices) (sm salt msg : List UInt8) (s2 : List ℤ)
    (h : decodeSm C sm = some (salt, msg, s2)) : encodeSm C salt msg s2 = some sm :=
  _root_.FalconPrecision.Exec.Codec.encodeSm_of_decodeSm (C := C) (sm := sm) (salt := salt)
    (msg := msg) (s2 := s2) (h := h)

example (b : ByteArray) :
    decodePk round3 b.data.toList = (Round3.decodePk b).map (·.toList) :=
  _root_.FalconPrecision.Exec.Codec.decodePk_round3 (b := b)

example (b : ByteArray) :
    decodeSk round3 b.data.toList =
      (Round3.decodeSk b).map fun k => ⟨k.1.toList, k.2.1.toList, k.2.2.toList, []⟩ :=
  _root_.FalconPrecision.Exec.Codec.decodeSk_round3 (b := b)
end FalconPrecision.Exec.Codec
end

section
namespace FalconPrecision.Exec.Codec
example {e : KatEntry} (h : entryOkB e = true) : EntryOk e :=
  _root_.FalconPrecision.Exec.Codec.entryOk_of (e := e) (h := h)

example {l : List KatEntry} (h : l.all entryOkB = true) : ∀ e ∈ l, EntryOk e :=
  _root_.FalconPrecision.Exec.Codec.entriesOk_of (l := l) (h := h)
end FalconPrecision.Exec.Codec
end

section
namespace FalconPrecision.Exec
namespace RMode
example (r : RMode) (y : ℝ) : |(r.rnd y : ℝ) - y| ≤ r.e :=
  _root_.FalconPrecision.Exec.RMode.rnd_err (r := r) (y := y)

example : ¬ |(floor.rnd (3 / 4) : ℝ) - 3 / 4| ≤ 1 / 2 :=
  _root_.FalconPrecision.Exec.RMode.not_isRound_floor
end RMode
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec
namespace Fx
variable {f g : ℕ}
example (r : RMode) (a b : Fx f) :
    |(a.mul r b).toReal - a.toReal * b.toReal| ≤ r.e / 2 ^ f :=
  _root_.FalconPrecision.Exec.Fx.mul_err (f := f) (r := r) (a := a) (b := b)

example (r : RMode) (a : Fx f) : |(a.half r).toReal - a.toReal / 2| ≤ r.e / 2 ^ f :=
  _root_.FalconPrecision.Exec.Fx.half_err (f := f) (r := r) (a := a)

example (r : RMode) (a b : Fx f) (hb : b.m ≠ 0) :
    |(a.div r b).toReal - a.toReal / b.toReal| ≤ r.e / 2 ^ f :=
  _root_.FalconPrecision.Exec.Fx.div_err (f := f) (r := r) (a := a) (b := b) (hb := hb)

example (r : RMode) (a : Fx f) : |(a.sqrt r).toReal - √a.toReal| ≤ r.e / 2 ^ f :=
  _root_.FalconPrecision.Exec.Fx.sqrt_err (f := f) (r := r) (a := a)

example {i : ℕ} {x : Fx f} (h : x.InRange (i + 1)) : Fx.wrap (i + f) x.m = x.m :=
  _root_.FalconPrecision.Exec.Fx.InRange.wrap (f := f) (i := i) (x := x) (h := h)
end Fx
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec
open FalconPrecision.Errors.Fixed
variable (r : RMode) (hr : r ≠ .floor)
example (z w : Cx 64) :
    (r.arith64 hr).mul (1 / 2 ^ 64) z.toC w.toC = (z.mul r w).toC :=
  _root_.FalconPrecision.Exec.RMode.arith64_mul (r := r) (hr := hr) (z := z) (w := w)

example (z : Cx 64) :
    (r.arith64 hr).halve (1 / 2 ^ 64) z.toC = (z.half r).toC :=
  _root_.FalconPrecision.Exec.RMode.arith64_halve (r := r) (hr := hr) (z := z)

example (z : Cx 64) : (r.arith64 hr).divq z.toC = (z.divq r).toC :=
  _root_.FalconPrecision.Exec.RMode.arith64_divq (r := r) (hr := hr) (z := z)
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
example : (2 : ℝ) ^ 39 * s2B (61 / 2) δ45 ≤ 1 / 2 ^ 9 :=
  _root_.FalconPrecision.Exec.s2B_falcon45
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable (P : XChoices) (n : ℕ) {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
    {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]
example [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK P n aux δ45q) α) (hq : PathSum (wKC P n δ45q) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ (embed P n δ45q oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed P n δ45q oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Exec.falcon512_fixed_vs_true45_checked (P := P) (n := n) (ιA := ιA)
    (aux := aux) (m := m) (ρ := ρ) (K := K) (hK := hK) (T := T) (hT := hT) (implA := implA)
    (implE := implE) (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF)
    (hE := hE) (hM := hM) (hF := hF) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs)
    (hwin := hwin)
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable (P : XChoices) (f : ℕ)
variable (n : ℕ)
example (δq : ℕ → ℚ) (k : RawKey) (h : check P n δq k = true) :
    (toKeyB P n δq k h).Good (fun j => (δq j : ℝ)) :=
  _root_.FalconPrecision.Exec.check_sound (P := P) (n := n) (δq := δq) (k := k) (h := h)
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable (P : XChoices) (f : ℕ)
variable (n : ℕ)
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]
example [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (δq : ℕ → ℚ) (ρ : Arith64 (1 / 2 ^ 78))
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9)
    (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK P n aux δq) α) (hq : PathSum (wKC P n δq) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ (embed P n δq oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed P n δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Exec.falcon512_fixed_vs_true_checked (P := P) (n := n) (ιA := ιA)
    (aux := aux) (m := m) (δq := δq) (ρ := ρ) (K := K) (hK := hK) (hδ := hδ) (T := T) (hT := hT)
    (implA := implA) (implE := implE) (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM)
    (hAF := hAF) (hE := hE) (hM := hM) (hF := hF) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs)
    (hwin := hwin)

example [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK P n aux δ127q) α) (hq : PathSum (wKC P n δ127q) oe K) {s : Set α}
    (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ (embed P n δ127q oe))] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed P n δ127q oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Exec.falcon512_fixed_vs_true127_checked (P := P) (n := n) (ιA := ιA)
    (aux := aux) (m := m) (ρ := ρ) (K := K) (hK := hK) (T := T) (hT := hT) (implA := implA)
    (implE := implE) (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF)
    (hE := hE) (hM := hM) (hF := hF) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs)
    (hwin := hwin)
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.Fixed
example (C : Choices) (hw : C.word = none) (htw : twOk C.x.rc = true)
    (δq : ℕ → ℚ) (k : RawKey) (hk : check C.x C.xn δq k = true) (c z0 z1 : ZPoly)
    (V : SignT MB) (hV : refVecB δq k c z0 z1 = some V) : V.Rel RX (traceX C k c z0 z1) :=
  _root_.FalconPrecision.Exec.refVec_sound (C := C) (hw := hw) (htw := htw) (δq := δq) (k := k)
    (hk := hk) (c := c) (z0 := z0) (z1 := z1) (V := V) (hV := hV)

example (C : Choices) (hC : Adm C) (δq : ℕ → ℚ) (k : RawKey)
    (hk : check C.x C.xn δq k = true) (c z0 z1 : ZPoly) (V : SignT MB)
    (hV : refVecB δq k c z0 z1 = some V) : V.Rel RX (traceX C k c z0 z1) :=
  _root_.FalconPrecision.Exec.refVec_adm (C := C) (hC := hC) (δq := δq) (k := k) (hk := hk) (c := c)
    (z0 := z0) (z1 := z1) (V := V) (hV := hV)

example (C : Choices) {i : ℕ} (hi : 1 ≤ i) (hw : C.word = some i)
    (htw : twOk C.x.rc = true) (δq : ℕ → ℚ) (k : RawKey) (hk : check C.x C.xn δq k = true)
    (c z0 z1 : ZPoly) (V : SignT MB) (hV : refVecB δq k c z0 z1 = some V)
    (hm : V.magOkB C.target i = true) : V.Rel RX (traceX C k c z0 z1) :=
  _root_.FalconPrecision.Exec.refVec_word (C := C) (i := i) (hi := hi) (hw := hw) (htw := htw)
    (δq := δq) (k := k) (hk := hk) (c := c) (z0 := z0) (z1 := z1) (V := V) (hV := hV) (hm := hm)

example (δq : ℕ → ℚ) (hδ : ∀ L, 0 ≤ δq L) (k : RawKey) (c z0 z1 : ZPoly)
    (V : SignT MB) (hV : refVecB δq k c z0 z1 = some V) : V.Rel RE (traceE k c z0 z1) :=
  _root_.FalconPrecision.Exec.refVec_exact (δq := δq) (hδ := hδ) (k := k) (c := c) (z0 := z0)
    (z1 := z1) (V := V) (hV := hV)

example (C : Choices) (hr : C.rchk = none) (k : RawKey) (c z0 z1 : ZPoly)
    (hc : ∀ i, |c i| < 12289) (g : ℕ → ℤ)
    (hg : ∀ i, i < (tapeOf 9 z0 z1).length → g i = (tapeOf 9 z0 z1).getD i 0) :
    ((signX C (logS g) (storeC C.x C.xn k) k c).run (0, [])).run =
      (some (z0, z1), ((tapeOf 9 z0 z1).length, (traceX C k c z0 z1).run.queries)) :=
  _root_.FalconPrecision.Exec.signX_log (C := C) (hr := hr) (k := k) (c := c) (z0 := z0) (z1 := z1)
    (hc := hc) (g := g) (hg := hg)
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec
open FalconPrecision.Errors.FFTRec
example {e : Codec.KatEntry} {k : RawKey} {c s1 s2 z0 z1 : ZPoly}
    (h : katIn e = some (k, c, s1, s2, z0, z1)) :
    (Round3.ofHex e.sk).bind Round3.decodeKey = some k ∧
      (∃ salt msg s2l cl hv, Codec.decodeSm Codec.round3 (Codec.hexL e.sm) = some (salt, msg, s2l) ∧
        Codec.hashToPoint 512 (salt ++ msg) = some cl ∧
        Codec.decodePk Codec.round3 (Codec.hexL e.pk) = some hv ∧
        c = Round3.polyOf (cl.map Int.ofNat).toArray ∧ s2 = Round3.polyOf s2l.toArray ∧
        s1 = Codec.s1Of cl s2l (hv.map Int.ofNat)) ∧
      sOf k c z0 z1 = (s1, s2) :=
  _root_.FalconPrecision.Exec.katIn_spec (e := e) (k := k) (c := c) (s1 := s1) (s2 := s2) (z0 := z0)
    (z1 := z1) (h := h)
end FalconPrecision.Exec
end

section
open MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]
example (b : BaseBits) {i : ℕ} (hi : i ≤ 18) :
    (pdtZ (falcon512S.tab b) i : ℝ) ≤
        pdtZ (falcon512S.tab b) 0 * Real.exp (-((i ^ 2 : ℕ) * kS)) * (1 + 1 / 2 ^ 45) ∧
      (pdtZ (falcon512S.tab b) 0 : ℝ) * Real.exp (-((i ^ 2 : ℕ) * kS)) * (1 - epsT i) ≤
        pdtZ (falcon512S.tab b) i :=
  _root_.FalconPrecision.Exec.tab_ok (b := b) (i := i) (hi := hi)

example (S : SampChoices) (hS : S.shiftRej = true) (σ t : Fx 64)
    (hσ : inRangeB falcon512S σ = true) :
    (∀ y, 0 ≤ lawZ falcon512S S σ t y) ∧
      (∀ y, (lawZ falcon512S S σ t y : ℝ) ≤
        uB * discreteGaussianPMF σ.toReal t.toReal y) ∧
      ∑' y, ENNReal.ofReal (((lawZ falcon512S S σ t y : ℝ) -
        discreteGaussianPMF σ.toReal t.toReal y) ^ 2 /
          discreteGaussianPMF σ.toReal t.toReal y) ≤ ENNReal.ofReal chi2B :=
  _root_.FalconPrecision.Exec.lawZ_close (S := S) (hS := hS) (σ := σ) (t := t) (hσ := hσ)

omit [LawfulMonad m] in
example {a : ℝ} (ha : 2 ≤ a) (S : SampChoices) (hS : S.shiftRej = true)
    (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64) (hσ : inRangeB falcon512S σ = true) :
    renyiMGF a 𝒟[samplerZ falcon512S S ub σ t] (discreteGaussianMeasure σ.toReal t.toReal) ≤
      ENNReal.ofReal (Real.exp ((a - 1) * εZ a)) :=
  _root_.FalconPrecision.Exec.samplerZ_mgf (m := m) (a := a) (ha := ha) (S := S) (hS := hS)
    (ub := ub) (hub := hub) (σ := σ) (t := t) (hσ := hσ)

omit [LawfulMonad m] in
example (S : SampChoices) (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64)
    (hσ : inRangeB falcon512S σ = true) :
    (𝒟[samplerZ falcon512S S ub σ t]).etvDist
        𝒟[samplerZ falcon512S { S with shiftRej := true } ub σ t] ≤
      ENNReal.ofReal (if S.shiftRej then 0 else 1 / 2 ^ 110) :=
  _root_.FalconPrecision.Exec.samplerZ_tv (m := m) (S := S) (ub := ub) (hub := hub) (σ := σ)
    (t := t) (hσ := hσ)
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact
  FalconPrecision.Errors.FFTRec
open scoped ENNReal
namespace FalconPrecision.Exec
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
section
variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : Adm C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9)
    (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (sampI : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = sampI σ t)
    (hI : ∀ σ t, inRangeB falcon512S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    (ub : ℕ → m ℕ) (hub : UnifBits ub)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specKS C.x C.xn aux δq) α) (hq : PathSum (wKS C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 61) <
      𝒟[simulateQ (execImplS C δq implA (samplerZ falcon512S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT _ (embed C.x C.xn δq (embedS C.x C.xn δq oe)))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Exec.falcon512_exec_sampler_vs_true (ιA := ιA) (aux := aux) (m := m)
    (C := C) (hC := hC) (hR := hR) (hq77 := hq77) (δq := δq) (K := K) (hK := hK) (hδ := hδ) (T := T)
    (hT := hT) (implA := implA) (implE := implE) (implM := implM) (implF := implF) (hAE := hAE)
    (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF) (sampI := sampI) (hsamp := hsamp)
    (hI := hI) (ub := ub) (hub := hub) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs)
    (hwin := hwin)
end
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact
  FalconPrecision.Errors.FFTRec
open scoped ENNReal
namespace FalconPrecision.Exec
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example [OracleSpec.AnswerMeasure aux] :
    ∃ (implA : QueryImpl aux (OracleComp (wspecU aux)))
      (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) (OracleComp (wspecU aux)))
      (sampI : Fx 64 → Fx 64 → OracleComp (wspecU aux) ℤ) (ub : ℕ → OracleComp (wspecU aux) ℕ),
      (∀ x, implE (.inl x) = implA x) ∧ (∀ x, implM (.inl x) = implA x) ∧
      (∀ x, implF (.inl x) = implA x) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
        discreteGaussianMeasure q.σ q.t) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
        discreteGaussianMeasure q.σbar q.t) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
        discreteGaussianMeasure q.σbar q.tbar) ∧
      (∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
        (implF (.inr q) : OracleComp (wspecU aux) ℤ) = sampI σ t) ∧
      (∀ σ t, inRangeB falcon512S σ = true →
        𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal) ∧
      UnifBits ub :=
  _root_.FalconPrecision.Exec.exec_sampler_worlds_exist (ιA := ιA) (aux := aux)
end FalconPrecision.Exec
end

section
open MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]
omit [LawfulMonad m] in
example (P : SampParams) (S : SampChoices) (hT : (P.tab S.base).okB = true)
    (ub : ℕ → m ℕ) (hub : UnifBits ub) (σ t : Fx 64) (y : ℤ) :
    𝒟[samplerZ P S ub σ t] {y} = ENNReal.ofReal (lawZ P S σ t y) :=
  _root_.FalconPrecision.Exec.samplerZ_law (m := m) (P := P) (S := S) (hT := hT) (ub := ub)
    (hub := hub) (σ := σ) (t := t) (y := y)
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFSamp
example (C : Choices) (δq : ℕ → ℚ) (W : ℕ) (k : RawKey)
    (hc : check C.x C.xn δq k = true) (h32 : checkRange C 32 W k = true)
    (h64 : checkRange C 64 W k = true) {m : Type → Type*} [Monad m] [LawfulMonad m] {S M : Type}
    (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S) (hash : S → M → m ZPoly)
    (msg : M) :
    signMsgX { C with word := some 32 } (fun s => clampS W (sampF s)) salt hash k msg =
      signMsgX { C with word := some 64 } (fun s => clampS W (sampF s)) salt hash k msg :=
  _root_.FalconPrecision.Exec.signMsgX_32_64 (C := C) (δq := δq) (W := W) (k := k) (hc := hc)
    (h32 := h32) (h64 := h64) (m := m) (S := S) (M := M) (sampF := sampF) (salt := salt)
    (hash := hash) (msg := msg)

example (C : Choices) (δq : ℕ → ℚ) (k : RawKey)
    (hc : check C.x C.xn δq k = true) (h32 : checkRange C 32 19 k = true)
    (h64 : checkRange C 64 19 k = true) {m : Type → Type*} [Monad m] [LawfulMonad m] {S M : Type}
    (ub : ℕ → m ℕ) (salt : m S) (hash : S → M → m ZPoly) (msg : M) :
    signMsgX { C with word := some 32 } (fun s => samplerZ falcon512S s ub) salt hash k msg =
      signMsgX { C with word := some 64 } (fun s => samplerZ falcon512S s ub) salt hash k msg :=
  _root_.FalconPrecision.Exec.signMsgZ_32_64 (C := C) (δq := δq) (k := k) (hc := hc) (h32 := h32)
    (h64 := h64) (m := m) (S := S) (M := M) (ub := ub) (salt := salt) (hash := hash) (msg := msg)

example (C : Choices) (rc : RMode) (h : tabEqB C.x.rc rc 64 = true) {m : Type → Type*}
    [Monad m] (samp : Fx 64 → Fx 64 → m ℤ) (T : CTree 64 9) (k : RawKey) (c : ZPoly) :
    signX C samp T k c = signX { C with x := { C.x with rc := rc } } samp T k c :=
  _root_.FalconPrecision.Exec.signX_rc (C := C) (rc := rc) (h := h) (m := m) (samp := samp) (T := T)
    (k := k) (c := c)

example (C : Choices) (rc : RMode) (h64 : tabEqB C.x.rc rc 64 = true)
    (hx : tabEqB C.x.rc rc (64 + C.xn) = true)
    (hσ : (Fx.ofRat C.x.rc σ512q : Fx (64 + C.xn)) = Fx.ofRat rc σ512q) {m : Type → Type*}
    [Monad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S)
    (hash : S → M → m ZPoly) (k : RawKey) (msg : M) :
    signMsgX C sampF salt hash k msg =
      signMsgX { C with x := { C.x with rc := rc } } sampF salt hash k msg :=
  _root_.FalconPrecision.Exec.signMsgX_rc (C := C) (rc := rc) (h64 := h64) (hx := hx) (hσ := hσ)
    (m := m) (S := S) (M := M) (sampF := sampF) (salt := salt) (hash := hash) (k := k) (msg := msg)

example (C : Choices) (P : XChoices) (n : ℕ) (hrm : P.rm = C.x.rm)
    (hrc : P.rc = C.x.rc) (k : RawKey) (hT : (storeC C.x C.xn k).eqB (storeC P n k) = true)
    {m : Type → Type*} [Monad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ)
    (salt : m S) (hash : S → M → m ZPoly) (msg : M) :
    signMsgX C sampF salt hash k msg =
      signMsgX { C with x := P, xn := n } sampF salt hash k msg :=
  _root_.FalconPrecision.Exec.signMsgX_store (C := C) (P := P) (n := n) (hrm := hrm) (hrc := hrc)
    (k := k) (hT := hT) (m := m) (S := S) (M := M) (sampF := sampF) (salt := salt) (hash := hash)
    (msg := msg)

example (C : Choices) (hs : C.salt = .perAttempt) {m : Type → Type*} [Monad m]
    [LawfulMonad m] {S M : Type} (sampF : SampChoices → Fx 64 → Fx 64 → m ℤ) (salt : m S)
    (hash : S → M → m ZPoly) (k : RawKey) (msg : M) (N j : ℕ) :
    signMsgX { C with cap := N + j } sampF salt hash k msg =
      signMsgX { C with cap := N } sampF salt hash k msg >>= fun r =>
        r.elim (signMsgX { C with cap := j } sampF salt hash k msg) fun b => pure (some b) :=
  _root_.FalconPrecision.Exec.signMsgX_cap_add (C := C) (hs := hs) (m := m) (S := S) (M := M)
    (sampF := sampF) (salt := salt) (hash := hash) (k := k) (msg := msg) (N := N) (j := j)

example {m : Type → Type*} [Monad m] [LawfulMonad m] {S M β : Type} (salt : m S)
    (hash : S → M → m ZPoly) (att : ZPoly → m (Option (ZPoly × ZPoly)))
    (acc : ZPoly → Option (ZPoly × ZPoly) → Option β) (msg : M) :
    signLoopX .reused salt hash att acc msg 1 = signLoopX .perAttempt salt hash att acc msg 1 :=
  _root_.FalconPrecision.Exec.signLoopX_one (m := m) (S := S) (M := M) (β := β) (salt := salt)
    (hash := hash) (att := att) (acc := acc) (msg := msg)
end FalconPrecision.Exec
end

section
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.FFTReal FalconPrecision.Errors.Fixed ComplexConjugate
namespace FalconPrecision.Exec
namespace Cx
example (r : RMode) (z : Cx 64) : ‖(z.half r).toC - z.toC / 2‖ ≤ 2 / 2 ^ 64 :=
  _root_.FalconPrecision.Exec.Cx.half_err (r := r) (z := z)
end Cx
end FalconPrecision.Exec
end

section
open FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.FFTReal FalconPrecision.Errors.Fixed ComplexConjugate
namespace FalconPrecision.Exec
example (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi64 : i ≤ 64) (k : RawKey)
    (hk : check C.x C.xn δq k = true) (hr : checkRange C i W k = true) (c : ZPoly)
    (hc : ∀ j, |c j| < 12289) {x : Cx 64}
    (hx : LeafX { C with word := none } W (storeC C.x C.xn k)
      (targetX { C with word := none } k.f k.F c).1
      (targetX { C with word := none } k.f k.F c).2 x) :
    |x.im.toRat| ≤ imE i :=
  _root_.FalconPrecision.Exec.leafX_im (C := C) (δq := δq) (i := i) (W := W) (hi64 := hi64) (k := k)
    (hk := hk) (hr := hr) (c := c) (hc := hc) (x := x) (hx := hx)

example (C : Choices) (δq : ℕ → ℚ) (i W : ℕ) (hi : 1 ≤ i) (hi64 : i ≤ 64)
    (k : RawKey) (hc : check C.x C.xn δq k = true) (hk : checkRange C i W k = true)
    {m : Type → Type*} [Monad m] [LawfulMonad m] (samp : Fx 64 → Fx 64 → m ℤ) (c : ZPoly) :
    signX { C with word := some i } (clampS W samp) (storeC C.x C.xn k) k c =
      signX { C with word := none } (clampS W samp) (storeC C.x C.xn k) k c :=
  _root_.FalconPrecision.Exec.signX_word (C := C) (δq := δq) (i := i) (W := W) (hi := hi)
    (hi64 := hi64) (k := k) (hc := hc) (hk := hk) (m := m) (samp := samp) (c := c)

example (C : Choices) (δq : ℕ → ℚ) (W : ℕ) (k : RawKey)
    (hc : check C.x C.xn δq k = true) (h32 : checkRange C 32 W k = true)
    (h64 : checkRange C 64 W k = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (samp : Fx 64 → Fx 64 → m ℤ) (c : ZPoly) :
    signX { C with word := some 32 } (clampS W samp) (storeC C.x C.xn k) k c =
      signX { C with word := some 64 } (clampS W samp) (storeC C.x C.xn k) k c :=
  _root_.FalconPrecision.Exec.sign32_eq_sign64 (C := C) (δq := δq) (W := W) (k := k) (hc := hc)
    (h32 := h32) (h64 := h64) (m := m) (samp := samp) (c := c)
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example (C : Choices) (h : Adm C) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t)
    {L : ℕ} (hL : L ≤ 9) (T : CTree 64 L) (hT : T.Ok) (t0 t1 : Out L → ℂ)
    (t0h t1h : Out L → Cx 64) :
    (fun r => r.map fun s => (s.z0, s.z1)) <$> simulateQ impl
        (ffsG (aux := aux) (arithX C h).toArith (1 / 2 ^ 64) (chkOf C.rchk) (T.toFTree hT) t0 t1
          (fun o => (t0h o).toC) (fun o => (t1h o).toC)) =
      (fun r => r.map fun s => (s.z0, s.z1)) <$> ffsX C samp T t0h t1h :=
  _root_.FalconPrecision.Exec.ffsX_refines (ιA := ιA) (aux := aux) (C := C) (h := h) (m := m)
    (impl := impl) (samp := samp) (himpl := himpl) (L := L) (hL := hL) (T := T) (hT := hT)
    (t0 := t0) (t1 := t1) (t0h := t0h) (t1h := t1h)

example (C : Choices) (h : Adm C) (δq : ℕ → ℚ) (k : RawKey)
    (hk : check C.x C.xn δq k = true) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (FalconGame.spec aux Falcon.CallP) m) (samp : Fx 64 → Fx 64 → m ℤ)
    (himpl : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (impl (.inr q) : m ℤ) = samp σ t) (c : ZPoly) :
    simulateQ impl (sign164G (aux := aux) (arithX C h) (chkOf C.rchk)
        (toKeyB C.x C.xn δq k hk).toKey c) = signX C samp (storeC C.x C.xn k) k c :=
  _root_.FalconPrecision.Exec.signX_refines (ιA := ιA) (aux := aux) (C := C) (h := h) (δq := δq)
    (k := k) (hk := hk) (m := m) (impl := impl) (samp := samp) (himpl := himpl) (c := c)
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
section
variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]
example [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : Adm C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9)
    (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (samp : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = samp σ t)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specK C.x C.xn aux δq) α) (hq : PathSum (wKC C.x C.xn δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ (execImpl C δq implA samp) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT _ (embed C.x C.xn δq oe))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Exec.falcon512_exec_vs_true (ιA := ιA) (aux := aux) (m := m) (C := C)
    (hC := hC) (hR := hR) (hq77 := hq77) (δq := δq) (K := K) (hK := hK) (hδ := hδ) (T := T)
    (hT := hT) (implA := implA) (implE := implE) (implM := implM) (implF := implF) (hAE := hAE)
    (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF) (samp := samp) (hsamp := hsamp)
    (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs) (hwin := hwin)
end
end FalconPrecision.Exec
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.HopB ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Exec
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example (P : XChoices) (n : ℕ) (δq : ℕ → ℚ) (kc : CheckedKey P n δq)
    {S M β : Type} (mode : SaltMode) (salt : OracleComp (specK P n aux δq) S)
    (hash : S → M → OracleComp (specK P n aux δq) ZPoly)
    (hs : PathSum (wKC P n δq) salt 0) (hh : ∀ s x, PathSum (wKC P n δq) (hash s x) 0)
    (acc : ZPoly → Option (ZPoly × ZPoly) → Option β) (msg : M) (N : ℕ) :
    PathSum (wKC P n δq) (signLoopX mode salt hash
      (fun c => (liftM (OracleSpec.query (spec := specK P n aux δq) (.inr (kc, c))) :
        OracleComp (specK P n aux δq) (Option (ZPoly × ZPoly)))) acc msg N) N :=
  _root_.FalconPrecision.Exec.pathSum_signLoopX (ιA := ιA) (aux := aux) (P := P) (n := n) (δq := δq)
    (kc := kc) (S := S) (M := M) (β := β) (mode := mode) (salt := salt) (hash := hash) (hs := hs)
    (hh := hh) (acc := acc) (msg := msg) (N := N)
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec.Witness
open FalconPrecision.Errors.FFTRec Round3
example (C : Choices) (k : RawKey) (c : ZPoly) :
    ofArr 9 (targetFracXA C k c).1 = (targetFracX C k c).1 ∧
      ofArr 9 (targetFracXA C k c).2 = (targetFracX C k c).2 :=
  _root_.FalconPrecision.Exec.Witness.ofArr_targetFracXA (C := C) (k := k) (c := c)

example (C : Choices) {m : Type → Type*} [Monad m] (samp : Fx 64 → Fx 64 → m ℤ)
    (T : CTree 64 9) (k : RawKey) (c : ZPoly) : signXcA C samp T k c = signXc C samp T k c :=
  _root_.FalconPrecision.Exec.Witness.signXcA_eq (C := C) (m := m) (samp := samp) (T := T) (k := k)
    (c := c)

example (C : Choices) (k : RawKey) (c : ZPoly) (scr : List (ℕ × List ℕ)) :
    attDcA C k c scr = attDc C k c scr :=
  _root_.FalconPrecision.Exec.Witness.attDcA_eq (C := C) (k := k) (c := c) (scr := scr)

example {C1 C2 : Choices} {k : RawKey} {c : ZPoly} {s1 s2 : List (ℕ × List ℕ)}
    (h : zl (attDcA C1 k c s1) ≠ zl (attDcA C2 k c s2)) : attDc C1 k c s1 ≠ attDc C2 k c s2 :=
  _root_.FalconPrecision.Exec.Witness.attDc_ne (C1 := C1) (C2 := C2) (k := k) (c := c) (s1 := s1)
    (s2 := s2) (h := h)

example {C1 C2 : Choices} {k : RawKey} {c : ZPoly} {scr : List (ℕ × List ℕ)}
    (h : attcNeB C1 C2 k c scr = true) : attDc C1 k c scr ≠ attDc C2 k c scr :=
  _root_.FalconPrecision.Exec.Witness.attDc_ne_of (C1 := C1) (C2 := C2) (k := k) (c := c)
    (scr := scr) (h := h)

example (h : witWordMfB = true) :
    attD cMF32 key70 c70 [] ≠ attD cMF64 key70 c70 [] :=
  _root_.FalconPrecision.Exec.Witness.wit_word_mf (h := h)

example (h : witTargetB = true) :
    attD cW key0 c0 scrTarget ≠ attD { cW with target := .multiplyFirst } key0 c0 scrTarget :=
  _root_.FalconPrecision.Exec.Witness.wit_target (h := h)

example (h : witDmB = true) :
    attD cW key0 c0 scrA ≠ attD { cW with x := { cW.x with dm := .invMul } } key0 c0 scrA :=
  _root_.FalconPrecision.Exec.Witness.wit_dm (h := h)

example (h : witRootB = true) :
    attD cW key0 c0 scrRoot ≠ attD { cW with x := { cW.x with root := .ntru } } key0 c0 scrRoot :=
  _root_.FalconPrecision.Exec.Witness.wit_root (h := h)

example (h : witRmUpB = true) :
    attD cW key0 c0 scrUp ≠ attD (cR .halfUp .halfEven) key0 c0 scrUp :=
  _root_.FalconPrecision.Exec.Witness.wit_rm_up (h := h)

example (h : witRmAwayB = true) :
    attD (cR .halfUp .halfEven) key0 c0 scrAway ≠ attD (cR .halfAway .halfEven) key0 c0 scrAway :=
  _root_.FalconPrecision.Exec.Witness.wit_rm_away (h := h)

example (h : witRmFloorB = true) :
    attD cW key0 c0 scrA ≠ attD (cR .floor .halfEven) key0 c0 scrA :=
  _root_.FalconPrecision.Exec.Witness.wit_rm_floor (h := h)

example (h : witRcFloorB = true) :
    attD cW key0 c0 scrA ≠ attD (cR .halfEven .floor) key0 c0 scrA :=
  _root_.FalconPrecision.Exec.Witness.wit_rc_floor (h := h)

example (h : witQinvB = true) :
    attD cW key0 c0 scrQinv ≠ attD { cW with qinv := .w64 } key0 c0 scrQinv :=
  _root_.FalconPrecision.Exec.Witness.wit_qinv (h := h)

example (h : witCentreB = true) :
    attDc cW key0 c0 scrCentre ≠
      attDc { cW with samp := { cW.samp with centre := .fractional } } key0 c0 scrCentre :=
  _root_.FalconPrecision.Exec.Witness.wit_centre (h := h)

example (h : witSaltB = true) :
    msgD cW key0 [c0, c70] scrRej ≠ msgD { cW with salt := .perAttempt } key0 [c0, c70] scrRej :=
  _root_.FalconPrecision.Exec.Witness.wit_salt (h := h)

example (h : witCapB = true) :
    msgD { cW with cap := 1 } key0 [c0, c70] scrRej ≠ msgD cW key0 [c0, c70] scrRej :=
  _root_.FalconPrecision.Exec.Witness.wit_cap (h := h)

example (h : witWordMfSigB = true) :
    msgD cMF32 key70 [c70] [] = none ∧ (msgD cMF64 key70 [c70] []).isSome = true :=
  _root_.FalconPrecision.Exec.Witness.wit_word_mf_none (h := h)

example (h : witWordMfSigB = true) :
    msgD cMF32 key70 [c70] [] ≠ msgD cMF64 key70 [c70] [] :=
  _root_.FalconPrecision.Exec.Witness.wit_word_mf_sig (h := h)

example :
    Id.run ((sampD [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
      ⟨33582297586188238716⟩ ⟨0⟩).run' {}) ≠
    Id.run ((sampD [(0, [198, 12, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b79⟩
      ⟨33582297586188238716⟩ ⟨0⟩).run' {}) :=
  _root_.FalconPrecision.Exec.Witness.samp_base

example :
    Id.run ((sampD [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, false, .b72⟩
      ⟨23571871177321116846⟩ ⟨0⟩).run' {}) ≠
    Id.run ((sampD [(0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] ⟨.plain, true, .b72⟩
      ⟨23571871177321116846⟩ ⟨0⟩).run' {}) :=
  _root_.FalconPrecision.Exec.Witness.samp_shift
end FalconPrecision.Exec.Witness
end

section
open OracleSpec OracleComp MeasureTheory InformationTheory LatticeCrypto FalconPrecision.RenyiPath
  FalconPrecision.Errors.HopB FalconPrecision.Errors.FFTRec
open scoped ENNReal
namespace FalconPrecision.Exec
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
section
variable [hA : ∀ t, Countable (aux t)] {m : Type → Type*} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example [∀ t, Nonempty (aux t)]
    (C : Choices) (hC : Adm C) (hR : C.rchk = none) (hq77 : C.qinv = .w77) (i : ℕ) (hi : 1 ≤ i)
    (hi64 : i ≤ 64) (δq : ℕ → ℚ)
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) (fun j => (δq j : ℝ)) ≤ 1 / 2 ^ 9)
    (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (sampI : Fx 64 → Fx 64 → m ℤ)
    (hsamp : ∀ (σ t : Fx 64) (q : Falcon.CallP), q.σbar = σ.toReal → q.tbar = t.toReal →
      (implF (.inr q) : m ℤ) = sampI σ t)
    (hI : ∀ σ t, inRangeB falcon512S σ = true →
      𝒟[sampI σ t] = discreteGaussianMeasure σ.toReal t.toReal)
    (ub : ℕ → m ℕ) (hub : UnifBits ub)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specKR C i aux δq) α) (hq : PathSum (wKR C i δq) oe K)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : (2 : ℝ≥0∞) ^ (1 / 64 : ℝ) * (T * 2 ^ (-(126 : ℝ)) + 2 ^ (-(140 : ℝ))) +
        ENNReal.ofReal (if C.samp.shiftRej then 0 else 1 / 2 ^ 61) <
      𝒟[simulateQ (execImplR C i δq implA (samplerZ falcon512S C.samp ub)) oe] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) <
      𝒟[simulateQ implE (runT _ (embed C.x C.xn δq (embedS C.x C.xn δq (embedR C i δq oe))))] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Exec.falcon512_exec_word_sampler_vs_true (ιA := ιA) (aux := aux) (m := m)
    (C := C) (hC := hC) (hR := hR) (hq77 := hq77) (i := i) (hi := hi) (hi64 := hi64) (δq := δq)
    (K := K) (hK := hK) (hδ := hδ) (T := T) (hT := hT) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (sampI := sampI) (hsamp := hsamp) (hI := hI) (ub := ub) (hub := hub) (α := α)
    (oe := oe) (hq := hq) (s := s) (hs := hs) (hwin := hwin)
end
end FalconPrecision.Exec
end

section
namespace FalconPrecision.Exec.Codec
open VCVio.Algorithms.Keccak (shake256)
open Round3 (qN centre modq polyOf inttq)
example {n : ℕ} {str : List UInt8} {c : List ℕ}
    (h : hashToPoint n str = some c) :
    ∃ L, ∀ L' ≥ L, htpOf n ((List.range L').map (xof str)) = some c :=
  _root_.FalconPrecision.Exec.Codec.hashToPoint_spec (n := n) (str := str) (c := c) (h := h)

example (V : VerChoices) (h c : List ℕ) (s2 : List ℤ) :
    verifyCore V h c s2 = true ↔ ∃ s1 : Fin (2 ^ 9) → ℤ,
      (∀ i : Fin (2 ^ 9), ((c.getD i 0 : ℤ) -
          ncoef (polyOf s2.toArray) (polyOf (h.map Int.ofNat).toArray) i - s1 i) % (qN : ℤ) = 0 ∧
        2 * |s1 i| < qN) ∧
      normSq s1 + normSq (polyOf s2.toArray) ≤ V.beta2 ∧ infOk V.infB s1 = true ∧
      infOk V.infB (polyOf s2.toArray) = true :=
  _root_.FalconPrecision.Exec.Codec.verifyCore_iff (V := V) (h := h) (c := c) (s2 := s2)
end FalconPrecision.Exec.Codec
end
