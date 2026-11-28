import FalconPrecision.Errors.AbortExact
import FalconPrecision.Errors.AbortTV
import FalconPrecision.Errors.FFSampModel
import FalconPrecision.Errors.FFTRec
import FalconPrecision.Errors.FalconCenters
import FalconPrecision.Errors.FalconLeaf
import FalconPrecision.Errors.FalconProved
import FalconPrecision.Errors.GaussTail
import FalconPrecision.Errors.HopB
import FalconPrecision.Errors.HopBCore
import FalconPrecision.Errors.PathCompose
import FalconPrecision.Errors.SignModel
import FalconPrecision.Errors.SignModel64
import FalconPrecision.Instances
import FalconPrecision.Lemma4
import FalconPrecision.Lemma5
import FalconPrecision.NumK
import FalconPrecision.NumTail
import FalconPrecision.RenyiHybrid
import FalconPrecision.RenyiPath
import FalconPrecision.RenyiScale
import FalconPrecision.RenyiShift
import FalconPrecision.Security
import FalconPrecision.ThetaTail
import FalconPrecision.Witness

/-! The statements of release 0.5.0, verbatim in their scopes, of every theorem outside
`FalconPrecision.Exec` that README.md or LIMITS.md names: each theorem, applied to the binders by
name, has the 0.5.0 type. -/

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFTReal
  FalconPrecision.Errors.AbortTV ComplexConjugate
namespace FalconPrecision.RenyiPath
section
variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]
example [∀ t, Nonempty (spec.Range t)] (impl : QueryImpl spec m)
    {so : QueryImpl spec (OracleComp spec)} (f : (t : ι) → spec.Range t → spec.Range t)
    (hso : ∀ t, so t = f t <$> liftM (OracleSpec.query t)) {c : ℝ} (hc : 0 ≤ c) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t)
    (hB : ∀ t, @MeasureTheory.Measure.etvDist _ ⊤ (@evalDist m _ (spec.Range t) ⊤ (impl t))
      (@MeasureTheory.Measure.map _ _ ⊤ ⊤ (f t) (@evalDist m _ (spec.Range t) ⊤ (impl t))) ≤
        ENNReal.ofReal (c * w t))
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) :
    ∀ S, PathSum w (simulateQ so oa) S →
      (𝒟[simulateQ impl oa]).etvDist 𝒟[simulateQ impl (simulateQ so oa)] ≤
          ENNReal.ofReal (c * S) :=
  _root_.FalconPrecision.RenyiPath.etvDist_simulateQ_rewrite (ι := ι) (spec := spec) (m := m)
    (impl := impl) (so := so) (f := f) (hso := hso) (c := c) (hc := hc) (w := w) (hw := hw)
    (hB := hB) (α := α) (oa := oa)
end
end FalconPrecision.RenyiPath
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFTReal
  FalconPrecision.Errors.AbortTV ComplexConjugate
namespace FalconPrecision.Errors.AbortExact
open FalconPrecision.Errors.FFSamp MeasureTheory LatticeCrypto
open scoped ENNReal
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example (ρ : Arith) (u : ℝ)
    (so : QueryImpl (FalconGame.spec aux Falcon.CallP)
        (OracleComp (FalconGame.spec aux Falcon.CallP)))
    (hso : ∀ q : Falcon.CallP, AllOut (fun z : ℤ => |(z : ℝ) - q.t| ≤ 30)
        (so (.inr q) : OracleComp _ ℤ))
    (chk : (L : ℕ) → (Out L → ℂ) → (Out L → ℂ) → Prop)
    (hchk : ∀ L vh v, (∀ o, ‖v o‖ ≤ 2 ^ 24 - 2) → chk L vh v) {L : ℕ} (T : FTree L) (hT : T.Real) :
    L ≤ 9 → ∀ (t0 t1 t0h t1h a0 a1 r0 r1 : Out L → ℂ), t0 = a0 + r0 → t1 = a1 + r1 →
      (∀ o, ‖a0 o‖ ≤ 1792000) → (∀ o, ‖a1 o‖ ≤ 1792000) → l2 r0 ≤ gT L → l2 r1 ≤ gT L →
      IsReal t0 → IsReal t1 →
      simulateQ so (ffsG (aux := aux) ρ u chk T t0 t1 t0h t1h) =
        simulateQ so (ffsG (aux := aux) ρ u (fun _ _ _ => True) T t0 t1 t0h t1h) ∧
      AllOut (Good t0 t1)
        (simulateQ so (ffsG (aux := aux) ρ u (fun _ _ _ => True) T t0 t1 t0h t1h)) :=
  _root_.FalconPrecision.Errors.AbortExact.ffsG_clamp (ιA := ιA) (aux := aux) (ρ := ρ) (u := u)
    (so := so) (hso := hso) (chk := chk) (hchk := hchk) (L := L) (T := T) (hT := hT)
end FalconPrecision.Errors.AbortExact
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFTReal
  FalconPrecision.Errors.AbortTV ComplexConjugate
namespace FalconPrecision.Errors.AbortExact
open FalconPrecision.Errors.FFSamp MeasureTheory LatticeCrypto
open scoped ENNReal
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
variable {εq : ℝ}
example {β : Type} (ρ : Arith64 εq) (k : Key) (hk : k.tree.Real)
    (c : Fin (2 ^ 9) → ℤ)
    (acc : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) → Option β) :
    ∀ n, Swap (aux := aux) (sign164 ρ)
        (sign164G ρ fun _ _ _ => True) n (signLoopG (sign164 ρ) k c acc n)
      (signLoopG (sign164G ρ fun _ _ _ => True) k c acc n) :=
  _root_.FalconPrecision.Errors.AbortExact.Swap.signLoopG (ιA := ιA) (aux := aux) (εq := εq)
    (β := β) (ρ := ρ) (k := k) (hk := hk) (c := c) (acc := acc)
end FalconPrecision.Errors.AbortExact
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFTReal
  FalconPrecision.Errors.AbortTV ComplexConjugate
namespace FalconPrecision.Errors.AbortExact
open FalconPrecision.Errors.FFSamp MeasureTheory LatticeCrypto
open scoped ENNReal
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
variable {εq : ℝ}
variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]
example (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) (y : ℝ) (hy : 1 / 2 ≤ y) (hy30 : y ≤ 30)
    (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (K : ℕ) {α : Type} [MeasurableSpace α] {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) :
    (𝒟[simulateQ implE oa]).etvDist 𝒟[simulateQ implE ox] ≤
      2 * ENNReal.ofReal (pclamp y * (K * 1024)) :=
  _root_.FalconPrecision.Errors.AbortExact.etvDist_E_X (ιA := ιA) (aux := aux) (εq := εq) (m := m)
    (ρ := ρ) (hεq := hεq) (e := e) (he := he) (he1 := he1) (y := y) (hy := hy) (hy30 := hy30)
    (implE := implE) (hE := hE) (K := K) (α := α) (oa := oa) (ox := ox) (h := h)

example (K : ℕ) (hK : K ≤ 2 ^ 39) :
    2 * ENNReal.ofReal (pclamp 30 * (K * 1024)) ≤ (2 : ℝ≥0∞) ^ (-(140 : ℝ)) :=
  _root_.FalconPrecision.Errors.AbortExact.eps_le (K := K) (hK := hK)

example (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) (y : ℝ) (hy : 1 / 2 ≤ y) (hy' : y ≤ 299 / 10)
    [hA : ∀ t, Nonempty (aux t)] (implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    (K : ℕ) (hKe : (K : ℝ) * (49 * e + 43700 / 2 ^ 40) ^ 2 ≤ 1 / 2 ^ 8) {α : Type}
        [MeasurableSpace α]
    {oa ox : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) :
    (𝒟[simulateQ implF oa]).etvDist 𝒟[simulateQ implF ox] ≤
      2 * ENNReal.ofReal (pclampF y * (K * 1024)) :=
  _root_.FalconPrecision.Errors.AbortExact.etvDist_F_F' (ιA := ιA) (aux := aux) (εq := εq) (m := m)
    (ρ := ρ) (hεq := hεq) (e := e) (he := he) (he1 := he1) (y := y) (hy := hy) (hy' := hy')
    (hA := hA) (implF := implF) (hF := hF) (K := K) (hKe := hKe) (α := α) (oa := oa) (ox := ox)
    (h := h)

example (K : ℕ) (hK : K ≤ 2 ^ 39) :
    2 * ENNReal.ofReal (pclampF (299 / 10) * (K * 1024)) ≤ (2 : ℝ≥0∞) ^ (-(140 : ℝ)) :=
  _root_.FalconPrecision.Errors.AbortExact.eps_leF (K := K) (hK := hK)
end FalconPrecision.Errors.AbortExact
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFTReal
  FalconPrecision.Errors.AbortTV ComplexConjugate
namespace FalconPrecision.Falcon
open MeasureTheory InformationTheory LatticeCrypto FalconPrecision.Errors.FFSamp
    FalconPrecision.Errors.AbortExact
open scoped ENNReal
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) :=
  _root_.FalconPrecision.Falcon.falcon512_exact64n (ιA := ιA) (aux := aux) (m := m) (ρ := ρ)
    (K := K) (hK := hK) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (ox := ox) (hswap := hswap) (s := s) (hs := hs) (hwin := hwin)

example (ρ : Arith64 (1 / 2 ^ 65)) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) :=
  _root_.FalconPrecision.Falcon.falcon512_exact64 (ιA := ιA) (aux := aux) (m := m) (ρ := ρ) (K := K)
    (hK := hK) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (ox := ox) (hswap := hswap) (s := s) (hs := hs) (hwin := hwin)

example (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    [hA : ∀ t, Nonempty (aux t)]
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) < 𝒟[simulateQ implF ox] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) :=
  _root_.FalconPrecision.Falcon.falcon512_exact64n' (ιA := ιA) (aux := aux) (m := m) (ρ := ρ)
    (K := K) (hK := hK) (T := T) (hT := hT) (hA := hA) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (α := α) (oa := oa) (ox := ox) (hswap := hswap) (s := s) (hs := hs) (hwin := hwin)

example (ρ : Arith64 (1 / 2 ^ 65)) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    [hA : ∀ t, Nonempty (aux t)]
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa ox : OracleComp (FalconGame.spec aux CallP) α)
    (hswap : Swap (sign164 ρ) (sign164G ρ fun _ _ _ => True) K oa ox) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) < 𝒟[simulateQ implF ox] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE ox] s + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) :=
  _root_.FalconPrecision.Falcon.falcon512_exact64' (ιA := ιA) (aux := aux) (m := m) (ρ := ρ)
    (K := K) (hK := hK) (T := T) (hT := hT) (hA := hA) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (α := α) (oa := oa) (ox := ox) (hswap := hswap) (s := s) (hs := hs) (hwin := hwin)
end FalconPrecision.Falcon
end

section
open MeasureTheory OracleSpec OracleComp LatticeCrypto FalconPrecision.ThetaTail
    FalconPrecision.RenyiPath
open scoped ENNReal
namespace FalconPrecision.Errors.AbortTV
variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example (implQ implP : QueryImpl spec m) {c : ℝ} (hc : 0 ≤ c) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t)
    (hB : ∀ t, @Measure.etvDist _ ⊤ (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (c * w t))
    {α : Type} [MeasurableSpace α] {oa : OracleComp spec α} {S : ℝ} (h : PathSum w oa S) :
    (S < 0 → 𝒟[simulateQ implQ oa] = 0 ∧ 𝒟[simulateQ implP oa] = 0) ∧
      (𝒟[simulateQ implQ oa]).etvDist 𝒟[simulateQ implP oa] ≤ ENNReal.ofReal (c * S) :=
  _root_.FalconPrecision.Errors.AbortTV.etvDist_simulateQ_le_path (ι := ι) (spec := spec) (m := m)
    (implQ := implQ) (implP := implP) (c := c) (hc := hc) (w := w) (hw := hw) (hB := hB) (α := α)
    (oa := oa) (S := S) (h := h)
end FalconPrecision.Errors.AbortTV
end

section
open MeasureTheory OracleSpec OracleComp LatticeCrypto FalconPrecision.ThetaTail
    FalconPrecision.RenyiPath
open scoped ENNReal
namespace FalconPrecision.Errors.AbortTV
variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example (y : ℝ) (hy : 0 ≤ y)
    (implE : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (w : ιA ⊕ Falcon.CallP → ℝ) (hw : ∀ t, 0 ≤ w t) (hw1 : ∀ q, 1 ≤ w (.inr q))
    {α : Type} [MeasurableSpace α] {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α} {N : ℝ}
    (h : PathSum w oa N) :
    (𝒟[simulateQ implE oa]).etvDist 𝒟[simulateQ (implT y implE) oa] ≤
      ENNReal.ofReal (pclamp y * N) :=
  _root_.FalconPrecision.Errors.AbortTV.etvDist_implT_le (m := m) (ιA := ιA) (aux := aux) (y := y)
    (hy := hy) (implE := implE) (hE := hE) (w := w) (hw := hw) (hw1 := hw1) (α := α) (oa := oa)
    (N := N) (h := h)
end FalconPrecision.Errors.AbortTV
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath
namespace FalconPrecision.Errors.FFSamp
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example (ρ : Arith) {L : ℕ} (T : FTree L) : L ≤ 9 → ∀ (t0 t1 t0h t1h : Out L → ℂ) (e : ℝ),
    l2 (pairF (t0h - t0) (t1h - t1)) ≤ e →
    coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L * e +
        coefC nn512 w512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) (29 / 10 / 2 ^ 42) L ≤ 1 / 2 ^ 10 →
    PathSumP wS (Inv L) (ffs (aux := aux) ρ T t0 t1 t0h t1h)
      ((coefA nn512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) L * e +
          coefC nn512 w512 (√2 * (1 / 2 + 7072 / 10000 / 2 ^ 63)) (29 / 10 / 2 ^ 42) L) ^ 2) :=
  _root_.FalconPrecision.Errors.FFSamp.ffs_pathS (ιA := ιA) (aux := aux) (ρ := ρ) (L := L) (T := T)

example (ρ : Arith) {L : ℕ} (T : FTree L) (t0 t1 t0h t1h : Out L → ℂ) :
    PathSum w1 (ffs (aux := aux) ρ T t0 t1 t0h t1h) (2 ^ (L + 1)) :=
  _root_.FalconPrecision.Errors.FFSamp.ffs_pathN (ιA := ιA) (aux := aux) (ρ := ρ) (L := L) (T := T)
    (t0 := t0) (t1 := t1) (t0h := t0h) (t1h := t1h)
end FalconPrecision.Errors.FFSamp
end

section
namespace FalconPrecision.Errors.FFTRec
open FalconPrecision.Errors.FFTDef
example (δ r A : ℝ) (E : ℕ → ℝ)
    (ζ ζh : (L : ℕ) → Out L → ℂ) (pt : (L : ℕ) → Out L → ℂ)
    (hpt : ∀ L o b, pt (L + 1) (o, b) = if b then -ζ L o else ζ L o)
    (hsq : ∀ L o, ζ L o ^ 2 = pt L o) (hζ : ∀ L o, ‖ζ L o‖ = 1) (hpt0 : ∀ o, ‖pt 0 o‖ = 1)
    (hδ : ∀ L o, ‖ζh L o - ζ L o‖ ≤ δ)
    (fftH : (L : ℕ) → (Fin (2 ^ L) → ℂ) → Out L → ℂ)
    (h0 : ∀ a o, ‖fftH 0 a o - a ⟨0, by norm_num⟩‖ ≤ E 0)
    (hrec : ∀ L a o, ∃ p : ℂ, ‖p - ζh L o * fftH L (odds (castC a)) o‖ ≤ r ∧
      fftH (L + 1) a (o, false) = fftH L (evens (castC a)) o + p ∧
      fftH (L + 1) a (o, true) = fftH L (evens (castC a)) o - p)
    (hE : ∀ L, E (L + 1) = E L * (2 + δ) + δ * (2 ^ L * A) + r) :
    ∀ L (a : Fin (2 ^ L) → ℂ), (∀ i, ‖a i‖ ≤ A) → ∀ o, ‖fftH L a o - evalAt a (pt L o)‖ ≤ E L :=
  _root_.FalconPrecision.Errors.FFTRec.fft_rec_err (δ := δ) (r := r) (A := A) (E := E) (ζ := ζ)
    (ζh := ζh) (pt := pt) (hpt := hpt) (hsq := hsq) (hζ := hζ) (hpt0 := hpt0) (hδ := hδ)
    (fftH := fftH) (h0 := h0) (hrec := hrec) (hE := hE)
end FalconPrecision.Errors.FFTRec
end

section
namespace FalconPrecision.Errors.FFSamp
open FalconPrecision.Errors.FFTRec
example (T : ETree 9) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 7072 / 10000 / 2 ^ 63)
    (hT : T.Hyp lam512 nn512 w512 δ (29 / 10 / 2 ^ 42)) :
    √T.leafSq ≤ 49 * l2 (pairF T.x0 T.x1) + 135700 / 2 ^ 42 :=
  _root_.FalconPrecision.Errors.FFSamp.falcon512_centers (T := T) (δ := δ) (hδ0 := hδ0) (hδ := hδ)
    (hT := hT)
end FalconPrecision.Errors.FFSamp
end

section
namespace FalconPrecision.Errors.LDL
example (σ : ℝ) (hσ : 0 < σ) (Idx : ℕ → Type) (V Vh : (ℓ : ℕ) → Idx ℓ → ℝ)
    (hroot : ∀ i, (12289 / 16 ≤ V 0 i ∧ V 0 i ≤ 16 * 12289) ∧ RelClose (1 / 2 ^ 45) (V 0 i)
        (Vh 0 i))
    (hstep : ∀ ℓ j, ∃ i₁ i₂,
      (V (ℓ + 1) j = am (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - am (Vh ℓ i₁) (Vh ℓ i₂)| ≤ 1 / 2 ^ 35) ∨
      (V (ℓ + 1) j = hm (V ℓ i₁) (V ℓ i₂) ∧ |Vh (ℓ + 1) j - hm (Vh ℓ i₁) (Vh ℓ i₂)| ≤ 1 / 2 ^ 35))
    (σh : Idx 8 → ℝ) (hs : ∀ j, |σh j - σ / √(Vh 8 j)| ≤ 1 / 2 ^ 50 * (σ / √(Vh 8 j))) (j : Idx 8) :
    |σh j / (σ / √(V 8 j)) - 1| ≤ 1 / 2 ^ 42 :=
  _root_.FalconPrecision.Errors.LDL.falcon512_leaf (σ := σ) (hσ := hσ) (Idx := Idx) (V := V)
    (Vh := Vh) (hroot := hroot) (hstep := hstep) (σh := σh) (hs := hs) (j := j)
end FalconPrecision.Errors.LDL
end

section
open MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Falcon
example : (2 : ℝ) ^ 38 * (49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42) ^ 2 ≤ 1 /
    2 ^ 9 :=
  _root_.FalconPrecision.Falcon.centers_budget
end FalconPrecision.Falcon
end

section
open MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Falcon
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example (T : ℝ≥0∞) (hT : 1 ≤ T) (implA : QueryImpl aux m)
    (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
        (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux CallP) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa (2 ^ 51))
    (hS₂ : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun q : CallP => (q.tbar - q.t) ^ 2) oa
        (1 / 2 ^ 9))
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.Falcon.falcon512_proved (ιA := ιA) (aux := aux) (m := m) (T := T)
    (hT := hT) (implA := implA) (implE := implE) (implM := implM) (implF := implF) (hAE := hAE)
    (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF) (α := α) (oa := oa) (hN := hN)
    (hS₂ := hS₂) (s := s) (hs := hs) (hwin := hwin)
end FalconPrecision.Falcon
end

section
open Real MeasureTheory LatticeCrypto FalconPrecision.ThetaTail
open scoped ENNReal
namespace FalconPrecision.Errors.GaussTail
example (σ c r : ℝ) (hσ : 0 < σ) (hT : tail σ < 1) (hr : 0 ≤ r) :
    discreteGaussianMeasure σ c {z | r ≤ |(z : ℝ) - c|} ≤
      ENNReal.ofReal (2 * kappa σ * Real.exp (-(r ^ 2 / (2 * σ ^ 2)))) :=
  _root_.FalconPrecision.Errors.GaussTail.measure_abs_ge_le (σ := σ) (c := c) (r := r) (hσ := hσ)
    (hT := hT) (hr := hr)

example (σ : ℝ) (hσ : 1277 / 1000 ≤ σ) : tail σ < 1 ∧ kappa σ ≤ 1 + 1 / 2 ^ 36 :=
  _root_.FalconPrecision.Errors.GaussTail.kappa_falcon (σ := σ) (hσ := hσ)
end FalconPrecision.Errors.GaussTail
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Errors.HopB
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} {δ : ℕ → ℝ} {εq : ℝ}
variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]
example (ρ : Arith64 εq) (implA : QueryImpl aux m)
    (implE implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] (oe : OracleComp (specS aux δ) α) :
    𝒟[simulateQ implE (runX ρ oe)] = 𝒟[simulateQ implF (runB δ oe)] :=
  _root_.FalconPrecision.Errors.HopB.relabel_X (ιA := ιA) (aux := aux) (δ := δ) (εq := εq) (m := m)
    (ρ := ρ) (implA := implA) (implE := implE) (implF := implF) (hAE := hAE) (hAF := hAF) (hE := hE)
    (hF := hF) (α := α) (oe := oe)

example [∀ t, Countable (aux t)] (K : ℕ) (hK : K ≤ 2 ^ 39)
    (hδ : (K : ℝ) * s2B (61 / 2) δ ≤ 1 / 2 ^ 9) (T : ℝ≥0∞) (hT : 1 ≤ T) (implA : QueryImpl aux m)
    (implE implM implF : QueryImpl (FalconGame.spec aux Falcon.CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oe : OracleComp (specS aux δ) α) (hq : PathSum (wK δ) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(129 : ℝ)) + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) <
        𝒟[simulateQ implF (runB δ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ oe)] s + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Errors.HopB.falcon512_hopB (ιA := ιA) (aux := aux) (δ := δ) (m := m)
    (K := K) (hK := hK) (hδ := hδ) (T := T) (hT := hT) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs) (hwin := hwin)

example [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78))
    (K : ℕ) (hK : K ≤ 2 ^ 39) (hδ : (K : ℝ) * s2B (61 / 2) δ ≤ 1 / 2 ^ 9) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS aux δ) α) (hq : PathSum (wK δ) oe K) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ oe)] s + (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Errors.HopB.falcon512_fixed_vs_true (ιA := ιA) (aux := aux) (δ := δ)
    (m := m) (ρ := ρ) (K := K) (hK := hK) (hδ := hδ) (T := T) (hT := hT) (implA := implA)
    (implE := implE) (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF)
    (hE := hE) (hM := hM) (hF := hF) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs)
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
    (oe : OracleComp (specS aux δ127) α) (hq : PathSum (wK δ127) oe K) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ127 oe)] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Errors.HopB.falcon512_fixed_vs_true127 (ιA := ιA) (aux := aux) (m := m)
    (ρ := ρ) (K := K) (hK := hK) (T := T) (hT := hT) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs) (hwin := hwin)

example [∀ t, Countable (aux t)] [∀ t, Nonempty (aux t)]
    (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 30) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    (oe : OracleComp (specS aux δ63) α) (hq : PathSum (wK δ63) oe K) {s : Set α}
        (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) + (2 : ℝ≥0∞) ^ (-(140 : ℝ)) <
        𝒟[simulateQ implF (runX ρ oe)] s) :
    T * (2 : ℝ≥0∞) ^ (-(131 : ℝ)) < 𝒟[simulateQ implE (runT δ63 oe)] s +
        (2 : ℝ≥0∞) ^ (-(141 : ℝ)) :=
  _root_.FalconPrecision.Errors.HopB.falcon512_fixed_vs_true63 (ιA := ιA) (aux := aux) (m := m)
    (ρ := ρ) (K := K) (hK := hK) (T := T) (hT := hT) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (α := α) (oe := oe) (hq := hq) (s := s) (hs := hs) (hwin := hwin)
end FalconPrecision.Errors.HopB
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath FalconPrecision.Errors.FFSamp
  FalconPrecision.Errors.AbortTV FalconPrecision.Errors.AbortExact FalconPrecision.Errors.FFTReal
      ComplexConjugate MeasureTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Errors.HopB
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
variable {δ : ℕ → ℝ} {εq : ℝ}
section
variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
example {α : Type} (oa : OracleComp spec α) : Hist (fun _ : ι => True)
    (fun _ => True) oa :=
  _root_.FalconPrecision.Errors.HopB.Hist.true (ι := ι) (spec := spec) (α := α) (oa := oa)
end
end FalconPrecision.Errors.HopB
end

section
open OracleSpec OracleComp
namespace FalconPrecision.RenyiPath
variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
example {w : ι → ℝ} {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {S T : ℝ} (h : PathSum w oa S) (hb : ∀ x, PathSum w (ob x) T) : PathSum w (oa >>= ob)
        (S + T) :=
  _root_.FalconPrecision.RenyiPath.PathSum.bind (ι := ι) (spec := spec) (w := w) (α := α) (β := β)
    (oa := oa) (ob := ob) (S := S) (T := T) (h := h) (hb := hb)

example {w : ι → ℝ} {α β : Type} {P : α → Prop} {Q : β → Prop}
    {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {S T : ℝ} (h : PathSumP w P oa S)
        (hb : ∀ x, P x → PathSumP w Q (ob x) T) :
    PathSumP w Q (oa >>= ob) (S + T) :=
  _root_.FalconPrecision.RenyiPath.PathSumP.bind (ι := ι) (spec := spec) (w := w) (α := α) (β := β)
    (P := P) (Q := Q) (oa := oa) (ob := ob) (S := S) (T := T) (h := h) (hb := hb)

example {w : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) {K : ℕ} {α : Type}
    {oa : OracleComp spec α}
    (h : BlockPath w c K oa) : PathSum w oa (K * c) :=
  _root_.FalconPrecision.RenyiPath.BlockPath.pathSum (ι := ι) (spec := spec) (w := w) (c := c)
    (hc := hc) (K := K) (α := α) (oa := oa) (h := h)
end FalconPrecision.RenyiPath
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath
namespace FalconPrecision.Errors.FFSamp
example (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) :
    l2 (pairF (t0C ρ k c - t0E k c) (t1C ρ k c - t1E k c)) ≤ 365 / 100 / 2 ^ 32 :=
  _root_.FalconPrecision.Errors.FFSamp.input_err (ρ := ρ) (k := k) (c := c) (hc := hc)
end FalconPrecision.Errors.FFSamp
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath
namespace FalconPrecision.Errors.FFSamp
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example {ρ : Arith} {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Uses ρ K oa) : PathSum wS oa (K * (49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42) ^ 2) :=
  _root_.FalconPrecision.Errors.FFSamp.Uses.pathS (ιA := ιA) (aux := aux) (ρ := ρ) (K := K) (α := α)
    (oa := oa) (h := h)

example {ρ : Arith} {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Uses ρ K oa) : PathSum w1 oa (K * 1024) :=
  _root_.FalconPrecision.Errors.FFSamp.Uses.pathN (ιA := ιA) (aux := aux) (ρ := ρ) (K := K) (α := α)
    (oa := oa) (h := h)
end FalconPrecision.Errors.FFSamp
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath
namespace FalconPrecision.Falcon
open MeasureTheory InformationTheory LatticeCrypto FalconPrecision.Errors.FFSamp
open scoped ENNReal
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example (ρ : Arith) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m)
    (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
        (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux CallP) α) (hoa : Uses ρ K oa)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.Falcon.falcon512_model (ιA := ιA) (aux := aux) (m := m) (ρ := ρ) (K := K)
    (hK := hK) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (hoa := hoa) (s := s) (hs := hs) (hwin := hwin)
end FalconPrecision.Falcon
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath
namespace FalconPrecision.Errors.FFSamp
variable {εq : ℝ}
example : inp64 (1 / 2 ^ 65) ≤ 33 / 10 / 2 ^ 32 :=
  _root_.FalconPrecision.Errors.FFSamp.inp64_base

example : inp64 (1 / 2 ^ 78) ≤ 54 / 100 / 2 ^ 32 :=
  _root_.FalconPrecision.Errors.FFSamp.inp64_norm

example (ρ : Arith64 εq) (hεq : 0 ≤ εq) (k : Key) (c : Fin (2 ^ 9) → ℤ)
    (hc : ∀ i, |c i| < 12289) :
    l2 (pairF (t0C64 ρ k c - t0E k c) (t1C64 ρ k c - t1E k c)) ≤ inp64 εq :=
  _root_.FalconPrecision.Errors.FFSamp.input_err64 (εq := εq) (ρ := ρ) (hεq := hεq) (k := k)
    (c := c) (hc := hc)
end FalconPrecision.Errors.FFSamp
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath
namespace FalconPrecision.Errors.FFSamp
variable {εq : ℝ}
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}
example (ρ : Arith64 εq) (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    sign164 (aux := aux) ρ k c = sign164G ρ (chkM R64) k c :=
  _root_.FalconPrecision.Errors.FFSamp.sign164_eq_margin (εq := εq) (ιA := ιA) (aux := aux) (ρ := ρ)
    (hεq := hεq) (e := e) (he := he) (he1 := he1) (k := k) (c := c)

example {ρ : Arith64 εq} (hεq : 0 ≤ εq) (e : ℝ) (he : inp64 εq ≤ e)
    (he1 : 49 * e + 43700 / 2 ^ 40 ≤ 1 / 2 ^ 10) {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α} (h : Uses64 ρ K oa) :
    PathSum wS oa (K * (49 * e + 43700 / 2 ^ 40) ^ 2) :=
  _root_.FalconPrecision.Errors.FFSamp.Uses64.pathS (εq := εq) (ιA := ιA) (aux := aux) (ρ := ρ)
    (hεq := hεq) (e := e) (he := he) (he1 := he1) (K := K) (α := α) (oa := oa) (h := h)
end FalconPrecision.Errors.FFSamp
end

section
open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath
namespace FalconPrecision.Falcon
open MeasureTheory InformationTheory LatticeCrypto FalconPrecision.Errors.FFSamp
open scoped ENNReal
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example (ρ : Arith64 (1 / 2 ^ 65)) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
        (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux CallP) α) (hoa : Uses64 ρ K oa)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.Falcon.falcon512_model64 (ιA := ιA) (aux := aux) (m := m) (ρ := ρ) (K := K)
    (hK := hK) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (hoa := hoa) (s := s) (hs := hs) (hwin := hwin)

example (ρ : Arith64 (1 / 2 ^ 78)) (K : ℕ) (hK : K ≤ 2 ^ 39) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux CallP) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
        (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux CallP) α) (hoa : Uses64 ρ K oa)
    {s : Set α} (hs : MeasurableSet s)
        (hwin : T * (2 : ℝ≥0∞) ^ (-(126 : ℝ)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.Falcon.falcon512_model64n (ιA := ιA) (aux := aux) (m := m) (ρ := ρ)
    (K := K) (hK := hK) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (hoa := hoa) (s := s) (hs := hs) (hwin := hwin)
end FalconPrecision.Falcon
end

section
open MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.Falcon
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example (lam : ℕ) (hlam : 3 ≤ lam) (hL : lam ≤ 128) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m)
        (implE implM implF : QueryImpl (FalconGame.spec aux (CallΔ (1 / 2 ^ 43))) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.1.σ q.1.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux (CallΔ (1 / 2 ^ 43))) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa ((2 ^ 75 : ℕ) : ℝ))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.Falcon.falcon512 (ιA := ιA) (aux := aux) (m := m) (lam := lam)
    (hlam := hlam) (hL := hL) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (hN := hN) (s := s) (hs := hs) (hwin := hwin)

example (lam : ℕ) (hlam : 3 ≤ lam) (hL : lam ≤ 256) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m)
        (implE implM implF : QueryImpl (FalconGame.spec aux (CallΔ (1 / 2 ^ 44))) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.1.σ q.1.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.1.σbar q.1.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux (CallΔ (1 / 2 ^ 44))) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa ((2 ^ 76 : ℕ) : ℝ))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.Falcon.falcon1024 (ιA := ιA) (aux := aux) (m := m) (lam := lam)
    (hlam := hlam) (hL := hL) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (hN := hN) (s := s) (hs := hs) (hwin := hwin)

example (lam : ℕ) (hlam : 3 ≤ lam) (hL : lam ≤ 128) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implA : QueryImpl aux m) (implE implM implF : QueryImpl (FalconGame.spec aux Call) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implE (.inr q)) =
      discreteGaussianMeasure q.σ q.t)
    (hM : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implM (.inr q)) =
      discreteGaussianMeasure q.σbar q.t)
    (hF : ∀ q, @evalDist m _ ((FalconGame.spec aux _).Range (.inr q)) ⊤ (implF (.inr q)) =
      discreteGaussianMeasure q.σbar q.tbar)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (FalconGame.spec aux Call) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa (2 ^ 71))
    (hS₂ : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun q : Call => (q.tbar - q.t) ^ 2) oa
        (1 / 2 ^ 9))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.Falcon.falcon512_rmse (ιA := ιA) (aux := aux) (m := m) (lam := lam)
    (hlam := hlam) (hL := hL) (T := T) (hT := hT) (implA := implA) (implE := implE) (implM := implM)
    (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM) (hF := hF)
    (α := α) (oa := oa) (hN := hN) (hS₂ := hS₂) (s := s) (hs := hs) (hwin := hwin)
end FalconPrecision.Falcon
end

section
open Real MeasureTheory InformationTheory LatticeCrypto FalconPrecision.ThetaTail
open scoped ENNReal
namespace FalconPrecision.Lemma4
example (σ c δ a : ℝ) (hσ : 0 < σ) (ha : 1 < a) (hT : tail σ < 1) :
    renyiDiv a (discreteGaussianMeasure σ (c + δ)) (discreteGaussianMeasure σ c) ≤
      ENNReal.ofReal
          (Real.exp (a * δ ^ 2 / (2 * σ ^ 2) + a * (a + 1) * δ ^ 2 * M σ / (2 * (a - 1)))) :=
  _root_.FalconPrecision.Lemma4.renyiDiv_shift_le (σ := σ) (c := c) (δ := δ) (a := a) (hσ := hσ)
    (ha := ha) (hT := hT)
end FalconPrecision.Lemma4
end

section
open Real FalconPrecision.ThetaTail FalconPrecision.ThetaT
namespace FalconPrecision.Lemma5
example (σ₁ σ₂ c a K : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (ha : 1 < a)
    (hseg : ∀ τ ∈ Set.uIcc (1 / σ₁ ^ 2) (1 / σ₁ ^ 2 + a * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2)),
      0 < τ ∧ tail (√τ⁻¹) < 1 ∧ |ψ₂ c τ| ≤ K) :
    InformationTheory.renyiDiv a (LatticeCrypto.discreteGaussianMeasure σ₂ c)
        (LatticeCrypto.discreteGaussianMeasure σ₁ c) ≤
      ENNReal.ofReal
          (Real.exp (a * (a + 1) * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ^ 2 * K / (2 * (a - 1)))) :=
  _root_.FalconPrecision.Lemma5.renyiDiv_scale_le (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (a := a) (K := K)
    (hσ₁ := hσ₁) (hσ₂ := hσ₂) (ha := ha) (hseg := hseg)
end FalconPrecision.Lemma5
end

section
open Real FalconPrecision.ThetaTail FalconPrecision.ThetaT FalconPrecision.NumTail
    FalconPrecision.Lemma5
namespace FalconPrecision.NumK
example (σ₁ σ₂ c a τlo : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (ha : 1 < a)
    (hlo : 1 / 4 ≤ τlo)
    (h₁ : τlo ≤ 1 / σ₁ ^ 2 ∧ 1 / σ₁ ^ 2 ≤ (1000 / 1277) ^ 2)
    (h' : τlo ≤ 1 / σ₁ ^ 2 + a * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ∧
      1 / σ₁ ^ 2 + a * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ≤ (1000 / 1277) ^ 2) :
    InformationTheory.renyiDiv a (LatticeCrypto.discreteGaussianMeasure σ₂ c)
        (LatticeCrypto.discreteGaussianMeasure σ₁ c) ≤
      ENNReal.ofReal (Real.exp (a * (a + 1) * (1 / σ₂ ^ 2 - 1 / σ₁ ^ 2) ^ 2 *
        ((1 / 2 + 1 / 2 ^ 19) / τlo ^ 2) / (2 * (a - 1)))) :=
  _root_.FalconPrecision.NumK.renyiDiv_scale_le_falcon (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (a := a)
    (τlo := τlo) (hσ₁ := hσ₁) (hσ₂ := hσ₂) (ha := ha) (hlo := hlo) (h₁ := h₁) (h' := h')
end FalconPrecision.NumK
end

section
open Real FalconPrecision.ThetaTail
namespace FalconPrecision.NumTail
example (σ : ℝ) (hσ : 1277 / 1000 ≤ σ) : tail σ < 1 ∧ M σ ≤ 1 / 2 ^ 30 :=
  _root_.FalconPrecision.NumTail.falcon_tail (σ := σ) (hσ := hσ)
end FalconPrecision.NumTail
end

section
open MeasureTheory ProbabilityTheory InformationTheory OracleSpec OracleComp
open scoped ENNReal
namespace FalconPrecision.RenyiHybrid
section
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [∀ t, Countable (spec.Range t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example {a : ℝ} (ha : 1 < a) (implQ implP : QueryImpl spec m) {B : ℝ≥0∞}
    (hB1 : 1 ≤ B)
    (hB : ∀ t, @renyiMGF _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ B)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] {n : ℕ}
    (oa : OracleComp spec α) (hn : IsTotalQueryBound oa n) :
    renyiMGF a 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] ≤ B ^ n :=
  _root_.FalconPrecision.RenyiHybrid.renyiMGF_simulateQ_le (ι := ι) (spec := spec) (m := m) (a := a)
    (ha := ha) (implQ := implQ) (implP := implP) (B := B) (hB1 := hB1) (hB := hB) (α := α) (n := n)
    (oa := oa) (hn := hn)
end
end FalconPrecision.RenyiHybrid
end

section
open MeasureTheory ProbabilityTheory InformationTheory OracleSpec OracleComp
open scoped ENNReal
namespace FalconPrecision.RenyiPath
variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
variable [∀ t, Countable (spec.Range t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example {a : ℝ} (ha : 1 < a) (implQ implP : QueryImpl spec m) {c : ℝ}
    (hc : 0 ≤ c)
    (w : ι → ℝ) (hB : ∀ t, @renyiMGF _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (Real.exp (c * w t)))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {oa : OracleComp spec α} {S : ℝ} (h : PathSum w oa S) :
    renyiMGF a 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] ≤ ENNReal.ofReal (Real.exp (c * S)) :=
  _root_.FalconPrecision.RenyiPath.renyiMGF_simulateQ_le_path (ι := ι) (spec := spec) (m := m)
    (a := a) (ha := ha) (implQ := implQ) (implP := implP) (c := c) (hc := hc) (w := w) (hB := hB)
    (α := α) (oa := oa) (S := S) (h := h)

example {α : Type} [MeasurableSpace α] (lam : ℕ) (hlam : 2 ≤ lam) (N : ℕ) (T : ℝ≥0∞)
    (hT : 1 ≤ T)
    (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : renyiMGF (2 * lam - 1) μ ν ≤
        (ENNReal.ofReal (1 + 1 / (4 * N)) ^ N) ^ ((2 * lam - 1 : ℝ) - 1))
    {s : Set α} (hs : MeasurableSet s) (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) < μ s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < ν s :=
  _root_.FalconPrecision.RenyiPath.lemma15 (α := α) (lam := lam) (hlam := hlam) (N := N) (T := T)
    (hT := hT) (μ := μ) (ν := ν) (h := h) (s := s) (hs := hs) (hwin := hwin)

example (lam : ℕ) (hlam : 2 ≤ lam) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (implQ implP : QueryImpl spec m) (n : ℕ)
    (hR : ∀ t, @renyiDiv _ ⊤ (2 * lam - 1 : ℝ) (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (1 + 1 / (4 * n)))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp spec α) (hn : IsTotalQueryBound oa n) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) < 𝒟[simulateQ implQ oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implP oa] s :=
  _root_.FalconPrecision.RenyiPath.lemma14 (ι := ι) (spec := spec) (m := m) (lam := lam)
    (hlam := hlam) (T := T) (hT := hT) (implQ := implQ) (implP := implP) (n := n) (hR := hR)
    (α := α) (oa := oa) (hn := hn) (s := s) (hs := hs) (hwin := hwin)
end FalconPrecision.RenyiPath
end

section
open Real MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.RenyiScale
example (σ₁ σ₂ σ' c a : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hσ' : 0 < σ')
    (ha : 0 ≤ a) (h : 1 / σ' ^ 2 = a / σ₂ ^ 2 + (1 - a) / σ₁ ^ 2) :
    renyiMGF a (discreteGaussianMeasure σ₂ c) (discreteGaussianMeasure σ₁ c) =
      ENNReal.ofReal (discreteGaussianSum σ' c /
        (discreteGaussianSum σ₂ c ^ a * discreteGaussianSum σ₁ c ^ (1 - a))) :=
  _root_.FalconPrecision.RenyiScale.renyiMGF_discreteGaussian_scale (σ₁ := σ₁) (σ₂ := σ₂) (σ' := σ')
    (c := c) (a := a) (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ' := hσ') (ha := ha) (h := h)
end FalconPrecision.RenyiScale
end

section
open Real MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.RenyiShift
example (σ c δ a : ℝ) (hσ : 0 < σ) (ha : 0 ≤ a) :
    renyiMGF a (discreteGaussianMeasure σ (c + δ)) (discreteGaussianMeasure σ c) =
      ENNReal.ofReal
          (Real.exp (a * (a - 1) * δ ^ 2 / (2 * σ ^ 2)) * discreteGaussianSum σ (c + a * δ) /
        (discreteGaussianSum σ (c + δ) ^ a * discreteGaussianSum σ c ^ (1 - a))) :=
  _root_.FalconPrecision.RenyiShift.renyiMGF_discreteGaussian_shift (σ := σ) (c := c) (δ := δ)
    (a := a) (hσ := hσ) (ha := ha)
end FalconPrecision.RenyiShift
end

section
open MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.FalconGame
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [hA : ∀ t, Countable (aux t)] {Q : Type}
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
example (lam N : ℕ) (hlam : 3 ≤ lam) (T : ℝ≥0∞) (hT : 1 ≤ T) (σ σbar t tbar : Q → ℝ)
    (τlo σlo S₁ S₂ : ℝ) (implA : QueryImpl aux m) (implE implM implF : QueryImpl (spec aux Q) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implE (.inr q)) =
        discreteGaussianMeasure (σ q) (t q))
    (hM : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implM (.inr q)) =
        discreteGaussianMeasure (σbar q) (t q))
    (hF : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implF (.inr q)) =
        discreteGaussianMeasure (σbar q) (tbar q))
    (hσ : ∀ q, 0 < σ q) (hτlo : 1 / 4 ≤ τlo)
    (hleaf : ∀ q, τlo ≤ 1 / σ q ^ 2 ∧ 1 / σ q ^ 2 ≤ (1000 / 1277) ^ 2 ∧
      τlo ≤ 1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ∧
      1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ≤ (1000 / 1277) ^ 2)
    (hσlo : 1277 / 1000 ≤ σlo) (hσbar : ∀ q, σlo ≤ σbar q)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (spec aux Q) α)
    (hS₁ : RenyiPath.PathSum
        (Sum.elim (fun _ => 0) fun q => (1 / σbar q ^ 2 - 1 / σ q ^ 2) ^ 2) oa S₁)
    (hS₂ : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun q => (tbar q - t q) ^ 2) oa S₂)
    (h35 : Real.exp
        ((2 * lam - 1) * (2 * lam) * S₁ * ((1 / 2 + 1 / 2 ^ 19) / τlo ^ 2) / (2 * (2 * lam - 2))) ≤
      (1 + 1 / (4 * N)) ^ N)
    (h36 : Real.exp ((2 * lam - 3) * S₂ / (2 * σlo ^ 2) +
      (2 * lam - 3) * (2 * lam - 2) * S₂ * (1 / 2 ^ 30) / (2 * (2 * lam - 4))) ≤
          (1 + 1 / (4 * N)) ^ N)
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.FalconGame.theorem2 (ιA := ιA) (aux := aux) (Q := Q) (m := m) (lam := lam)
    (N := N) (hlam := hlam) (T := T) (hT := hT) (σ := σ) (σbar := σbar) (t := t) (tbar := tbar)
    (τlo := τlo) (σlo := σlo) (S₁ := S₁) (S₂ := S₂) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (hσ := hσ) (hτlo := hτlo) (hleaf := hleaf) (hσlo := hσlo) (hσbar := hσbar) (α := α)
    (oa := oa) (hS₁ := hS₁) (hS₂ := hS₂) (h35 := h35) (h36 := h36) (s := s) (hs := hs)
    (hwin := hwin)

example (lam N : ℕ) (hlam : 3 ≤ lam) (T : ℝ≥0∞) (hT : 1 ≤ T) (σ σbar t tbar : Q → ℝ)
    (τlo σlo Δτ Δt : ℝ) (implA : QueryImpl aux m) (implE implM implF : QueryImpl (spec aux Q) m)
    (hAE : ∀ x, implE (.inl x) = implA x) (hAM : ∀ x, implM (.inl x) = implA x)
    (hAF : ∀ x, implF (.inl x) = implA x)
    (hE : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implE (.inr q)) =
        discreteGaussianMeasure (σ q) (t q))
    (hM : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implM (.inr q)) =
        discreteGaussianMeasure (σbar q) (t q))
    (hF : ∀ q, @evalDist m _ ((spec aux Q).Range (.inr q)) ⊤ (implF (.inr q)) =
        discreteGaussianMeasure (σbar q) (tbar q))
    (hσ : ∀ q, 0 < σ q) (hτlo : 1 / 4 ≤ τlo)
    (hleaf : ∀ q, τlo ≤ 1 / σ q ^ 2 ∧ 1 / σ q ^ 2 ≤ (1000 / 1277) ^ 2 ∧
      τlo ≤ 1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ∧
      1 / σ q ^ 2 + (2 * lam - 1) * (1 / σbar q ^ 2 - 1 / σ q ^ 2) ≤ (1000 / 1277) ^ 2)
    (hσlo : 1277 / 1000 ≤ σlo) (hσbar : ∀ q, σlo ≤ σbar q)
    (hΔτ : ∀ q, |1 / σbar q ^ 2 - 1 / σ q ^ 2| ≤ Δτ) (hΔt : ∀ q, |tbar q - t q| ≤ Δt)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (spec aux Q) α)
    (hN : RenyiPath.PathSum (Sum.elim (fun _ => 0) fun _ => 1) oa N)
    (h26 : Real.exp ((2 * lam - 1) * (2 * lam) * Δτ ^ 2 * ((1 / 2 + 1 / 2 ^ 19) / τlo ^ 2) /
      (2 * (2 * lam - 2))) ≤ 1 + 1 / (4 * N))
    (h27 : Real.exp ((2 * lam - 3) * Δt ^ 2 / (2 * σlo ^ 2) +
      (2 * lam - 3) * (2 * lam - 2) * Δt ^ 2 * (1 / 2 ^ 30) / (2 * (2 * lam - 4))) ≤ 1 + 1 /
          (4 * N))
    {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 2)) < 𝒟[simulateQ implF oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) < 𝒟[simulateQ implE oa] s :=
  _root_.FalconPrecision.FalconGame.theorem1 (ιA := ιA) (aux := aux) (Q := Q) (m := m) (lam := lam)
    (N := N) (hlam := hlam) (T := T) (hT := hT) (σ := σ) (σbar := σbar) (t := t) (tbar := tbar)
    (τlo := τlo) (σlo := σlo) (Δτ := Δτ) (Δt := Δt) (implA := implA) (implE := implE)
    (implM := implM) (implF := implF) (hAE := hAE) (hAM := hAM) (hAF := hAF) (hE := hE) (hM := hM)
    (hF := hF) (hσ := hσ) (hτlo := hτlo) (hleaf := hleaf) (hσlo := hσlo) (hσbar := hσbar)
    (hΔτ := hΔτ) (hΔt := hΔt) (α := α) (oa := oa) (hN := hN) (h26 := h26) (h27 := h27) (s := s)
    (hs := hs) (hwin := hwin)
end FalconPrecision.FalconGame
end

section
open Real Complex LatticeCrypto
namespace FalconPrecision.ThetaTail
example (σ u : ℝ) (hσ : 0 < σ) :
    discreteGaussianSum σ u =
      σ * √(2 * π) * ∑' n : ℤ, Real.exp (-(2 * π ^ 2 * σ ^ 2) * n ^ 2) *
          Real.cos (2 * π * n * u) :=
  _root_.FalconPrecision.ThetaTail.discreteGaussianSum_eq_fourier (σ := σ) (u := u) (hσ := hσ)

example (σ u : ℝ) (hσ : 0 < σ) :
    σ * √(2 * π) * (1 - tail σ) ≤ discreteGaussianSum σ u ∧
      discreteGaussianSum σ u ≤ σ * √(2 * π) * (1 + tail σ) :=
  _root_.FalconPrecision.ThetaTail.discreteGaussianSum_mem (σ := σ) (u := u) (hσ := hσ)
end FalconPrecision.ThetaTail
end

section
open MeasureTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal
namespace FalconPrecision.FalconWitness
variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [OracleSpec.AnswerMeasure aux] {Q : Type}
example (σ σbar t tbar : Q → ℝ) (hσ : ∀ q, 0 < σ q) (hσbar : ∀ q, 0 < σbar q) :
    ∃ (implA' : QueryImpl aux (OracleComp (wspec aux)))
      (implE implM implF : QueryImpl (FalconGame.spec aux Q) (OracleComp (wspec aux))),
      (∀ x, implE (.inl x) = implA' x) ∧ (∀ x, implM (.inl x) = implA' x) ∧
          (∀ x, implF (.inl x) = implA' x) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux Q).Range (.inr q)) ⊤ (implE (.inr q)) =
        discreteGaussianMeasure (σ q) (t q)) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux Q).Range (.inr q)) ⊤ (implM (.inr q)) =
        discreteGaussianMeasure (σbar q) (t q)) ∧
      (∀ q, @evalDist _ _ ((FalconGame.spec aux Q).Range (.inr q)) ⊤ (implF (.inr q)) =
        discreteGaussianMeasure (σbar q) (tbar q)) :=
  _root_.FalconPrecision.FalconWitness.worlds_exist (ιA := ιA) (aux := aux) (Q := Q) (σ := σ)
    (σbar := σbar) (t := t) (tbar := tbar) (hσ := hσ) (hσbar := hσbar)
end FalconPrecision.FalconWitness
end
