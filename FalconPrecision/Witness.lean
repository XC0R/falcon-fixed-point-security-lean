/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Security

/-! # Non-vacuity of the game hypotheses: perfect samplers exist

For any auxiliary oracle specification with chosen answer measures (e.g. uniform coins), the oracle
specification `Sum.elim aux (σ, c ↦ ℤ)` with `D_{Z,σ,c}` as the answer measure on SamplerZ queries
realises the three worlds of `FalconGame.theorem1`/`theorem2`: auxiliary queries answered
identically, SamplerZ answered by `D_{σ,t}`, `D_{σ̄,t}`, `D_{σ̄,t̄}`. -/

@[expose] public section

open MeasureTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal

namespace FalconPrecision.FalconWitness

/-- Queries to a perfect discrete Gaussian sampler. -/
abbrev GQuery := {p : ℝ × ℝ // 0 < p.1}

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [OracleSpec.AnswerMeasure aux] {Q : Type}

/-- Auxiliary oracles plus a perfect discrete Gaussian sampler. -/
@[reducible] def wspec (aux : OracleSpec.{0, 0} ιA) : OracleSpec (ιA ⊕ GQuery) :=
    Sum.elim aux fun _ => ℤ

noncomputable instance : OracleSpec.AnswerMeasure (wspec aux) :=
  @PFunctor.AnswerMeasure.mk (wspec aux).toPFunctor (fun _ => ⊤)
    (fun | .inl t => OracleSpec.AnswerMeasure.toMeasure (spec := aux) t
         | .inr p => discreteGaussianMeasure p.1.1 p.1.2)
    (fun | .inl t => OracleSpec.AnswerMeasure.isProbabilityMeasure_toMeasure (spec := aux) t
         | .inr p => isProbabilityMeasure_discreteGaussianMeasure p.1.1 p.1.2 p.2)

/-- The shared auxiliary implementation: forward the query. -/
def implA : QueryImpl aux (OracleComp (wspec aux)) :=
  fun t => (liftM (OracleSpec.query (spec := wspec aux) (.inl t)) : OracleComp (wspec aux) (aux t))

/-- A world: auxiliary queries forwarded, SamplerZ at leaf `w q` and center `c q`. -/
def world (w c : Q → ℝ) (hw : ∀ q, 0 < w q) : QueryImpl (FalconGame.spec aux Q)
    (OracleComp (wspec aux))
  | .inl t => implA t
  | .inr q =>
      (liftM (OracleSpec.query (spec := wspec aux) (.inr ⟨(w q, c q), hw q⟩)) : OracleComp
          (wspec aux) ℤ)

omit [OracleSpec.AnswerMeasure aux] in
theorem world_inl (w c : Q → ℝ) (hw : ∀ q, 0 < w q)
    (t : ιA) : world w c hw (.inl t) = implA (aux := aux) t := rfl

theorem evalDist_world (w c : Q → ℝ) (hw : ∀ q, 0 < w q) (q : Q) :
    @evalDist _ _ ((FalconGame.spec aux Q).Range (.inr q)) ⊤ (world w c hw (.inr q)) =
      discreteGaussianMeasure (w q) (c q) :=
  (@evalDist_liftM_query _ (wspec aux) _ (.inr ⟨(w q, c q), hw q⟩) ⊤).trans
      (@MeasureTheory.trim_eq_self _ ⊤ _)

/-- The sampler and auxiliary hypotheses of `FalconGame.theorem1`/`theorem2` are met. -/
theorem worlds_exist (σ σbar t tbar : Q → ℝ) (hσ : ∀ q, 0 < σ q) (hσbar : ∀ q, 0 < σbar q) :
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
  ⟨implA, world σ t hσ, world σbar t hσbar, world σbar tbar hσbar, world_inl _ _ _, world_inl _ _ _,
    world_inl _ _ _, evalDist_world _ _ _, evalDist_world _ _ _, evalDist_world _ _ _⟩

end FalconPrecision.FalconWitness
