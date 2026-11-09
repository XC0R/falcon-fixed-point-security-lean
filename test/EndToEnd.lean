import FalconPrecision

/-!
End-to-end non-vacuity: `Falcon.falcon512` applied to a concrete experiment over uniform auxiliary
coins (`unifSpec`) that makes one SamplerZ call and outputs whether the sample is `0`, with the
three worlds realised by perfect discrete Gaussian oracles (`FalconWitness.world`). Every hypothesis
except the premise on the fixed-point success probability is discharged. -/

open MeasureTheory OracleSpec OracleComp LatticeCrypto FalconPrecision
open scoped ENNReal

/-- A SamplerZ call at leaf `σ = σ̄ = 1.5`, center `t = t̄ = 0`. -/
noncomputable def call₀ : Falcon.CallΔ (1 / 2 ^ 43) :=
  ⟨⟨3 / 2, 3 / 2, 0, 0, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩

/-- One SamplerZ call; win iff the sample is `0`. -/
noncomputable def game₀ : OracleComp (FalconGame.spec unifSpec (Falcon.CallΔ (1 / 2 ^ 43))) Bool :=
  liftM (OracleSpec.query (spec := FalconGame.spec unifSpec (Falcon.CallΔ (1 / 2 ^ 43)))
      (.inr call₀)) >>=
    fun z => pure (decide ((show ℤ from z) = 0))

theorem σ_pos (q : Falcon.CallΔ (1 / 2 ^ 43)) : 0 < q.1.σ := by linarith [q.1.hσ.1]
theorem σbar_pos (q : Falcon.CallΔ (1 / 2 ^ 43)) : 0 < q.1.σbar := by linarith [q.1.hσbar_ge]

/-- Exact, intermediate and fixed-point worlds. -/
noncomputable abbrev worldE :=
    FalconWitness.world (aux := unifSpec) (Q := Falcon.CallΔ (1 / 2 ^ 43)) (fun q => q.1.σ)
        (fun q => q.1.t) σ_pos
noncomputable abbrev worldM :=
  FalconWitness.world (aux := unifSpec) (Q := Falcon.CallΔ (1 / 2 ^ 43)) (fun q => q.1.σbar)
      (fun q => q.1.t) σbar_pos
noncomputable abbrev worldF :=
  FalconWitness.world (aux := unifSpec) (Q := Falcon.CallΔ (1 / 2 ^ 43)) (fun q => q.1.σbar)
      (fun q => q.1.tbar) σbar_pos

example (T : ℝ≥0∞) (hT : 1 ≤ T)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) - 2 : ℝ)) < 𝒟[simulateQ worldF game₀] {true}) :
    T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) : ℝ)) < 𝒟[simulateQ worldE game₀] {true} :=
  Falcon.falcon512 128 (by norm_num) le_rfl T hT FalconWitness.implA worldE worldM worldF
    (FalconWitness.world_inl _ _ _) (FalconWitness.world_inl _ _ _) (FalconWitness.world_inl _ _ _)
    (FalconWitness.evalDist_world _ _ _) (FalconWitness.evalDist_world _ _ _)
    (FalconWitness.evalDist_world _ _ _) game₀
    (.query_bind _ _ fun _ => .pure _ (by norm_num)) (measurableSet_singleton _) hwin
