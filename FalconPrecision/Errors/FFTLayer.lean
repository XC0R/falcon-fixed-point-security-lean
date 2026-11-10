/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.Butterfly
public import Mathlib.Analysis.Normed.Group.Constructions

/-! # One merge layer of Falcon's FFT in fixed point (TASK-009 S7c)

A layer merges two half-size transforms `u, v` with twiddles `ζ`: `w_j = (u_j + ζ_j v_j, u_j - ζ_j
v_j)`. In the sup norm (`Fin k → ℂ × ℂ`) the exact layer satisfies `‖w‖ ≤ ‖u‖ + ‖v‖`, and a computed
layer (inputs within `E`, twiddles within `δ`, products rounded within `r`) is within `E(2 + δ) +
δ‖v‖ + r`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFTLayer

variable {k : ℕ}

/-- The exact merge layer. -/
def merge (ζ u v : Fin k → ℂ) : Fin k → ℂ × ℂ := fun j => (u j + ζ j * v j, u j - ζ j * v j)

/-- The computed merge layer, with rounded products `p`. -/
def mergeH (uh p : Fin k → ℂ) : Fin k → ℂ × ℂ := fun j => (uh j + p j, uh j - p j)

theorem norm_merge_le (ζ u v : Fin k → ℂ) (hζ : ∀ j, ‖ζ j‖ = 1) : ‖merge ζ u v‖ ≤ ‖u‖ + ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hu := norm_le_pi_norm u j
  have hv := norm_le_pi_norm v j
  have hm : ‖ζ j * v j‖ ≤ ‖v‖ := by rw [norm_mul, hζ j, one_mul]; exact hv
  refine (norm_prod_le_iff).2 ⟨?_, ?_⟩
  · exact (norm_add_le _ _).trans (by linarith)
  · exact (norm_sub_le _ _).trans (by linarith)

theorem mergeH_err (ζ ζh u uh v vh p : Fin k → ℂ) (E δ r : ℝ) (hζ : ∀ j, ‖ζ j‖ = 1)
    (hδ : ∀ j, ‖ζh j - ζ j‖ ≤ δ) (hu : ‖uh - u‖ ≤ E) (hv : ‖vh - v‖ ≤ E)
        (hp : ∀ j, ‖p j - ζh j * vh j‖ ≤ r)
    (hδ0 : 0 ≤ δ) (hr : 0 ≤ r) :
    ‖mergeH uh p - merge ζ u v‖ ≤ E * (2 + δ) + δ * ‖v‖ + r := by
  have hE : 0 ≤ E := (norm_nonneg _).trans hu
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hb :=
      FalconPrecision.Errors.Butterfly.butterfly_err (u j) (uh j) (ζ j) (ζh j) (v j) (vh j)
          (p j) E δ r (hζ j) (hδ j)
    (by simpa using (norm_le_pi_norm (uh - u) j).trans hu)
        (by simpa using (norm_le_pi_norm (vh - v) j).trans hv)
    (hp j)
  have hvj : δ * ‖v j‖ ≤ δ * ‖v‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) hδ0
  refine (norm_prod_le_iff).2 ⟨?_, ?_⟩
  · simp only [Pi.sub_apply, Prod.fst_sub, mergeH, merge]; linarith [hb.1]
  · simp only [Pi.sub_apply, Prod.snd_sub, mergeH, merge]; linarith [hb.2]

end FalconPrecision.Errors.FFTLayer
