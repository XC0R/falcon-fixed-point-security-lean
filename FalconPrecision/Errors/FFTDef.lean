/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFTLayer
public import Mathlib.Algebra.BigOperators.Fin

/-! # The split identity behind Falcon's FFT

Falcon evaluates `f ∈ ℂ[x]/(xⁿ + 1)` at the roots of `xⁿ + 1` by splitting `f(x) = f₀(x²) +
x·f₁(x²)`: the roots come in pairs `±ζ` whose squares are the roots of `x^{n/2} + 1`, so `f(±ζ) =
f₀(ζ²) ± ζ·f₁(ζ²)`, which is the merge layer of `FFTLayer`. -/

@[expose] public section

namespace FalconPrecision.Errors.FFTDef

open Finset

/-- Evaluate a coefficient vector at `z`. -/
noncomputable def evalAt {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ := ∑ i : Fin n, a i * z ^ (i : ℕ)

/-- Even-index coefficients. -/
def evens {m : ℕ} (a : Fin (2 * m) → ℂ) : Fin m → ℂ := fun i => a ⟨2 * i, by omega⟩

/-- Odd-index coefficients. -/
def odds {m : ℕ} (a : Fin (2 * m) → ℂ) : Fin m → ℂ := fun i => a ⟨2 * i + 1, by omega⟩

theorem sum_range_two_mul (g : ℕ → ℂ) (m : ℕ) :
    ∑ i ∈ range (2 * m), g i = ∑ i ∈ range m, (g (2 * i) + g (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ,
        ih]
    ring

/-- **Split identity.** `f(z) = f₀(z²) + z·f₁(z²)`. -/
theorem evalAt_split {m : ℕ} (a : Fin (2 * m) → ℂ) (z : ℂ) :
    evalAt a z = evalAt (evens a) (z ^ 2) + z * evalAt (odds a) (z ^ 2) := by
  set g : ℕ → ℂ := fun i => if h : i < 2 * m then a ⟨i, h⟩ * z ^ i else 0 with hg
  have hL : evalAt a z = ∑ i ∈ range (2 * m), g i := by
    rw [evalAt, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hg, i.2]
  have h0 : evalAt (evens a) (z ^ 2) = ∑ i ∈ range m, g (2 * i) := by
    rw [evalAt, ← Fin.sum_univ_eq_sum_range (fun i => g (2 * i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : 2 * (i : ℕ) < 2 * m := by omega
    simp only [hg, hi, ↓reduceDIte, evens, ← pow_mul]
  have h1 : z * evalAt (odds a) (z ^ 2) = ∑ i ∈ range m, g (2 * i + 1) := by
    rw [evalAt, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => g (2 * i + 1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : 2 * (i : ℕ) + 1 < 2 * m := by omega
    simp only [hg, hi, ↓reduceDIte, odds, pow_succ]
    ring
  rw [hL, sum_range_two_mul, Finset.sum_add_distrib, h0, h1]

/--
**The merge layer computes the transform.** With the half-size transforms evaluated at the squares
of the twiddles, `FFTLayer.merge` outputs `(f(ζ_j), f(-ζ_j))`. -/
theorem merge_eval {m k : ℕ} (a : Fin (2 * m) → ℂ) (ζ : Fin k → ℂ) :
    FFTLayer.merge ζ (fun j => evalAt (evens a) (ζ j ^ 2)) (fun j => evalAt (odds a) (ζ j ^ 2)) =
      fun j => (evalAt a (ζ j), evalAt a (-ζ j)) := by
  funext j
  simp only [FFTLayer.merge, evalAt_split a (ζ j), evalAt_split a (-ζ j), neg_sq]
  ring_nf

end FalconPrecision.Errors.FFTDef
