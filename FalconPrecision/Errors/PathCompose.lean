/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.RenyiPath

/-! # Composing path sums (TASK-009 S7f)

`PathSum.bind`: path budgets add along `>>=`. `BlockPath K c oa`: `oa` runs at most `K` blocks in
sequence, each with path sum at most `c`, with no other weighted queries between them; then `oa` has
path sum at most `K·c` (`BlockPath.pathSum`). This is additivity of budgets only. `PathSumP` is a
`PathSum` with a postcondition on the results; `PathSumP.bind` adds budgets along `>>=` using the
postcondition. `FFSampModel` and `SignModel` derive `hS₂` of Theorem 2 for an `OracleComp` model of
fixed-point signing with them (`ffs_pathS`, `Uses.pathS`). -/

@[expose] public section

open OracleSpec OracleComp

namespace FalconPrecision.RenyiPath

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- **Path budgets add along `>>=`.** -/
theorem PathSum.bind {w : ι → ℝ} {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {S T : ℝ} (h : PathSum w oa S) (hb : ∀ x, PathSum w (ob x) T) : PathSum w (oa >>= ob)
        (S + T) := by
  induction h with
  | pure x hS =>
    rw [pure_bind]
    exact (hb x).weaken (by linarith)
  | @query_bind t k S _ ih =>
    rw [bind_assoc]
    exact .query_bind t _ fun u => by
      have := ih u
      rwa [show S - w t + T = S + T - w t by ring] at this

/-- `PathSum` with the postcondition `P` on every result. -/
inductive PathSumP (w : ι → ℝ) {α : Type} (P : α → Prop) : OracleComp spec α → ℝ → Prop
  | pure (x : α) {S : ℝ} (h : 0 ≤ S) (hx : P x) : PathSumP w P (pure x) S
  | query_bind (t : ι) (k : spec.Range t → OracleComp spec α) {S : ℝ}
      (h : ∀ u, PathSumP w P (k u) (S - w t)) : PathSumP w P (liftM (OracleSpec.query t) >>= k) S

theorem PathSumP.weaken {w : ι → ℝ} {α : Type} {P : α → Prop} {oa : OracleComp spec α} {S S' : ℝ}
    (h : PathSumP w P oa S) (hS : S ≤ S') : PathSumP w P oa S' := by
  induction h generalizing S' with
  | pure x h0 hx => exact .pure x (h0.trans hS) hx
  | query_bind t k _ ih => exact .query_bind t k fun u => ih u (by linarith)

theorem PathSumP.toPathSum {w : ι → ℝ} {α : Type} {P : α → Prop} {oa : OracleComp spec α} {S : ℝ}
    (h : PathSumP w P oa S) : PathSum w oa S := by
  induction h with
  | pure x h0 _ => exact .pure x h0
  | query_bind t k _ ih => exact .query_bind t k ih

/-- **Path budgets add along `>>=`**, the continuation used only on results satisfying `P`. -/
theorem PathSumP.bind {w : ι → ℝ} {α β : Type} {P : α → Prop} {Q : β → Prop}
    {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {S T : ℝ} (h : PathSumP w P oa S)
        (hb : ∀ x, P x → PathSumP w Q (ob x) T) :
    PathSumP w Q (oa >>= ob) (S + T) := by
  induction h with
  | pure x hS hx =>
    rw [pure_bind]
    exact (hb x hx).weaken (by linarith)
  | @query_bind t k S _ ih =>
    rw [bind_assoc]
    exact .query_bind t _ fun u => by
      have := ih u
      rwa [show S - w t + T = S + T - w t by ring] at this

/-- `oa` runs at most `K` blocks in sequence, each with path sum at most `c`. -/
inductive BlockPath (w : ι → ℝ) (c : ℝ) : ℕ → {α : Type} → OracleComp spec α → Prop
  | pure {α : Type} (K : ℕ) (x : α) : BlockPath w c K (pure x)
  | block {α β : Type} (K : ℕ) (b : OracleComp spec β) (k : β → OracleComp spec α)
      (hb : PathSum w b c) (hk : ∀ y, BlockPath w c K (k y)) : BlockPath w c (K + 1) (b >>= k)

/-- **At most `K` blocks of budget `c` give path sum `K·c`.** -/
theorem BlockPath.pathSum {w : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) {K : ℕ} {α : Type}
    {oa : OracleComp spec α}
    (h : BlockPath w c K oa) : PathSum w oa (K * c) := by
  induction h with
  | pure K x => exact .pure x (by positivity)
  | block K b k hb _ ih =>
    have := hb.bind ih
    rwa [show c + K * c = ((K + 1 : ℕ) : ℝ) * c by push_cast; ring] at this

end FalconPrecision.RenyiPath
