/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.LDLLeaf
public import FalconPrecision.Errors.FFTCert

/-! # Root relative error of ffLDL⋆ at Falcon-512

`f̂, ĝ` by the certified FFT at tag 8 (`‖f̂‖∞ ≤ γf,g = 255`, footnote 9, for keys passing the keygen
check of Alg. 2 l. 7, §8.3; `δ ≤ 0.7072·2⁻⁶³` assumes the size-2 merge multiplies by `±i` exactly,
which tag 0 cannot represent; `r ≤ √2·2⁻⁵⁵`): `E₉ = (δ·255 + r)·Σ_{j<9}(2 + δ)^j ≤ 277300·2⁻⁶³`
(`cert_closed`). Then `Ĝ00 = |f̂|² + |ĝ|² ≥ q/16` (Lemma 8) computed within `2⁻⁴⁴` has relative
error `≤ 2⁻⁴⁶` (`gram_err`). Each theorem takes its input errors as hypotheses; they are not
composed into `hroot` of `falcon512_leaf`. -/

@[expose] public section

namespace FalconPrecision.Errors.LDL

theorem fft512_err (δ r : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 7072 / 10000 / 2 ^ 63)
    (hr : r ≤ 141422 / 100000 / 2 ^ 55) :
    (δ * 255 + r) * ∑ j ∈ Finset.range 9, (2 + δ) ^ j ≤ 277300 / 2 ^ 63 := by
  have hδ' : δ ≤ 1 / 2 ^ 63 := hδ.trans (by norm_num)
  have hs : ∑ j ∈ Finset.range 9, (2 + δ) ^ j ≤ ∑ j ∈ Finset.range 9, (2 + 1 / 2 ^ 63 : ℝ) ^ j :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (by positivity) (by linarith) j
  have hs' : ∑ j ∈ Finset.range 9, (2 + 1 / 2 ^ 63 : ℝ) ^ j ≤ 5111 / 10 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hc : δ * 255 + r ≤ 7072 / 10000 / 2 ^ 63 * 255 + 141422 / 100000 / 2 ^ 55 := by nlinarith
  calc _ ≤ (7072 / 10000 / 2 ^ 63 * 255 + 141422 / 100000 / 2 ^ 55) * (5111 / 10) :=
        mul_le_mul hc (hs.trans hs') (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ ≤ 277300 / 2 ^ 63 := by norm_num

/-- **Root Gram value.** -/
theorem root512 (G Gh E e : ℝ) (hG : 12289 / 16 ≤ G) (hE0 : 0 ≤ E) (hE : E ≤ 277300 / 2 ^ 63)
    (he : e ≤ 1 / 2 ^ 44)
        (h : |Gh - G| ≤ 2 * E * √(2 * G) + 2 * E ^ 2 + e) : RelClose (1 / 2 ^ 46) G Gh := by
  unfold RelClose
  have hG0 : 0 < G := by linarith
  have h1 : 2 * E * √(2 * G) ≤ 1 / 2 ^ 47 * G := by
    have hl : 0 ≤ 2 * E * √(2 * G) := by positivity
    rw [← Real.sqrt_sq hl, ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / 2 ^ 47 * G)]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hE2 : E ^ 2 ≤ (277300 / 2 ^ 63) ^ 2 := pow_le_pow_left₀ hE0 hE 2
    have : (2 : ℝ) ^ 2 * (277300 / 2 ^ 63) ^ 2 * 2 ≤ (1 / 2 ^ 47) ^ 2 * (12289 / 16) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left hE2 (by positivity : (0:ℝ) ≤ 2 ^ 2 * (2 * G)),
      mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ (1 / 2 ^ 47) ^ 2 * G)]
  have h2 : 2 * E ^ 2 + e ≤ 1 / 2 ^ 47 * G := by
    have hE2 : E ^ 2 ≤ (277300 / 2 ^ 63) ^ 2 := pow_le_pow_left₀ hE0 hE 2
    have : 2 * (277300 / 2 ^ 63 : ℝ) ^ 2 + 1 / 2 ^ 44 ≤ 1 / 2 ^ 47 * (12289 / 16) := by norm_num
    nlinarith
  have : (1 / 2 ^ 47 : ℝ) * G + 1 / 2 ^ 47 * G = 1 / 2 ^ 46 * G := by ring
  linarith

/-- **Root `D̂11 = q²/Ĝ00`** (symplectic, §7.3 item 3a): with `Ĝ00` relative `2⁻⁴⁶` and the computed
`q·(q·inv Ĝ00)` within relative `2⁻⁵²` of `q²/Ĝ00`, `D̂11` has relative error `≤ 2⁻⁴⁵`. -/
theorem root11_512 (G Gh D Dh : ℝ) (hG : 0 < G) (hD : D = 12289 ^ 2 / G)
    (h : RelClose (1 / 2 ^ 46) G Gh)
    (hDh : |Dh - 12289 ^ 2 / Gh| ≤ 1 / 2 ^ 52 * (12289 ^ 2 / Gh)) : RelClose (1 / 2 ^ 45) D Dh := by
  have hi := inv_rel (1 / 2 ^ 46) G Gh hG (by norm_num) h
  unfold RelClose at *
  rw [abs_le] at hi hDh ⊢
  have hq : (0 : ℝ) < 12289 ^ 2 := by norm_num
  have e1 : 12289 ^ 2 / Gh = 12289 ^ 2 * (1 / Gh) := by ring
  have e2 : D = 12289 ^ 2 * (1 / G) := by rw [hD]; ring
  rw [e1] at hDh; rw [e2]
  have hG' : 0 < 1 / G := by positivity
  set x := 1 / G; set y := 1 / Gh
  have hy1 : y ≤ x * (1 + 1 / 2 ^ 46 / (1 - 1 / 2 ^ 46)) := by nlinarith [hi.2]
  have hy0 : x * (1 - 1 / 2 ^ 46 / (1 - 1 / 2 ^ 46)) ≤ y := by nlinarith [hi.1]
  have c1 : (1 / 2 ^ 46 / (1 - 1 / 2 ^ 46) : ℝ) + 1 / 2 ^ 52 *
      (1 + 1 / 2 ^ 46 / (1 - 1 / 2 ^ 46)) ≤ 1 / 2 ^ 45 := by
    norm_num
  constructor <;> nlinarith
      [mul_le_mul_of_nonneg_left hy1 hq.le, mul_le_mul_of_nonneg_left hy0 hq.le]

end FalconPrecision.Errors.LDL
