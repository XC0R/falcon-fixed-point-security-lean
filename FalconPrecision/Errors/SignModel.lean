/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.FFSampModel
public import FalconPrecision.Errors.FalconInput
public import FalconPrecision.Errors.FalconRoot

/-! # Fixed-point signing as an execution model; Theorem 2 without `hN`, `hS₂` (TASK-009 S7g)

Standard signing (spec Alg. 10 l. 3, 6; ePrint 2026/1531 §7.3 item 4): `t̂ = (-FFT(c/q)⊙F̂,
FFT(c/q)⊙f̂)`. Exact: `FFT` is evaluation at the roots `pt 9`. Fixed point (arithmetic `ρ : Arith`,
`FxModel`): `c/q` at tag 0 (`quot`), retagged to tag 9 (`retag`; `pre`), `FFT(c/q)` at tag 9 (the
non-certified rule of §7.3 item 1, `m(c/q) + log₂ n`), `F̂` at tag 12, `f̂` at tag 8 (`Arith.fft`,
Table 4), products at tag 21. `input_err`: the ℓ2 input error of ffSampling is `≤ 3.65·2⁻³²`,
composing `fft_rec_err_l2`, `ec_le`, `fft_rec_err_cert`, `parseval` and `prod_l2` (`input512`); it
uses retags within `½` ulp, so truncating retags are not covered. `sign1` runs `ffs` on that input;
`Uses ρ K oa`: along every execution `oa` calls `sign1` at most `K` times (restarts included, e.g.
`signLoop`) and makes otherwise only auxiliary queries.

`falcon512_model` is `falcon512_proved` for every such `oa` with `K ≤ 2³⁸`: `hN` (`≤ 1024·K ≤ 2⁵¹`
SamplerZ calls) and `hS₂` (`≤ K·(49·3.65·2⁻³² + 135700·2⁻⁴²)² ≤ 2⁻⁹`, `centers_budget`) are proved,
not assumed.

The worlds. F is fixed-point signing with arithmetic `ρ`: SamplerZ at the computed centres `t̄`, and
`⊥` when a range check of `ffs` on computed values fails (`‖·‖ ≤ 2²¹ - 1`). A signer is F when its
operations form an `Arith`, follow `ffs`'s order of operations with the same result for the same
output ulp and operands at every call site, return `⊥` exactly on these checks and overflow no other
register. E is exact signing on the stored tree with the same aborts. For exact stored-tree signing
X without aborts, `Pr_X[s] ≥ Pr_E[s] - Pr_E[abort]`, so `Pr_F[s] > T·2⁻¹²⁶` gives `Pr_X[s] > T·2⁻¹²⁸
- Pr_E[abort]`; bounding `Pr_E[abort]` is a Lemma 12-type statement about exact signing, not proved.
Neither world is the FIPS 206 draft signer, which signs in binary64 floating point; the draft as
previewed by NIST does not specify fixed-point signing (paper §7, Type 2, tag 21) and asked for
feedback on adding it.

Keys. The keys are those of the paper's modified NTRUGen (Alg. 2), not Falcon round 3 or FIPS 206
draft keys: the checks `γf,g = 255` (l. 7, §8.3), `γF,G = 3500` (l. 13, §8.4), `γhybrid = 4` (l. 8,
§8.5), `γroot = 24` (l. 14-15, §8.6) and the `‖ℓ̂‖∞` check of `FTree` are in neither. `Key` states
the first two on the exact FFT; keygen runs them in fixed point, so they hold only up to keygen's
rounding (not formalised). The root `ℓ̂` bound comes from `γroot` directly (Lemma 7 (12)); the inner
one uses Lemma 8 (16), which is pen-and-paper only.

Remaining hypotheses (all local): `ρ : Arith`, each operation within its bound, including the
twiddle tables within `0.7072·2⁻⁶³` of the exact roots and `c/q` within `½` ulp at tag 0 (the paper
gives the tags of `c/q`, not its computation; §3.4 describes division as a reciprocal followed by a
product); `tw 0 ()` is within `0.7072·2⁻⁶³` of `i`, which tag 0 cannot hold, so an implementation is
an instance when its size-2 merge multiplies by `±i` exactly; the bounds of `Key`; the stored tree
passed the checks of `FTree` (leaves, FIPS 206 draft; `ℓ̂` ranges).

Not proved: hop B (stored tree to true tree), so no statement relative to exact Falcon;
`Pr_E[abort]` (Lemma 12); register overflow outside the checked values; the computation of the
stored tree (ffLDL⋆, reciprocal and rsqrt); SamplerZ is assumed perfect (`hE`, `hM`, `hF`; paper
footnote 7: BerExp caps `s` at 63); no UF-CMA game is defined (`oa` is any experiment and the
conclusion transfers a success probability; the UF-CMA reading is the framing of `Theorem2`); the
norm check and restarts (`acc`) are integer code on `z` in `oa` (§7.3 item 4), so signers computing
`s = (t - z)B̂` in floating point are not modelled; recovering `z` from the FFT form; tweak signing
(tag 18). `g, G` enter only the integer computation of the signature from `z`, which is shared code
of `oa`. -/

@[expose] public section

open OracleSpec OracleComp FalconPrecision.Errors.FFTRec FalconPrecision.Errors.FFTDef
    FalconPrecision.Errors.Fixed FalconPrecision.RenyiPath

namespace FalconPrecision.Errors.FFSamp

/-- `c/q` (`q = 12289`). -/
noncomputable def cdq (c : Fin (2 ^ 9) → ℤ) : Fin (2 ^ 9) → ℂ := fun i => ((c i : ℝ) / 12289 : ℝ)

/-- `c/q` at tag 0, retagged to tag 9 (real part; the imaginary part is `0` here). -/
noncomputable def pre (ρ : Arith) (z : ℂ) : ℂ := ⟨ρ.retag (1 / 2 ^ 54) (ρ.quot z.re), z.im⟩

theorem pre_err (ρ : Arith) (z : ℂ) : ‖pre ρ z - z‖ ≤ 1 / 2 ^ 55 + 1 / 2 ^ 64 := by
  have h1 := ρ.retag_err (by positivity : (0 : ℝ) < 1 / 2 ^ 54) (ρ.quot z.re)
  have h2 := ρ.quot_err z.re
  have h : pre ρ z - z = ((ρ.retag (1 / 2 ^ 54) (ρ.quot z.re) - z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pre]
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  linarith [abs_sub_le (ρ.retag (1 / 2 ^ 54) (ρ.quot z.re)) (ρ.quot z.re) z.re]

/-- Exact `FFT(a)` at Falcon-512. -/
noncomputable def fftE (a : Fin (2 ^ 9) → ℂ) (o : Out 9) : ℂ := evalAt a (pt 9 o)

/--
A Falcon-512 key for standard signing from the paper's modified NTRUGen: `f, F`, the bounds `γf,g =
255`, `γF,G = 3500` (Alg. 2 l. 7, 13) on their exact FFTs, and a stored tree after the expansion
checks (not tied to `f, F`). -/
structure Key where
  f : Fin (2 ^ 9) → ℤ
  F : Fin (2 ^ 9) → ℤ
  hf : ∀ o, ‖fftE (fun i => (f i : ℂ)) o‖ ≤ 255
  hF : ∀ o, ‖fftE (fun i => (F i : ℂ)) o‖ ≤ 3500
  tree : FTree 9

/-- `t̂0 = -FFT(c/q)⊙F̂`, exact. -/
noncomputable def t0E (k : Key) (c : Fin (2 ^ 9) → ℤ) (o : Out 9) : ℂ :=
  -(fftE (cdq c) o * fftE (fun i => (k.F i : ℂ)) o)

/-- `t̂1 = FFT(c/q)⊙f̂`, exact. -/
noncomputable def t1E (k : Key) (c : Fin (2 ^ 9) → ℤ) (o : Out 9) : ℂ :=
  fftE (cdq c) o * fftE (fun i => (k.f i : ℂ)) o

/-- `FFT(c/q)` at tag 9. -/
noncomputable def chC (ρ : Arith) (c : Fin (2 ^ 9) → ℤ) : Out 9 → ℂ :=
    ρ.fft (1 / 2 ^ 54) 9 fun i => pre ρ (cdq c i)

/-- `t̂0` at tag 21 (`F̂` at tag 12). -/
noncomputable def t0C (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ) (o : Out 9) : ℂ :=
  -ρ.mul (1 / 2 ^ 42) (chC ρ c o) (ρ.fft (1 / 2 ^ 51) 9 (fun i => (k.F i : ℂ)) o)

/-- `t̂1` at tag 21 (`f̂` at tag 8). -/
noncomputable def t1C (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ) (o : Out 9) : ℂ :=
  ρ.mul (1 / 2 ^ 42) (chC ρ c o) (ρ.fft (1 / 2 ^ 55) 9 (fun i => (k.f i : ℂ)) o)

theorem l2_out0 (f : Out 0 → ℂ) : l2 f = ‖f ()‖ := by
  unfold l2
  change √(∑ _o : Unit, ‖f ()‖ ^ 2) = _
  simp

theorem l2_neg {ι : Type} [Fintype ι] (f : ι → ℂ) : l2 (fun i => -f i) = l2 f := by
  simp only [l2, norm_neg]

theorem l2_pairF_le {L : ℕ} (a b : Out L → ℂ) : l2 (pairF a b) ≤ l2 a + l2 b := by
  have h := l2_pairF_sq a b
  refine (pow_le_pow_iff_left₀ (l2_nonneg _)
      (add_nonneg (l2_nonneg a) (l2_nonneg b)) two_ne_zero).1 ?_
  nlinarith [l2_nonneg a, l2_nonneg b]

/-- The computed `FFT(c/q)` is within `1414600·2⁻⁶³` in ℓ2. -/
theorem chC_err (ρ : Arith) (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) :
    l2 (chC ρ c - fun o => fftE (cdq c) o) ≤ 1414600 / 2 ^ 63 := by
  set E : ℕ → ℝ := fun L => Nat.rec (motive := fun _ => ℝ) (1 / 2 ^ 55 + 1 / 2 ^ 64)
    (fun L e => 2 * (1 + 7072 / 10000 / 2 ^ 63) * e +
      √2 * (√(2 ^ L) * (7072 / 10000 / 2 ^ 63 * 512 + 141422 / 100000 / 2 ^ 54))) L
  have hu : (0 : ℝ) < 1 / 2 ^ 54 := by positivity
  have hr : √2 * (1 / 2 ^ 54) ≤ (141422 / 100000 / 2 ^ 54 : ℝ) :=
    (mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num)
  have ha : ∀ i, ‖cdq c i‖ ≤ 1 := fun i => by
    have : |(c i : ℝ)| < 12289 := by exact_mod_cast hc i
    rw [cdq, Complex.norm_real, Real.norm_eq_abs, abs_div, div_le_one (by norm_num)]
    norm_num; linarith
  have h := fft_rec_err_l2 (7072 / 10000 / 2 ^ 63) (141422 / 100000 / 2 ^ 54) 512 E zeta ρ.tw pt
    pt_succ zeta_sq norm_zeta ρ.tw_err (fun L a => ρ.fft (1 / 2 ^ 54) L fun i => pre ρ (a i))
    (fun a => by rw [l2_out0]; exact pre_err ρ _)
    (fun L a => ⟨_, fun o => (ρ.mul_err hu _ _).trans hr, fun o => ⟨rfl, rfl⟩⟩) (fun L => rfl) 9
    (cdq c) fun o => (norm_evalAt_le _ _ (norm_pt 9 o) 1 ha).trans (by norm_num)
  have he := (ec_le (7072 / 10000 / 2 ^ 63) (7072 / 10000 / 2 ^ 63 * 512 + 141422 / 100000 / 2 ^ 54)
    (by positivity) (by norm_num) (by positivity) E le_rfl
    (by change (0 : ℝ) ≤ 1 / 2 ^ 55 + 1 / 2 ^ 64; positivity) (fun L => rfl) 9).2
  exact h.trans (he.trans ec512)

/--
Certified FFT at Falcon-512 (`‖FFT(a)‖∞ ≤ B`, footnote 9): sup error `(δB + r)·Σ_{j<9}(2 + δ)^j`. -/
theorem fft_cert512 (ρ : Arith) (u B r : ℝ) (hu : 0 < u) (hr : √2 * u ≤ r) (a : Fin (2 ^ 9) → ℂ)
    (hB : ∀ o, ‖fftE a o‖ ≤ B) (o : Out 9) :
    ‖ρ.fft u 9 a o - fftE a o‖ ≤
      (7072 / 10000 / 2 ^ 63 * B + r) * ∑ j ∈ Finset.range 9, (2 + 7072 / 10000 / 2 ^ 63) ^ j := by
  set E : ℕ → ℝ := fun L => Nat.rec (motive := fun _ => ℝ) 0
    (fun _ e => e * (2 + 7072 / 10000 / 2 ^ 63) + 7072 / 10000 / 2 ^ 63 * B + r) L
  have hE : ∀ L, E (L + 1) = E L * (2 + 7072 / 10000 / 2 ^ 63) + 7072 / 10000 / 2 ^ 63 * B + r :=
      fun _ => rfl
  have h :=
      fft_rec_err_cert (7072 / 10000 / 2 ^ 63) r B E zeta ρ.tw pt pt_succ zeta_sq norm_zeta ρ.tw_err
    (fun L a => ρ.fft u L a) (fun a o => by change ‖a _ - a _‖ ≤ 0; simp)
    (fun L a o => ⟨_, (ρ.mul_err hu _ _).trans hr, rfl, rfl⟩) hE 9 a hB o
  rw [cert_closed _ _ _ E hE 9] at h
  simpa [E, fftE] using h

theorem fftE_l2 (c : Fin (2 ^ 9) → ℤ)
    (hc : ∀ i, |c i| < 12289) : l2 (fun o => fftE (cdq c) o) ≤ 512 := by
  have hp := parseval zeta pt pt_succ zeta_sq norm_zeta 9 (cdq c)
  have hs : ∑ i, ‖cdq c i‖ ^ 2 ≤ 2 ^ 9 := by
    calc ∑ i, ‖cdq c i‖ ^ 2 ≤ ∑ _i : Fin (2 ^ 9), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have : |(c i : ℝ)| < 12289 := by exact_mod_cast hc i
          have h1 : ‖cdq c i‖ ≤ 1 := by
            rw [cdq, Complex.norm_real, Real.norm_eq_abs, abs_div, div_le_one (by norm_num)]
            norm_num; linarith
          nlinarith [norm_nonneg (cdq c i)]
      _ = 2 ^ 9 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  unfold l2
  rw [Real.sqrt_le_left (by norm_num)]
  change ∑ o, ‖evalAt (cdq c) (pt 9 o)‖ ^ 2 ≤ _
  rw [hp]
  nlinarith

/-- **Input error of ffSampling at Falcon-512**: `‖(t̂0, t̂1) computed - exact‖₂ ≤ 3.65·2⁻³²`. -/
theorem input_err (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ) (hc : ∀ i, |c i| < 12289) :
    l2 (pairF (t0C ρ k c - t0E k c) (t1C ρ k c - t1E k c)) ≤ 365 / 100 / 2 ^ 32 := by
  have hcard : √(Fintype.card (Out 9) : ℝ) ≤ 2 ^ 5 := by
    rw [card_out, Real.sqrt_le_left (by norm_num)]; norm_num
  have hr : √2 * (1 / 2 ^ 42) ≤ (141422 / 100000 / 2 ^ 42 : ℝ) := sqrt_two_ulp21
  have hc' := chC_err ρ c hc
  have hn := fftE_l2 c hc
  have hF := fft_cert512 ρ (1 / 2 ^ 51) 3500 (141422 / 100000 / 2 ^ 51) (by positivity)
    ((mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num)) _ k.hF
  have hf := fft_cert512 ρ (1 / 2 ^ 55) 255 (141422 / 100000 / 2 ^ 55) (by positivity)
    ((mul_le_mul_of_nonneg_right sqrt_two_le (by positivity)).trans (by norm_num)) _ k.hf
  have h0 := prod_l2 (fun o => fftE (cdq c) o) (chC ρ c) (fftE fun i => (k.F i : ℂ))
    (ρ.fft (1 / 2 ^ 51) 9 fun i => (k.F i : ℂ)) (fun o => ρ.mul (1 / 2 ^ 42) (chC ρ c o)
      (ρ.fft (1 / 2 ^ 51) 9 (fun i => (k.F i : ℂ)) o)) 3500 (4226000 / 2 ^ 63)
          (1414600 / 2 ^ 63) 512
    (141422 / 100000 / 2 ^ 42) (by norm_num) (by positivity) (by positivity) k.hF
    (fun o => (hF o).trans (fftF512_err _ _ (by positivity) le_rfl le_rfl)) hc' hn
    (fun o => (ρ.mul_err (by positivity) _ _).trans hr)
  have h1 := prod_l2 (fun o => fftE (cdq c) o) (chC ρ c) (fftE fun i => (k.f i : ℂ))
    (ρ.fft (1 / 2 ^ 55) 9 fun i => (k.f i : ℂ)) (fun o => ρ.mul (1 / 2 ^ 42) (chC ρ c o)
      (ρ.fft (1 / 2 ^ 55) 9 (fun i => (k.f i : ℂ)) o)) 255 (277300 / 2 ^ 63) (1414600 / 2 ^ 63) 512
    (141422 / 100000 / 2 ^ 42) (by norm_num) (by positivity) (by positivity) k.hf
    (fun o => (hf o).trans
        (FalconPrecision.Errors.LDL.fft512_err _ _ (by positivity) le_rfl le_rfl)) hc' hn
    (fun o => (ρ.mul_err (by positivity) _ _).trans hr)
  have e0 : t0C ρ k c - t0E k c = fun o => -(ρ.mul (1 / 2 ^ 42) (chC ρ c o)
      (ρ.fft (1 / 2 ^ 51) 9 (fun i => (k.F i : ℂ)) o) -
        fftE (cdq c) o * fftE (fun i => (k.F i : ℂ)) o) := by
    funext o; simp only [Pi.sub_apply, t0C, t0E]; ring
  have e1 : l2 (t1C ρ k c - t1E k c) = l2 (fun o => ρ.mul (1 / 2 ^ 42) (chC ρ c o)
      (ρ.fft (1 / 2 ^ 55) 9 (fun i => (k.f i : ℂ)) o) -
        fftE (cdq c) o * fftE (fun i => (k.f i : ℂ)) o) := rfl
  have hi := input512 (1414600 / 2 ^ 63) le_rfl
  refine (l2_pairF_le _ _).trans ?_
  rw [e0, l2_neg, e1]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ 141422 / 100000 / 2 ^ 42)
  linarith

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA}

open Classical in
/--
One ffSampling call of standard signing (spec Alg. 10 l. 3, 6) on the hash `c`: `none` (`⊥`) unless
`|c i| < q`, else the integer `z = (z0, z1)` of `ffs` (or `⊥`). -/
noncomputable def sign1 (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    OracleComp (FalconGame.spec aux Falcon.CallP)
        (Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ))) :=
  if ∀ i, |c i| < 12289 then
    (fun r => r.map fun s => (s.z0, s.z1)) <$> ffs ρ k.tree (t0E k c) (t1E k c) (t0C ρ k c)
        (t1C ρ k c)
  else pure none

/-- **Centre-error budget of one ffSampling call** of standard signing. -/
theorem sign1_pathS (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    PathSum wS (sign1 (aux := aux) ρ k c) ((49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42) ^ 2) := by
  unfold sign1
  split_ifs with hc
  · rw [map_eq_bind_pure_comp]
    obtain ⟨h0, hA, hC⟩ := coef512 (7072 / 10000 / 2 ^ 63) (by positivity) le_rfl
    have h := mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ 365 / 100 / 2 ^ 32)
    refine (PathSum.bind
        (ffs_pathS ρ k.tree le_rfl _ _ _ _ _ (input_err ρ k c hc) (by linarith)).toPathSum
      (T := 0) fun _ => .pure _ le_rfl).weaken ?_
    rw [add_zero]
    refine pow_le_pow_left₀ (add_nonneg (mul_nonneg (h0 9).1 (by positivity)) (h0 9).2) ?_ 2
    linarith
  · exact .pure _ (by positivity)

/-- **SamplerZ calls of one ffSampling call**: at most `1024`. -/
theorem sign1_pathN (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ) :
    PathSum w1 (sign1 (aux := aux) ρ k c) 1024 := by
  unfold sign1
  split_ifs
  · rw [map_eq_bind_pure_comp]
    refine (PathSum.bind (ffs_pathN ρ k.tree _ _ _ _) (T := 0) fun _ => .pure _ le_rfl).weaken ?_
    norm_num
  · exact .pure _ (by norm_num)

/-- `oa` calls `sign1` at most `K` times along every execution; every other query is auxiliary. -/
inductive Uses (ρ : Arith) : ℕ → {α : Type} → OracleComp (FalconGame.spec aux Falcon.CallP) α → Prop
  | pure (K : ℕ) {α : Type} (x : α) : Uses ρ K (pure x)
  | query (K : ℕ) {α : Type} (t : ιA)
      (k : (FalconGame.spec aux Falcon.CallP).Range (.inl t) →
          OracleComp (FalconGame.spec aux Falcon.CallP) α)
      (h : ∀ u, Uses ρ K (k u)) :
      Uses ρ K (liftM (OracleSpec.query (spec := FalconGame.spec aux Falcon.CallP) (.inl t)) >>= k)
  | sign (K : ℕ) {α : Type} (key : Key) (c : Fin (2 ^ 9) → ℤ)
      (k : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) →
          OracleComp (FalconGame.spec aux Falcon.CallP) α)
      (h : ∀ y, Uses ρ K (k y)) : Uses ρ (K + 1) (sign1 ρ key c >>= k)

theorem Uses.mono {ρ : Arith} {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Uses ρ K oa) {K' : ℕ} (hK : K ≤ K') : Uses ρ K' oa := by
  induction h generalizing K' with
  | pure K x => exact .pure K' x
  | query K t k _ ih => exact .query K' t k fun u => ih u hK
  | sign K key c k _ ih =>
    obtain ⟨K'', rfl⟩ : ∃ K'', K' = K'' + 1 := ⟨K' - 1, by omega⟩
    exact .sign K'' key c k fun y => ih y (by omega)

/-- Calls add along `>>=`. -/
theorem Uses.bind {ρ : Arith} {K K' : ℕ} {α β : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    {ob : α → OracleComp (FalconGame.spec aux Falcon.CallP) β} (h : Uses ρ K oa)
        (hb : ∀ x, Uses ρ K' (ob x)) :
    Uses ρ (K + K') (oa >>= ob) := by
  induction h with
  | pure K x => rw [pure_bind]; exact (hb x).mono (by omega)
  | query K t k _ ih => rw [bind_assoc]; exact .query _ t _ fun u => ih u hb
  | sign K key c k _ ih =>
    rw [bind_assoc, show K + 1 + K' = K + K' + 1 by omega]
    exact .sign _ key c _ fun y => ih y hb

/--
Spec Alg. 10 l. 4-11 with at most `n` ffSampling calls: `acc` (norm check and compression of `z`,
shared integer code) returns a signature or restarts. -/
noncomputable def signLoop {β : Type} (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ)
    (acc : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) → Option β) :
    ℕ → OracleComp (FalconGame.spec aux Falcon.CallP) (Option β)
  | 0 => pure none
  | n + 1 => sign1 ρ k c >>= fun y => (acc y).elim (signLoop ρ k c acc n) fun b => pure (some b)

theorem Uses.signLoop {β : Type} (ρ : Arith) (k : Key) (c : Fin (2 ^ 9) → ℤ)
    (acc : Option ((Fin (2 ^ 9) → ℤ) × (Fin (2 ^ 9) → ℤ)) → Option β) :
    ∀ n, Uses ρ n (signLoop (aux := aux) ρ k c acc n)
  | 0 => .pure 0 none
  | n + 1 => .sign n k c _ fun y => by
    rcases acc y with _ | b
    exacts [Uses.signLoop ρ k c acc n, .pure n _]

theorem Uses.pathS {ρ : Arith} {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Uses ρ K oa) : PathSum wS oa (K * (49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42) ^ 2) := by
  induction h with
  | pure K x => exact .pure x (by positivity)
  | query K t k _ ih =>
    refine .query_bind _ k fun u => ?_
    rw [show wS (Sum.inl t) = 0 from rfl, sub_zero]
    exact ih u
  | sign K key c k _ ih =>
    have := (sign1_pathS ρ key c).bind ih
    rwa [show (49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42 : ℝ) ^ 2 + K *
        (49 * (365 / 100 / 2 ^ 32) +
      135700 / 2 ^ 42) ^ 2 = ((K + 1 : ℕ) : ℝ) *
          (49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42) ^ 2 by
        push_cast; ring] at this

theorem Uses.pathN {ρ : Arith} {K : ℕ} {α : Type}
    {oa : OracleComp (FalconGame.spec aux Falcon.CallP) α}
    (h : Uses ρ K oa) : PathSum w1 oa (K * 1024) := by
  induction h with
  | pure K x => exact .pure x (by positivity)
  | query K t k _ ih =>
    refine .query_bind _ k fun u => ?_
    rw [show w1 (Sum.inl t) = 0 from rfl, sub_zero]
    exact ih u
  | sign K key c k _ ih =>
    have := (sign1_pathN ρ key c).bind ih
    rwa [show (1024 : ℝ) + K * 1024 = ((K + 1 : ℕ) : ℝ) * 1024 by push_cast; ring] at this

end FalconPrecision.Errors.FFSamp

namespace FalconPrecision.Falcon

open MeasureTheory InformationTheory LatticeCrypto FalconPrecision.Errors.FFSamp
open scoped ENNReal

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [∀ t, Countable (aux t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Theorem 2 at Falcon-512 for the fixed-point signing model** (`λ = 128`, hop A). For every
arithmetic `ρ` and every experiment `oa` that calls standard-signing ffSampling (`sign1`) at most `K
≤ 2³⁸` times along every execution and makes otherwise only auxiliary queries: success `> T·2⁻¹²⁶`
in F (fixed-point signing with `ρ`, range checks on computed values, `⊥` when one fails) gives
success `> T·2⁻¹²⁸` in E (exact signing on the stored tree with the same aborts). `hN` and `hS₂` of
`falcon512_proved` are proved (`Uses.pathN`, `Uses.pathS`).

Not a statement about exact signing without aborts X: `Pr_F[s] > T·2⁻¹²⁶` gives `Pr_X[s] > T·2⁻¹²⁸ -
Pr_E[abort]`, and `Pr_E[abort]` (a Lemma 12-type bound on exact values at range `2²¹ - 2`; Lemma 12
at `λ = 128` gives only about `K·2⁻¹²⁸`) is not bounded; hop B (true tree) is not proved. Keys: the
paper's modified NTRUGen (Alg. 2), not Falcon round 3 or FIPS 206 draft keys; `Key`'s exact bounds
hold up to keygen's fixed-point rounding. SamplerZ is assumed perfect (`hE`, `hM`, `hF`). No UF-CMA
game is defined: `oa` is any experiment. The FIPS 206 draft signs in binary64 floating point; the
draft as previewed by NIST does not specify fixed-point signing (NIST asked for feedback on adding
it). The norm check and restarts are integer code in `oa`. Other hypotheses: those of the module
docstring (`ρ`, `Key`, `FTree`). -/
theorem falcon512_model (ρ : Arith) (K : ℕ) (hK : K ≤ 2 ^ 38) (T : ℝ≥0∞) (hT : 1 ≤ T)
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
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implE oa] s := by
  have hK' : (K : ℝ) ≤ 2 ^ 38 := by exact_mod_cast hK
  refine falcon512_proved T hT implA implE implM implF hAE hAM hAF hE hM hF oa
    (hoa.pathN.weaken (by linarith)) (hoa.pathS.weaken ?_) hs hwin
  have := mul_le_mul_of_nonneg_right hK'
      (sq_nonneg (49 * (365 / 100 / 2 ^ 32) + 135700 / 2 ^ 42 : ℝ))
  linarith [centers_budget]

end FalconPrecision.Falcon
