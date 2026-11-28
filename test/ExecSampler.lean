import FalconPrecision.Exec.SamplerHop

/-! `FalconPrecision.Exec.SamplerZ`, `SamplerClose`, `SamplerHop`: SamplerZ on the 16 test vectors
of Falcon round 3 Table 3.2 (p. 44), tables, laws; axioms. -/

open FalconPrecision.Exec

/-- Uniform bits from a byte list, big-endian (the order of the spec test vectors). -/
def ubL (k : ℕ) : StateM (List ℕ) ℕ := modifyGet fun l =>
  ((l.take ((k + 7) / 8)).foldl (fun a b => 256 * a + b) 0 % 2 ^ k, l.drop ((k + 7) / 8))

/-- A hex string as bytes. -/
def hexB (s : String) : List ℕ :=
  let d (c : Char) : ℕ := if c.isDigit then c.toNat - 48 else c.toNat - 87
  ((s.toList.zip s.toList.tail).zipIdx.filter (·.2 % 2 = 0)).map fun ((a, b), _) => 16 * d a + d b

/-- Spec Table 3.2: centre, `σ′`, random bytes, output. -/
def kat : List (ℚ × ℚ × String × ℤ) := [
  (-9190471153063714 / 10 ^ 14, 17037990414754918 / 10 ^ 16,
    "0fc5442ff043d66e91d1eacac64ea5450a22941edc6c", -92),
  (-8322564895434937 / 10 ^ 15, 17037990414754918 / 10 ^ 16,
    "f4da0f8d8444d1a77265c2ef6f98bbbb4bee7db8d9b3", -8),
  (-19096516109216804 / 10 ^ 15, 17035823083824078 / 10 ^ 16,
    "db47f6d7fb9b19f25c36d6b9334d477a8bc0be68145d", -20),
  (-11335543982423326 / 10 ^ 15, 17035823083824078 / 10 ^ 16,
    "ae41b4f5209665c74d00dcc1a8168a7bb516b3190cb42c1ded26cd52aed770eca7" ++
      "dd334e0547bcc3c163ce0b", -12),
  (79386734193997555 / 10 ^ 16, 16984647769450156 / 10 ^ 16,
    "31054166c1012780c603ae9b833cec73f2f41ca5807cc89c92158834632f9b1555", 8),
  (-28990850086867255 / 10 ^ 15, 16984647769450156 / 10 ^ 16,
    "737e9d68a50a06dbbc6477", -30),
  (-9071257914091655 / 10 ^ 15, 16980782114808988 / 10 ^ 16,
    "a98ddd14bf0bf22061d632", -10),
  (-4388754568839566 / 10 ^ 14, 16980782114808988 / 10 ^ 16,
    "3cbf6818a68f7ab9991514", -41),
  (-5817435547946095 / 10 ^ 14, 17010983419195522 / 10 ^ 16,
    "6f8633f5bfa5d26848668e3d5ddd46958e97630410587c", -61),
  (-4358664906684732 / 10 ^ 14, 17010983419195522 / 10 ^ 16,
    "272bc6c25f5c5ee53f83c43a361fbc7cc91dc783e20a", -46),
  (-3470565203313315 / 10 ^ 14, 17009387219711465 / 10 ^ 16,
    "45443c59574c2c3b07e2e1d9071e6d133dbe32754b0a", -34),
  (-4436009577368896 / 10 ^ 14, 17009387219711465 / 10 ^ 16,
    "6ac116ed60c258e2cbaeab728c4823e6da36e18d08da5d0cc104e21cc7fd1f5ca8" ++
      "d9dbb675266c928448059e", -44),
  (-21783037079346236 / 10 ^ 15, 16958406126012802 / 10 ^ 16,
    "68163bc1e2cbf3e18e7426", -23),
  (-3968827784633828 / 10 ^ 14, 16958406126012802 / 10 ^ 16,
    "d6a1b51d76222a705a0259", -40),
  (-18488607061056847 / 10 ^ 15, 16955259305261838 / 10 ^ 16,
    "f0523bfaa8a394bf4ea5c10f842366fde286d6a30803", -22),
  (-4839610939101591 / 10 ^ 14, 16955259305261838 / 10 ^ 16,
    "87bd87e63374cee62127fc6931104aab64f136a0485b", -50)]

/-- SamplerZ (72 bits, saturated shift as the spec) on a vector, inputs rounded to `Fx 64`:
the output and the unused bytes. -/
def runKat (v : ℚ × ℚ × String × ℤ) : ℤ × List ℕ :=
  Id.run ((samplerZ falcon512S ⟨.plain, false, .b72⟩ ubL (Fx.ofRat .halfEven v.2.1)
    (Fx.ofRat .halfEven v.1)).run (hexB v.2.2.1))

-- all 16 vectors: the spec output, every byte used
/-- info: true -/
#guard_msgs in
#eval kat.all fun v => runKat v == (v.2.2.2, [])

-- the same with shift rejection (no vector reaches a shift ≥ 64)
/-- info: true -/
#guard_msgs in
#eval kat.all fun v => Id.run ((samplerZ falcon512S ⟨.plain, true, .b72⟩ ubL
  (Fx.ofRat .halfEven v.2.1) (Fx.ofRat .halfEven v.1)).run (hexB v.2.2.1)) == (v.2.2.2, [])

-- table shapes; pdt sums to 2^w
/-- info: true -/
#guard_msgs in
#eval tab72.okB && tab79.okB && ((List.range 19).map (pdtZ tab72)).sum == 2 ^ 72 &&
  ((List.range 19).map (pdtZ tab79)).sum == 2 ^ 79

-- spot values of pdt (the rule `pdt[i] = ⌊2^w·D(i)⌋` is checked outside Lean)
/-- info: (1697680241746640300030, 1, 128) -/
#guard_msgs in
#eval (pdtZ tab72 0, pdtZ tab72 18, pdtZ tab79 18)

-- BaseSampler: u = 0 gives 18, u ≥ RCDT[0] gives 0
/-- info: (18, 0, 1) -/
#guard_msgs in
#eval (baseZ tab72 0, baseZ tab72 rcdt72.head!, baseZ tab72 (rcdt72.head! - 1))

-- ApproxExp at x = 0, ccs = 1: 2^63; accW at x = 0, ccs = 1: 2^64 - 1
/-- info: (9223372036854775808, 18446744073709551615) -/
#guard_msgs in
#eval (approxExp 0 1, accW falcon512S false 0 1)

-- a shift ≥ 64: rejected under shiftRej, saturated otherwise
/-- info: (0, 1) -/
#guard_msgs in
#eval (accW falcon512S true 45 1, accW falcon512S false 45 1)

-- the law sums to 1 over ⌊t̄⌋ − 20 … ⌊t̄⌋ + 20 (σ̄ = 1.5, t̄ = 2.25)
/-- info: true -/
#guard_msgs in
#eval
  let σ : Fx 64 := ⟨3 * 2 ^ 63⟩
  let t : Fx 64 := ⟨9 * 2 ^ 62⟩
  ((List.range 41).map fun i => lawZ falcon512S ⟨.plain, true, .b72⟩ σ t (i - 18 : ℤ)).sum == 1

-- range check
/-- info: (true, false, false) -/
#guard_msgs in
#eval (inRangeB falcon512S ⟨3 * 2 ^ 63⟩, inRangeB falcon512S ⟨2 ^ 64⟩,
  inRangeB falcon512S ⟨2 ^ 65⟩)

/--
info: 'FalconPrecision.Exec.tab_okB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tab_okB

/--
info: 'FalconPrecision.Exec.samplerZ_mgf' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samplerZ_mgf

/--
info: 'FalconPrecision.Exec.sampler_hop' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampler_hop

/--
info: 'FalconPrecision.Exec.falcon512_exec_sampler_vs_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512_exec_sampler_vs_true

/--
info: 'FalconPrecision.Exec.baseZ_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms baseZ_law

/--
info: 'FalconPrecision.Exec.berExp_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms berExp_law

/--
info: 'FalconPrecision.Exec.samplerZ_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samplerZ_law

/--
info: 'FalconPrecision.Exec.renyiMGF_le_chi2' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms renyiMGF_le_chi2

/--
info: 'FalconPrecision.Exec.tab_ok' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tab_ok

/--
info: 'FalconPrecision.Exec.approxExp_err' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms approxExp_err

/--
info: 'FalconPrecision.Exec.lawZ_close' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lawZ_close

/--
info: 'FalconPrecision.Exec.samplerZ_tv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samplerZ_tv

/--
info: 'FalconPrecision.Exec.exec_factor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_factor

/--
info: 'FalconPrecision.Exec.embedS_exec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms embedS_exec

/--
info: 'FalconPrecision.Exec.pathSum_embedS' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_embedS

/--
info: 'FalconPrecision.Exec.pathSum_execZ' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_execZ

/--
info: 'FalconPrecision.Exec.thresh_sampler' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms thresh_sampler

/--
info: 'FalconPrecision.Exec.exec_sampler_worlds_exist' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exec_sampler_worlds_exist

-- Falcon-1024: σ̄ = 1.29 is in SamplerZ's range at Falcon-512, not at Falcon-1024; σ̄ = 1.5 at both
/-- info: (true, false, true) -/
#guard_msgs in
#eval (inRangeB falcon512S ⟨129 * 2 ^ 64 / 100⟩, inRangeB falcon1024S ⟨129 * 2 ^ 64 / 100⟩,
  inRangeB falcon1024S ⟨3 * 2 ^ 63⟩)

-- the Falcon-1024 law sums to 1 over ⌊t̄⌋ − 20 … ⌊t̄⌋ + 20 (σ̄ = 1.5, t̄ = 2.25)
/-- info: true -/
#guard_msgs in
#eval
  let σ : Fx 64 := ⟨3 * 2 ^ 63⟩
  let t : Fx 64 := ⟨9 * 2 ^ 62⟩
  ((List.range 41).map fun i => lawZ falcon1024S ⟨.plain, true, .b72⟩ σ t (i - 18 : ℤ)).sum == 1

/--
info: 'FalconPrecision.Exec.sminOk512' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sminOk512

/--
info: 'FalconPrecision.Exec.sminOk1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sminOk1024

/--
info: 'FalconPrecision.Exec.falcon512S_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon512S_eq

/--
info: 'FalconPrecision.Exec.falcon1024S_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms falcon1024S_eq

/--
info: 'FalconPrecision.Exec.sampS_σmin' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampS_σmin

/--
info: 'FalconPrecision.Exec.sampS_tab' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampS_tab

/--
info: 'FalconPrecision.Exec.xOf_sampS' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms xOf_sampS

/--
info: 'FalconPrecision.Exec.accW_sampS' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accW_sampS

/--
info: 'FalconPrecision.Exec.sampS_σ_pos' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampS_σ_pos

/--
info: 'FalconPrecision.Exec.cand_boundsP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cand_boundsP

/--
info: 'FalconPrecision.Exec.wsZP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wsZP_eq

/--
info: 'FalconPrecision.Exec.K0ZP_theta' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms K0ZP_theta

/--
info: 'FalconPrecision.Exec.wZz_outP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wZz_outP

/--
info: 'FalconPrecision.Exec.AsZP_mem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AsZP_mem

/--
info: 'FalconPrecision.Exec.DZP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DZP_eq

/--
info: 'FalconPrecision.Exec.hws0P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hws0P

/--
info: 'FalconPrecision.Exec.sum_ws_candCP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_ws_candCP

/--
info: 'FalconPrecision.Exec.ws_le_EP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ws_le_EP

/--
info: 'FalconPrecision.Exec.eps_ws_candCP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eps_ws_candCP

/--
info: 'FalconPrecision.Exec.accZ_candCP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accZ_candCP

/--
info: 'FalconPrecision.Exec.accZ_boundsP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms accZ_boundsP

/--
info: 'FalconPrecision.Exec.chi_finP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chi_finP

/--
info: 'FalconPrecision.Exec.lawZ_closeP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lawZ_closeP

/--
info: 'FalconPrecision.Exec.samplerZ_mgfP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samplerZ_mgfP

/--
info: 'FalconPrecision.Exec.wZ_satP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wZ_satP

/--
info: 'FalconPrecision.Exec.samplerZ_tvP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samplerZ_tvP

/--
info: 'FalconPrecision.Exec.lawZ_close1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lawZ_close1024

/--
info: 'FalconPrecision.Exec.samplerZ_mgf1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samplerZ_mgf1024

/--
info: 'FalconPrecision.Exec.samplerZ_tv1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms samplerZ_tv1024

/--
info: 'FalconPrecision.Exec.simulateQ_sampQP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_sampQP

/--
info: 'FalconPrecision.Exec.simulateQ_ffsXP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_ffsXP

/--
info: 'FalconPrecision.Exec.implZ_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms implZ_eq

/--
info: 'FalconPrecision.Exec.pathSum_sampQP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_sampQP

/--
info: 'FalconPrecision.Exec.pathSum_ffsXP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pathSum_ffsXP

/--
info: 'FalconPrecision.Exec.sampler_hopP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampler_hopP

/--
info: 'FalconPrecision.Exec.sampler_hop1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sampler_hop1024

/--
info: 'FalconPrecision.Exec.thresh_samplerE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms thresh_samplerE

/--
info: 'FalconPrecision.Exec.thresh_sampler1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms thresh_sampler1024

/--
info: 'FalconPrecision.Exec.thresh_sampler1024_256' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms thresh_sampler1024_256
