import FalconPrecision.Errors.Falcon1024Abort
import FalconPrecision.Errors.Falcon1024HopB

/-! The Type 1 error model at Falcon-1024 (`Errors.Falcon1024Model`, `Errors.Falcon1024Abort`),
hop B at Falcon-1024 (`Errors.Falcon1024HopB`), the depth-generic lemmas they instantiate and
`Falcon.CallP.hleaf1023` depend only on the standard axioms. -/

/--
info: 'FalconPrecision.Errors.FFSamp.tb512' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.tb512
/--
info: 'FalconPrecision.Errors.FFSamp.ffs_pathSP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.ffs_pathSP
/--
info: 'FalconPrecision.Errors.FFSamp.ffsU_eq_marginP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.ffsU_eq_marginP
/--
info: 'FalconPrecision.Errors.FFSamp.ffs_pathNGP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.ffs_pathNGP
/--
info: 'FalconPrecision.Errors.FFSamp.node_stepP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.node_stepP
/--
info: 'FalconPrecision.Errors.FFSamp.UsesGP.path' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.UsesGP.path
/--
info: 'FalconPrecision.Errors.FFSamp.fftE_l2P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.fftE_l2P
/--
info: 'FalconPrecision.Errors.FFSamp.fft_cert64P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.fft_cert64P
/--
info: 'FalconPrecision.Errors.FFSamp.fftE_cdqP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.fftE_cdqP
/--
info: 'FalconPrecision.Errors.FFSamp.tb1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.tb1024
/--
info: 'FalconPrecision.Errors.FFSamp.coef64_1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.coef64_1024
/--
info: 'FalconPrecision.Errors.FFSamp.ffs64_pathS1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.ffs64_pathS1024
/--
info: 'FalconPrecision.Errors.FFSamp.ffs64_pathN1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.ffs64_pathN1024
/--
info: 'FalconPrecision.Errors.FFSamp.ffs64_eq_margin1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.ffs64_eq_margin1024
/--
info: 'FalconPrecision.Errors.FFSamp.input_err64_1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.input_err64_1024
/--
info: 'FalconPrecision.Errors.FFSamp.inp64_1024_base' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.inp64_1024_base
/--
info: 'FalconPrecision.Errors.FFSamp.inp64_1024_norm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.inp64_1024_norm
/--
info: 'FalconPrecision.Errors.FFSamp.sign1024_eq_margin' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.sign1024_eq_margin
/--
info: 'FalconPrecision.Errors.FFSamp.sign1024_pathS' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.sign1024_pathS
/--
info: 'FalconPrecision.Errors.FFSamp.sign1024_pathN' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.sign1024_pathN
/--
info: 'FalconPrecision.Errors.FFSamp.Uses1024.pathS' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.Uses1024.pathS
/--
info: 'FalconPrecision.Errors.FFSamp.Uses1024.pathN' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.Uses1024.pathN
/--
info: 'FalconPrecision.Errors.FFSamp.centers_budget1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.centers_budget1024
/--
info: 'FalconPrecision.Errors.FFSamp.centers_budget1024n' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.FFSamp.centers_budget1024n
/--
info: 'FalconPrecision.Errors.AbortExact.ffsG_clampP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.ffsG_clampP
/--
info: 'FalconPrecision.Errors.AbortExact.SwapP.simulateQ_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.SwapP.simulateQ_eq
/--
info: 'FalconPrecision.Errors.AbortExact.norm_fftE_cdqP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.norm_fftE_cdqP
/--
info: 'FalconPrecision.Errors.AbortExact.isReal_t0EP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.isReal_t0EP
/--
info: 'FalconPrecision.Errors.AbortExact.isReal_t1EP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.isReal_t1EP
/--
info: 'FalconPrecision.Errors.AbortExact.etvDist_E_XP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.etvDist_E_XP
/--
info: 'FalconPrecision.Errors.AbortExact.etvDist_F_F'P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.etvDist_F_F'P
/--
info: 'FalconPrecision.Errors.AbortExact.tables1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.tables1024
/--
info: 'FalconPrecision.Errors.AbortExact.sign1024G_clamp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.sign1024G_clamp
/--
info: 'FalconPrecision.Errors.AbortExact.sign1024_clamp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.sign1024_clamp
/--
info: 'FalconPrecision.Errors.AbortExact.etvDist_E_X1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.etvDist_E_X1024
/--
info: 'FalconPrecision.Errors.AbortExact.etvDist_F_F'1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.etvDist_F_F'1024
/--
info: 'FalconPrecision.Errors.AbortExact.eps_le1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.eps_le1024
/--
info: 'FalconPrecision.Errors.AbortExact.eps_leF1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.AbortExact.eps_leF1024
/--
info: 'FalconPrecision.Errors.HopB.KeyB.Good.real' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.KeyB.Good.real
/--
info: 'FalconPrecision.Errors.HopB.KeyB.Good.close' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.KeyB.Good.close
/--
info: 'FalconPrecision.Errors.HopB.isReal_fftZP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.isReal_fftZP
/--
info: 'FalconPrecision.Errors.HopB.isReal_trueTreeP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.isReal_trueTreeP
/--
info: 'FalconPrecision.Errors.HopB.gainAP_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.gainAP_nonneg
/--
info: 'FalconPrecision.Errors.HopB.devBP_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.devBP_nonneg
/--
info: 'FalconPrecision.Errors.HopB.cBP_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.cBP_nonneg
/--
info: 'FalconPrecision.Errors.HopB.cBP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.cBP_eq
/--
info: 'FalconPrecision.Errors.HopB.s2BP_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.s2BP_eq
/--
info: 'FalconPrecision.Errors.HopB.s2BP_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.s2BP_nonneg
/--
info: 'FalconPrecision.Errors.HopB.ffsB_clampP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.ffsB_clampP
/--
info: 'FalconPrecision.Errors.HopB.signB_clampP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.signB_clampP
/--
info: 'FalconPrecision.Errors.HopB.simulateQ_clampQ_signImplP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.simulateQ_clampQ_signImplP
/--
info: 'FalconPrecision.Errors.HopB.clampQ_inlP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.clampQ_inlP
/--
info: 'FalconPrecision.Errors.HopB.hist_clampP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.hist_clampP
/--
info: 'FalconPrecision.Errors.HopB.pathS_clampP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.pathS_clampP
/--
info: 'FalconPrecision.Errors.HopB.ffsB_pathNP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.ffsB_pathNP
/--
info: 'FalconPrecision.Errors.HopB.pathN_runBP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.pathN_runBP
/--
info: 'FalconPrecision.Errors.HopB.sameQ_ffsG_ffsBP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.sameQ_ffsG_ffsBP
/--
info: 'FalconPrecision.Errors.HopB.sameQ_ffsB_ffsTP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.sameQ_ffsB_ffsTP
/--
info: 'FalconPrecision.Errors.HopB.canon_signXP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.canon_signXP
/--
info: 'FalconPrecision.Errors.HopB.canon_signTP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.canon_signTP
/--
info: 'FalconPrecision.Errors.HopB.canon_runXP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.canon_runXP
/--
info: 'FalconPrecision.Errors.HopB.canon_runTP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.canon_runTP
/--
info: 'FalconPrecision.Errors.HopB.relabel_XP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.relabel_XP
/--
info: 'FalconPrecision.Errors.HopB.relabel_YP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.relabel_YP
/--
info: 'FalconPrecision.Errors.HopB.swap_runAP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.swap_runAP
/--
info: 'FalconPrecision.Errors.HopB.tv_clamp_FP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.tv_clamp_FP
/--
info: 'FalconPrecision.Errors.HopB.renyiP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.renyiP
/--
info: 'FalconPrecision.Errors.HopB.certs131' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.certs131
/--
info: 'FalconPrecision.Errors.HopB.hopBP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.hopBP
/--
info: 'FalconPrecision.Falcon.falcon1024_exact64n'' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Falcon.falcon1024_exact64n'
/--
info: 'FalconPrecision.Errors.HopB.gainA1024_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.gainA1024_le
/--
info: 'FalconPrecision.Errors.HopB.devB1024_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.devB1024_le
/--
info: 'FalconPrecision.Errors.HopB.s2B1024_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.s2B1024_le
/--
info: 'FalconPrecision.Errors.HopB.s2B1024_43' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.s2B1024_43
/--
info: 'FalconPrecision.Errors.HopB.s2B1024_127' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.s2B1024_127
/--
info: 'FalconPrecision.Errors.HopB.eps281' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.eps281
/--
info: 'FalconPrecision.Errors.HopB.thresh1024' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.thresh1024
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_hopB' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_hopB
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true43' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true43
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true127' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true127
/--
info: 'FalconPrecision.Falcon.CallP.hleaf1023' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Falcon.CallP.hleaf1023
/--
info: 'FalconPrecision.Errors.HopB.certs256' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.certs256
/--
info: 'FalconPrecision.Errors.HopB.certs259' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.certs259
/--
info: 'FalconPrecision.Errors.HopB.thresh256' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.thresh256
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_exact256'' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_exact256'
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_hopB259' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_hopB259
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true256' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true256
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true256_43' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true256_43
/--
info: 'FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true256_127' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FalconPrecision.Errors.HopB.falcon1024_fixed_vs_true256_127
