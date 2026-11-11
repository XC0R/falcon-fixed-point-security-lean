import FalconPrecision.Errors.FalconProved
import FalconPrecision.Errors.FalconInput
import FalconPrecision.Errors.FalconLeaf
import FalconPrecision.Errors.FalconRoot
import FalconPrecision.Errors.IFFTRec
import FalconPrecision.Errors.FxC
import FalconPrecision.Errors.PathCompose
import FalconPrecision.Errors.SignModel
import FalconPrecision.Errors.SignModel64
import FalconPrecision.Errors.GaussTail
import FalconPrecision.Errors.AbortTV
import FalconPrecision.Errors.FFTReal
import FalconPrecision.Errors.AbortExact
import FalconPrecision.Errors.HopB

/-- info: 'FalconPrecision.Falcon.falcon512_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_proved

/-- info: 'FalconPrecision.Falcon.centers_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.centers_budget

/-- info: 'FalconPrecision.Errors.FFSamp.falcon512_centers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.falcon512_centers

/-- info: 'FalconPrecision.Errors.FFSamp.run_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.run_l2

/-- info: 'FalconPrecision.Errors.FFSamp.input512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.input512

/-- info: 'FalconPrecision.Errors.FFSamp.ec512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ec512

/-- info: 'FalconPrecision.Errors.FFSamp.fftF512_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.fftF512_err

/-- info: 'FalconPrecision.Errors.FFSamp.ez512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ez512

/-- info: 'FalconPrecision.Errors.FFSamp.split512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.split512

/-- info: 'FalconPrecision.Errors.LDL.falcon512_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.LDL.falcon512_leaf

/-- info: 'FalconPrecision.Errors.LDL.step512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.LDL.step512

/-- info: 'FalconPrecision.Errors.LDL.root512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.LDL.root512

/-- info: 'FalconPrecision.Errors.LDL.root11_512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.LDL.root11_512

/-- info: 'FalconPrecision.Errors.LDL.fft512_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.LDL.fft512_err

/-- info: 'FalconPrecision.Errors.FFTRec.fft_rec_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTRec.fft_rec_err

/-- info: 'FalconPrecision.Errors.FFTRec.fft_rec_err_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTRec.fft_rec_err_l2

/-- info: 'FalconPrecision.Errors.FFTRec.fft_rec_err_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTRec.fft_rec_err_cert

/-- info: 'FalconPrecision.Errors.FFTRec.parseval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTRec.parseval

/-- info: 'FalconPrecision.Errors.FFTRec.ifft_rec_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTRec.ifft_rec_err

/-- info: 'FalconPrecision.Errors.Fixed.twiddle_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.twiddle_err

/-- info: 'FalconPrecision.Errors.Fixed.fxc_mul_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.fxc_mul_err

/-- info: 'FalconPrecision.RenyiPath.PathSum.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.PathSum.bind

/-- info: 'FalconPrecision.RenyiPath.BlockPath.pathSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.BlockPath.pathSum

/-- info: 'FalconPrecision.Falcon.falcon512_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_model

/-- info: 'FalconPrecision.Errors.FFSamp.input_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.input_err

/-- info: 'FalconPrecision.Errors.FFSamp.chC_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.chC_err

/-- info: 'FalconPrecision.Errors.FFSamp.fft_cert512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.fft_cert512

/-- info: 'FalconPrecision.Errors.FFSamp.sign1_pathS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.sign1_pathS

/-- info: 'FalconPrecision.Errors.FFSamp.sign1_pathN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.sign1_pathN

/-- info: 'FalconPrecision.Errors.FFSamp.Uses.pathS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.Uses.pathS

/-- info: 'FalconPrecision.Errors.FFSamp.Uses.pathN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.Uses.pathN

/-- info: 'FalconPrecision.Errors.FFSamp.Uses.signLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.Uses.signLoop

/-- info: 'FalconPrecision.Errors.FFSamp.Uses.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.Uses.bind

/-- info: 'FalconPrecision.Errors.FFSamp.ffs_pathS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs_pathS

/-- info: 'FalconPrecision.Errors.FFSamp.ffs_pathN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs_pathN

/-- info: 'FalconPrecision.Errors.FFSamp.node_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.node_step

/-- info: 'FalconPrecision.Errors.FFSamp.split_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.split_rel

/-- info: 'FalconPrecision.Errors.FFSamp.w_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.w_bound

/-- info: 'FalconPrecision.Errors.FFSamp.merge_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.merge_inv

/-- info: 'FalconPrecision.Errors.FFSamp.join_fft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.join_fft

/-- info: 'FalconPrecision.Errors.FFSamp.coef512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.coef512

/-- info: 'FalconPrecision.Errors.Fixed.merge_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.merge_l2

/-- info: 'FalconPrecision.Errors.Fixed.Rnd.cmul_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.Rnd.cmul_err

/-- info: 'FalconPrecision.RenyiPath.PathSumP.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.PathSumP.bind

/-- info: 'FalconPrecision.Errors.FFSamp.node_a1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.node_a1

/-- info: 'FalconPrecision.Errors.FFSamp.upd_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.upd_err

/-- info: 'FalconPrecision.Errors.FFSamp.InC.inB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.InC.inB

/-- info: 'FalconPrecision.Errors.FFSamp.one_le_coefA512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.one_le_coefA512

/-- info: 'FalconPrecision.Errors.FFSamp.ezU512_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ezU512_le

/-- info: 'FalconPrecision.Errors.FFSamp.l2_le_pairF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.l2_le_pairF

/-- info: 'FalconPrecision.Errors.FFSamp.pre_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.pre_err

/-- info: 'FalconPrecision.Errors.Fixed.Arith.norm_tws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.Arith.norm_tws

/-- info: 'FalconPrecision.Errors.Fixed.Rnd.arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.Rnd.arith

/-- info: 'FalconPrecision.Errors.GaussTail.tsum_pmf_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.GaussTail.tsum_pmf_mul_exp

/-- info: 'FalconPrecision.Errors.GaussTail.lintegral_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.GaussTail.lintegral_exp_le

/-- info: 'FalconPrecision.Errors.GaussTail.measure_ge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.GaussTail.measure_ge_le

/-- info: 'FalconPrecision.Errors.GaussTail.measure_le_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.GaussTail.measure_le_le

/-- info: 'FalconPrecision.Errors.GaussTail.measure_abs_ge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.GaussTail.measure_abs_ge_le

/-- info: 'FalconPrecision.Errors.GaussTail.kappa_falcon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.GaussTail.kappa_falcon

/-- info: 'FalconPrecision.Errors.GaussTail.measure_abs_ge_falcon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.GaussTail.measure_abs_ge_falcon

/-- info: 'FalconPrecision.Errors.AbortTV.etvDist_map_self_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortTV.etvDist_map_self_le

/-- info: 'FalconPrecision.Errors.AbortTV.etvDist_clamp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortTV.etvDist_clamp_le

/-- info: 'FalconPrecision.Errors.AbortTV.etvDist_simulateQ_le_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortTV.etvDist_simulateQ_le_path

/-- info: 'FalconPrecision.Errors.AbortTV.etvDist_map_clamp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortTV.etvDist_map_clamp_le

/-- info: 'FalconPrecision.Errors.AbortTV.etvDist_implT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortTV.etvDist_implT_le

/-- info: 'FalconPrecision.Errors.FFTReal.pt_cj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTReal.pt_cj

/-- info: 'FalconPrecision.Errors.FFTReal.isReal_evalAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTReal.isReal_evalAt

/-- info: 'FalconPrecision.Errors.FFTReal.im_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTReal.im_eq_zero

/-- info: 'FalconPrecision.Errors.FFTReal.isReal_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTReal.isReal_upd

/-- info: 'FalconPrecision.Errors.FFTReal.isReal_splitE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTReal.isReal_splitE

/-- info: 'FalconPrecision.Errors.FFTReal.isReal_mergeE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFTReal.isReal_mergeE

/-- info: 'FalconPrecision.Falcon.falcon512_model64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_model64

/-- info: 'FalconPrecision.Falcon.falcon512_model64n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_model64n

/-- info: 'FalconPrecision.Falcon.falcon512_proved_n64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_proved_n64

/-- info: 'FalconPrecision.Falcon.centers_budget64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.centers_budget64

/-- info: 'FalconPrecision.Falcon.centers_budget64n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.centers_budget64n

/-- info: 'FalconPrecision.Errors.FFSamp.input_err64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.input_err64

/-- info: 'FalconPrecision.Errors.FFSamp.inp64_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.inp64_base

/-- info: 'FalconPrecision.Errors.FFSamp.inp64_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.inp64_norm

/-- info: 'FalconPrecision.Errors.FFSamp.chC64_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.chC64_err

/-- info: 'FalconPrecision.Errors.FFSamp.cqC64_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.cqC64_err

/-- info: 'FalconPrecision.Errors.FFSamp.fft_cert64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.fft_cert64

/-- info: 'FalconPrecision.Errors.FFSamp.sign164_pathS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.sign164_pathS

/-- info: 'FalconPrecision.Errors.FFSamp.sign164_pathN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.sign164_pathN

/-- info: 'FalconPrecision.Errors.FFSamp.Uses64.pathS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.Uses64.pathS

/-- info: 'FalconPrecision.Errors.FFSamp.Uses64.pathN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.Uses64.pathN

/-- info: 'FalconPrecision.Errors.FFSamp.UsesG.path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.UsesG.path

/-- info: 'FalconPrecision.Errors.FFSamp.UsesG.signLoopG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.UsesG.signLoopG

/-- info: 'FalconPrecision.Errors.FFSamp.ffs64_pathS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs64_pathS

/-- info: 'FalconPrecision.Errors.FFSamp.ffs64_pathN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs64_pathN

/-- info: 'FalconPrecision.Errors.FFSamp.coef64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.coef64

/-- info: 'FalconPrecision.Errors.FFSamp.ez64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ez64

/-- info: 'FalconPrecision.Errors.FFSamp.ffs_pathSU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs_pathSU

/-- info: 'FalconPrecision.Errors.FFSamp.ffs_pathNU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs_pathNU

/-- info: 'FalconPrecision.Errors.FFSamp.node_stepU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.node_stepU

/-- info: 'FalconPrecision.Errors.Fixed.Rnd.arith64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.Rnd.arith64

/-- info: 'FalconPrecision.Errors.Fixed.Rnd.divq_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.Fixed.Rnd.divq_err

/-- info: 'FalconPrecision.Errors.FFSamp.sign164_eq_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.sign164_eq_margin

/-- info: 'FalconPrecision.Errors.FFSamp.ffs64_eq_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs64_eq_margin

/-- info: 'FalconPrecision.Errors.FFSamp.ffsU_eq_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffsU_eq_margin

/-- info: 'FalconPrecision.Errors.FFSamp.InBR.chkM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.InBR.chkM

/-- info: 'FalconPrecision.RenyiPath.PathSumP.bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.PathSumP.bind_congr

/-- info: 'FalconPrecision.Errors.FFSamp.ffs_pathNG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.ffs_pathNG

/-- info: 'FalconPrecision.Errors.FFSamp.budget64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.FFSamp.budget64

/-- info: 'FalconPrecision.Errors.AbortExact.simulateQ_clampQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.simulateQ_clampQ

/-- info: 'FalconPrecision.Errors.AbortExact.ffsG_clamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.ffsG_clamp

/-- info: 'FalconPrecision.Errors.AbortExact.sign164G_clamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.sign164G_clamp

/-- info: 'FalconPrecision.Errors.AbortExact.sign164_clamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.sign164_clamp

/-- info: 'FalconPrecision.Errors.AbortExact.etvDist_E_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.etvDist_E_X

/-- info: 'FalconPrecision.Errors.AbortExact.exp_thirty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.exp_thirty

/-- info: 'FalconPrecision.Errors.AbortExact.eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.eps_le

/-- info: 'FalconPrecision.Errors.AbortExact.isReal_t0E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.isReal_t0E

/-- info: 'FalconPrecision.Errors.AbortExact.isReal_t1E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.isReal_t1E

/-- info: 'FalconPrecision.Falcon.falcon512_exact64n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_exact64n

/-- info: 'FalconPrecision.Falcon.falcon512_exact64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_exact64

/-- info: 'FalconPrecision.RenyiPath.PathSum.inv_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.PathSum.inv_query

/-- info: 'FalconPrecision.RenyiPath.PathSum.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.PathSum.add

/-- info: 'FalconPrecision.RenyiPath.PathSum.indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.PathSum.indicator

/-- info: 'FalconPrecision.RenyiPath.PathSum.simulateQ_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.PathSum.simulateQ_map

/-- info: 'FalconPrecision.RenyiPath.etvDist_simulateQ_rewrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.RenyiPath.etvDist_simulateQ_rewrite

/-- info: 'FalconPrecision.Errors.AbortExact.etvDist_map_clampF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.etvDist_map_clampF_le

/-- info: 'FalconPrecision.Errors.AbortExact.etvDist_F_F'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.etvDist_F_F'

/-- info: 'FalconPrecision.Errors.AbortExact.exp_299' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.exp_299

/-- info: 'FalconPrecision.Errors.AbortExact.eps_leF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.eps_leF

/-- info: 'FalconPrecision.Errors.AbortExact.Swap.signLoopG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.AbortExact.Swap.signLoopG

/-- info: 'FalconPrecision.Falcon.falcon512_exact64n'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_exact64n'

/-- info: 'FalconPrecision.Falcon.falcon512_exact64'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Falcon.falcon512_exact64'

/-- info: 'FalconPrecision.Errors.HopB.falcon512_hopB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.HopB.falcon512_hopB

/-- info: 'FalconPrecision.Errors.HopB.falcon512_fixed_vs_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.HopB.falcon512_fixed_vs_true

/-- info: 'FalconPrecision.Errors.HopB.falcon512_fixed_vs_true127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.HopB.falcon512_fixed_vs_true127

/-- info: 'FalconPrecision.Errors.HopB.falcon512_fixed_vs_true63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FalconPrecision.Errors.HopB.falcon512_fixed_vs_true63
