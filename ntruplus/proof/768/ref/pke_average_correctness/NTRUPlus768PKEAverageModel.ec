require import AllCore Distr.
from Jasmin require import JWord.
require import Array192 Array768 Array1152.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw.
require import NTRUPlus768KEMProposalContext.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures.

(* This is the implementation's accepted fresh-key experiment. Its message
   and encryption randomness are separate uniform-buffer CBD1 samples;
   it does not identify the paper's Rq-unit-conditioned key generator. *)
module PKEAverageTrial = {
 proc run(x:kem_keygen_observation) : bool = {
  var r,m:pke_poly;
  var ct:W8.t Array1152.t option; var recovered:pke_poly option;
  var failed:bool;
  r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,x.`2);
  m <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,x.`3);
  ct <@ PKEEnc.run(x.`1.`1.`kg_pk,m,r);
  failed <- true;
  if(ct<>None){
   recovered <@ PKEDec.run(oget ct,pke_secret_bytes x.`1.`1);
   failed <- recovered<>Some m;
  }
  return failed;
 }
}.

module PKEAverage(E:KeygenExpand) = {
 proc run() : bool = {
  var x:kem_keygen_observation; var failed:bool;
  x <@ KeygenThenUniform(E).run();
  failed <@ PKEAverageTrial.run(x);
  return failed;
 }
}.

module PKEAverageObserved(E:KeygenExpand) = {
 proc run() : bool * bool = {
  var x:kem_keygen_observation; var failed:bool;
  x <@ KeygenThenUniform(E).run();
  failed <@ PKEAverageTrial.run(x);
  return(failed,!honest_no_wrap x);
 }
}.

(* The ROM variant retains unrestricted KeyGen. Initializing its two used
   tables does not assert that its rejection loops are lossless. *)
module PKEAverageROM = {
 proc run() : bool = {
  var failed:bool;
  ROE.init(); ROF.init();
  failed <@ PKEAverage(ExpandROM).run();
  return failed;
 }
}.

lemma pke_average_trial_lossless : islossless PKEAverageTrial.run.
proof.
 proc; seq 4:true; 1,4,5:by auto.
 + wp; call pke_enc_lossless; call poly_cbd1_lossless; call poly_cbd1_lossless; auto.
 if; last by auto.
 wp; call pke_dec_lossless; auto.
qed.

lemma pke_average_fresh_lossless : islossless PKEAverage(FreshExpand).run.
proof.
 proc; call pke_average_trial_lossless; call fresh_keygen_then_uniform_lossless; auto.
qed.

lemma pke_average_observed_fresh_lossless : islossless PKEAverageObserved(FreshExpand).run.
proof.
 proc; call pke_average_trial_lossless; call fresh_keygen_then_uniform_lossless; auto.
qed.
