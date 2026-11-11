require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152 Array2336.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Procedures NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ACWC2Error NTRUPlus768ACWC2Recovery NTRUPlus768ACWC2HashG.

(* The already chosen G table is preserved. Only the encryption randomness
   is sampled here, through the actual checked CBD kernel and actual
   transformed encryption/decryption procedures. *)
module ACWC2RandomTrial = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t) : bool = {
  var buf:W8.t Array192.t; var r:pke_poly; var failed:bool;
  buf <$ uniform192;
  r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);
  failed <@ ACWC2ROMRoundTrip.run(pk,sk,msg,r);
  return failed;
 }
}.
module ACWC2RandomSpec = {
 proc run(g:acwc2_g_function,pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t) : bool = {
  var buf:W8.t Array192.t;
  buf <$ uniform192;
  return acwc2_failure g pk sk msg (poly_cbd1_spec buf);
 }
}.

lemma acwc2_random_trial_lossless : islossless ACWC2RandomTrial.run.
proof.
 proc; call acwc2_rom_roundtrip_lossless; call poly_cbd1_lossless.
 rnd; auto=> />; exact uniform192_ll.
qed.
lemma acwc2_random_spec_lossless : islossless ACWC2RandomSpec.run.
proof. proc; rnd; auto=> />; exact uniform192_ll. qed.

lemma acwc2_cbd_roundtrip_functional g gm0 pk0 sk0 msg0 buf0 :
 acwc2_cache_matches g gm0 =>
 hoare[ACWC2ROMRoundTrip.run:
 pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=poly_cbd1_spec buf0 /\ ROG.m=gm0 ==>
 res=acwc2_failure g pk0 sk0 msg0 (poly_cbd1_spec buf0) /\ ROG.m=gm0].
proof.
 move=>hg.
 have hG:forall x,pke_domain x =>
   hoare[ACWC2HashG.run:r=x /\ ROG.m=gm0 ==>res=g x /\ ROG.m=gm0].
 + move=>x hx; exact(acwc2_prepared_hash_g x g gm0 hx hg).
 exact(acwc2_roundtrip_functional ACWC2HashG g (fun gm=>gm=gm0)
   pk0 sk0 msg0 (poly_cbd1_spec buf0) hG (pke_domain_cbd buf0)).
qed.
lemma acwc2_cbd_roundtrip_correct g gm0 pk0 sk0 msg0 buf0 :
 acwc2_cache_matches g gm0 =>
 phoare[ACWC2ROMRoundTrip.run:
 pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=poly_cbd1_spec buf0 /\ ROG.m=gm0 ==>
 res=acwc2_failure g pk0 sk0 msg0 (poly_cbd1_spec buf0) /\ ROG.m=gm0]=1%r.
proof.
 move=>hg; exact(acwc2_prepared_roundtrip_correct g gm0 pk0 sk0 msg0
   (poly_cbd1_spec buf0) (pke_domain_cbd buf0) hg).
qed.
lemma acwc2_random_trial_equiv g0 gm0 : acwc2_cache_matches g0 gm0 =>
 equiv[ACWC2RandomTrial.run ~ ACWC2RandomSpec.run:
 ={pk,sk,msg} /\ g{2}=g0 /\ ROG.m{1}=gm0 ==>
 ={res} /\ ROG.m{1}=gm0].
proof.
 move=>hg; proc; seq 1 1:(={pk,sk,msg,buf} /\ g{2}=g0 /\ ROG.m{1}=gm0).
 + by rnd; auto.
 wp; ecall{1}(acwc2_cbd_roundtrip_correct g0 gm0 pk{1} sk{1} msg{1} buf{1} hg).
 ecall{1}(poly_cbd1_correct witness buf{1}); auto.
qed.
lemma acwc2_random_trial_cache_preserved g gm0 : acwc2_cache_matches g gm0 =>
 phoare[ACWC2RandomTrial.run:ROG.m=gm0 ==> ROG.m=gm0]=1%r.
proof.
 move=>hg; conseq acwc2_random_trial_lossless (_:ROG.m=gm0 ==> ROG.m=gm0)=> //.
 proc; ecall(acwc2_cbd_roundtrip_functional g gm0 pk sk msg buf hg).
 ecall(poly_cbd1_functional witness buf); rnd; auto.
qed.
lemma acwc2_random_spec_probability &m g0 pk0 sk0 msg0 :
 Pr[ACWC2RandomSpec.run(g0,pk0,sk0,msg0) @ &m:res]=
 mu pke_psi1 (fun r=>acwc2_failure g0 pk0 sk0 msg0 r).
proof.
 rewrite -pke_cbd1_uniform dmapE /(\o).
 byphoare(_:g=g0 /\ pk=pk0 /\ sk=sk0 /\ msg=msg0 ==>res)=> //.
 proc; rnd; auto.
qed.
lemma acwc2_random_trial_probability &m g0 pk0 sk0 msg0 :
 acwc2_cache_matches g0 ROG.m{m} =>
 Pr[ACWC2RandomTrial.run(pk0,sk0,msg0) @ &m:res]=
 mu pke_psi1 (fun r=>acwc2_failure g0 pk0 sk0 msg0 r).
proof.
 move=>hg; rewrite -(acwc2_random_spec_probability &m g0 pk0 sk0 msg0).
 by byequiv(acwc2_random_trial_equiv g0 ROG.m{m} hg).
qed.

(* This is a conditional failure probability after fixing the accepted
   key and G table. It includes a new uniform-buffer CBD draw; no G
   reinitialization or fixed-randomness replacement occurs in the trial. *)
lemma acwc2_random_trial_error &m w g msg :
 acwc2_cache_matches g ROG.m{m} =>
 Pr[ACWC2RandomTrial.run(w.`kg_pk,w.`kg_sk,msg) @ &m:res]=acwc2_message_error w g msg.
proof.
 move=>hg; rewrite /acwc2_message_error.
 exact(acwc2_random_trial_probability &m g w.`kg_pk w.`kg_sk msg hg).
qed.

(* This entry point installs an already selected pads vector. It does not
   draw another oracle: all conditional message trials use that same G. *)
module ACWC2FixedOracleTrial = {
 proc run(pads:W8.t Array192.t list,pk:W8.t Array1152.t,sk:W8.t Array2336.t,
          msg:W8.t Array96.t) : bool = {
  var failed:bool;
  ROG.init();
  ACWC2EagerOracle.prepare(pads);
  failed <@ ACWC2RandomTrial.run(pk,sk,msg);
  return failed;
 }
}.
lemma acwc2_fixed_oracle_trial_lossless : islossless ACWC2FixedOracleTrial.run.
proof.
 proc; call acwc2_random_trial_lossless; call acwc2_prepare_lossless; call rog_init_ll; auto.
qed.
lemma acwc2_fixed_oracle_trial_equiv pads0 :
 equiv[ACWC2FixedOracleTrial.run ~ ACWC2RandomSpec.run:
 ={pk,sk,msg} /\ pads{1}=pads0 /\ g{2}=acwc2_gfun pads0 ==> ={res}].
proof.
 proc*; inline{1} ACWC2FixedOracleTrial.run; wp.
 call(acwc2_random_trial_equiv (acwc2_gfun pads0) (acwc2_g_cache pads0+empty)
   (acwc2_prepare_matches pads0)).
 inline{1} ACWC2EagerOracle.prepare ROG.init; auto.
qed.
lemma acwc2_fixed_oracle_trial_error &m w pads msg :
 Pr[ACWC2FixedOracleTrial.run(pads,w.`kg_pk,w.`kg_sk,msg) @ &m:res]=
 acwc2_message_error w (acwc2_gfun pads) msg.
proof.
 have he:Pr[ACWC2FixedOracleTrial.run(pads,w.`kg_pk,w.`kg_sk,msg) @ &m:res]=
   Pr[ACWC2RandomSpec.run(acwc2_gfun pads,w.`kg_pk,w.`kg_sk,msg) @ &m:res]
   by byequiv(acwc2_fixed_oracle_trial_equiv pads).
 by rewrite he acwc2_random_spec_probability /acwc2_message_error.
qed.
