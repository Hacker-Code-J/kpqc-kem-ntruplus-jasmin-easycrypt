require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152 Array2336 Array14466.
require import NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures NTRUPlus768SOTPContracts.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Procedures NTRUPlus768ACWC2HashG.
require import NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2Execution NTRUPlus768ACWC2Error.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768RRecLinearProcedures NTRUPlus768RRecLinearProof.

(* The encryption procedure is unchanged. This array-model decoder only
   substitutes LinearRRec for checked RRec; all guards, G calls, and SOTP
   calls retain their original order. It is not a native Decaps export. *)
module LinearACWC2Dec(G:ACWC2GPort) = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,ct:W8.t Array1152.t) : W8.t Array96.t option = {
  var code,recovered:pke_poly option; var pad:W8.t Array192.t;
  var msg:W8.t Array96.t option;
  code <@ PKEDec.run(ct,acwc2_secret_bytes sk);
  msg <- None;
  if(code<>None){
   recovered <@ LinearRRec.run(pk,oget code,ct);
   if(recovered<>None){
    pad <@ G.run(oget recovered);
    msg <@ SOTPDecode.run(oget code,pad);
   }
  }
  return msg;
 }
}.
module LinearACWC2RoundTrip(G:ACWC2GPort) = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t,r:pke_poly) : bool = {
  var ct:W8.t Array1152.t option; var decoded:W8.t Array96.t option; var failed:bool;
  ct <@ ACWC2Enc(G).run(pk,msg,r);
  failed <- true;
  if(ct<>None){
   decoded <@ LinearACWC2Dec(G).run(pk,sk,oget ct);
   failed <- decoded<>Some msg;
  }
  return failed;
 }
}.
module LinearACWC2ROMDec=LinearACWC2Dec(ACWC2HashG).
module LinearACWC2ROMRoundTrip=LinearACWC2RoundTrip(ACWC2HashG).
module LinearACWC2RandomTrial = {
 proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t) : bool = {
  var buf:W8.t Array192.t; var r:pke_poly; var failed:bool;
  buf <$ uniform192;
  r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,buf);
  failed <@ LinearACWC2ROMRoundTrip.run(pk,sk,msg,r);
  return failed;
 }
}.
module LinearACWC2FixedOracleTrial = {
 proc run(pads:W8.t Array192.t list,pk:W8.t Array1152.t,sk:W8.t Array2336.t,
          msg:W8.t Array96.t) : bool = {
  var failed:bool;
  ROG.init();
  ACWC2EagerOracle.prepare(pads);
  failed <@ LinearACWC2RandomTrial.run(pk,sk,msg);
  return failed;
 }
}.

(* Reflexive coupling of the same G call needs neither termination nor
   a functional full-oracle hypothesis. The invariant includes G state. *)
lemma linear_acwc2_dec_equiv (G<:ACWC2GPort) :
 equiv[LinearACWC2Dec(G).run ~ ACWC2Dec(G).run:
 ={pk,sk,ct,glob G} ==> ={res,glob G}].
proof.
 proc; seq 2 2:(={pk,sk,ct,code,msg,glob G}).
 + wp; call(_: ={arg} ==> ={res}); first by sim. auto.
 if; 1,3:by auto.
 seq 1 1:(={pk,sk,ct,code,msg,recovered,glob G}).
 + call linear_rrec_actual_equiv; auto.
 if; 1,3:by auto.
 call(_: ={arg} ==> ={res}); first by sim.
 call(_: ={arg,glob G} ==> ={res,glob G}); first by proc true; auto.
 auto.
qed.
lemma linear_acwc2_roundtrip_equiv (G<:ACWC2GPort) :
 equiv[LinearACWC2RoundTrip(G).run ~ ACWC2RoundTrip(G).run:
 ={pk,sk,msg,r,glob G} ==> ={res,glob G}].
proof.
 proc; seq 2 2:(={pk,sk,msg,ct,failed,glob G}).
 + wp; call(_: ={pk,msg,r,glob G} ==> ={res,glob G}); first by sim.
   auto.
 if; 1,3:by auto.
 wp; call(linear_acwc2_dec_equiv G); auto.
qed.
lemma linear_acwc2_random_trial_equiv :
 equiv[LinearACWC2RandomTrial.run ~ ACWC2RandomTrial.run:
 ={pk,sk,msg,glob ROG} ==> ={res,glob ROG}].
proof.
 proc; call(linear_acwc2_roundtrip_equiv ACWC2HashG).
 call(_: ={arg} ==> ={res}); first by sim.
 rnd; auto.
qed.
lemma linear_acwc2_fixed_oracle_trial_equiv :
 equiv[LinearACWC2FixedOracleTrial.run ~ ACWC2FixedOracleTrial.run:
 ={pads,pk,sk,msg} ==> ={res,glob ROG}].
proof.
 proc; call linear_acwc2_random_trial_equiv.
 inline ACWC2EagerOracle.prepare ROG.init; auto.
qed.
lemma linear_acwc2_fixed_oracle_failure_probability &m pads pk0 sk0 msg0 :
 Pr[LinearACWC2FixedOracleTrial.run(pads,pk0,sk0,msg0) @ &m:res]=
 Pr[ACWC2FixedOracleTrial.run(pads,pk0,sk0,msg0) @ &m:res].
proof. byequiv linear_acwc2_fixed_oracle_trial_equiv=> //. qed.
lemma linear_acwc2_fixed_oracle_error &m w pads msg :
 Pr[LinearACWC2FixedOracleTrial.run(pads,w.`kg_pk,w.`kg_sk,msg) @ &m:res]=
 acwc2_message_error w (acwc2_gfun pads) msg.
proof.
 rewrite linear_acwc2_fixed_oracle_failure_probability.
 exact(acwc2_fixed_oracle_trial_error &m w pads msg).
qed.

require import NTRUPlus768KeygenCompleteProof NTRUPlus768StoppedKeygenModel.
require import NTRUPlus768KEMProposalContext NTRUPlus768FreshRetryLaw.
require import NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Concentration NTRUPlus768ACWC2WorstCase.

lemma linear_acwc2_expected_worst_as_checked_calls &m (dk:keygen_output distr) :
 E dk(fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum
     (fun (msg:W8.t Array96.t)=>
       Pr[LinearACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])))=
 E dk(fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum
     (fun (msg:W8.t Array96.t)=>
       Pr[ACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res]))).
proof.
 apply eq_exp=>out hout /=; apply eq_exp=>pads hp /=.
 have he:(fun (msg:W8.t Array96.t)=>
   Pr[LinearACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])=
   (fun (msg:W8.t Array96.t)=>
   Pr[ACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res]).
 + apply fun_ext=>msg; exact(linear_acwc2_fixed_oracle_failure_probability &m pads _ _ msg).
 by rewrite he.
qed.

(* The same actual fresh key law, chosen oracle pads, and maximum over
   messages are retained. Only the redundant RRec verification is removed. *)
lemma linear_acwc2_fresh_worst_actual_calls &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
  (fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum
    (fun (msg:W8.t Array96.t)=>
      Pr[LinearACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])))
 <1%r/(2%r^353).
proof.
 rewrite linear_acwc2_expected_worst_as_checked_calls.
 exact(acwc2_fresh_worst_actual_calls &m).
qed.
