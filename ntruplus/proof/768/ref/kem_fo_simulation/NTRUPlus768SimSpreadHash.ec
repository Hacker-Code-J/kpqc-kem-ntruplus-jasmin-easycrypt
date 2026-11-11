require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles NTRUPlus768ROMPayloadHash.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768PKECallProof NTRUPlus768ACWC2Model NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOAlgebra.
require import NTRUPlus768FOProcedures NTRUPlus768FONativeBridge.
require import NTRUPlus768SpreadTransfer NTRUPlus768SpreadWeak.
require import NTRUPlus768RRecModel NTRUPlus768SOTPContracts.
require import NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapFinishCorrectness.
require import NTRUPlus768EncapGuardSpec NTRUPlus768SimModel.
require import NTRUPlus768FOGAdapters NTRUPlus768FOEagerG.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768SimSampling NTRUPlus768SimAnswer.
import RealOrder.

(* This is a pointwise law for a fixed key and a fixed G function.
   Only the complete H answer is sampled in this leaf experiment. *)
lemma sim_fresh_reencryption_probability w g msg ct :
 mu uniform224(fun hout=>fo_reencryption w g msg hout=Some ct)=
 spread_cipher_mass w msg g ct.
proof.
 rewrite /spread_cipher_mass -fo_randomness_law
  (dmapE uniform224 fo_randomness
   (fun r=>pke_enc_spec w.`kg_pk
     (NTRUPlus768PolySOTPEncodeAlgebra.poly_sotp_encode_spec msg(g r))r=Some ct)).
 by rewrite /(\o) /fo_reencryption /acwc2_code.
qed.

lemma sim_fresh_reencryption_bound w g msg ct : pke_key_relation w=>
 mu uniform224(fun hout=>fo_reencryption w g msg hout=Some ct)<=
 1%r/(2%r^768)+fo_error w g.
proof.
 move=>hk; rewrite sim_fresh_reencryption_probability.
 exact(spread_cipher_mass_fixed w msg g ct hk).
qed.

lemma sim_full_fresh_hash_bound w g ct pad : pke_key_relation w=>
 mu uniform224(fo_full_accept w g ct pad)<=1%r/(2%r^768)+fo_error w g.
proof.
 move=>hk.
 apply(ler_trans _ _ _ _ (sim_fresh_reencryption_bound w g (fo_candidate_message w ct pad) ct hk)).
 apply mu_le=>hout hh; by rewrite /fo_full_accept; smt().
qed.

(* The actual regeneration caller accepts arbitrary decode status words.
   The first G reply and pre-H secret computation are outside this leaf. *)
lemma sim_regenerate_functional pk0 ct0 m0 msg0 hout0 df0 g gm0 :
 encap_key_canonical pk0=>acwc2_cache_matches g gm0=>
 hoare[FORegenerateFinish(SHAKEGROM).run:
 pk=pk0 /\ ct=ct0 /\ m1=m0 /\ msg=msg0 /\ hashout=hout0 /\
 decode_fail=df0 /\ ROG.m=gm0 ==>
 res=fo_result hout0 (df0=W32.zero /\ rrec_spec pk0 m0 ct0<>None /\
   pke_enc_spec pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0)=Some ct0) /\ ROG.m=gm0].
proof.
 move=>hp hg.
 have hr:=fo_randomness_domain hout0.
 have hm:=acwc2_code_domain g msg0 (fo_randomness hout0).
 have he:=pke_enc_accept pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0) hp.
 proc; seq 6:(pk=pk0 /\ ct=ct0 /\ msg=msg0 /\ hashout=hout0 /\
  decoded=(if df0=W32.zero then Some msg0 else None) /\ recovered=rrec_spec pk0 m0 ct0 /\
  ct2=Some(pke_ciphertext pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0)) /\ ROG.m=gm0).
 + call(pke_enc_functional pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0) hm hr).
   call(sotp_encode_functional msg0 (g(fo_randomness hout0))).
   call(fo_hash_g_prepared (fo_randomness hout0) g gm0 hr hg).
   call(poly_cbd1_functional witness (complete_hash_tail hout0)).
   wp; call(fo_linear_checked_functional pk0 m0 ct0).
   skip; rewrite fo_randomnessE fo_codeE he; auto.
 rcondt 4; first by auto.
 call(finish_functional witness hout0 ct0
   (pke_ciphertext pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0))
   (df0<>W32.zero \/ rrec_spec pk0 m0 ct0=None)).
 auto=> />; rewrite he /= fo_finish_option_result.
 case(df0=W32.zero); auto.
qed.

module SimFreshRegenerate = {
 proc run(q:sim_request) : W8.t Array32.t * W32.t = {
  var hout:W8.t Array224.t;
  var result:W8.t Array32.t * W32.t;
  hout <$ uniform224;
  result <@ FORegenerateFinish(SHAKEGROM).run(q.`sr_pk,q.`sr_ct,q.`sr_code,q.`sr_msg,hout,q.`sr_fail);
  return result;
 }
}.

lemma sim_fresh_regenerate_lossless : islossless SimFreshRegenerate.run.
proof.
 proc; call(fo_regenerate_finish_lossless SHAKEGROM ro_g_shake_ll).
 auto=> />; exact uniform224_ll.
qed.

lemma sim_fo_result_status hout accept :
 ((fo_result hout accept).`2=W32.zero)=accept.
proof. case accept; rewrite /fo_result /=; smt(W32.to_uint0 W32.to_uint1). qed.

lemma sim_regenerate_correct pk0 ct0 m0 msg0 hout0 df0 g gm0 :
 encap_key_canonical pk0=>acwc2_cache_matches g gm0=>
 phoare[FORegenerateFinish(SHAKEGROM).run:
 pk=pk0 /\ ct=ct0 /\ m1=m0 /\ msg=msg0 /\ hashout=hout0 /\
 decode_fail=df0 /\ ROG.m=gm0 ==>
 res=fo_result hout0 (df0=W32.zero /\ rrec_spec pk0 m0 ct0<>None /\
   pke_enc_spec pk0 (acwc2_code g msg0 (fo_randomness hout0)) (fo_randomness hout0)=Some ct0) /\ ROG.m=gm0]=1%r.
proof.
 move=>hp hg; by conseq(fo_regenerate_finish_lossless SHAKEGROM ro_g_shake_ll)
  (sim_regenerate_functional pk0 ct0 m0 msg0 hout0 df0 g gm0 hp hg).
qed.

lemma sim_fresh_regenerate_frame q0 g gm0 :
 encap_key_canonical q0.`sr_pk=>acwc2_cache_matches g gm0=>
 hoare[SimFreshRegenerate.run:q=q0 /\ ROG.m=gm0 ==>ROG.m=gm0].
proof.
 move=>hp hg; proc.
 ecall(sim_regenerate_functional q0.`sr_pk q0.`sr_ct q0.`sr_code q0.`sr_msg hout q0.`sr_fail g gm0 hp hg).
 auto.
qed.

lemma sim_fresh_regenerate_bound w g q0 gm0 :
 pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>
 phoare[SimFreshRegenerate.run:q=q0 /\ ROG.m=gm0 ==>res.`2=W32.zero]
 <=(1%r/(2%r^768)+fo_error w g).
proof.
 move=>hk hp hg.
 have hc:encap_key_canonical q0.`sr_pk by rewrite hp; exact(pke_key_canonical w hk).
 proc; seq 1:(fo_reencryption w g q0.`sr_msg hout=Some q0.`sr_ct)
  (1%r/(2%r^768)+fo_error w g) 1%r 1%r 0%r (q=q0 /\ ROG.m=gm0)=> //.
 + by auto.
 + rnd (fun hout=>fo_reencryption w g q0.`sr_msg hout=Some q0.`sr_ct).
   skip; auto=> />; exact(sim_fresh_reencryption_bound w g q0.`sr_msg q0.`sr_ct hk).
 hoare.
 ecall(sim_regenerate_functional q0.`sr_pk q0.`sr_ct q0.`sr_code q0.`sr_msg hout q0.`sr_fail g gm0 hc hg).
 auto=> /> &hr hbad.
 by rewrite sim_fo_result_status hp -/(fo_reencryption w g q0.`sr_msg hout{hr}) hbad /=.
qed.

lemma sim_regenerate_g_actual :
 equiv[FORegenerateFinish(FOGHash(FOGActual)).run ~ FORegenerateFinish(SHAKEGROM).run:
 ={arg,ROG.m} ==> ={res,ROG.m}].
proof. proc; sim. qed.

(* Freshness is in the physical H table. The sampled response remains
   stored there, so subsequent public queries receive the same value. *)
lemma sim_answer_fresh_actual q0 hm0 :
 equiv[SimAnswerReal(FOGActual,SimHActual).answer ~ SimFreshRegenerate.run:
 ={q,ROG.m} /\ q{1}=q0 /\ ROH.m{1}=hm0 /\ sim_h_input q0 \notin hm0 ==>
 res{1}=cca_status_result res.`1{2} res.`2{2} /\ ={ROG.m} /\ cache_extends hm0 ROH.m{1}].
proof.
 proc; call sim_regenerate_g_actual.
 inline{1} ROH.get; sp; rcondt{1} 1; first by auto.
 wp; rnd; auto=> />.
 move=>hfresh hout hh; rewrite get_set_sameE /=.
 exact(cache_extends_fresh hm0 (sim_h_input q0) hout hfresh).
qed.

lemma sim_answer_actual_fresh_probability q0 hm0 &m :
 ROH.m{m}=hm0=>sim_h_input q0 \notin hm0=>
 Pr[SimAnswerReal(FOGActual,SimHActual).answer(q0) @ &m:res<>None]=
 Pr[SimFreshRegenerate.run(q0) @ &m:res.`2=W32.zero].
proof.
 move=>hm hf.
 byequiv(sim_answer_fresh_actual q0 hm0)=> //.
 smt(cca_status_none).
qed.

lemma sim_answer_actual_fresh_frame q0 g gm0 hm0 :
 encap_key_canonical q0.`sr_pk=>acwc2_cache_matches g gm0=>
 hoare[SimAnswerReal(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 /\ sim_h_input q0 \notin hm0 ==>
 ROG.m=gm0 /\ cache_extends hm0 ROH.m].
proof.
 move=>hp hg.
 conseq(sim_answer_fresh_actual q0 hm0) (sim_fresh_regenerate_frame q0 g gm0 hp hg); smt().
qed.

lemma sim_answer_actual_fresh_bound w g q0 gm0 hm0 :
 pke_key_relation w=>q0.`sr_pk=w.`kg_pk=>acwc2_cache_matches g gm0=>
 sim_h_input q0 \notin hm0=>
 phoare[SimAnswerReal(FOGActual,SimHActual).answer:
 q=q0 /\ ROG.m=gm0 /\ ROH.m=hm0 ==>res<>None]
 <=(1%r/(2%r^768)+fo_error w g).
proof.
 move=>hk hp hg hf; bypr=> &m [hq [hgm hhm]].
 rewrite hq (sim_answer_actual_fresh_probability q0 hm0 &m hhm hf).
 byphoare(sim_fresh_regenerate_bound w g q0 gm0 hk hp hg)=> //.
qed.
