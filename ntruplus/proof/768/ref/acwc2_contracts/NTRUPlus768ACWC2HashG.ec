require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array192 Array768 Array1152 Array1153.
require import NTRUPlus768PKEModel NTRUPlus768RRecCodec.
require import NTRUPlus768NTT NTRUPlus768NTTProof NTRUPlus768NTTAlgebra.
require import NTRUPlus768DecapMessagePrepare NTRUPlus768DecapMessagePrepareProof.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyToBytesProof.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMDomains NTRUPlus768ROMOracles.
require import NTRUPlus768ROMPayloadHash NTRUPlus768CCAQueryCodec.

op [opaque] rr_G_query (r:pke_poly) : W8.t Array1153.t = encode_g(rr_G_input r).

(* The existing extracted NTT and message-preparation kernels compute the
   1152-byte payload and its tag-1, 1153-byte query. The SHAKE call below is
   the ROM wrapper, not a claim about the concrete SHAKE distribution. *)
module ACWC2GPrepare = {
 proc run(r:pke_poly) : W8.t Array1152.t * W8.t Array1153.t = {
  var rhat:pke_poly; var serialized:W8.t Array1152.t; var input:W8.t Array1153.t;
  rhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
  (serialized,input) <@ NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(witness,witness,rhat);
  return(serialized,input);
 }
}.
module ACWC2HashG = {
 proc run(r:pke_poly) : W8.t Array192.t = {
  var serialized:W8.t Array1152.t; var input:W8.t Array1153.t; var pad:W8.t Array192.t;
  (serialized,input) <@ ACWC2GPrepare.run(r);
  pad <@ SHAKEGROM.shake(input);
  return pad;
 }
}.

lemma acwc2_g_query_tag r : (rr_G_query r).[0]=W8.one.
proof. rewrite /rr_G_query; exact(encode_g_tag _). qed.
lemma acwc2_g_query_payload r : peel1153(rr_G_query r)=rr_G_input r.
proof. rewrite /rr_G_query; exact(peel_encode_g _). qed.
lemma acwc2_g_payload_length r : size(Array1152.to_list(rr_G_input r))=1152.
proof. exact(Array1152.size_to_list _). qed.
lemma acwc2_g_query_raw r : Array1153.to_list(rr_G_query r)=raw_query(G(rr_G_input r)).
proof. by rewrite /rr_G_query. qed.
lemma acwc2_g_query_typed r :
 decode_typed(Array1153.to_list(rr_G_query r))=Some(G(rr_G_input r)).
proof. rewrite acwc2_g_query_raw; exact(decode_typed_encode _). qed.
lemma acwc2_g_query_length r : size(Array1153.to_list(rr_G_query r))=1153.
proof. rewrite acwc2_g_query_raw; exact(raw_g_length _). qed.
lemma acwc2_g_query_injective r s :
 pke_domain r => pke_domain s => rr_G_query r=rr_G_query s => r=s.
proof.
 move=>hr hs; rewrite /rr_G_query=>he.
 exact(rr_G_input_injective r s hr hs (encode_g_inj _ _ he)).
qed.
lemma acwc2_g_raw_injective r s : pke_domain r => pke_domain s =>
 raw_query(G(rr_G_input r))=raw_query(G(rr_G_input s)) => r=s.
proof.
 move=>hr hs; rewrite -!acwc2_g_query_raw=>he.
 exact(acwc2_g_query_injective r s hr hs (Array1153.to_list_inj _ _ he)).
qed.

lemma acwc2_g_prepare_lossless : islossless ACWC2GPrepare.run.
proof. proc; call message_prepare_lossless; call ntt_lossless; auto. qed.
lemma acwc2_hash_g_lossless : islossless ACWC2HashG.run.
proof. proc; call ro_g_shake_ll; call acwc2_g_prepare_lossless; auto. qed.
lemma acwc2_g_prepare_functional r0 :
 hoare[ACWC2GPrepare.run:r=r0 /\ pke_domain r0 ==>
 res=(rr_G_input r0,rr_G_query r0)].
proof.
 case(pke_domain r0)=>hr; last by conseq (_:false ==>true)=> //; smt().
 proc; call(message_prepare_functional witness witness (pke_rhat r0) (rr_G_input_serializer r0 hr)).
 call(ntt_functional witness r0); auto=> />.
 by rewrite pke_rhatE /rr_G_query rr_G_inputE !poly_tobytes_procedure_specE payload_g_preparation.
qed.
lemma acwc2_g_prepare_correct r0 :
 phoare[ACWC2GPrepare.run:r=r0 /\ pke_domain r0 ==>
 res=(rr_G_input r0,rr_G_query r0)]=1%r.
proof. by conseq acwc2_g_prepare_lossless (acwc2_g_prepare_functional r0). qed.

lemma acwc2_shake_g_equiv :
 equiv[SHAKEGROM.shake ~ ROG.get:
 input{1}=encode_g input{2} /\ ={glob ROG} ==> ={res,glob ROG}].
proof.
 proc*; inline{1} SHAKEGROM.shake; wp.
 call(_: ={input,glob ROG} ==> ={res,glob ROG}); first by sim.
 auto=> /> &hr; exact(peel_encode_g input{hr}).
qed.
lemma acwc2_hash_g_equiv :
 equiv[ACWC2HashG.run ~ ROG.get:
 pke_domain r{1} /\ input{2}=rr_G_input r{1} /\ ={glob ROG} ==> ={res,glob ROG}].
proof.
 proc*; inline{1} ACWC2HashG.run; wp.
 call acwc2_shake_g_equiv.
 ecall{1}(acwc2_g_prepare_correct r{1}); auto=> />; by rewrite /rr_G_query.
qed.

(* Every old entry is preserved. A cached query reuses its stored value
   and leaves the entire table unchanged; it is not resampled uniformly. *)
lemma acwc2_hash_g_value r0 gm0 :
 hoare[ACWC2HashG.run:r=r0 /\ pke_domain r0 /\ ROG.m=gm0 ==>
 ROG.m.[rr_G_input r0]=Some res /\ cache_extends gm0 ROG.m /\
 size(Array192.to_list res)=192].
proof.
 proc; call(ro_g_shake_value gm0 (rr_G_input r0)).
 call(acwc2_g_prepare_functional r0); auto=> />.
 rewrite /rr_G_query; smt(Array192.size_to_list).
qed.
lemma acwc2_hash_g_cached r0 gm0 pad0 :
 hoare[ACWC2HashG.run:r=r0 /\ pke_domain r0 /\ ROG.m=gm0 /\
 gm0.[rr_G_input r0]=Some pad0 ==> res=pad0 /\ ROG.m=gm0].
proof.
 proc; call(ro_g_shake_cached gm0 (rr_G_input r0) pad0).
 call(acwc2_g_prepare_functional r0); auto=> />; by rewrite /rr_G_query.
qed.
lemma acwc2_hash_g_preserves r0 old pad0 :
 hoare[ACWC2HashG.run:r=r0 /\ pke_domain r0 /\ ROG.m.[old]=Some pad0 ==>
 ROG.m.[old]=Some pad0].
proof.
 proc; inline SHAKEGROM.shake; wp.
 call(rog_get_preserves old pad0); wp; call(acwc2_g_prepare_functional r0); auto.
qed.

lemma acwc2_rog_fresh_event gm0 x0 event :
 phoare[ROG.get:ROG.m=gm0 /\ input=x0 /\ x0 \notin gm0 ==> event res]
 =(mu uniform192 event).
proof.
 proc; rcondt 1; first by auto.
 wp; rnd event; auto=> />.
 move=>hx v hv; by rewrite get_set_sameE /=.
qed.
lemma acwc2_hash_g_probability &m r0 event : pke_domain r0 =>
 Pr[ACWC2HashG.run(r0) @ &m:event res]=
 Pr[ROG.get(rr_G_input r0) @ &m:event res].
proof. move=>hr; byequiv acwc2_hash_g_equiv=> //; smt(). qed.

(* The freshness premise is essential: this exact uniform law applies
   only to a new serialized randomness input in the current G table. *)
lemma acwc2_hash_g_fresh_law &m r0 event :
 pke_domain r0 => rr_G_input r0 \notin ROG.m{m} =>
 Pr[ACWC2HashG.run(r0) @ &m:event res]=mu uniform192 event.
proof.
 move=>hr hf; rewrite(acwc2_hash_g_probability &m r0 event hr).
 byphoare(acwc2_rog_fresh_event ROG.m{m} (rr_G_input r0) event)=> //.
qed.
