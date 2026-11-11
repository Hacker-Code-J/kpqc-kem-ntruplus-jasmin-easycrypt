require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152 Array2336 Array13506.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteProof.
require import NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec NTRUPlus768DecapClearProof.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDecap.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KEMPayloadSpec.
require import NTRUPlus768ValidKeyM1Recovery NTRUPlus768PolyToBytesAlgebra.

type cca_reply = W8.t Array32.t option.
op cca_status_result (ss:W8.t Array32.t) (status:W32.t) : cca_reply =
 if status=W32.zero then Some ss else None.

(* Acceptance is determined by status, including for an all-zero key. *)
lemma cca_status_accept ss : cca_status_result ss W32.zero=Some ss.
proof. by rewrite /cca_status_result. qed.
lemma cca_status_reject ss status : status<>W32.zero =>
 cca_status_result ss status=None.
proof. by move=> hs; rewrite /cca_status_result hs. qed.
lemma cca_status_some ss status key :
 cca_status_result ss status=Some key <=> status=W32.zero /\ ss=key.
proof. rewrite /cca_status_result; case(status=W32.zero); smt(). qed.
lemma cca_status_none ss status :
 cca_status_result ss status=None <=> status<>W32.zero.
proof. rewrite /cca_status_result; case(status=W32.zero); smt(). qed.
lemma cca_zero_key_is_some : cca_status_result encap_zero_ss W32.zero=Some encap_zero_ss.
proof. exact(cca_status_accept encap_zero_ss). qed.
lemma cca_zero_key_is_not_rejection : cca_status_result encap_zero_ss W32.zero<>None.
proof. by rewrite cca_status_accept. qed.

module CCAStatusAdapter = {
 proc run(ct:W8.t Array1152.t,sk:W8.t Array2336.t) : cca_reply = {
  var result:W8.t Array32.t*W32.t*W8.t Array13506.t;
  result <@ CompleteDecaps(SHAKEGROM,SHAKEHROM).run(ct,sk,witness);
  return cca_status_result result.`1 result.`2;
 }
}.

lemma cca_status_adapter_lossless : islossless CCAStatusAdapter.run.
proof.
 proc; call(complete_lossless SHAKEGROM SHAKEHROM ro_g_shake_ll ro_h_shake_ll); auto.
qed.

(* Exact relational projection: the actual guard, message, tail, and clear
   calls execute, and their shared G/H table updates are retained. *)
lemma cca_status_adapter_projection :
 equiv[CCAStatusAdapter.run ~ CompleteDecaps(SHAKEGROM,SHAKEHROM).run :
 ={ct,sk,glob ROG,glob ROH} /\ workspace{2}=witness ==>
 res{1}=cca_status_result res.`1{2} res.`2{2} /\ ={glob ROG,glob ROH}].
proof.
 proc; inline{1} CompleteDecaps(SHAKEGROM,SHAKEHROM).run; wp.
 call (_: ={workspace} ==> ={res}); first by sim.
 call (_: ={ct,sk,glob ROG,glob ROH} ==> ={res,glob ROG,glob ROH}); first by sim.
 auto.
qed.

lemma cca_status_adapter_entry_reject ct0 sk0 &m :
 !complete_entry_accepts ct0 sk0 =>
 phoare[CCAStatusAdapter.run : ct=ct0 /\ sk=sk0 /\
 ROG.m=ROG.m{m} /\ ROH.m=ROH.m{m} ==>
 res=None /\ ROG.m=ROG.m{m} /\ ROH.m=ROH.m{m}]=1%r.
proof.
 move=> hr; proc.
 call(complete_entry_reject SHAKEGROM SHAKEHROM ct0 sk0 witness &m hr).
 auto=> />; rewrite /cca_status_result; smt(W32.to_uint0 W32.to_uint1).
qed.
lemma cca_noncanonical_entry_reject ct sk :
 !encap_key_canonical ct => !complete_entry_accepts ct sk.
proof. by rewrite /complete_entry_accepts /decap_guard_accepts; smt(). qed.
lemma cca_status_adapter_noncanonical ct0 sk0 &m :
 !encap_key_canonical ct0 =>
 phoare[CCAStatusAdapter.run : ct=ct0 /\ sk=sk0 /\
 ROG.m=ROG.m{m} /\ ROH.m=ROH.m{m} ==>
 res=None /\ ROG.m=ROG.m{m} /\ ROH.m=ROH.m{m}]=1%r.
proof.
 move=> hc; exact(cca_status_adapter_entry_reject ct0 sk0 &m
   (cca_noncanonical_entry_reject ct0 sk0 hc)).
qed.

lemma cca_status_adapter_payload (w:keygen_witness) coins hout pad gm hm :
 payload_key_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv
   w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk =>
 gm.[payload_serialized hout]=Some pad =>
 hm.[(coins,complete_sk_suffix w.`kg_sk)]=Some hout =>
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf (payload_r hout) (payload_m coins pad) =>
 hoare[CCAStatusAdapter.run :
 ct=poly_tobytes_spec(payload_cipher w.`kg_pk coins hout pad) /\
 sk=w.`kg_sk /\ ROG.m=gm /\ ROH.m=hm ==>
 res=Some(payload_shared_key hout) /\ ROG.m=gm /\ ROH.m=hm].
proof.
 move=> hk hg hh hn; proc.
 call(rom_decap_success w coins hout pad gm hm witness hk hg hh hn).
 by auto=> />; rewrite cca_status_accept.
qed.
