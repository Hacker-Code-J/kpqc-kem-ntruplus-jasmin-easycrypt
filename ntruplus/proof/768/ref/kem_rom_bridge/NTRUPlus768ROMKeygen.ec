require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array1152 Array1153 Array2304 Array2336.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenHBridge NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768KeygenSamplerBridge NTRUPlus768PolyBaseInvBridge NTRUPlus768HashFProof NTRUPlus768PolyBasemulProof.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768KeygenSecretFBridge NTRUPlus768R2Serialization.
require import NTRUPlus768KEMAgreementContext NTRUPlus768DecapCompleteSpec NTRUPlus768DecapGuardSpec.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768EncapHashFPrepare NTRUPlus768EncapHashFPrepareProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768KeygenPackSK NTRUPlus768KeygenPackSKProof.

require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteFinish NTRUPlus768KeygenCompleteRetry NTRUPlus768KeygenClearProof NTRUPlus768KeygenInverseBridge.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768ROMOracles NTRUPlus768ROMDomains NTRUPlus768ROMPayloadHash.


op [opaque] rom_key_relation (w:keygen_witness)
    (fm:(W8.t Array1152.t,W8.t Array32.t) fmap) =
  payload_key_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv
    w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk /\
  fm.[w.`kg_pk]=Some (complete_sk_suffix w.`kg_sk).

op [opaque] rom_raw_finish_valid f0 finv0 g0 ginv0
 (r:W8.t Array1152.t * W8.t Array2336.t * W16.t Array768.t * W16.t Array768.t)
 (fm:(W8.t Array1152.t,W8.t Array32.t) fmap) =
 keygen_keypair_ntt_relation f0 finv0 g0 ginv0 r.`3 r.`4 /\
 r.`1=keygen_public_key_bytes r.`3 /\
 decap_fbytes(complete_sk_poly r.`2)=keygen_secret_f_bytes f0 /\
 decap_hbytes(complete_sk_poly r.`2)=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec r.`4 /\
 fm.[r.`1]=Some(complete_sk_suffix r.`2).

lemma rom_keygen_finish_raw (f0 g0 finv0 ginv0:W16.t Array768.t) :
 in_qrange768 f0 => in_qrange768 g0 =>
 poly_baseinv_success f0 finv0 => poly_baseinv_success g0 ginv0 =>
 hoare[KeygenFinish(SHAKEFROM).run:f=f0 /\ finv=finv0 /\ g=g0 /\ ginv=ginv0 ==>
 rom_raw_finish_valid f0 finv0 g0 ginv0 res ROF.m].
proof.
 move=> hfr hgr hfi hgi; proc.
 seq 1 : (f=f0 /\ g=g0 /\ keygen_pair_valid f0 finv0 g0 ginv0 h hinv).
 + rewrite /keygen_pair_valid.
   call(keypair_products_jasmin_calls_correct f0 finv0 g0 ginv0 witness witness hfr hgr hfi hgi).
   by wp; skip => />.
 seq 3 : (f=f0 /\ g=g0 /\ keygen_pair_valid f0 finv0 g0 ginv0 h hinv /\
 pk=keygen_public_key_bytes h /\
 fbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec f0 /\
 hinvbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv).
 + ecall(keygen_serializer_guarded hinv).
   ecall(keygen_serializer_guarded f0).
   ecall(keygen_serializer_guarded h).
   skip => &hr [hf [hg hk]].
   have hkeep := hk; rewrite /keygen_pair_valid in hk.
   rewrite !poly_tobytes_procedure_input_qrangeE.
   have hhr := keygen_public_h_tobytes_input_qrange f0 finv0 g0 ginv0 h{hr} hinv{hr} hk.
   have hsr := keygen_secret_f_tobytes_input_qrange f0 (keygen_secret_f_qrange f0 finv0 g0 ginv0 h{hr} hinv{hr} hk).
   have hir := keygen_hinv_tobytes_input_qrange f0 finv0 g0 ginv0 h{hr} hinv{hr} hk.
   rewrite /keygen_public_key_bytes; by progress.
 seq 2 : (f=f0 /\ g=g0 /\ keygen_pair_valid f0 finv0 g0 ginv0 h hinv /\
 pk=keygen_public_key_bytes h /\
 fbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec f0 /\
 hinvbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv /\ ROF.m.[pk]=Some hashf).
 + ecall(rom_f_value pk); ecall(encap_hash_f_prepare_functional witness pk); by wp; skip => />.
 ecall(keygen_pack_sk_functional witness fbytes hinvbytes hashf).
 skip => &hr [hf [hg [hk [hp [hfb [hhb hhash]]]]]] /=; move=> result ->.
 rewrite /rom_raw_finish_valid; rewrite /keygen_pair_valid in hk.
 have [hfb' [hhb' hs']] := keygen_pack_decap_projections fbytes{hr} hinvbytes{hr} hashf{hr}.
 split; first exact hk.
 split; first exact hp.
 split.
 + rewrite hfb' /keygen_secret_f_bytes; exact hfb.
 split.
 + rewrite hhb'; exact hhb.
 rewrite hs'; exact hhash.
qed.

op [opaque] rom_finish_valid fbuf gbuf finv ginv
    (r:W8.t Array1152.t * W8.t Array2336.t * W16.t Array768.t * W16.t Array768.t)
    (fm:(W8.t Array1152.t,W8.t Array32.t) fmap) =
  payload_key_relation fbuf gbuf finv ginv r.`3 r.`4 r.`1 r.`2 /\
  fm.[r.`1]=Some (complete_sk_suffix r.`2).

lemma rom_keygen_finish_from_accepted fbuf gbuf f0 finv0 g0 ginv0 :
 hoare[KeygenFinish(SHAKEFROM).run : f=f0 /\ finv=finv0 /\ g=g0 /\ ginv=ginv0 /\
 keygen_f_accepted fbuf f0 finv0 /\ keygen_g_accepted gbuf g0 ginv0 ==>
 rom_finish_valid fbuf gbuf finv0 ginv0 res ROF.m].
proof.
 case(keygen_f_accepted fbuf f0 finv0 /\ keygen_g_accepted gbuf g0 ginv0) => hk.
 + rewrite /keygen_f_accepted /keygen_g_accepted in hk.
   move: hk => [[hf hfi] [hg hgi]].
   have hfr:=keygen_f_ntt_qrange fbuf.
   have hgr:=keygen_g_ntt_qrange gbuf.
   rewrite -hf in hfr; rewrite -hg in hgr.
   conseq(rom_keygen_finish_raw f0 g0 finv0 ginv0 hfr hgr hfi hgi).
   move=> &hr hpre result m H.
   rewrite /rom_finish_valid /payload_key_relation.
   rewrite -hf -hg.
   rewrite /rom_raw_finish_valid in H.
   move: H => [hr [hp [hfb [hh hm]]]].
   split.
   - split; first exact hr.
     split; first exact hp.
     split; first exact hfb.
     split; first exact hh.
     done.
   exact hm.
 conseq (_:false ==> true) => //; smt().
qed.

lemma rom_keygen_instrumented (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF}) :
 hoare[KeygenInstrumented(R,E,SHAKEFROM).run:true ==>
   rom_key_relation res.`1 ROF.m /\ res.`2=keygen_clear_zero_spec].
proof.
 proc; ecall(keygen_clear_functional workspace).
 seq 2 : (keygen_f_accepted fbuf f finv /\ keygen_g_accepted gbuf g ginv).
 + call(keygen_retry_g_accepted R E); call(keygen_retry_f_accepted R E); auto.
 ecall(rom_keygen_finish_from_accepted fbuf gbuf f finv g ginv).
 auto => /> &hr hf hg result fm hout.
 rewrite /rom_finish_valid /= in hout.
 by rewrite /rom_key_relation /=.
qed.

lemma rom_keygen_public (R<:KeygenSeedRNG {-ROF}) (E<:KeygenExpand {-ROF}) :
 hoare[Keygen(R,E,SHAKEFROM).run:true ==>
   exists (w:keygen_witness), rom_key_relation w ROF.m /\ res=(w.`kg_pk,w.`kg_sk)].
proof.
 proc; call(rom_keygen_instrumented R E).
 auto => /> result fm hv hc; exists (result.`1); done.
qed.
