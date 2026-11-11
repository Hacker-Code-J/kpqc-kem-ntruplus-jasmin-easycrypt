require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768 Array1152 Array1153 Array2304 Array2336.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenHBridge.
require import NTRUPlus768KeygenSamplerBridge NTRUPlus768PolyBaseInvBridge NTRUPlus768HashFProof NTRUPlus768PolyBasemulProof.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768KeygenSecretFBridge NTRUPlus768R2Serialization.
require import NTRUPlus768KEMAgreementContext NTRUPlus768DecapCompleteSpec NTRUPlus768DecapGuardSpec.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768EncapHashFPrepare NTRUPlus768EncapHashFPrepareProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768KeygenPackSK NTRUPlus768KeygenPackSKProof.

lemma keygen_pack_decap_projections fbytes hinvbytes hf :
 decap_fbytes(complete_sk_poly(keygen_pack_sk_spec fbytes hinvbytes hf))=fbytes /\
 decap_hbytes(complete_sk_poly(keygen_pack_sk_spec fbytes hinvbytes hf))=hinvbytes /\
 complete_sk_suffix(keygen_pack_sk_spec fbytes hinvbytes hf)=hf.
proof.
 have [hf0 [hh0 hs0]] := keygen_pack_sk_components fbytes hinvbytes hf.
 split.
 + rewrite /decap_fbytes /complete_sk_poly.
   apply Array1152.tP => j hj.
   rewrite Array1152.initiE 1:hj /=.
   rewrite Array2304.initiE 1:/# /=.
   rewrite keygen_pack_sk_bytes 1:/# /keygen_pack_sk_byte; smt().
 split.
 + rewrite /decap_hbytes /complete_sk_poly.
   apply Array1152.tP => j hj.
   rewrite Array1152.initiE 1:hj /=.
   rewrite Array2304.initiE 1:/# /=.
   rewrite keygen_pack_sk_bytes 1:/# /keygen_pack_sk_byte; smt().
 exact hs0.
qed.
lemma keygen_finish_layout_generic fbuf gbuf f0 g0 finv ginv h hinv pk hf :
 f0=keygen_f_ntt_spec fbuf => g0=keygen_g_ntt_spec gbuf =>
 keygen_keypair_ntt_relation f0 finv g0 ginv h hinv =>
 pk=keygen_public_key_bytes h => hf=hash_f_spec pk =>
 agreement_key_relation fbuf gbuf finv ginv h hinv pk
 (keygen_pack_sk_spec (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec f0)
 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv) hf).
proof.
 move=> hff hgg hk hp hhash; rewrite /agreement_key_relation -hff -hgg.
 split; first exact hk.
 split; first exact hp.
 have [hfb [hhb hhbhash]] := keygen_pack_decap_projections
 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec f0)
 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv) hf.
 split; first exact hfb.
 split; first exact hhb.
 rewrite -hhash; exact hhbhash.
qed.

module KeygenFinish(F : EncapSHAKEF) = {
 proc run(f:W16.t Array768.t,finv:W16.t Array768.t,g:W16.t Array768.t,ginv:W16.t Array768.t) :
  W8.t Array1152.t * W8.t Array2336.t * W16.t Array768.t * W16.t Array768.t = {
  var h,hinv:W16.t Array768.t;
  var pk,fbytes,hinvbytes:W8.t Array1152.t; var input:W8.t Array1153.t;
  var hashf:W8.t Array32.t; var sk:W8.t Array2336.t;
  (h,hinv) <@ KeygenHComposition.derive_products(f,finv,g,ginv,witness,witness);
  pk <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,h);
  fbytes <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,f);
  hinvbytes <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,hinv);
  input <@ NTRUPlus768EncapHashFPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare(witness,pk);
  hashf <@ F.shake(input);
  sk <@ NTRUPlus768KeygenPackSK.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_pack_sk(witness,fbytes,hinvbytes,hashf);
  return(pk,sk,h,hinv);
 }
}.

lemma keygen_serializer_guarded p0 :
 hoare[NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
 rp=witness /\ ap=p0 /\ NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange p0 ==>
 res=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p0].
proof.
 case(NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange p0) => hp.
 + conseq(poly_tobytes_functional witness p0 hp) => />.
 conseq (_:false ==> true) => //; smt().
qed.

op [opaque] keygen_pair_valid f finv g ginv h hinv =
 keygen_keypair_ntt_relation f finv g ginv h hinv.
lemma keygen_products_compact fbuf gbuf finv0 ginv0 :
 poly_baseinv_success(keygen_f_ntt_spec fbuf) finv0 =>
 poly_baseinv_success(keygen_g_ntt_spec gbuf) ginv0 =>
 hoare[KeygenHComposition.derive_products :
 arg=(keygen_f_ntt_spec fbuf,finv0,keygen_g_ntt_spec gbuf,ginv0,witness,witness) ==>
 keygen_pair_valid(keygen_f_ntt_spec fbuf) finv0(keygen_g_ntt_spec gbuf) ginv0 res.`1 res.`2].
proof.
 rewrite /keygen_pair_valid; exact(keygen_sampled_keypair_jasmin_calls_correct fbuf gbuf finv0 ginv0 witness witness).
qed.

lemma keygen_finish_functional (F <: EncapSHAKEF) fbuf gbuf finv0 ginv0 :
 (forall x, hoare [F.shake : input=x ==> res=encap_shake_f_spec x]) =>
 poly_baseinv_success(keygen_f_ntt_spec fbuf) finv0 =>
 poly_baseinv_success(keygen_g_ntt_spec gbuf) ginv0 =>
 hoare [KeygenFinish(F).run : f=keygen_f_ntt_spec fbuf /\ finv=finv0 /\
 g=keygen_g_ntt_spec gbuf /\ ginv=ginv0 ==>
 agreement_key_relation fbuf gbuf finv0 ginv0 res.`3 res.`4 res.`1 res.`2].
proof.
 move=> hF hfi hgi; proc.
 seq 1 : (f=keygen_f_ntt_spec fbuf /\ g=keygen_g_ntt_spec gbuf /\
 keygen_pair_valid f finv0 g ginv0 h hinv).
 + call(keygen_products_compact fbuf gbuf finv0 ginv0 hfi hgi).
   by auto => />.
 seq 3 : (f=keygen_f_ntt_spec fbuf /\ g=keygen_g_ntt_spec gbuf /\
 keygen_pair_valid f finv0 g ginv0 h hinv /\
 pk=keygen_public_key_bytes h /\
 fbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec f /\
 hinvbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv).
 + ecall(keygen_serializer_guarded hinv).
   ecall(keygen_serializer_guarded f).
   ecall(keygen_serializer_guarded h).
   skip => &hr [hf [hg hk]].
   have hkeep := hk.
   rewrite /keygen_pair_valid in hk.
   rewrite !poly_tobytes_procedure_input_qrangeE.
   have hhr := keygen_public_h_tobytes_input_qrange _ _ _ _ _ _ hk.
   have hfr := keygen_secret_f_tobytes_input_qrange _ (keygen_secret_f_qrange _ _ _ _ _ _ hk).
   have hir := keygen_hinv_tobytes_input_qrange _ _ _ _ _ _ hk.
   rewrite /keygen_public_key_bytes.
   by progress.
 seq 2 : (f=keygen_f_ntt_spec fbuf /\ g=keygen_g_ntt_spec gbuf /\
 keygen_pair_valid f finv0 g ginv0 h hinv /\
 pk=keygen_public_key_bytes h /\
 fbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec f /\
 hinvbytes=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv /\ hashf=hash_f_spec pk).
 + ecall(hF(encap_hash_f_input_spec pk)).
   ecall(encap_hash_f_prepare_functional witness pk).
   auto => /> &hr; by rewrite encap_shake_f_agreement.
 ecall(keygen_pack_sk_functional witness fbytes hinvbytes hashf).
 skip => &hr [hf [hg [hk [hp [hfb [hhb hhash]]]]]] /=.
 move=> result ->.
 rewrite /keygen_pair_valid in hk.
 rewrite hfb hhb.
 exact(keygen_finish_layout_generic fbuf gbuf f{hr} g{hr} finv0 ginv0 h{hr} hinv{hr} pk{hr} hashf{hr}
 hf hg hk hp hhash).
qed.

lemma keygen_finish_lossless (F <: EncapSHAKEF) : islossless F.shake => islossless KeygenFinish(F).run.
proof.
 move=> hF; proc; call keygen_pack_sk_lossless; call hF; call encap_hash_f_prepare_lossless;
 call poly_tobytes_lossless; call poly_tobytes_lossless; call poly_tobytes_lossless.
 inline KeygenHComposition.derive_products; wp; call poly_basemul_lossless; call poly_basemul_lossless; auto.
qed.

op [opaque] keygen_finish_output_valid fbuf gbuf finv ginv
 (r:W8.t Array1152.t * W8.t Array2336.t * W16.t Array768.t * W16.t Array768.t) =
 agreement_key_relation fbuf gbuf finv ginv r.`3 r.`4 r.`1 r.`2.

lemma keygen_finish_from_accepted (F <: EncapSHAKEF) fbuf gbuf f0 finv0 g0 ginv0 :
 (forall x,hoare[F.shake:input=x ==> res=encap_shake_f_spec x]) =>
 hoare[KeygenFinish(F).run : f=f0 /\ finv=finv0 /\ g=g0 /\ ginv=ginv0 /\
 keygen_f_accepted fbuf f0 finv0 /\ keygen_g_accepted gbuf g0 ginv0 ==>
 keygen_finish_output_valid fbuf gbuf finv0 ginv0 res].
proof.
 move=> hF; rewrite /keygen_finish_output_valid; case(keygen_f_accepted fbuf f0 finv0 /\ keygen_g_accepted gbuf g0 ginv0) => hk.
 + rewrite /keygen_f_accepted /keygen_g_accepted in hk.
   move: hk => [ [hf hfi] [hg hgi] ].
   rewrite hf in hfi; rewrite hg in hgi.
   conseq(keygen_finish_functional F fbuf gbuf finv0 ginv0 hF hfi hgi) => />; smt().
 conseq (_:false ==> true) => //; smt().
qed.
