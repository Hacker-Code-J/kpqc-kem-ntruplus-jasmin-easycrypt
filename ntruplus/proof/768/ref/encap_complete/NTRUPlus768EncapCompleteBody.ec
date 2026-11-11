require import AllCore Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array1153 Array32 Array96 Array192 Array224.
require import NTRUPlus768EncapCompleteSpec NTRUPlus768EncapCompleteAlgebra NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessagePrepare NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapHashGBridge.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPEncodeChecked NTRUPlus768PolySOTPEncodeCheckedProof NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768NTT NTRUPlus768NTTProof.
require import NTRUPlus768PolyBasemul NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyCenteredAdd NTRUPlus768PolyCenteredAddCorrectness NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof NTRUPlus768EncapCopyKey NTRUPlus768EncapCopyKeyProof.

lemma encap_product_functional rp0 ap0 bp0 :
  hoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp=rp0 /\ ap=ap0 /\ bp=bp0 ==> res=candidate_product_spec ap0 bp0].
proof.
  conseq (poly_basemul_functional rp0 ap0 bp0) => />.
  move=> &hr result hh; exact(candidate_product_unique _ _ result hh).
qed.

module EncapBody(G:MessageSHAKE) = {
  proc run(hp : W16.t Array768.t,coins:W8.t Array96.t,hashout:W8.t Array224.t) : W8.t Array1152.t * W8.t Array32.t = {
    var r,rhat,m,mhat,product,cipher:W16.t Array768.t;
    var serialized,ct:W8.t Array1152.t; var input:W8.t Array1153.t;
    var pad:W8.t Array192.t; var ss:W8.t Array32.t;
    r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hashout);
    rhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);
    (serialized,input) <@ NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(witness,witness,rhat);
    pad <@ G.shake(input);
    m <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,coins,pad);
    mhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,m);
    product <@ NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,hp,rhat);
    cipher <@ NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(witness,product,mhat);
    ct <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,cipher);
    ss <@ NTRUPlus768EncapCopyKey.M.jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key(witness,hashout);
    return(ct,ss);
  }
}.
lemma encap_body_functional (G<:MessageSHAKE) pk0 coins0 :
  (forall x, hoare [G.shake : input=x ==> res=message_shake_spec x]) => encap_key_canonical pk0 =>
  hoare [EncapBody(G).run : hp=decoded_poly pk0 /\ coins=coins0 /\ hashout=encap_full_hash pk0 coins0 ==>
    res=(poly_tobytes_spec(encap_full_cipher pk0 coins0),encap_full_key pk0 coins0)].
proof.
  move=> hg hk; proc.
  call(encap_copy_key_functional witness(encap_full_hash pk0 coins0)).
  call(poly_tobytes_functional witness(encap_full_cipher pk0 coins0)(encap_full_cipher_serializer pk0 coins0 hk)).
  call(poly_centered_add_functional witness(encap_full_product pk0 coins0)(encap_full_mhat pk0 coins0)
    (encap_full_product_range pk0 coins0 hk)(encap_full_mhat_centered pk0 coins0)).
  call(encap_product_functional witness(decoded_poly pk0)(encap_full_rhat pk0 coins0)).
  call(ntt_functional witness(encap_full_m pk0 coins0)).
  call(poly_sotp_encode_functional witness coins0(encap_full_pad pk0 coins0)).
  call(hg(message_hash_input(poly_tobytes_spec(encap_full_rhat pk0 coins0)))).
  call(message_prepare_functional witness witness(encap_full_rhat pk0 coins0)(encap_full_rhat_serializer pk0 coins0)).
  call(ntt_functional witness(encap_full_r pk0 coins0)).
  call(poly_cbd1_functional witness(complete_hash_tail(encap_full_hash pk0 coins0))).
  auto => />; by rewrite message_shake_hash_g.
qed.
lemma encap_body_lossless (G<:MessageSHAKE) : islossless G.shake => islossless EncapBody(G).run.
proof.
  move=> gl; proc; call encap_copy_key_lossless; call poly_tobytes_lossless; call poly_centered_add_lossless;
    call poly_basemul_lossless; call ntt_lossless; call poly_sotp_encode_lossless; call gl;
    call message_prepare_lossless; call ntt_lossless; call poly_cbd1_lossless; by auto.
qed.
