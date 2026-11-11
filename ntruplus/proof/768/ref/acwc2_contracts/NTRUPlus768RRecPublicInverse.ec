require import AllCore IntDiv Distr.
from Jasmin require import JWord.
require import Array4 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBaseInv NTRUPlus768PolyBaseInvProof NTRUPlus768PolyBaseInvBridge.
require import NTRUPlus768KeygenCompleteInverse NTRUPlus768KeygenPublicKeyBridge.
require import NTRUPlus768ValidKeyR2Algebra NTRUPlus768R2Serialization.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.
require import NTRUPlus768CanonicalDecoder.

(* The only input is the decoded public polynomial. BaseInv computes its
   inverse; serialization and checked decoding put successful output in
   the canonical range needed by the existing asymmetric multiplication. *)
op [opaque] rrec_public_inverse (hp:W16.t Array768.t) : W16.t Array768.t option =
 if keygen_inverse_status hp=W64.zero then
 Some(r2_serialized_decode(keygen_inverse_value hp)) else None.
module RRecPublicInverse = {
 proc run(hp:W16.t Array768.t) : W16.t Array768.t option = {
  var raw,canonical:W16.t Array768.t;
  var status:W64.t; var decoded_status:W32.t;
  var bytes:W8.t Array1152.t; var result:W16.t Array768.t option;
  result<-None;
  (raw,status)<@NTRUPlus768PolyBaseInv.M.__poly_baseinv_core(witness,hp);
  if(status=W64.zero){
   bytes<@NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,raw);
   (canonical,decoded_status)<@NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,bytes);
   if(decoded_status=W32.zero){result<-Some canonical;}
  }
  return result;
 }
}.

lemma rrec_inverse_value_exact hp :
 poly_baseinv_exact_post hp (keygen_inverse_value hp) (keygen_inverse_status hp).
proof.
 rewrite /poly_baseinv_exact_post; case(poly_blocks_succeed hp 192)=>hs.
 + left; split; first by rewrite /keygen_inverse_status hs.
   split; first done.
   move=>k hk; apply Array4.tP=>i hi.
   rewrite /block4 Array4.initiE // /keygen_inverse_value hs /= Array768.initiE 1:/# /=.
   have hd:(4*k+i)%/4=k by smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod).
   have hm:(4*k+i)%%4=i by smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod).
   by rewrite hd hm.
 right; split; first by rewrite /keygen_inverse_status hs.
 split; first smt(poly_no_failure_blocks_succeed).
 by rewrite /keygen_inverse_value hs.
qed.
lemma rrec_raw_inverse_success hp :
 in_qrange768 hp => keygen_inverse_status hp=W64.zero =>
 poly_baseinv_success hp (keygen_inverse_value hp).
proof.
 move=>hr hs; exact(poly_baseinv_exact_success_semantic hp
  (keygen_inverse_value hp) (keygen_inverse_status hp) hr (rrec_inverse_value_exact hp) hs).
qed.
lemma rrec_raw_inverse_serializer hp :
 in_qrange768 hp => keygen_inverse_status hp=W64.zero =>
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange(keygen_inverse_value hp).
proof.
 move=>hr hs; apply in_qrange768_poly_tobytes_input_qrange.
 exact(poly_baseinv_success_output_qrange hp _ (rrec_raw_inverse_success hp hr hs)).
qed.
lemma rrec_tobytes_functional p0 : NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p0 =>
 hoare[NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
 rp=witness /\ ap=p0 ==> res=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p0].
proof.
 move=>hp; conseq(poly_tobytes_functional witness p0 hp)=> />.
qed.
lemma rrec_checked_normalize p0 : NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p0 =>
 hoare[NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
 rp=witness /\ ap=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p0 ==>
 res=(r2_serialized_decode p0,W32.zero)].
proof.
 move=>hp; have [_ hs]:=canonical_tobytes_roundtrip p0 hp.
 conseq(poly_frombytes_checked_functional witness (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p0))=> /> &hr _ _.
 apply W32.to_uint_eq.
 by rewrite W32.to_uint0 -/canonical_return.
qed.
lemma rrec_public_inverse_lossless : islossless RRecPublicInverse.run.
proof.
 proc; seq 2:true; 1,4,5:by auto.
 + call keygen_inverse_lossless; auto.
 if; last by auto.
 seq 2:true; 1,4,5:by auto.
 + call poly_frombytes_checked_lossless; call poly_tobytes_lossless; auto.
 if; auto.
qed.
lemma rrec_public_inverse_functional hp0 : in_qrange768 hp0 =>
 hoare[RRecPublicInverse.run : hp=hp0 ==> res=rrec_public_inverse hp0].
proof.
 move=>hq; case(keygen_inverse_status hp0=W64.zero)=>hs.
 + have hr:=rrec_raw_inverse_serializer hp0 hq hs.
   proc; rcondt 3.
   + call(keygen_inverse_functional witness hp0); auto.
   rcondt 5.
   + call(rrec_checked_normalize (keygen_inverse_value hp0) hr).
     call(rrec_tobytes_functional (keygen_inverse_value hp0) hr).
     call(keygen_inverse_functional witness hp0); auto.
   wp; call(rrec_checked_normalize (keygen_inverse_value hp0) hr).
   call(rrec_tobytes_functional (keygen_inverse_value hp0) hr).
   call(keygen_inverse_functional witness hp0); auto=> />.
   by rewrite /rrec_public_inverse hs.
 proc; rcondf 3.
 + call(keygen_inverse_functional witness hp0); auto.
 call(keygen_inverse_functional witness hp0); auto=> />.
 by rewrite /rrec_public_inverse hs.
qed.
lemma rrec_public_inverse_canonical hp : in_qrange768 hp =>
 rrec_public_inverse hp<>None => in_canonical_range768(oget(rrec_public_inverse hp)).
proof.
 move=>hq; rewrite /rrec_public_inverse; case(keygen_inverse_status hp=W64.zero)=>hs //=.
 apply r2_serialized_decode_canonical_range; exact(rrec_raw_inverse_serializer hp hq hs).
qed.
lemma rrec_public_inverse_product hp : in_qrange768 hp =>
 rrec_public_inverse hp<>None =>
 poly_basemul_qring hp (oget(rrec_public_inverse hp)) ntt_block_identity 192.
proof.
 move=>hq; rewrite /rrec_public_inverse; case(keygen_inverse_status hp=W64.zero)=>hs //=.
 have hi:=poly_baseinv_success_product_identity hp _ (rrec_raw_inverse_success hp hq hs).
 have hc:=r2_serialized_decode_mod_q (keygen_inverse_value hp) (rrec_raw_inverse_serializer hp hq hs).
 apply poly_basemul_qring_comm.
 apply(poly_basemul_qring_left_mod_q_congr (keygen_inverse_value hp)
   (r2_serialized_decode(keygen_inverse_value hp)) hp ntt_block_identity hc).
 exact(poly_basemul_qring_comm _ _ _ hi).
qed.
