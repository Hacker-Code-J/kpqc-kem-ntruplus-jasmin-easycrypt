require import AllCore Distr IntDiv.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecProof NTRUPlus768OWUniform.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768PKECallProof.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768BasemulAlgebra.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768NTTStage1Algebra NTRUPlus768NTTAlgebra NTRUPlus768NTTProof NTRUPlus768NTT.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytes.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.
require import NTRUPlus768RRecCanonical NTRUPlus768RRecTransform NTRUPlus768RRecPublicInverse NTRUPlus768RRecAlgebra.
require import NTRUPlus768RRecLinearModel NTRUPlus768RRecLinearProcedures NTRUPlus768RRecLinearProof.
require import NTRUPlus768R2Serialization NTRUPlus768ValidKeyR2Recovery NTRUPlus768KeygenSecretFBridge.

lemma ow_encode_ntt_serializer p :
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange(ntt_spec(ow_coeff_words p)).
proof.
 rewrite ntt_specE;move=>j hj.
 have h:=forward_ntt_centered_coeff_range (ow_coeff_words p) j
  (rrec_canonical_domain_input_qrange _ (ow_coeff_words_canonical p)) hj.
 move:h;rewrite /q;smt().
qed.
lemma ow_encode_direct p : ow_encode p=
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(ntt_spec(ow_coeff_words p)).
proof.
 rewrite /ow_encode;apply(poly_tobytes_mod_q_congr _ _ (ow_encoded_terminal_serializer p) (ow_encode_ntt_serializer p)).
 rewrite /rrec_canonical_forward ntt_specE;exact(rrec_canonical_mod _).
qed.

(* Fixed 768 coefficient conversions followed by the existing extracted
   NTT/serialization kernels. These are reduction-side array procedures,
   not new exported native entry points or a machine-cost theorem. *)
module OWEncode = {
 proc run(p:NTRUPlus768CyclotomicFactorization.NTRUPoly.poly) : W8.t Array1152.t = {
  var a,h:pke_poly;var bytes:W8.t Array1152.t;
  a<-ow_coeff_words p;
  h<@NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,a);
  bytes<@NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,h);
  return bytes;
 }
}.
module OWUnitTest = {
 proc run(p:NTRUPlus768CyclotomicFactorization.NTRUPoly.poly) : bool = {
  var pk:W8.t Array1152.t;var hp:pke_poly;var status:W32.t;var inverse:pke_poly option;
  pk<@OWEncode.run(p);
  (hp,status)<@NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk);
  inverse<@RRecPublicInverse.run(hp);
  return inverse<>None;
 }
}.
module OWRecover = {
 proc run(a b:NTRUPlus768CyclotomicFactorization.NTRUPoly.poly,code:pke_poly) : NTRUPlus768CyclotomicFactorization.NTRUPoly.poly = {
  var pk,ct:W8.t Array1152.t;var answer:pke_poly option;
  pk<@OWEncode.run(a);ct<@OWEncode.run(b);
  answer<@LinearRRec.run(pk,code,ct);
  return if answer=None then NTRUPlus768CyclotomicFactorization.NTRUPoly.poly0 else input_poly(oget answer);
 }
}.
lemma ow_encode_ll : islossless OWEncode.run.
proof. proc;call poly_tobytes_lossless;call ntt_lossless;auto. qed.
lemma ow_encode_functional p0 : hoare[OWEncode.run:p=p0 ==>res=ow_encode p0].
proof.
 proc;call(rrec_tobytes_functional (ntt_spec(ow_coeff_words p0)) (ow_encode_ntt_serializer p0)).
 call(ntt_functional witness(ow_coeff_words p0));auto=> />.
 by rewrite(ow_encode_direct p0).
qed.
lemma ow_encode_correct p0 : phoare[OWEncode.run:p=p0 ==>res=ow_encode p0]=1%r.
proof. by conseq ow_encode_ll (ow_encode_functional p0). qed.
lemma ow_unit_test_ll : islossless OWUnitTest.run.
proof. proc;call rrec_public_inverse_lossless;call poly_frombytes_checked_lossless;call ow_encode_ll;auto. qed.
lemma ow_unit_test_functional p0 : hoare[OWUnitTest.run:p=p0 ==>res=ow_unit_test p0].
proof.
 proc;call(rrec_public_inverse_functional (decoded_poly(ow_encode p0))
  (rrec_public_key_range _ (ow_encode_canonical p0))).
 call(pke_decoder_functional witness(ow_encode p0));call(ow_encode_functional p0).
 auto=> />;by rewrite /ow_unit_test.
qed.
lemma ow_unit_test_correct p0 : phoare[OWUnitTest.run:p=p0 ==>res=ow_unit_test p0]=1%r.
proof. by conseq ow_unit_test_ll (ow_unit_test_functional p0). qed.
lemma ow_unit_test_semantic p0 : ow_rq_domain p0=>
 phoare[OWUnitTest.run:p=p0 ==>res=pke_rq_unit p0]=1%r.
proof. move=>hp;rewrite -(ow_unit_test_iff p0 hp);exact(ow_unit_test_correct p0). qed.
lemma ow_recover_ll : islossless OWRecover.run.
proof. proc;call linear_rrec_lossless;call ow_encode_ll;call ow_encode_ll;auto. qed.
lemma ow_recover_functional a0 b0 code0 :
 hoare[OWRecover.run:a=a0 /\ b=b0 /\ code=code0 ==>res=ow_recover a0 b0 code0].
proof.
 proc;call(linear_rrec_functional (ow_encode a0) code0 (ow_encode b0)).
 call(ow_encode_functional b0);call(ow_encode_functional a0).
 auto=> />;by rewrite /ow_recover.
qed.
lemma ow_recover_correct a0 b0 code0 :
 phoare[OWRecover.run:a=a0 /\ b=b0 /\ code=code0 ==>res=ow_recover a0 b0 code0]=1%r.
proof. by conseq ow_recover_ll (ow_recover_functional a0 b0 code0). qed.
lemma ow_recover_rlwe_call a0 secret error :
 ow_rq_domain a0=>pke_domain secret=>pke_domain error=>ow_unit_test a0=>
 phoare[OWRecover.run:a=a0 /\ b=ow_rlwe_value a0 secret error /\ code=error ==>res=input_poly secret]=1%r.
proof.
 move=>ha hs he hu;rewrite -(ow_recover_rlwe a0 secret error ha hs he hu).
 exact(ow_recover_correct a0 (ow_rlwe_value a0 secret error) error).
qed.
