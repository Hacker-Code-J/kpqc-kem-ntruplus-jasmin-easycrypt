require import AllCore Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768NTTProof NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolyFromBytesCheckedProof NTRUPlus768PolyCenteredAddCorrectness.
require import NTRUPlus768EncapCompleteBody NTRUPlus768DecapCandidateProof.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures.

lemma pke_decoder_functional out0 bytes0 :
 hoare[NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
 rp=out0 /\ ap=bytes0 ==> res=(decoded_poly bytes0,encap_status bytes0)].
proof.
 conseq(poly_frombytes_checked_functional out0 bytes0)=> />.
 move=> &hr; exact(encap_decoder_status ap{hr}).
qed.

lemma pke_dec_functional ct0 fbytes0 :
 hoare[PKEDec.run : ct=ct0 /\ fbytes=fbytes0 ==> res=pke_dec_spec ct0 fbytes0].
proof.
 case(encap_key_canonical ct0)=>hc; last first.
 + proc; rcondf 3.
   - call(pke_decoder_functional witness ct0); auto=> />; rewrite /encap_status hc; smt(W32.to_uint0 W32.to_uint1).
   call(pke_decoder_functional witness ct0); auto=> />; by rewrite /pke_dec_spec hc.
 case(encap_key_canonical fbytes0)=>hf; proc; rcondt 3.
 + call(pke_decoder_functional witness ct0); auto=> />; by rewrite /encap_status hc.
 + rcondt 4.
   - call(pke_decoder_functional witness fbytes0); call(pke_decoder_functional witness ct0);
     auto=> />; by rewrite /encap_status hf.
   wp; call(decap_candidate_functional witness (decoded_poly ct0) (decoded_poly fbytes0)).
   call(pke_decoder_functional witness fbytes0); call(pke_decoder_functional witness ct0).
   auto=> />; by rewrite /pke_dec_spec hc hf.
 + call(pke_decoder_functional witness ct0); auto=> />; by rewrite /encap_status hc.
 rcondf 4.
 + call(pke_decoder_functional witness fbytes0); call(pke_decoder_functional witness ct0);
   auto=> />; rewrite /encap_status hf; smt(W32.to_uint0 W32.to_uint1).
 call(pke_decoder_functional witness fbytes0); call(pke_decoder_functional witness ct0).
 auto=> />; by rewrite /pke_dec_spec hc hf.
qed.

lemma pke_dec_correct ct0 fbytes0 :
 phoare[PKEDec.run : ct=ct0 /\ fbytes=fbytes0 ==> res=pke_dec_spec ct0 fbytes0]=1%r.
proof. by conseq pke_dec_lossless (pke_dec_functional ct0 fbytes0). qed.

require import NTRUPlus768PKEAlgebra.

lemma pke_enc_body_functional pk0 m0 r0 :
 encap_key_canonical pk0 => pke_domain m0 => pke_domain r0 =>
 hoare[PKEEncBody.run : hp=decoded_poly pk0 /\ m=m0 /\ r=r0 ==>
 res=pke_ciphertext pk0 m0 r0].
proof.
 move=>hk hm hr; proc.
 call(poly_tobytes_functional witness (pke_cipher pk0 m0 r0)
   (pke_cipher_serializer pk0 m0 r0 hk hm hr)).
 call(poly_centered_add_functional witness (pke_product pk0 r0) (pke_mhat m0)
   (pke_product_range pk0 r0 hk hr) (pke_mhat_centered m0 hm)).
 call(encap_product_functional witness (decoded_poly pk0) (pke_rhat r0)).
 call(ntt_functional witness m0); call(ntt_functional witness r0).
 skip; rewrite (pke_rhatE r0) (pke_mhatE m0) (pke_productE pk0 r0)
   (pke_cipherE pk0 m0 r0) NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE
   (pke_ciphertextE pk0 m0 r0); auto.
qed.

(* The accepted plaintext domain is every ternary polynomial. Sampling
   from CBD is used only by the later average-correctness experiment. *)
lemma pke_enc_functional pk0 m0 r0 : pke_domain m0 => pke_domain r0 =>
 hoare[PKEEnc.run : pk=pk0 /\ m=m0 /\ r=r0 ==> res=pke_enc_spec pk0 m0 r0].
proof.
 move=>hm hr; case(encap_key_canonical pk0)=>hk; proc.
 + rcondt 3.
   - call(pke_decoder_functional witness pk0); auto=> />; by rewrite /encap_status hk.
   wp; call(pke_enc_body_functional pk0 m0 r0 hk hm hr).
   call(pke_decoder_functional witness pk0); auto=> />; by rewrite /pke_enc_spec hk.
 rcondf 3.
 + call(pke_decoder_functional witness pk0); auto=> />; rewrite /encap_status hk; smt(W32.to_uint0 W32.to_uint1).
 call(pke_decoder_functional witness pk0); auto=> />; by rewrite /pke_enc_spec hk.
qed.

lemma pke_enc_correct pk0 m0 r0 : pke_domain m0 => pke_domain r0 =>
 phoare[PKEEnc.run : pk=pk0 /\ m=m0 /\ r=r0 ==> res=pke_enc_spec pk0 m0 r0]=1%r.
proof. move=>hm hr; by conseq pke_enc_lossless (pke_enc_functional pk0 m0 r0 hm hr). qed.
lemma pke_enc_keyed w m0 r0 :
 pke_key_relation w => pke_domain m0 => pke_domain r0 =>
 phoare[PKEEnc.run : pk=w.`kg_pk /\ m=m0 /\ r=r0 ==>
 res=Some(pke_ciphertext w.`kg_pk m0 r0)]=1%r.
proof.
 move=>hk hm hr.
 have he:=pke_enc_accept w.`kg_pk m0 r0 (pke_key_canonical w hk).
 rewrite -he; exact(pke_enc_correct w.`kg_pk m0 r0 hm hr).
qed.

(* This is conditional recovery for every ternary plaintext and every
   ternary randomness polynomial; the no-wrap premise is explicit. *)
lemma pke_dec_no_wrap w m0 r0 :
 pke_key_relation w => pke_domain m0 => pke_domain r0 =>
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r0 m0 =>
 phoare[PKEDec.run : ct=pke_ciphertext w.`kg_pk m0 r0 /\ fbytes=pke_secret_bytes w ==>
 res=Some m0]=1%r.
proof.
 move=>hk hm hr hn.
 have hd:=pke_no_wrap_recovery w m0 r0 hk hm hr hn.
 rewrite -hd; exact(pke_dec_correct (pke_ciphertext w.`kg_pk m0 r0) (pke_secret_bytes w)).
qed.
