require import AllCore Distr.
from Jasmin require import JWord.
require import Array768.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBaseInv NTRUPlus768PolyBaseInvBridge NTRUPlus768PolyBaseInvProof.
require import NTRUPlus768KeygenCompleteInverse.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecInverseAlgebra.

(* An inverse in the product of the actual 192 terminal quartics. The
   equivalence with the coefficient-domain quotient ring is proved separately. *)
op [opaque] gen_terminal_unit (a:W16.t Array768.t) : bool =
 exists inverse, poly_basemul_qring a inverse ntt_block_identity 192.

lemma gen_inverse_status_iff a :
 in_qrange768 a =>
 (keygen_inverse_status a=W64.zero <=> gen_terminal_unit a).
proof.
 move=>ha; rewrite /gen_terminal_unit; split.
 + move=>hs; exists(keygen_inverse_value a).
   exact(poly_baseinv_success_product_identity a _ (rrec_raw_inverse_success a ha hs)).
 move=>[inverse hi]; exact(rrec_known_inverse_status a inverse ha hi).
qed.

lemma gen_inverse_reject_iff a :
 in_qrange768 a =>
 (keygen_inverse_status a=W64.one <=> !gen_terminal_unit a).
proof.
 move=>ha.
 have hc : (keygen_inverse_status a=W64.one) = !(keygen_inverse_status a=W64.zero).
 + rewrite /keygen_inverse_status; case(poly_blocks_succeed a 192)=> /=;
   smt(poly_baseinv_w64_zero_neq_one).
 by rewrite hc (gen_inverse_status_iff a ha).
qed.

lemma gen_inverse_value_product a :
 in_qrange768 a => gen_terminal_unit a =>
 poly_basemul_qring a (keygen_inverse_value a) ntt_block_identity 192.
proof.
 move=>ha hu; have hs:=iffRL _ _ (gen_inverse_status_iff a ha) hu.
 exact(poly_baseinv_success_product_identity a _ (rrec_raw_inverse_success a ha hs)).
qed.

(* This is the complete PolyBaseInv core's failure behavior. Scalar BaseInv
   alone instead retains its input output-buffer on failure. *)
lemma gen_inverse_reject_zero a :
 in_qrange768 a => !gen_terminal_unit a => keygen_inverse_value a=poly_zero.
proof.
 move=>ha hu; have hs:=iffRL _ _ (gen_inverse_reject_iff a ha) hu.
 exact(poly_baseinv_exact_failure_zero a (keygen_inverse_value a)
   (keygen_inverse_status a) (rrec_inverse_value_exact a) hs).
qed.

lemma gen_inverse_core_functional rp0 a0 :
 in_qrange768 a0 =>
 hoare[NTRUPlus768PolyBaseInv.M.__poly_baseinv_core : rp=rp0 /\ ap=a0 ==>
   res=(keygen_inverse_value a0,keygen_inverse_status a0) /\
   (res.`2=W64.zero <=> gen_terminal_unit a0) /\
   (res.`2=W64.one <=> !gen_terminal_unit a0) /\
   (res.`2=W64.zero => poly_basemul_qring a0 res.`1 ntt_block_identity 192) /\
   (res.`2=W64.one => res.`1=poly_zero)].
proof.
 move=>ha.
 have hs:=gen_inverse_status_iff a0 ha.
 have hf:=gen_inverse_reject_iff a0 ha.
 have hp:=gen_inverse_value_product a0 ha.
 have hz:=gen_inverse_reject_zero a0 ha.
 conseq(keygen_inverse_functional rp0 a0)=> /> &hr ->.
 split.
 + move=>h; apply hp; exact(iffLR _ _ hs h).
 move=>h; apply hz; exact(iffLR _ _ hf h).
qed.

lemma gen_inverse_core_correct rp0 a0 :
 in_qrange768 a0 =>
 phoare[NTRUPlus768PolyBaseInv.M.__poly_baseinv_core : rp=rp0 /\ ap=a0 ==>
   res=(keygen_inverse_value a0,keygen_inverse_status a0) /\
   (res.`2=W64.zero <=> gen_terminal_unit a0) /\
   (res.`2=W64.one <=> !gen_terminal_unit a0) /\
   (res.`2=W64.zero => poly_basemul_qring a0 res.`1 ntt_block_identity 192) /\
   (res.`2=W64.one => res.`1=poly_zero)] = 1%r.
proof.
 move=>ha; by conseq keygen_inverse_lossless (gen_inverse_core_functional rp0 a0 ha).
qed.
