require import AllCore IntDiv.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768BasemulAlgebra NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require NTRUPlus768PolyFromBytesAlgebra NTRUPlus768PolyToBytesAlgebra.

(* The arithmetic decoder retains both 12-bit coefficients even when the
   canonical-status guard rejects. The following pure pack/unpack result
   does not claim that the checked option-valued decoder is injective. *)
lemma rrec_decoded_signed_coeff ct j : 0<=j<768 =>
 coeff (decoded_poly ct).[j]=NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int ct j.
proof.
 move=>hj.
 have hr:=NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_coeff_range ct j hj.
 have hs:W16.to_sint(decoded_poly ct).[j]=W16.to_uint(decoded_poly ct).[j].
 + apply NTRUPlus768PolyFromBytesAlgebra.coeff_uint_small; smt().
 rewrite /coeff hs.
 exact(NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_coeff_uint ct j hj).
qed.
lemma rrec_decoded_canonical_coeff ct j : 0<=j<768 =>
 NTRUPlus768PolyToBytesAlgebra.canonical_coeff(decoded_poly ct).[j]=
 NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int ct j.
proof.
 move=>hj; rewrite /NTRUPlus768PolyToBytesAlgebra.canonical_coeff (rrec_decoded_signed_coeff ct j hj).
 have h:=NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int_range ct j hj; smt().
qed.
lemma rrec_decoded_even ct i : 0<=i<384 =>
 NTRUPlus768PolyToBytesAlgebra.canonical_coeff(decoded_poly ct).[2*i]=
 NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int ct i.
proof.
 move=>hi; rewrite rrec_decoded_canonical_coeff 1:/# /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int.
 have hm:(2*i)%%2=0 by smt().
 have hd:(2*i)%/2=i by smt().
 by rewrite hm hd.
qed.
lemma rrec_decoded_odd ct i : 0<=i<384 =>
 NTRUPlus768PolyToBytesAlgebra.canonical_coeff(decoded_poly ct).[2*i+1]=
 NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int ct i.
proof.
 move=>hi; rewrite rrec_decoded_canonical_coeff 1:/# /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int.
 have hm:(2*i+1)%%2=1 by smt().
 have hd:(2*i+1)%/2=i by smt().
 by rewrite hm hd.
qed.

lemma rrec_reencode_byte0 ct i : 0<=i<384 =>
 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(decoded_poly ct)).[3*i]=ct.[3*i].
proof.
 move=>hi; rewrite NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec_byte0E //
 /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_byte0_int (rrec_decoded_even ct i hi)
 /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int.
 have /= h0:=W8.to_uint_cmp ct.[3*i]; have /= h1:=W8.to_uint_cmp ct.[3*i+1].
 have he:(W8.to_uint ct.[3*i]+256*(W8.to_uint ct.[3*i+1]%%16))%%256=W8.to_uint ct.[3*i] by smt().
 by rewrite he W8.to_uintK.
qed.
lemma rrec_reencode_byte1 ct i : 0<=i<384 =>
 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(decoded_poly ct)).[3*i+1]=ct.[3*i+1].
proof.
 move=>hi; rewrite NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec_byte1E //
 /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_byte1_int (rrec_decoded_even ct i hi) (rrec_decoded_odd ct i hi)
 /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int.
 have /= h0:=W8.to_uint_cmp ct.[3*i]; have /= h1:=W8.to_uint_cmp ct.[3*i+1]; have /= h2:=W8.to_uint_cmp ct.[3*i+2].
 have he:(W8.to_uint ct.[3*i]+256*(W8.to_uint ct.[3*i+1]%%16))%/256+
   16*((W8.to_uint ct.[3*i+1]%/16+16*W8.to_uint ct.[3*i+2])%%16)=W8.to_uint ct.[3*i+1] by smt(IntDiv.edivzP).
 by rewrite he W8.to_uintK.
qed.
lemma rrec_reencode_byte2 ct i : 0<=i<384 =>
 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(decoded_poly ct)).[3*i+2]=ct.[3*i+2].
proof.
 move=>hi; rewrite NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec_byte2E //
 /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_byte2_int (rrec_decoded_odd ct i hi)
 /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int.
 have /= h1:=W8.to_uint_cmp ct.[3*i+1]; have /= h2:=W8.to_uint_cmp ct.[3*i+2].
 have he:(W8.to_uint ct.[3*i+1]%/16+16*W8.to_uint ct.[3*i+2])%/16=W8.to_uint ct.[3*i+2] by smt(IntDiv.edivzP).
 by rewrite he W8.to_uintK.
qed.
lemma rrec_reencode_all ct :
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(decoded_poly ct)=ct.
proof.
 apply Array1152.tP=>j hj.
 have hi:0<=j%/3<384 by smt().
 have hm:0<=j%%3<3 by smt().
 case(j%%3=0)=>h0.
 + have he:j=3*(j%/3) by smt(IntDiv.divz_eq).
   have h:=rrec_reencode_byte0 ct (j%/3) hi; by rewrite -he in h.
 case(j%%3=1)=>h1.
 + have he:j=3*(j%/3)+1 by smt(IntDiv.divz_eq).
   have h:=rrec_reencode_byte1 ct (j%/3) hi; by rewrite -he in h.
 have he:j=3*(j%/3)+2 by smt(IntDiv.divz_eq).
 have h:=rrec_reencode_byte2 ct (j%/3) hi; by rewrite -he in h.
qed.
lemma rrec_decoded_poly_injective ct1 ct2 : decoded_poly ct1=decoded_poly ct2 =>ct1=ct2.
proof.
 move=>h.
 by rewrite -(rrec_reencode_all ct1) -(rrec_reencode_all ct2) h.
qed.
lemma rrec_canonical_reencode ct : encap_key_canonical ct =>
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(decoded_poly ct)=ct.
proof. move=>_; exact(rrec_reencode_all ct). qed.
