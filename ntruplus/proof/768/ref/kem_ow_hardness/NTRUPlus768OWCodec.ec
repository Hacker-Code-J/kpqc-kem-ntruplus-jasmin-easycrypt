require import AllCore IntDiv Ring.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics NTRUPlus768ForwardNTTStage1Semantics.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution NTRUPlus768CanonicalDecoder.
require import NTRUPlus768PolyToBytesAlgebra NTRUPlus768RRecCanonical NTRUPlus768RRecTransform.
require import NTRUPlus768RRecPublicInverse NTRUPlus768RRecLinearModel NTRUPlus768GenKeyProjection NTRUPlus768KeygenGlobalUnit.

(* External hardness inputs are ordinary F_q polynomials of coefficient
   length at most 768. These finite word arrays are an internal codec only. *)
op [opaque] ow_coeff_words (p:NTRUPoly.poly) : pke_poly =
 Array768.init(fun i=>W16.of_int(CycloFq.asint (NTRUPoly."_.[_]" p i))).
op [opaque] ow_encode (p:NTRUPoly.poly) : W8.t Array1152.t =
 NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(rrec_canonical_forward(ow_coeff_words p)).
op [opaque] ow_decode (bytes:W8.t Array1152.t) : pke_poly =
 rrec_canonical_inverse(decoded_poly bytes).
op [opaque] ow_key_poly (bytes:W8.t Array1152.t) : NTRUPoly.poly = input_poly(ow_decode bytes).

(* The status of the existing finite public inversion kernel decides the
   unit guard. The proof identifies it with genuine R_q invertibility. *)
op [opaque] ow_unit_test (a:NTRUPoly.poly) : bool =
 rrec_public_inverse(decoded_poly(ow_encode a))<>None.
(* The ring result is computed using public finite kernels. Independent
   relation and uniqueness theorems identify it with a*s+e in R_q. *)
op [opaque] ow_rlwe_value (a:NTRUPoly.poly) (secret error:pke_poly) : NTRUPoly.poly =
 ow_key_poly(pke_ciphertext(ow_encode a)error secret).
(* Public subtraction, unit inversion and inverse NTT recover a candidate
   secret. The invalid/nonunit branch is explicit and has no inverse value. *)
op [opaque] ow_recover (a b:NTRUPoly.poly) (code:pke_poly) : NTRUPoly.poly =
 let answer=rrec_linear_spec(ow_encode a)code(ow_encode b) in
 if answer=None then NTRUPoly.poly0 else input_poly(oget answer).

lemma ow_decode_poly bytes : ow_key_poly bytes=gen_inverse_poly(decoded_poly bytes).
proof.
 rewrite /ow_key_poly /ow_decode /rrec_canonical_inverse rrec_canonical_input_poly.
 by rewrite /gen_inverse_poly.
qed.
