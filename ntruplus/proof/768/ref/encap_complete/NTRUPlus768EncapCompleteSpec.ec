require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768HashFProof NTRUPlus768DecapHashHBridge NTRUPlus768DecapHashGBridge.
require import NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768NTTProof.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768EncapPolyBasemulAddAlgebra NTRUPlus768PolyToBytesProof.

op encap_full_hash pk coins = hash_h_spec coins (hash_f_spec pk).
op encap_full_r pk coins = poly_cbd1_spec (complete_hash_tail (encap_full_hash pk coins)).
op encap_full_rhat pk coins = ntt_spec (encap_full_r pk coins).
op encap_full_pad pk coins = hash_g_spec (poly_tobytes_spec (encap_full_rhat pk coins)).
op encap_full_m pk coins = poly_sotp_encode_spec coins (encap_full_pad pk coins).
op encap_full_mhat pk coins = ntt_spec (encap_full_m pk coins).
op encap_full_product pk coins = candidate_product_spec (decoded_poly pk) (encap_full_rhat pk coins).
op encap_full_cipher pk coins = poly_centered_add_spec (encap_full_product pk coins) (encap_full_mhat pk coins).
op encap_full_key pk coins : W8.t Array32.t = Array32.init (fun i => (encap_full_hash pk coins).[i]).
op encap_derand_spec pk coins : W8.t Array1152.t * W8.t Array32.t * W32.t =
  if encap_key_canonical pk then
    (poly_tobytes_spec (encap_full_cipher pk coins),encap_full_key pk coins,W32.zero)
  else (encap_zero_ct,encap_zero_ss,W32.one).

lemma encap_derand_accept pk coins : encap_key_canonical pk =>
  encap_derand_spec pk coins=(poly_tobytes_spec(encap_full_cipher pk coins),encap_full_key pk coins,W32.zero).
proof. move=> h; by rewrite /encap_derand_spec h. qed.
lemma encap_derand_reject pk coins : !encap_key_canonical pk =>
  encap_derand_spec pk coins=(encap_zero_ct,encap_zero_ss,W32.one).
proof. move=> h; by rewrite /encap_derand_spec h. qed.
lemma encap_derand_status pk coins : ((encap_derand_spec pk coins).`3=W32.zero)=encap_key_canonical pk.
proof. rewrite /encap_derand_spec; case (encap_key_canonical pk); smt(W32.to_uint0 W32.to_uint1). qed.
