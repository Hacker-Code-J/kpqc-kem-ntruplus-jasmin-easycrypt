require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768.
require import NTRUPlus768KeygenSamplerBridge NTRUPlus768KeygenInverseBridge.
require import NTRUPlus768KeygenCompleteInverse NTRUPlus768PolyBaseInvProof NTRUPlus768PolyBaseInvBridge.

module type KeygenSeedRNG = { proc sample() : W8.t Array32.t }.
module type KeygenExpand = { proc shake(seed : W8.t Array32.t) : W8.t Array192.t }.

op keygen_f_accept (buf : W8.t Array192.t) = poly_blocks_succeed (keygen_f_ntt_spec buf) 192.
op keygen_g_accept (buf : W8.t Array192.t) = poly_blocks_succeed (keygen_g_ntt_spec buf) 192.
op keygen_f_attempt_result (buf : W8.t Array192.t) =
 (buf,keygen_f_ntt_spec buf,keygen_inverse_value(keygen_f_ntt_spec buf),keygen_inverse_status(keygen_f_ntt_spec buf)).
op keygen_g_attempt_result (buf : W8.t Array192.t) =
 (buf,keygen_g_ntt_spec buf,keygen_inverse_value(keygen_g_ntt_spec buf),keygen_inverse_status(keygen_g_ntt_spec buf)).
op [opaque] keygen_f_accepted (buf : W8.t Array192.t) (f finv : W16.t Array768.t) =
 f=keygen_f_ntt_spec buf /\ poly_baseinv_success f finv.
op [opaque] keygen_g_accepted (buf : W8.t Array192.t) (g ginv : W16.t Array768.t) =
 g=keygen_g_ntt_spec buf /\ poly_baseinv_success g ginv.

lemma keygen_f_attempt_accept buf : (keygen_f_attempt_result buf).`4=W64.zero <=> keygen_f_accept buf.
proof. rewrite /keygen_f_attempt_result /keygen_inverse_status /keygen_f_accept; case(poly_blocks_succeed _ _) => //; smt(poly_baseinv_w64_zero_neq_one). qed.
lemma keygen_g_attempt_accept buf : (keygen_g_attempt_result buf).`4=W64.zero <=> keygen_g_accept buf.
proof. rewrite /keygen_g_attempt_result /keygen_inverse_status /keygen_g_accept; case(poly_blocks_succeed _ _) => //; smt(poly_baseinv_w64_zero_neq_one). qed.
