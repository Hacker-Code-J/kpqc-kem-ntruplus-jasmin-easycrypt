require import AllCore Distr.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152 Array2336.
require import NTRUPlus768PKEModel NTRUPlus768SOTPContracts NTRUPlus768RRecModel.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolySOTPRoundTrip NTRUPlus768PolySOTPEncodeCheckedRoundTrip.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapGuardSpec.

type acwc2_g_map = pke_poly -> W8.t Array192.t.
op [opaque] acwc2_secret_bytes (sk:W8.t Array2336.t) = decap_fbytes(complete_sk_poly sk).
op [opaque] acwc2_code (g:acwc2_g_map) (msg:W8.t Array96.t) (r:pke_poly) =
 poly_sotp_encode_spec msg (g r).
op [opaque] acwc2_enc_spec (g:acwc2_g_map) (pk:W8.t Array1152.t)
 (msg:W8.t Array96.t) (r:pke_poly) = pke_enc_spec pk (acwc2_code g msg r) r.
op [opaque] acwc2_dec_spec (g:acwc2_g_map) (pk:W8.t Array1152.t)
 (sk:W8.t Array2336.t) (ct:W8.t Array1152.t) : W8.t Array96.t option =
 let code=pke_dec_spec ct (acwc2_secret_bytes sk) in
 if code=None then None else
 let recovered=rrec_spec pk (oget code) ct in
 if recovered=None then None else sotp_decode_option (oget code) (g (oget recovered)).
op [opaque] acwc2_failure (g:acwc2_g_map) (pk:W8.t Array1152.t)
 (sk:W8.t Array2336.t) (msg:W8.t Array96.t) (r:pke_poly) =
 let ct=acwc2_enc_spec g pk msg r in
 ct=None \/ acwc2_dec_spec g pk sk (oget ct)<>Some msg.
op [opaque] acwc2_transformed_base_failure (g:acwc2_g_map) (pk:W8.t Array1152.t)
 (sk:W8.t Array2336.t) (msg:W8.t Array96.t) (r:pke_poly) =
 let ct=acwc2_enc_spec g pk msg r in
 ct=None \/ pke_dec_spec (oget ct) (acwc2_secret_bytes sk)<>Some(acwc2_code g msg r).

lemma acwc2_codeE g msg r : poly_sotp_encode_spec msg (g r)=acwc2_code g msg r.
proof. by rewrite /acwc2_code. qed.
lemma acwc2_enc_specE g pk msg r : pke_enc_spec pk (acwc2_code g msg r) r=acwc2_enc_spec g pk msg r.
proof. by rewrite /acwc2_enc_spec. qed.
lemma acwc2_code_domain g msg r : pke_domain(acwc2_code g msg r).
proof. rewrite /acwc2_code sotp_domainE; exact(poly_sotp_encode_spec_trit_input msg (g r)). qed.
lemma acwc2_dec_reject_base g pk sk ct : pke_dec_spec ct (acwc2_secret_bytes sk)=None =>
 acwc2_dec_spec g pk sk ct=None.
proof. by move=>h; rewrite /acwc2_dec_spec h. qed.
