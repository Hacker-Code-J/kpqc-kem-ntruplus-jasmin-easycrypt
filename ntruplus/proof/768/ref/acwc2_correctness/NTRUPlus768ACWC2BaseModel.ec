require import AllCore Distr DProd.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768PolySOTPEncodeAlgebra.

(* The envelope uses one G(r) only. The transformed decoder may query a
   second, different entry after a failed underlying message recovery. *)
op [opaque] acwc2_base_failure (w:keygen_witness) (code r:pke_poly) : bool =
 let ct=pke_enc_spec w.`kg_pk code r in
 ct=None \/ pke_dec_spec(oget ct)(pke_secret_bytes w)<>Some code.
op [opaque] acwc2_pad_bad (w:keygen_witness) (msg:W8.t Array96.t)
 (r:pke_poly) (pad:W8.t Array192.t) : bool =
 acwc2_base_failure w (poly_sotp_encode_spec msg pad) r.
op [opaque] acwc2_base_mean (w:keygen_witness) : real =
 mu (pke_psi1 `*` pke_psi1)
   (fun (rc:pke_poly*pke_poly)=>acwc2_base_failure w rc.`2 rc.`1).

lemma acwc2_base_failureE w code r :
 acwc2_base_failure w code r =
 (pke_enc_spec w.`kg_pk code r=None \/
 pke_dec_spec(oget(pke_enc_spec w.`kg_pk code r))(pke_secret_bytes w)<>Some code).
proof. by rewrite /acwc2_base_failure. qed.
lemma acwc2_pad_badE w msg r pad :
 acwc2_pad_bad w msg r pad=acwc2_base_failure w(poly_sotp_encode_spec msg pad)r.
proof. by rewrite /acwc2_pad_bad. qed.
lemma acwc2_base_meanE w : acwc2_base_mean w =
 mu (pke_psi1 `*` pke_psi1)
   (fun (rc:pke_poly*pke_poly)=>acwc2_base_failure w rc.`2 rc.`1).
proof. by rewrite /acwc2_base_mean. qed.
lemma acwc2_base_mean_range w : 0%r<=acwc2_base_mean w<=1%r.
proof. rewrite acwc2_base_meanE; exact(mu_bounded _ _). qed.
lemma acwc2_base_success w code r ct :
 pke_enc_spec w.`kg_pk code r=Some ct =>
 pke_dec_spec ct (pke_secret_bytes w)=Some code =>
 !acwc2_base_failure w code r.
proof. by move=>he hd; rewrite acwc2_base_failureE he /= hd. qed.
