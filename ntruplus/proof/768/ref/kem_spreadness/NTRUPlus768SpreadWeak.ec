require import AllCore List Distr RealSeries StdOrder.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768SOTPContracts.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2BaseModel NTRUPlus768ACWC2Domains.
require import NTRUPlus768ACWC2Concentration NTRUPlus768ACWC2Error.
require import NTRUPlus768ACWC2Mean NTRUPlus768ACWC2Oracle NTRUPlus768ACWC2WorstCase.
require import NTRUPlus768SpreadCBD NTRUPlus768SpreadBase NTRUPlus768SpreadTransfer.
require import NTRUPlus768FOModel NTRUPlus768FOError.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation.
import RealOrder RField.

(* On successful underlying decryption, the encoded polynomial is fixed
   by the chosen ciphertext. G need not be fresh, random, or independent. *)
lemma spread_good_cipher_code w msg g ct r :
 pke_enc_spec w.`kg_pk (poly_sotp_encode_spec msg(g r)) r=Some ct =>
 !acwc2_pad_bad w msg r(g r) =>
 let code=oget(pke_dec_spec ct (pke_secret_bytes w)) in
 pke_domain code /\ pke_enc_spec w.`kg_pk code r=Some ct.
proof.
 move=>he hb.
 have hd:pke_dec_spec ct (pke_secret_bytes w)=Some(poly_sotp_encode_spec msg(g r)).
 + move:hb; rewrite acwc2_pad_badE acwc2_base_failureE he /=; smt().
 rewrite hd /=; split; last exact he.
 have h:=acwc2_code_domain g msg r; by move:h; rewrite /acwc2_code.
qed.

lemma spread_good_cipher_mass w msg g ct : pke_key_relation w =>
 mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk (poly_sotp_encode_spec msg(g r))r=Some ct /\
   !acwc2_pad_bad w msg r(g r))<=1%r/(2%r^768).
proof.
 move=>hk; pose code:=oget(pke_dec_spec ct(pke_secret_bytes w)).
 case(pke_domain code)=>hc.
 + apply(ler_trans _ _ _ _ (spread_base_bound w code ct hk hc)).
   apply mu_le=>r hr [he hb].
   have [_ h]:=spread_good_cipher_code w msg g ct r he hb; exact h.
 have hz:mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct /\
   !acwc2_pad_bad w msg r(g r))=0%r.
 + apply mu0_false=>r hr.
   have h:=spread_good_cipher_code w msg g ct r; smt().
 rewrite hz; exact(ltrW _ _ spread_cbd_bound_positive).
qed.

lemma spread_cipher_mass_range w msg g ct : 0%r<=spread_cipher_mass w msg g ct<=1%r.
proof. rewrite /spread_cipher_mass; exact(mu_bounded _ _). qed.

lemma spread_cipher_mass_fixed w msg g ct : pke_key_relation w =>
 spread_cipher_mass w msg g ct<=1%r/(2%r^768)+fo_error w g.
proof.
 move=>hk; rewrite /spread_cipher_mass.
 rewrite(mu_split pke_psi1
  (fun r=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct)
  (fun r=>acwc2_pad_bad w msg r(g r))).
 have hg:=spread_good_cipher_mass w msg g ct hk.
 have hb:mu pke_psi1(predI
   (fun r=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct)
   (fun r=>acwc2_pad_bad w msg r(g r)))<=fo_error w g.
 + apply(ler_trans _ _ _ _ (fo_message_error_bound w g msg)).
   rewrite acwc2_weighted_bad_probability; apply mu_le; smt().
 change (mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct /\
  acwc2_pad_bad w msg r(g r)) +
  mu pke_psi1(fun r=>pke_enc_spec w.`kg_pk(poly_sotp_encode_spec msg(g r))r=Some ct /\
  !acwc2_pad_bad w msg r(g r))<=1%r/(2%r^768)+fo_error w g).
 by move:hb; rewrite /predI; smt().
qed.

(* The selectors may depend on the entire private setup observation:
   key witness, retained F cache, and fixed G pads. This quantifies choices
   inside the expectation and never interchanges expectation and maximum. *)
lemma spread_weak_selector_expectation
 (d:fo_setup_observation distr)
 (message:fo_setup_observation->W8.t Array96.t)
 (ciphertext:fo_setup_observation->W8.t Array1152.t) :
 is_lossless d =>(forall s,s \in d=>pke_key_relation s.`1.`1) =>
 E d(fun (s:fo_setup_observation)=>spread_cipher_mass s.`1.`1 (message s)(acwc2_gfun s.`3)(ciphertext s))<=
 1%r/(2%r^768)+E d fo_setup_error.
proof.
 move=>hll hk.
 have hl:hasE d(fun (s:fo_setup_observation)=>spread_cipher_mass s.`1.`1(message s)(acwc2_gfun s.`3)(ciphertext s)).
 + apply(acwc2_bounded_hasE d _ 1%r)=> // s; exact(spread_cipher_mass_range _ _ _ _).
 have hr:hasE d(fun (s:fo_setup_observation)=>1%r/(2%r^768)+fo_setup_error s).
 + apply(acwc2_bounded_hasE d _ (1%r/(2%r^768)+1%r)); first by have h:=spread_cbd_bound_positive; smt().
   move=>s; have h:=fo_setup_error_range s; have hp:=spread_cbd_bound_positive; smt().
 have h:=in_ler_exp d _ _ hl hr _.
 + move=>s hs; rewrite /fo_setup_error; exact(spread_cipher_mass_fixed _ _ _ _ (hk s hs)).
 move:h; rewrite expD 1:(hasEC d _) 1:(fo_setup_error_hasE d) expC hll /=; done.
qed.

lemma spread_weak_setup_selector_bound &m
 (message:fo_setup_observation->W8.t Array96.t)
 (ciphertext:fo_setup_observation->W8.t Array1152.t) :
 E(mk(fun (s:fo_setup_observation)=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun (s:fo_setup_observation)=>spread_cipher_mass s.`1.`1(message s)(acwc2_gfun s.`3)(ciphertext s))<
 1%r/(2%r^768)+1%r/(2%r^353).
proof.
 have hb:=spread_weak_selector_expectation
   (mk(fun (s:fo_setup_observation)=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))message ciphertext
   (fo_setup_law_lossless &m witness) _.
 + move=>s hs; have h:=fo_setup_law_support &m witness s hs.
   move:h; rewrite /fo_setup_valid; smt().
 apply(ler_lt_trans _ _ _ hb).
 rewrite ltr_add2l; exact(fo_setup_error_expectation &m).
qed.

lemma spread_weak_scale : 1%r/(2%r^768)+1%r/(2%r^353)<1%r/(2%r^352).
proof.
 have h354:0%r<2%r^354 by apply expr_gt0; smt().
 have h768:0%r<2%r^768 by apply expr_gt0; smt().
 have h352:0%r<2%r^352 by apply expr_gt0; smt().
 have hs:1%r/(2%r^768)<=1%r/(2%r^354).
 + rewrite !div1r (lef_pinv _ _ h354 h768); apply ler_weexpn2l; smt().
 have hA:2%r^354=4%r*(2%r^352).
 + rewrite (_:354=2+352) 1:// exprD_nneg 1,2://; ring.
 have hB:2%r^353=2%r*(2%r^352).
 + rewrite (_:353=1+352) 1:// exprD_nneg 1,2://; ring.
 smt().
qed.

lemma spread_weak_setup_selector_352 &m
 (message:fo_setup_observation->W8.t Array96.t)
 (ciphertext:fo_setup_observation->W8.t Array1152.t) :
 E(mk(fun (s:fo_setup_observation)=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun (s:fo_setup_observation)=>spread_cipher_mass s.`1.`1(message s)(acwc2_gfun s.`3)(ciphertext s))<1%r/(2%r^352).
proof.
 have h:=spread_weak_setup_selector_bound &m message ciphertext.
 exact(ltr_trans _ _ _ h spread_weak_scale).
qed.

(* All attainable ciphertexts lie in this symbolic finite image. It uses
   both ternary code and randomness; no enumeration is expanded at runtime. *)
op [opaque] spread_cipher_enum (w:keygen_witness) : W8.t Array1152.t list =
 flatten(map(fun code=>map(pke_ciphertext w.`kg_pk code)acwc2_r_enum)acwc2_r_enum).
op [opaque] spread_cipher_max (w:keygen_witness) (g:acwc2_g_function) =
 acwc2_finite_max acwc2_message_enum(fun msg=>
  acwc2_finite_max (spread_cipher_enum w)(spread_cipher_mass w msg g)).

lemma spread_cipher_enum_cover w code r ct :
 pke_key_relation w=>pke_domain code=>pke_domain r=>
 pke_enc_spec w.`kg_pk code r=Some ct=>ct \in spread_cipher_enum w.
proof.
 move=>hk hm hr he.
 have hc:pke_ciphertext w.`kg_pk code r=ct.
 + move:he; rewrite(pke_enc_accept _ _ _ (pke_key_canonical w hk)); smt().
 rewrite /spread_cipher_enum -flatten_mapP; exists code; split.
 + by rewrite acwc2_r_enum_domain.
 have hrm:r \in acwc2_r_enum by rewrite acwc2_r_enum_domain.
 have hmem:=map_f (pke_ciphertext w.`kg_pk code) acwc2_r_enum r hrm.
 by move:hmem; rewrite hc.
qed.

lemma spread_cipher_mass_outside w msg g ct :
 pke_key_relation w=>!(ct \in spread_cipher_enum w)=>spread_cipher_mass w msg g ct=0%r.
proof.
 move=>hk hc; rewrite /spread_cipher_mass; apply mu0_false=>r hr.
 have hdom:pke_domain r by move:hr; rewrite acwc2_psi1_support.
 have hm:pke_domain(poly_sotp_encode_spec msg(g r)).
 + have h:=acwc2_code_domain g msg r; by move:h; rewrite /acwc2_code.
 have h:=spread_cipher_enum_cover w (poly_sotp_encode_spec msg(g r)) r ct hk hm hdom; smt().
qed.

lemma spread_cipher_max_range w g : 0%r<=spread_cipher_max w g<=1%r.
proof.
 rewrite /spread_cipher_max; split; first exact(acwc2_max_nonnegative _ _).
 move=>_; apply acwc2_max_upper=> // msg hm.
 apply acwc2_max_upper=> // ct hc.
 have [_ h]:=spread_cipher_mass_range w msg g ct; exact h.
qed.

lemma spread_cipher_max_covers w msg g ct : pke_key_relation w=>
 spread_cipher_mass w msg g ct<=spread_cipher_max w g.
proof.
 move=>hk; case(ct \in spread_cipher_enum w)=>hc.
 + rewrite /spread_cipher_max.
   apply(ler_trans _ _ _ (acwc2_finite_max_member (spread_cipher_enum w)
     (spread_cipher_mass w msg g) ct hc)).
   exact(acwc2_finite_max_member acwc2_message_enum
     (fun msg0=>acwc2_finite_max(spread_cipher_enum w)(spread_cipher_mass w msg0 g))
     msg (acwc2_message_enum_full msg)).
 rewrite(spread_cipher_mass_outside w msg g ct hk hc).
 have [h _]:=spread_cipher_max_range w g; exact h.
qed.

(* This characterization is the all-message/all-ciphertext maximum, not
   the maximum of an arbitrarily restricted test list. *)
lemma spread_cipher_max_upper_iff w g B : pke_key_relation w=>0%r<=B=>
 (spread_cipher_max w g<=B <=>forall msg ct,spread_cipher_mass w msg g ct<=B).
proof.
 move=>hk hB; split.
 + move=>hb msg ct; exact(ler_trans _ _ _ (spread_cipher_max_covers w msg g ct hk) hb).
 move=>h; rewrite /spread_cipher_max.
 apply acwc2_max_upper=> // msg hm; apply acwc2_max_upper=> // ct hc; exact(h msg ct).
qed.

lemma spread_cipher_max_fixed w g : pke_key_relation w=>
 spread_cipher_max w g<=1%r/(2%r^768)+fo_error w g.
proof.
 move=>hk.
 have hp:0%r<=1%r/(2%r^768)+fo_error w g.
 + have h:=spread_cbd_bound_positive; have h0:=fo_error_range w g; smt().
 rewrite(spread_cipher_max_upper_iff w g _ hk hp).
 move=>msg ct; exact(spread_cipher_mass_fixed w msg g ct hk).
qed.

lemma spread_weak_setup_max_bound &m :
 E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3))<=
 1%r/(2%r^768)+E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))fo_setup_error.
proof.
 pose d:=mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]).
 have hll:is_lossless d by exact(fo_setup_law_lossless &m witness).
 have hl:hasE d(fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3)).
 + apply(acwc2_bounded_hasE d _ 1%r)=> // s; exact(spread_cipher_max_range _ _).
 have hr:hasE d(fun s=>1%r/(2%r^768)+fo_setup_error s).
 + apply(acwc2_bounded_hasE d _ (1%r/(2%r^768)+1%r)); first by have h:=spread_cbd_bound_positive; smt().
   move=>s; have h:=fo_setup_error_range s; have hp:=spread_cbd_bound_positive; smt().
 have h:=in_ler_exp d _ _ hl hr _.
 + move=>s hs; rewrite /fo_setup_error; apply spread_cipher_max_fixed.
   have hv:=fo_setup_law_support &m witness s hs; move:hv; rewrite /fo_setup_valid; smt().
 move:h; rewrite expD 1:(hasEC d _) 1:(fo_setup_error_hasE d) expC hll /=; done.
qed.

lemma spread_weak_setup_max_small &m :
 E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3))<
 1%r/(2%r^768)+1%r/(2%r^353).
proof.
 have hb:=spread_weak_setup_max_bound &m.
 apply(ler_lt_trans _ _ _ hb).
 rewrite ltr_add2l; exact(fo_setup_error_expectation &m).
qed.

(* Literal E_setup[max_message,ciphertext] for the actual fresh key/F
   source and independent full G pads. No expectation/maximum swap and no
   replacement by a fixed-G rho bound or actual-ROM key law occurs. *)
lemma spread_weak_setup_max_352 &m :
 E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3))<1%r/(2%r^352).
proof.
 exact(ltr_trans _ _ _ (spread_weak_setup_max_small &m) spread_weak_scale).
qed.
