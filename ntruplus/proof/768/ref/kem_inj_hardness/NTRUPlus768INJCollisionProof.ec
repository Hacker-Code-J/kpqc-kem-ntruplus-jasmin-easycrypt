require import AllCore IntDiv Ring.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768INJCollision NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768SecModel.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecProof NTRUPlus768OWUniform.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec NTRUPlus768BasemulAlgebra.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768CoefficientRecovery.
require import NTRUPlus768RRecCanonical NTRUPlus768KeygenGlobalUnit.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).
abbrev [ - ] = NTRUPoly.PolyComRing.([-]).
abbrev ( - ) (p q:NTRUPoly.poly) = p+(-q).

lemma inj_difference_polynomial x y :
 int_poly(inj_word_difference x y)=input_poly x-input_poly y.
proof.
 apply/NTRUPoly.poly_eqP=>i hi.
 rewrite -!int_poly_words NTRUPoly.polyDE NTRUPoly.polyNE.
 case(i<768)=>hn.
 + rewrite !int_poly_coeff 1,2,3:/# (inj_word_difference_get x y i _) 1:/#
   !Array768.mapiE 1,2:/# /lift_int CycloFq.incyclocoeffB;done.
 rewrite !int_poly_coeff_out 1,2,3:/#;ring.
qed.

lemma inj_key_represents pk : encap_key_canonical pk=>
 terminal_represents(decoded_poly pk)(ow_key_poly pk).
proof.
 move=>hp;have h:=ow_encoded_represents (ow_key_poly pk) (ow_key_poly_domain pk).
 by move:h;rewrite(ow_encode_decode pk hp).
qed.
lemma inj_cipher_equation pk m1 m2 r1 r2 :
 encap_key_canonical pk=>pke_domain m1=>pke_domain m2=>pke_domain r1=>pke_domain r2=>
 pke_enc_spec pk m1 r1=pke_enc_spec pk m2 r2=>
 eqm_global(ow_key_poly pk*input_poly r1+input_poly m1)
 (ow_key_poly pk*input_poly r2+input_poly m2).
proof.
 move=>hp hm1 hm2 hr1 hr2.
 rewrite(pke_enc_accept pk m1 r1 hp)(pke_enc_accept pk m2 r2 hp)=>/someI he.
 have hpk:=inj_key_represents pk hp.
 have h1:=pke_serialized_cipher_represents pk m1 r1 (ow_key_poly pk) hp hm1 hr1 hpk.
 have h2:=pke_serialized_cipher_represents pk m2 r2 (ow_key_poly pk) hp hm2 hr2 hpk.
 rewrite -he in h2.
 have hs:=rrec_canonical_domain_qrange _
  (ow_decoded_canonical _ (pke_cipher_canonical pk m1 r1 hp hm1 hr1)).
 exact(gen_terminal_global_congr _ _ _ hs h1 h2).
qed.
lemma inj_equation_difference h r1 r2 m1 m2 :
 eqm_global(h*r1+m1)(h*r2+m2)=>eqm_global(h*(r1-r2)+(m1-m2))NTRUPoly.poly0.
proof.
 move=>he.
 have hx:=eqm_global_add _ _ (-(h*r2+m2)) (-(h*r2+m2)) he (eqm_global_refl (-(h*r2+m2))).
 have hl:h*r1+m1+(-(h*r2+m2))=h*(r1-r2)+(m1-m2) by ring.
 have hr:h*r2+m2+(-(h*r2+m2))=NTRUPoly.PolyComRing.zeror by ring.
 by move:hx;rewrite hl hr.
qed.
lemma inj_win_canonical pk z : sec_inj_win pk z=>encap_key_canonical pk.
proof.
 rewrite /sec_inj_win /pke_enc_spec;case(encap_key_canonical pk)=>hp;smt().
qed.
lemma inj_collision_relation pk z : sec_inj_win pk z=>
 inj_relation(ow_key_poly pk)(inj_difference_pair z).`1 (inj_difference_pair z).`2.
proof.
 move=>hw;have hp:=inj_win_canonical pk z hw.
 have hm1:pke_domain z.`1 by move:hw;rewrite /sec_inj_win;smt().
 have hm2:pke_domain z.`2 by move:hw;rewrite /sec_inj_win;smt().
 have hr1:pke_domain z.`3 by move:hw;rewrite /sec_inj_win;smt().
 have hr2:pke_domain z.`4 by move:hw;rewrite /sec_inj_win;smt().
 have he:pke_enc_spec pk z.`1 z.`3=pke_enc_spec pk z.`2 z.`4 by move:hw;rewrite /sec_inj_win;smt().
 rewrite /inj_relation /inj_difference_pair /= !inj_difference_polynomial.
 exact(inj_equation_difference _ _ _ _ _ (inj_cipher_equation pk _ _ _ _ hp hm1 hm2 hr1 hr2 he)).
qed.

(* The universal bridge consumes an actual nonfailure collision. It adds
   no collision-hardness assumption and needs no public-key inverse. *)
lemma inj_collision_bridge pk z : sec_inj_win pk z=>
 inj_short_win(ow_key_poly pk)(inj_difference_pair z).
proof.
 move=>hw;have hrel:=inj_collision_relation pk z hw.
 have hm1:pke_domain z.`1 by move:hw;rewrite /sec_inj_win;smt().
 have hm2:pke_domain z.`2 by move:hw;rewrite /sec_inj_win;smt().
 have hr1:pke_domain z.`3 by move:hw;rewrite /sec_inj_win;smt().
 have hr2:pke_domain z.`4 by move:hw;rewrite /sec_inj_win;smt().
 have hne:(z.`1,z.`3)<>(z.`2,z.`4) by move:hw;rewrite /sec_inj_win;smt().
 rewrite /inj_short_win;split.
 + rewrite /inj_difference_pair /=;exact(inj_word_difference_short _ _ hr1 hr2).
 split.
 + rewrite /inj_difference_pair /=;exact(inj_word_difference_short _ _ hm1 hm2).
 split;first exact(inj_difference_pair_nonzero z hne).
 exact hrel.
qed.
lemma inj_encoded_collision a z : ow_rq_domain a=>sec_inj_win(ow_encode a)z=>
 inj_short_win a (inj_difference_pair z).
proof.
 move=>ha hz;have h:=inj_collision_bridge (ow_encode a)z hz.
 by move:h;rewrite(ow_decode_encode a ha).
qed.
