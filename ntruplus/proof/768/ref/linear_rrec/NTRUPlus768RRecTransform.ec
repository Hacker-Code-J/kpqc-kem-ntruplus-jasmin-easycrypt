require import AllCore List Finite.

(* The argument is about a proved finite predicate, not a new surjectivity
   axiom. A left inverse makes an endomap injective; its finite image has
   the same cardinality and therefore covers the predicate. *)
lemma rrec_finite_right_inverse ['a] (S:'a->bool) (F I:'a->'a) :
 is_finite S => (forall x,S x=>S(F x)) =>
 (forall x,S x=>I(F x)=x) => forall y,S y=>F(I y)=y.
proof.
 move=>[s [hu hs]] hF hI y hy.
 have hinj:forall x z,x \in s=>z \in s=>F x=F z=>x=z.
 + move=>x z hx hz he.
   have hxS:S x by rewrite -(hs x).
   have hzS:S z by rewrite -(hs z).
   by rewrite -(hI x hxS) -(hI z hzS) he.
 have hmap:uniq(map F s).
 + rewrite (map_inj_in_uniq F s hinj); exact hu.
 have hsub:mem(map F s)<=mem s.
 + move=>z; move/mapP=>[x [hx ->]].
   rewrite hs; apply hF; by rewrite -(hs x).
 have hsize:size s<=size(map F s) by rewrite size_map.
 have hp:=uniq_le_perm_eq (map F s) s hmap hsub hsize.
 have hym:y \in map F s.
 + rewrite (perm_eq_mem _ _ hp y) (hs y); exact hy.
 move/mapP:hym=>[x [hx he]].
 have hxS:S x by rewrite -(hs x).
 by rewrite he (hI x hxS).
qed.

from Jasmin require import JWord.
require import Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768KeygenPublicKeyBridge NTRUPlus768KeygenSecretFBridge.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768RRecWordChecks NTRUPlus768RRecCodec.
require import NTRUPlus768NTTAlgebra NTRUPlus768NTTStage1Algebra NTRUPlus768NTTProof.
require import NTRUPlus768InvNTTAlgebra NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768ForwardNTTSemantics.
require import NTRUPlus768TerminalRepresentation NTRUPlus768InverseNTTSemantics.
require import NTRUPlus768Crepmod3DecapBridge.

lemma rrec_normalize_mod a : poly_coeff_eq_mod_q(rrec_normalize a)a.
proof.
 move=>j hj.
 by rewrite (rrec_normalize_coeff a j hj) /q rrec_center_mod.
qed.

require import NTRUPlus768RRecCanonical.

op [opaque] rrec_canonical_forward (x:W16.t Array768.t) =
 rrec_canonical(forward_ntt_spec x).
op [opaque] rrec_canonical_inverse (y:W16.t Array768.t) =
 rrec_canonical(inverse_invntt_spec y).

lemma rrec_canonical_forward_closed x : rrec_canonical_domain x =>
 rrec_canonical_domain(rrec_canonical_forward x).
proof. move=>_; rewrite /rrec_canonical_forward; exact(rrec_canonical_range _). qed.
lemma rrec_canonical_inverse_closed y :
 rrec_canonical_domain(rrec_canonical_inverse y).
proof. rewrite /rrec_canonical_inverse; exact(rrec_canonical_range _). qed.

lemma rrec_canonical_forward_represents x : rrec_canonical_domain x =>
 terminal_represents (rrec_canonical_forward x) (input_poly x).
proof.
 move=>hx; rewrite /rrec_canonical_forward.
 apply(terminal_represents_mod_q_replacement (forward_ntt_spec x)).
 + exact(rrec_canonical_mod _).
 exact(forward_ntt_spec_terminal_represents x (rrec_canonical_domain_input_qrange x hx)).
qed.

lemma rrec_canonical_left_inverse x : rrec_canonical_domain x =>
 rrec_canonical_inverse(rrec_canonical_forward x)=x.
proof.
 move=>hx.
 have hf:=rrec_canonical_forward_represents x hx.
 have hr:=rrec_canonical_domain_qrange _ (rrec_canonical_forward_closed x hx).
 have hi:=inverse_invntt_spec_semantics (input_poly x) (rrec_canonical_forward x) hf hr.
 have hc:=rrec_eqm_canonical x (inverse_invntt_spec(rrec_canonical_forward x)) hi.
 rewrite /rrec_canonical_inverse -hc.
 exact(rrec_canonical_fixed x hx).
qed.

lemma rrec_canonical_right_inverse y : rrec_canonical_domain y =>
 rrec_canonical_forward(rrec_canonical_inverse y)=y.
proof.
 exact(rrec_finite_right_inverse rrec_canonical_domain
   rrec_canonical_forward rrec_canonical_inverse
   rrec_canonical_domain_finite rrec_canonical_forward_closed rrec_canonical_left_inverse y).
qed.

lemma rrec_canonical_represented y : rrec_canonical_domain y =>
 exists p,terminal_represents y p.
proof.
 move=>hy; exists(input_poly(rrec_canonical_inverse y)).
 have h:=rrec_canonical_forward_represents (rrec_canonical_inverse y)
   (rrec_canonical_inverse_closed y).
 rewrite (rrec_canonical_right_inverse y hy) in h.
 exact h.
qed.

(* Every word-valued terminal array has a global representative. This is
   derived from the finite endomap argument, without a CRT premise. *)
lemma rrec_terminal_represented y : exists p,terminal_represents y p.
proof.
 have [p hp]:=rrec_canonical_represented (rrec_canonical y) (rrec_canonical_range y).
 exists p; apply(terminal_represents_mod_q_replacement (rrec_canonical y)).
 + move=>j hj; apply/eq_sym; exact(rrec_canonical_mod y j hj).
 exact hp.
qed.

lemma rrec_terminal_inverse_represents y : qrange_input_shape y =>
 terminal_represents y (input_poly(inverse_invntt_spec y)).
proof.
 move=>hy; have [p hp]:=rrec_terminal_represented y.
 have hi:=inverse_invntt_spec_semantics p y hp hy.
 exact(terminal_represents_global_congr y p (input_poly(inverse_invntt_spec y)) hi hp).
qed.

require import NTRUPlus768RRecTerminal.

lemma rrec_inverse_forward_mod y : qrange_input_shape y =>
 poly_coeff_eq_mod_q (forward_ntt_spec(inverse_invntt_spec y)) y.
proof.
 move=>hy; apply(rrec_terminal_same_poly_mod_q _ _ (input_poly(inverse_invntt_spec y))).
 + exact(forward_ntt_spec_terminal_represents _ (inverse_invntt_spec_ntt_input_qrange y hy)).
 exact(rrec_terminal_inverse_represents y hy).
qed.

lemma rrec_inverse_forward_trit y r :
 qrange_input_shape y =>pke_domain r =>rrec_normalize(inverse_invntt_spec y)=r =>
 poly_coeff_eq_mod_q (pke_rhat r) y.
proof.
 move=>hy hr he.
 have heq:input_poly r=input_poly(inverse_invntt_spec y).
 + rewrite -he; exact(rrec_input_poly_mod_congr _ _ (rrec_normalize_mod _)).
 have hyr:terminal_represents y (input_poly r).
 + rewrite heq; exact(rrec_terminal_inverse_represents y hy).
 apply(rrec_terminal_same_poly_mod_q _ _ (input_poly r)).
 + rewrite /pke_rhat ntt_specE; exact(forward_ntt_spec_terminal_represents r (pke_domain_qrange r hr)).
 exact hyr.
qed.
