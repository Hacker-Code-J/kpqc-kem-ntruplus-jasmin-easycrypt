require import AllCore List Distr StdOrder.
from Jasmin require import JWord.
require import Array96.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Model NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ACWC2Recovery NTRUPlus768ACWC2Mean NTRUPlus768ACWC2Concentration.
import RealOrder RField.

(* The G function is fixed before the remaining encryption randomness is
   sampled. The maximum ranges over every 96-byte message. *)
op [opaque] acwc2_message_error (w:keygen_witness) (g:acwc2_g_function)
 (msg:W8.t Array96.t) =
 mu pke_psi1 (fun r=>acwc2_failure g w.`kg_pk w.`kg_sk msg r).
op [opaque] acwc2_worst_error (w:keygen_witness) (g:acwc2_g_function) =
 acwc2_finite_max acwc2_message_enum (fun msg=>acwc2_message_error w g msg).

lemma acwc2_finite_max_mono ['a] (xs:'a list) (f h:'a->real) :
 (forall x,x \in xs=>f x<=h x) => acwc2_finite_max xs f<=acwc2_finite_max xs h.
proof.
 elim:xs=>[|x xs ih] /=; first by rewrite /acwc2_finite_max /=.
 move=>he; have hx:=he x _; first by smt().
 have ht:acwc2_finite_max xs f<=acwc2_finite_max xs h.
 + apply ih=>y hy; apply he; smt().
 rewrite /acwc2_finite_max /= -/acwc2_finite_max.
 exact(ler_maxr_trans _ _ _ _ hx ht).
qed.
lemma acwc2_finite_max_member ['a] (xs:'a list) (f:'a->real) x :
 x \in xs => f x<=acwc2_finite_max xs f.
proof.
 elim:xs=>[|y ys ih] //=.
 move=>[he|hx]; rewrite /acwc2_finite_max /= -/acwc2_finite_max.
 + rewrite he; exact(maxrl _ _).
 exact(ler_trans _ _ _ (ih hx) (maxrr _ _)).
qed.
lemma acwc2_message_error_range w g msg : 0%r<=acwc2_message_error w g msg<=1%r.
proof. rewrite /acwc2_message_error; exact(mu_bounded _ _). qed.
lemma acwc2_worst_error_range w g : 0%r<=acwc2_worst_error w g<=1%r.
proof.
 rewrite /acwc2_worst_error; split; first exact(acwc2_max_nonnegative _ _).
 move=>_; apply acwc2_max_upper=> // msg hm.
 have [_ h]:=acwc2_message_error_range w g msg; exact h.
qed.
lemma acwc2_message_error_le_worst w g msg : acwc2_message_error w g msg<=acwc2_worst_error w g.
proof.
 rewrite /acwc2_worst_error.
 apply(acwc2_finite_max_member acwc2_message_enum (fun m=>acwc2_message_error w g m) msg).
 exact(acwc2_message_enum_full msg).
qed.
lemma acwc2_message_error_bound w g msg : pke_key_relation w =>
 acwc2_message_error w g msg<=acwc2_weighted_bad w msg g.
proof.
 move=>hk; rewrite /acwc2_message_error acwc2_weighted_bad_probability.
 apply mu_le=>r hr.
 have hdom:pke_domain r by move:hr; rewrite acwc2_psi1_support.
 exact(acwc2_failure_pad_inclusion g w msg r hk hdom).
qed.
lemma acwc2_worst_error_bound w g : pke_key_relation w =>
 acwc2_worst_error w g<=
 acwc2_finite_max acwc2_message_enum (fun msg=>acwc2_weighted_bad w msg g).
proof.
 move=>hk; rewrite /acwc2_worst_error.
 apply(acwc2_finite_max_mono acwc2_message_enum
   (fun msg=>acwc2_message_error w g msg) (fun msg=>acwc2_weighted_bad w msg g))=>msg hm.
 exact(acwc2_message_error_bound w g msg hk).
qed.
