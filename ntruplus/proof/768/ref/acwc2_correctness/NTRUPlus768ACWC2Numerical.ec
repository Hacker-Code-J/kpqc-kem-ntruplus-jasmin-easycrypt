require import AllCore StdOrder.
import RealOrder RField.

(* A conservative rational certificate. No concentration or cryptographic
   conclusion is assumed here: those contracts supply the scalar inputs. *)
op acwc2_collision_mass = (3%r/8%r)^768.
op acwc2_epsilon = (1%r/2%r)^356.
op acwc2_union_tail = 2%r^768 * 65536%r * acwc2_collision_mass^4 / acwc2_epsilon^8.

lemma acwc2_power8_certificate : (3%r/8%r)^8 <= (1%r/2%r)^11.
proof.
 have hn:3%r^8=6561%r by ring.
 have hd:8%r^8=16777216%r by ring.
 have h2:2%r^11=2048%r by ring.
 by rewrite !exprMn 1,2:// !exprVn 1,2:// hn hd h2 expr1z; smt().
qed.
lemma acwc2_collision_coarse : acwc2_collision_mass <= (1%r/2%r)^1056.
proof.
 have hb:=acwc2_power8_certificate.
 have h0:0%r<=(3%r/8%r)^8 by apply expr_ge0; smt().
 have hp:=ler_pexp 96 ((3%r/8%r)^8) ((1%r/2%r)^11) _ _; first 2 smt().
 have hL:(3%r/8%r)^768=((3%r/8%r)^8)^96 by exact(exprM _ 8 96).
 have hR:(1%r/2%r)^1056=((1%r/2%r)^11)^96 by exact(exprM _ 11 96).
 by rewrite /acwc2_collision_mass hL hR.
qed.
lemma acwc2_epsilon_positive : 0%r<acwc2_epsilon.
proof. rewrite /acwc2_epsilon; apply expr_gt0; smt(). qed.
lemma acwc2_inverse_power n : 0<=n => 2%r^n*(1%r/2%r)^n=1%r.
proof.
 move=>hn; rewrite -exprMn 1:hn.
 have he:2%r*(1%r/2%r)=1%r by field.
 by rewrite he expr1z.
qed.
lemma acwc2_tail_coarse : acwc2_union_tail <= (1%r/2%r)^592.
proof.
 have hc:=acwc2_collision_coarse.
 have h0:0%r<=acwc2_collision_mass by rewrite /acwc2_collision_mass; apply expr_ge0; smt().
 have h4:=ler_pexp 4 acwc2_collision_mass ((1%r/2%r)^1056) _ _; first 2 smt().
 have he4:(1%r/2%r)^4224=((1%r/2%r)^1056)^4 by exact(exprM _ 1056 4).
 move:h4; rewrite -he4=>h4.
 have he8:acwc2_epsilon^8=(1%r/2%r)^2848 by rewrite /acwc2_epsilon -exprM.
 have hm:2%r^768*65536%r=2%r^784.
 + have h16:65536%r=2%r^16 by ring.
   by rewrite h16 -exprD_nneg 1,2:// /=.
 have hsplit:(1%r/2%r)^4224=(1%r/2%r)^2848*(1%r/2%r)^784*(1%r/2%r)^592.
 + by rewrite -!exprD_nneg 1,2,3,4:// /=.
 have hd:0%r<(1%r/2%r)^2848 by apply expr_gt0; smt().
 have hp:0%r<=2%r^784 by apply expr_ge0; smt().
 have hi:=acwc2_inverse_power 784 _; first smt().
 have he:2%r^784*(1%r/2%r)^4224/(1%r/2%r)^2848=(1%r/2%r)^592.
 + rewrite hsplit; field; smt().
 rewrite /acwc2_union_tail he8 hm.
 have hu:2%r^784*acwc2_collision_mass^4/(1%r/2%r)^2848<=
         2%r^784*(1%r/2%r)^4224/(1%r/2%r)^2848.
 + apply ler_wpmul2r; first by apply invr_ge0; smt().
   apply ler_wpmul2l; assumption.
 by rewrite -he.
qed.
lemma acwc2_error_scales :
 1%r/(2%r^354)+acwc2_epsilon+acwc2_union_tail < 1%r/(2%r^353).
proof.
 have ht:=acwc2_tail_coarse.
 have he:acwc2_epsilon=1%r/(2%r^356).
 + by rewrite /acwc2_epsilon exprMn 1:// exprVn 1:// expr1z.
 have hsmall:(1%r/2%r)^592<=1%r/(2%r^356).
 + rewrite exprMn 1:// exprVn 1:// expr1z !div1r.
   have h356:0%r<2%r^356 by apply expr_gt0; smt().
   have h592:0%r<2%r^592 by apply expr_gt0; smt().
   rewrite (lef_pinv _ _ h356 h592); apply ler_weexpn2l; smt().
 have h354:0%r<2%r^354 by apply expr_gt0; smt().
 have h353:0%r<2%r^353 by apply expr_gt0; smt().
 have hA:2%r^356=4%r*(2%r^354).
 + rewrite (_:356=2+354) 1:// exprD_nneg 1,2://; ring.
 have hB:2%r^354=2%r*(2%r^353).
 + rewrite (_:354=1+353) 1:// exprD_nneg 1,2://; ring.
 rewrite he; smt().
qed.
lemma acwc2_numerical_combination (average worst:real) :
 average<1%r/(2%r^354) => worst<=average+acwc2_epsilon+acwc2_union_tail =>
 worst<1%r/(2%r^353).
proof. have h:=acwc2_error_scales; smt(). qed.
