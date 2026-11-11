require import AllCore Ring StdOrder.
import RealOrder RField.

(* Closed rational certificates only. This file assumes no probability,
   determinant, lattice, or cryptographic bound. *)
op [opaque] sr_ratio =7680000%r/11950849%r.
op [opaque] sr_determinant_height =12288%r^384.
lemma sr_ratio_positive : 0%r<sr_ratio.
proof. rewrite /sr_ratio;smt(). qed.
lemma sr_ratio_rational_upper : sr_ratio<9%r/14%r.
proof. rewrite /sr_ratio;smt(). qed.
lemma sr_rational_power96 : (9%r/14%r)^96<1%r/(2%r^61).
proof.
 have hn:9%r^96=40483766022843281411184472189571654752207506882090305742200116101065766026718820758174775041%r by ring.
 have hd:14%r^96=106731208060441818006290130478631227993026518960308276036539791640849974350798230701134691852097734849578663936%r by ring.
 have h2:2%r^61=2305843009213693952%r by ring.
 rewrite exprMn 1:// exprVn 1:// hn hd h2;smt().
qed.
lemma sr_ratio_power96 : sr_ratio^96<1%r/(2%r^61).
proof.
 have hp:sr_ratio^96<=(9%r/14%r)^96.
 + apply ler_pexp;first by done.
   have h0:=sr_ratio_positive;have h1:=sr_ratio_rational_upper;smt().
 exact(ler_lt_trans _ _ _ hp sr_rational_power96).
qed.
lemma sr_square_strict (x y:real) : 0%r<=x<y=>x^2<y^2.
proof. rewrite !expr2;smt(). qed.
lemma sr_power4_strict (x y:real) : 0%r<=x<y=>x^4<y^4.
proof.
 move=>h;have h2:=sr_square_strict x y h.
 have hx:0%r<=x^2 by apply expr_ge0;smt().
 have h4:=sr_square_strict (x^2)(y^2) _;first by smt().
 by move:h4;rewrite -!exprM.
qed.
lemma sr_ratio_power384 : sr_ratio^384<1%r/(2%r^244).
proof.
 have hb:=sr_ratio_power96.
 have h0:0%r<=sr_ratio^96 by apply expr_ge0;have h:=sr_ratio_positive;smt().
 have h4:=sr_power4_strict (sr_ratio^96)(1%r/(2%r^61)) _;first by smt().
 move:h4;rewrite -exprM exprMn 1:// exprVn 1:// expr1z -exprM /=.
 done.
qed.
lemma sr_ratio_squared_bound : sr_ratio^768<1%r/(2%r^488).
proof.
 have hb:=sr_ratio_power384.
 have h0:0%r<=sr_ratio^384 by apply expr_ge0;have h:=sr_ratio_positive;smt().
 have h2:=sr_square_strict (sr_ratio^384)(1%r/(2%r^244)) _;first by smt().
 move:h2;rewrite -exprM exprMn 1:// exprVn 1:// expr1z -exprM /=.
 done.
qed.
lemma sr_union_ratio_identity :
 25%r^768*sr_determinant_height/(3457%r^768)=sr_ratio^384.
proof.
 have h25:25%r^768=(25%r^2)^384 by exact(exprM 25%r 2 384).
 have hq:3457%r^768=(3457%r^2)^384 by exact(exprM 3457%r 2 384).
 rewrite h25 hq /sr_determinant_height -exprMn 1:// -exprVn 1:// -exprMn 1://.
 have he:25%r^2*12288%r/(3457%r^2)=sr_ratio by rewrite /sr_ratio;field.
 by rewrite he.
qed.
lemma sr_union_numeric_bound :
 25%r^768*sr_determinant_height/(3457%r^768)<1%r/(2%r^244).
proof. rewrite sr_union_ratio_identity;exact sr_ratio_power384. qed.
lemma sr_fixed_bound_nonnegative : 0%r<=sr_determinant_height/(3457%r^768).
proof. rewrite /sr_determinant_height;apply divr_ge0;apply expr_ge0;done. qed.

lemma sr_union_numeric_integer_bound :
 25%r^768*((12288^384)%r/(3457^768)%r)<1%r/(2%r^244).
proof.
 have hH:(12288^384)%r=sr_determinant_height by rewrite /sr_determinant_height fromintXn.
 have hq:(3457^768)%r=3457%r^768 by rewrite fromintXn.
 rewrite hH hq.
 have he:25%r^768*(sr_determinant_height/(3457%r^768))=
  25%r^768*sr_determinant_height/(3457%r^768) by ring.
 rewrite he;exact sr_union_numeric_bound.
qed.
