require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4.
require import NTRUPlus768BasemulAlgebra.

import Ring.IntID IntOrder.

(* Mathematical quartic inverse algebra.  The C fqinv/baseinv procedures are
   checked independently; this theory does not claim word-level equivalence
   or that a C return value supplies the inverse witness used below. *)

op inverse_u (a : W16.t Array4.t) (z : int) : int =
  coeff a.[0] * coeff a.[0] +
  z * (coeff a.[2] * coeff a.[2] -
       2 * coeff a.[1] * coeff a.[3]).

op inverse_v (a : W16.t Array4.t) (z : int) : int =
  coeff a.[1] * coeff a.[1] +
  z * coeff a.[3] * coeff a.[3] -
  2 * coeff a.[0] * coeff a.[2].

op inverse_determinant (a : W16.t Array4.t) (z : int) : int =
  inverse_u a z * inverse_u a z -
  z * inverse_v a z * inverse_v a z.

op inverse_numerator0 (a : W16.t Array4.t) (z : int) : int =
  coeff a.[0] * inverse_u a z +
  z * coeff a.[2] * inverse_v a z.

op inverse_numerator1 (a : W16.t Array4.t) (z : int) : int =
  -(coeff a.[1] * inverse_u a z +
    z * coeff a.[3] * inverse_v a z).

op inverse_numerator2 (a : W16.t Array4.t) (z : int) : int =
  coeff a.[2] * inverse_u a z +
  coeff a.[0] * inverse_v a z.

op inverse_numerator3 (a : W16.t Array4.t) (z : int) : int =
  -(coeff a.[3] * inverse_u a z +
    coeff a.[1] * inverse_v a z).

op inverse_numerator_at
    (a : W16.t Array4.t) (z : int) (i : int) : int =
  if i = 0 then inverse_numerator0 a z
  else if i = 1 then inverse_numerator1 a z
  else if i = 2 then inverse_numerator2 a z
  else inverse_numerator3 a z.

op determinant_inverse_witness
    (a : W16.t Array4.t) (z dinv : int) : bool =
  (inverse_determinant a z * dinv) %% q = 1 %% q.

op canonical_qword (x : int) : W16.t = W16.of_int (x %% q).

op baseinv_math_spec
    (a : W16.t Array4.t) (z dinv : int) : W16.t Array4.t =
  Array4.init (fun i =>
    canonical_qword (inverse_numerator_at a z i * dinv)).

op inverse_coeff_relation
    (a r : W16.t Array4.t) (z dinv : int) : bool =
  in_qrange4 r /\
  coeff r.[0] %% q = (inverse_numerator0 a z * dinv) %% q /\
  coeff r.[1] %% q = (inverse_numerator1 a z * dinv) %% q /\
  coeff r.[2] %% q = (inverse_numerator2 a z * dinv) %% q /\
  coeff r.[3] %% q = (inverse_numerator3 a z * dinv) %% q.

op block_inverse_qring
    (a r : W16.t Array4.t) (z : int) : bool =
  in_qrange4 r /\
  coeff0 a r z %% q = 1 %% q /\
  coeff1 a r z %% q = 0 %% q /\
  coeff2 a r z %% q = 0 %% q /\
  coeff3 a r z %% q = 0 %% q.

lemma numerator_product0_identity (a : W16.t Array4.t) (z : int) :
  coeff a.[0] * inverse_numerator0 a z +
  z * (coeff a.[1] * inverse_numerator3 a z +
       coeff a.[2] * inverse_numerator2 a z +
       coeff a.[3] * inverse_numerator1 a z) =
  inverse_determinant a z.
proof.
  rewrite /inverse_numerator0 /inverse_numerator1.
  rewrite /inverse_numerator2 /inverse_numerator3.
  rewrite /inverse_determinant /inverse_u /inverse_v.
  ring.
qed.

lemma numerator_product1_zero (a : W16.t Array4.t) (z : int) :
  coeff a.[0] * inverse_numerator1 a z +
  coeff a.[1] * inverse_numerator0 a z +
  z * (coeff a.[2] * inverse_numerator3 a z +
       coeff a.[3] * inverse_numerator2 a z) = 0.
proof.
  rewrite /inverse_numerator0 /inverse_numerator1.
  rewrite /inverse_numerator2 /inverse_numerator3.
  rewrite /inverse_u /inverse_v.
  ring.
qed.

lemma numerator_product2_zero (a : W16.t Array4.t) (z : int) :
  coeff a.[0] * inverse_numerator2 a z +
  coeff a.[1] * inverse_numerator1 a z +
  coeff a.[2] * inverse_numerator0 a z +
  z * coeff a.[3] * inverse_numerator3 a z = 0.
proof.
  rewrite /inverse_numerator0 /inverse_numerator1.
  rewrite /inverse_numerator2 /inverse_numerator3.
  rewrite /inverse_u /inverse_v.
  ring.
qed.

lemma numerator_product3_zero (a : W16.t Array4.t) (z : int) :
  coeff a.[0] * inverse_numerator3 a z +
  coeff a.[1] * inverse_numerator2 a z +
  coeff a.[2] * inverse_numerator1 a z +
  coeff a.[3] * inverse_numerator0 a z = 0.
proof.
  rewrite /inverse_numerator0 /inverse_numerator1.
  rewrite /inverse_numerator2 /inverse_numerator3.
  rewrite /inverse_u /inverse_v.
  ring.
qed.

lemma scaled_numerator_product0_identity
    (a : W16.t Array4.t) (z dinv : int) :
  coeff a.[0] * (inverse_numerator0 a z * dinv) +
  z * (coeff a.[1] * (inverse_numerator3 a z * dinv) +
       coeff a.[2] * (inverse_numerator2 a z * dinv) +
       coeff a.[3] * (inverse_numerator1 a z * dinv)) =
  inverse_determinant a z * dinv.
proof.
  rewrite -numerator_product0_identity.
  ring.
qed.

lemma scaled_numerator_product1_zero
    (a : W16.t Array4.t) (z dinv : int) :
  coeff a.[0] * (inverse_numerator1 a z * dinv) +
  coeff a.[1] * (inverse_numerator0 a z * dinv) +
  z * (coeff a.[2] * (inverse_numerator3 a z * dinv) +
       coeff a.[3] * (inverse_numerator2 a z * dinv)) = 0.
proof.
  have H := numerator_product1_zero a z.
  rewrite (_ :
    coeff a.[0] * (inverse_numerator1 a z * dinv) +
    coeff a.[1] * (inverse_numerator0 a z * dinv) +
    z * (coeff a.[2] * (inverse_numerator3 a z * dinv) +
         coeff a.[3] * (inverse_numerator2 a z * dinv)) =
    (coeff a.[0] * inverse_numerator1 a z +
     coeff a.[1] * inverse_numerator0 a z +
     z * (coeff a.[2] * inverse_numerator3 a z +
          coeff a.[3] * inverse_numerator2 a z)) * dinv) 1:/#.
  by rewrite H.
qed.

lemma scaled_numerator_product2_zero
    (a : W16.t Array4.t) (z dinv : int) :
  coeff a.[0] * (inverse_numerator2 a z * dinv) +
  coeff a.[1] * (inverse_numerator1 a z * dinv) +
  coeff a.[2] * (inverse_numerator0 a z * dinv) +
  z * (coeff a.[3] * (inverse_numerator3 a z * dinv)) = 0.
proof.
  have H := numerator_product2_zero a z.
  rewrite (_ :
    coeff a.[0] * (inverse_numerator2 a z * dinv) +
    coeff a.[1] * (inverse_numerator1 a z * dinv) +
    coeff a.[2] * (inverse_numerator0 a z * dinv) +
    z * (coeff a.[3] * (inverse_numerator3 a z * dinv)) =
    (coeff a.[0] * inverse_numerator2 a z +
     coeff a.[1] * inverse_numerator1 a z +
     coeff a.[2] * inverse_numerator0 a z +
     z * coeff a.[3] * inverse_numerator3 a z) * dinv) 1:/#.
  by rewrite H.
qed.

lemma scaled_numerator_product3_zero
    (a : W16.t Array4.t) (z dinv : int) :
  coeff a.[0] * (inverse_numerator3 a z * dinv) +
  coeff a.[1] * (inverse_numerator2 a z * dinv) +
  coeff a.[2] * (inverse_numerator1 a z * dinv) +
  coeff a.[3] * (inverse_numerator0 a z * dinv) = 0.
proof.
  have H := numerator_product3_zero a z.
  rewrite (_ :
    coeff a.[0] * (inverse_numerator3 a z * dinv) +
    coeff a.[1] * (inverse_numerator2 a z * dinv) +
    coeff a.[2] * (inverse_numerator1 a z * dinv) +
    coeff a.[3] * (inverse_numerator0 a z * dinv) =
    (coeff a.[0] * inverse_numerator3 a z +
     coeff a.[1] * inverse_numerator2 a z +
     coeff a.[2] * inverse_numerator1 a z +
     coeff a.[3] * inverse_numerator0 a z) * dinv) 1:/#.
  by rewrite H.
qed.

lemma add_mod_q_congr (x y x' y' : int) :
  x %% q = x' %% q =>
  y %% q = y' %% q =>
  (x + y) %% q = (x' + y') %% q.
proof. by move=> Hx Hy; rewrite -modzDml Hx modzDml -modzDmr Hy modzDmr. qed.

lemma scale_mod_q_congr (c x y : int) :
  x %% q = y %% q =>
  (c * x) %% q = (c * y) %% q.
proof. by move=> Hxy; rewrite -modzMmr Hxy modzMmr. qed.

lemma coeff0_mod_congr_right
    (a b : W16.t Array4.t) (z x0 x1 x2 x3 : int) :
  coeff b.[0] %% q = x0 %% q =>
  coeff b.[1] %% q = x1 %% q =>
  coeff b.[2] %% q = x2 %% q =>
  coeff b.[3] %% q = x3 %% q =>
  coeff0 a b z %% q =
    (coeff a.[0] * x0 +
     z * (coeff a.[1] * x3 + coeff a.[2] * x2 + coeff a.[3] * x1)) %% q.
proof.
  move=> H0 H1 H2 H3.
  rewrite /coeff0.
  apply add_mod_q_congr.
  + exact (scale_mod_q_congr (coeff a.[0]) (coeff b.[0]) x0 H0).
  apply scale_mod_q_congr.
  apply add_mod_q_congr.
  + apply add_mod_q_congr.
    - exact (scale_mod_q_congr (coeff a.[1]) (coeff b.[3]) x3 H3).
    exact (scale_mod_q_congr (coeff a.[2]) (coeff b.[2]) x2 H2).
  exact (scale_mod_q_congr (coeff a.[3]) (coeff b.[1]) x1 H1).
qed.

lemma coeff1_mod_congr_right
    (a b : W16.t Array4.t) (z x0 x1 x2 x3 : int) :
  coeff b.[0] %% q = x0 %% q =>
  coeff b.[1] %% q = x1 %% q =>
  coeff b.[2] %% q = x2 %% q =>
  coeff b.[3] %% q = x3 %% q =>
  coeff1 a b z %% q =
    (coeff a.[0] * x1 + coeff a.[1] * x0 +
     z * (coeff a.[2] * x3 + coeff a.[3] * x2)) %% q.
proof.
  move=> H0 H1 H2 H3.
  rewrite /coeff1.
  apply add_mod_q_congr.
  + apply add_mod_q_congr.
    - exact (scale_mod_q_congr (coeff a.[0]) (coeff b.[1]) x1 H1).
    exact (scale_mod_q_congr (coeff a.[1]) (coeff b.[0]) x0 H0).
  apply scale_mod_q_congr.
  apply add_mod_q_congr.
  + exact (scale_mod_q_congr (coeff a.[2]) (coeff b.[3]) x3 H3).
  exact (scale_mod_q_congr (coeff a.[3]) (coeff b.[2]) x2 H2).
qed.

lemma coeff2_mod_congr_right
    (a b : W16.t Array4.t) (z x0 x1 x2 x3 : int) :
  coeff b.[0] %% q = x0 %% q =>
  coeff b.[1] %% q = x1 %% q =>
  coeff b.[2] %% q = x2 %% q =>
  coeff b.[3] %% q = x3 %% q =>
  coeff2 a b z %% q =
    (coeff a.[0] * x2 + coeff a.[1] * x1 + coeff a.[2] * x0 +
     z * (coeff a.[3] * x3)) %% q.
proof.
  move=> H0 H1 H2 H3.
  rewrite /coeff2.
  apply add_mod_q_congr.
  + apply add_mod_q_congr.
    - apply add_mod_q_congr.
      * exact (scale_mod_q_congr (coeff a.[0]) (coeff b.[2]) x2 H2).
      exact (scale_mod_q_congr (coeff a.[1]) (coeff b.[1]) x1 H1).
    exact (scale_mod_q_congr (coeff a.[2]) (coeff b.[0]) x0 H0).
  apply scale_mod_q_congr.
  exact (scale_mod_q_congr (coeff a.[3]) (coeff b.[3]) x3 H3).
qed.

lemma coeff3_mod_congr_right
    (a b : W16.t Array4.t) (z x0 x1 x2 x3 : int) :
  coeff b.[0] %% q = x0 %% q =>
  coeff b.[1] %% q = x1 %% q =>
  coeff b.[2] %% q = x2 %% q =>
  coeff b.[3] %% q = x3 %% q =>
  coeff3 a b z %% q =
    (coeff a.[0] * x3 + coeff a.[1] * x2 +
     coeff a.[2] * x1 + coeff a.[3] * x0) %% q.
proof.
  move=> H0 H1 H2 H3.
  rewrite /coeff3.
  apply add_mod_q_congr.
  + apply add_mod_q_congr.
    - apply add_mod_q_congr.
      * exact (scale_mod_q_congr (coeff a.[0]) (coeff b.[3]) x3 H3).
      exact (scale_mod_q_congr (coeff a.[1]) (coeff b.[2]) x2 H2).
    exact (scale_mod_q_congr (coeff a.[2]) (coeff b.[1]) x1 H1).
  exact (scale_mod_q_congr (coeff a.[3]) (coeff b.[0]) x0 H0).
qed.

lemma canonical_qword_coeff (x : int) :
  coeff (canonical_qword x) = x %% q.
proof.
  rewrite /canonical_qword /coeff.
  apply W16.to_sintK_small.
  have Hmod : 0 <= x %% q < q by rewrite /q; smt(modz_cmp).
  move: Hmod; rewrite /q; smt().
qed.

lemma canonical_qword_in_qrange (x : int) :
  in_qrange (canonical_qword x).
proof.
  rewrite /in_qrange canonical_qword_coeff.
  have Hmod : 0 <= x %% q < q by rewrite /q; smt(modz_cmp).
  smt().
qed.

lemma canonical_qword_mod_q (x : int) :
  coeff (canonical_qword x) %% q = x %% q.
proof.
  rewrite canonical_qword_coeff.
  smt(edivzP).
qed.

lemma baseinv_math_spec_word
    (a : W16.t Array4.t) (z dinv : int) (i : int) :
  0 <= i < 4 =>
  (baseinv_math_spec a z dinv).[i] =
    canonical_qword (inverse_numerator_at a z i * dinv).
proof. by move=> Hi; rewrite /baseinv_math_spec Array4.initiE. qed.

lemma baseinv_math_spec_relation
    (a : W16.t Array4.t) (z dinv : int) :
  inverse_coeff_relation a (baseinv_math_spec a z dinv) z dinv.
proof.
  rewrite /inverse_coeff_relation.
  split.
  + rewrite /in_qrange4.
    split.
    - rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
      exact (canonical_qword_in_qrange (inverse_numerator0 a z * dinv)).
    split.
    - rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
      exact (canonical_qword_in_qrange (inverse_numerator1 a z * dinv)).
    split.
    - rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
      exact (canonical_qword_in_qrange (inverse_numerator2 a z * dinv)).
    rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
    exact (canonical_qword_in_qrange (inverse_numerator3 a z * dinv)).
  split.
  + rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
    exact (canonical_qword_mod_q (inverse_numerator0 a z * dinv)).
  split.
  + rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
    exact (canonical_qword_mod_q (inverse_numerator1 a z * dinv)).
  split.
  + rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
    exact (canonical_qword_mod_q (inverse_numerator2 a z * dinv)).
  rewrite baseinv_math_spec_word 1:/# /inverse_numerator_at /=.
  exact (canonical_qword_mod_q (inverse_numerator3 a z * dinv)).
qed.

lemma inverse_coeff_relation_implies_block_inverse
    (a r : W16.t Array4.t) (z dinv : int) :
  determinant_inverse_witness a z dinv =>
  inverse_coeff_relation a r z dinv =>
  block_inverse_qring a r z.
proof.
  move=> Hdet Hrel.
  move: Hrel => [Hrange [H0 [H1 [H2 H3]]]].
  rewrite /block_inverse_qring.
  split; first exact Hrange.
  split.
  + have H := coeff0_mod_congr_right a r z
      (inverse_numerator0 a z * dinv)
      (inverse_numerator1 a z * dinv)
      (inverse_numerator2 a z * dinv)
      (inverse_numerator3 a z * dinv) H0 H1 H2 H3.
    rewrite H scaled_numerator_product0_identity.
    exact Hdet.
  split.
  + have H := coeff1_mod_congr_right a r z
      (inverse_numerator0 a z * dinv)
      (inverse_numerator1 a z * dinv)
      (inverse_numerator2 a z * dinv)
      (inverse_numerator3 a z * dinv) H0 H1 H2 H3.
    rewrite H scaled_numerator_product1_zero.
    done.
  split.
  + have H := coeff2_mod_congr_right a r z
      (inverse_numerator0 a z * dinv)
      (inverse_numerator1 a z * dinv)
      (inverse_numerator2 a z * dinv)
      (inverse_numerator3 a z * dinv) H0 H1 H2 H3.
    rewrite H scaled_numerator_product2_zero.
    done.
  have H := coeff3_mod_congr_right a r z
    (inverse_numerator0 a z * dinv)
    (inverse_numerator1 a z * dinv)
    (inverse_numerator2 a z * dinv)
    (inverse_numerator3 a z * dinv) H0 H1 H2 H3.
  rewrite H scaled_numerator_product3_zero.
  done.
qed.

lemma baseinv_math_spec_block_inverse
    (a : W16.t Array4.t) (z dinv : int) :
  determinant_inverse_witness a z dinv =>
  block_inverse_qring a (baseinv_math_spec a z dinv) z.
proof.
  move=> Hdet.
  exact (inverse_coeff_relation_implies_block_inverse
    a (baseinv_math_spec a z dinv) z dinv Hdet
    (baseinv_math_spec_relation a z dinv)).
qed.
