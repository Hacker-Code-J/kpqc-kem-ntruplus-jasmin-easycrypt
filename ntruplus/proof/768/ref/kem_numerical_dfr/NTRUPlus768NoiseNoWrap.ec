require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JWord.
require import Array192 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768IntegerConvolution NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768NoiseDecomposition.
import IntOrder Ring.IntID.

lemma sampled_noise_blocks fbuf gbuf r m k : 0<=k<768 =>
 (sampled_m1_noise fbuf gbuf r m).[k]=
 noise_product_blocks (integer_coefficients(poly_cbd1_spec gbuf))
   (integer_coefficients r) k +
 noise_product_blocks (integer_coefficients m)
   (integer_coefficients(poly_cbd1_spec fbuf)) k.
proof.
 move=> hk; rewrite /sampled_m1_noise.
 exact(two_integer_products_noise_blocks _ _ _ _ k hk).
qed.

lemma noise_small_implies_no_wrap fbuf gbuf r m :
 (forall k,0<=k<768 => -1<=coeff m.[k]<=1) =>
 (forall k,0<=k<768 => `|(sampled_m1_noise fbuf gbuf r m).[k]|<576) =>
 sampled_m1_no_wrap fbuf gbuf r m.
proof.
 move=> hm hn; rewrite /sampled_m1_no_wrap=>k hk.
 rewrite sampled_m1_integer_lift_coeff 1:hk.
 have hk_m:=hm k hk; have hk_n:=hn k hk.
 move:hk_n; rewrite ltr_norml; smt().
qed.

lemma no_wrap_violation_noise576 fbuf gbuf r m :
 (forall k,0<=k<768 => -1<=coeff m.[k]<=1) =>
 !sampled_m1_no_wrap fbuf gbuf r m =>
 exists k,0<=k<768 /\ 576<=`|(sampled_m1_noise fbuf gbuf r m).[k]|.
proof.
 move=> hm hn.
 have h:=noise_small_implies_no_wrap fbuf gbuf r m hm.
 smt().
qed.

lemma no_wrap_violation_blocks576 fbuf gbuf r m :
 (forall k,0<=k<768 => -1<=coeff m.[k]<=1) =>
 !sampled_m1_no_wrap fbuf gbuf r m =>
 exists k,0<=k<768 /\
 576<=`|noise_product_blocks (integer_coefficients(poly_cbd1_spec gbuf))
   (integer_coefficients r) k +
 noise_product_blocks (integer_coefficients m)
   (integer_coefficients(poly_cbd1_spec fbuf)) k|.
proof.
 move=> hm hn; have [k [hk hb]]:=no_wrap_violation_noise576 fbuf gbuf r m hm hn.
 exists k; split; first exact hk.
 by rewrite -(sampled_noise_blocks fbuf gbuf r m k hk).
qed.
