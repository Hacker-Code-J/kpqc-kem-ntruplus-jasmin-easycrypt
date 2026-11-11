require import AllCore IntDiv List Ring StdBigop.
require import Array768.
require import NTRUPlus768IntegerConvolution NTRUPlus768NoiseDecomposition.
require import NTRUPlus768INJCollision NTRUPlus768SRMultiplication NTRUPlus768SRMatrixCounting.

(* The native Coq obligation is an integer convolution statement. Its
   generated context preserves the actual finite sums and Phi reduction
   weights; no determinant or nonsingularity assumption is added. *)
lemma sr_convolution_kernel (v a:int->int) :
 (exists i,0<=i<768 /\ v i<>0)=>
 (forall k,0<=k<768=>
  Bigint.BIA.bigi predT(fun i=>Bigint.BIA.bigi predT(fun j=>
   a i*v j*noise_reduce_weight k (i+j))0 768)0 768=0)=>
 forall i,0<=i<768=>a i=0.
proof.
 rewrite /noise_reduce_weight /b2i.
 coq check "sr_convolution_kernel" (range_geq range_ltn).
qed.

lemma sr_mul_kernel_trivial v : v<>inj_zero=>sr_integer_kernel_trivial(sr_mul_matrix v).
proof.
 move=>hv;rewrite /sr_integer_kernel_trivial=>a ha.
 have hp:integer_product(Array768.init a)v=inj_zero.
 + rewrite -sr_mul_matrix_product;apply Array768.tP=>k hk.
   rewrite(sr_matvec_get _ _ k hk)(inj_zero_get k hk).
   have he:Bigint.BIA.bigi predT(fun j=>sr_mul_matrix v k j*(Array768.init a).[j])0 768=
     Bigint.BIA.bigi predT(fun j=>sr_mul_matrix v k j*a j)0 768.
   + apply Bigint.BIA.eq_big_int=>j hj /=;by rewrite Array768.initiE.
   by rewrite he(ha k hk).
 have hn:exists i,0<=i<768 /\ v.[i]<>0.
 + have hz:(forall i,0<=i<768=>v.[i]=0)=>v=inj_zero.
   + move=>hz;apply Array768.tP=>i hi;rewrite(inj_zero_get i hi);exact(hz i hi).
   smt().
 apply(sr_convolution_kernel(fun i=>v.[i])a hn)=>k hk.
 have he:Bigint.BIA.bigi predT(fun i=>Bigint.BIA.bigi predT(fun j=>
   a i*v.[j]*noise_reduce_weight k (i+j))0 768)0 768=
  (integer_product(Array768.init a)v).[k].
 + rewrite(integer_product_coefficient _ _ k hk).
   apply Bigint.BIA.eq_big_int=>i hi /=.
   apply Bigint.BIA.eq_big_int=>j hj /=.
   by rewrite Array768.initiE.
 by rewrite he hp(inj_zero_get k hk).
qed.
