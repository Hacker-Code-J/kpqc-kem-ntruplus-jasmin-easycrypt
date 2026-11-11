require import AllCore IntDiv List Ring StdBigop StdOrder.
require import Array768.
require import NTRUPlus768INJCollision.
require import NTRUPlus768IntegerConvolution NTRUPlus768NoiseDecomposition.
import IntOrder Ring.IntID.

type sr_matrix = int -> int -> int.

(* Rows are output coefficients and columns are multiplier coefficients.
   Each entry is the signed sum of at most two coefficients of v. The
   four cases are the actual reduction by X^768-X^384+1. *)
op sr_mul_matrix (v:inj_vector) : sr_matrix = fun k j =>
 let i = j %% 384 in
 let p = noise_partner k i in
 if k < 384 then
   if i <= k then (if j < 384 then v.[p] else -v.[p+384])
   else (if j < 384 then -v.[p+384] else -(v.[p]+v.[p+384]))
 else
   if i <= k-384 then (if j < 384 then v.[p+384] else v.[p]+v.[p+384])
   else (if j < 384 then v.[p]+v.[p+384] else v.[p]).

op sr_matvec (m:sr_matrix) (a:inj_vector) : inj_vector =
 Array768.init(fun k=>Bigint.BIA.bigi predT(fun j=>m k j*a.[j])0 768).
op sr_row_sqnorm (m:sr_matrix) (k:int) : int =
 Bigint.BIA.bigi predT(fun j=>m k j*m k j)0 768.

lemma sr_matvec_get m a k : 0<=k<768=>
 (sr_matvec m a).[k]=Bigint.BIA.bigi predT(fun j=>m k j*a.[j])0 768.
proof. by move=>hk;rewrite /sr_matvec Array768.initiE. qed.

lemma sr_mul_matrix_low v k i : 0<=i<384=>
 sr_mul_matrix v k i=
 let p=noise_partner k i in
 if k<384 then (if i<=k then v.[p] else -v.[p+384])
 else (if i<=k-384 then v.[p+384] else v.[p]+v.[p+384]).
proof. move=>hi;rewrite /sr_mul_matrix modz_small 1:hi;smt(). qed.

lemma sr_mul_matrix_high v k i : 0<=i<384=>
 sr_mul_matrix v k (i+384)=
 let p=noise_partner k i in
 if k<384 then (if i<=k then -v.[p+384] else -(v.[p]+v.[p+384]))
 else (if i<=k-384 then v.[p]+v.[p+384] else v.[p]).
proof.
 move=>hi;have hm:(i+384)%%384=i by smt(modz_small modzDl).
 rewrite /sr_mul_matrix hm;smt().
qed.

lemma sr_mul_matrix_block v a k i : 0<=i<384=>
 sr_mul_matrix v k i*a.[i]+sr_mul_matrix v k (i+384)*a.[i+384]=
 noise_block k i a.[i] a.[i+384]
  v.[noise_partner k i] v.[noise_partner k i+384].
proof.
 move=>hi;rewrite(sr_mul_matrix_low v k i hi)(sr_mul_matrix_high v k i hi)
 /noise_block /=.
 case(k<384)=>h1;case(i<=k)=>h2;case(i<=k-384)=>h3;ring.
qed.

lemma sr_mul_matrix_product a v :
 sr_matvec(sr_mul_matrix v)a=integer_product a v.
proof.
 apply Array768.tP=>k hk.
 rewrite(sr_matvec_get _ a k hk)(integer_product_noise_blocks a v k hk)
 noise_sum_halves /noise_product_blocks.
 apply Bigint.BIA.eq_big_int=>i hi /=.
 exact(sr_mul_matrix_block v a k i hi).
qed.

lemma sr_mul_matrix_entry_bound v k j : inj_short v=>
 -4<=sr_mul_matrix v k j<=4.
proof.
 move=>hv;have hp:=noise_partner_range k (j%%384).
 have h1:=hv (noise_partner k (j%%384)) _;first smt().
 have h2:=hv (noise_partner k (j%%384)+384) _;first smt().
 rewrite /sr_mul_matrix /=;smt().
qed.

lemma sr_mul_matrix_entry_abs v k j : inj_short v=>
 `|sr_mul_matrix v k j|<=4.
proof. move=>hv;rewrite IntOrder.ler_norml;exact(sr_mul_matrix_entry_bound v k j hv). qed.

lemma sr_mul_matrix_entry_square v k j : inj_short v=>
 sr_mul_matrix v k j*sr_mul_matrix v k j<=16.
proof. move=>hv;have h:=sr_mul_matrix_entry_bound v k j hv;smt(). qed.

lemma sr_mul_matrix_row_bound v k : inj_short v=>sr_row_sqnorm(sr_mul_matrix v)k<=12288.
proof.
 move=>hv;have h:sr_row_sqnorm(sr_mul_matrix v)k<=Bigint.BIA.bigi predT(fun _=>16)0 768.
 + rewrite /sr_row_sqnorm;apply Bigint.ler_sum_seq=>j _ _.
   exact(sr_mul_matrix_entry_square v k j hv).
 by move:h;rewrite Bigint.bigi_constz.
qed.
