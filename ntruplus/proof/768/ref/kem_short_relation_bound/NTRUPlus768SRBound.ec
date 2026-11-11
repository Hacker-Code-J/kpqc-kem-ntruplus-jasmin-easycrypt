require import AllCore IntDiv List Distr Ring StdBigop StdOrder.
require import Array768.
require import NTRUPlus768INJCollision NTRUPlus768INJExistence NTRUPlus768OWUniform.
require import NTRUPlus768SRMultiplication NTRUPlus768SRMultiplicationKernel.
require import NTRUPlus768SRMatrixCounting NTRUPlus768SRProbability.
require import NTRUPlus768SRUnion NTRUPlus768SRNumerical.
import RealOrder.

lemma sr_actual_rows_bounded v : inj_short v=>sr_matrix_rows_bounded(sr_mul_matrix v).
proof.
 move=>hv;rewrite /sr_matrix_rows_bounded=>k hk.
 exact(sr_mul_matrix_row_bound v k hv).
qed.

lemma sr_actual_fiber_bound v w : inj_short v=>v<>inj_zero=>
 size(sr_equation_lists(sr_mul_matrix v)w)<=12288^384.
proof.
 move=>hv hn.
 have hb:=sr_matrix_fiber_bound (sr_mul_matrix v)(fun k=>w.[k])sr_residue_lists
 (sr_mul_kernel_trivial v hn)(sr_actual_rows_bounded v hv)sr_residue_lists_uniq _.
 + move=>xs hx;split.
   - exact(sr_residue_list_size xs hx).
   exact(sr_residue_list_range xs hx).
 exact hb.
qed.

lemma sr_fixed_pair_bound v w : inj_short v=>v<>inj_zero=>
 mu ow_uniform_rq(fun h=>inj_relation h v w)<=(12288^384)%r/(3457^768)%r.
proof.
 move=>hv hn;exact(sr_uniform_fixed_pair_height v w (sr_actual_fiber_bound v w hv hn)).
qed.

(* Unconditional numerical bound for the existing all-ring existence event. *)
lemma sr_uniform_bad_mass_244 : inj_uniform_bad_mass<1%r/(2%r^244).
proof.
 have he:0%r<=(12288^384)%r/(3457^768)%r.
 + apply divr_ge0;rewrite le_fromint;apply IntOrder.expr_ge0;done.
 have hb:=sr_uniform_from_nonzero_bound ((12288^384)%r/(3457^768)%r) he _.
 + move=>v w hv hw hn;exact(sr_fixed_pair_bound v w hv hn).
 exact(ler_lt_trans _ _ _ hb sr_union_numeric_integer_bound).
qed.
