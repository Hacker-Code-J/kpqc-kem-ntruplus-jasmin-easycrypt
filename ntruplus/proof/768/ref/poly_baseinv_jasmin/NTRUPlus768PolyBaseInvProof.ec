require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array4 Array96 Array768.
require import NTRUPlus768PolyBaseInv.
require import NTRUPlus768BaseInv.
require import NTRUPlus768BaseInvProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemul.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBaseInvBridge.

(* Scope: this theory proves the freshly extracted Jasmin poly_baseinv core
   against the exact scalar baseinv word result, including all-success and
   fail-closed zeroization outcomes.  Production-C semantics and C/Jasmin
   program equivalence remain executable seams.  The early determinant
   failure path is secret-dependent, so no CT or SCT claim is made. *)

op poly_zero : W16.t Array768.t =
  Array768.init (fun _ => W16.zero).

op poly_block_zeta (k : int) : W16.t =
  if k %% 2 = 0 then
    NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[k %/ 2]
  else
    -NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[k %/ 2].

op poly_block_status (ap : W16.t Array768.t) (k : int) : W64.t =
  exact_status (block4 ap k) (poly_block_zeta k).

op poly_block_output (ap : W16.t Array768.t) (k : int) : W16.t Array4.t =
  exact_output (Array4.init (fun _ => W16.zero))
    (block4 ap k) (poly_block_zeta k).

op poly_apply_output
    (rp ap : W16.t Array768.t) (k : int) : W16.t Array768.t =
  if poly_block_status ap k = W64.of_int 0 then
    write_block4 rp k (poly_block_output ap k)
  else rp.

op poly_apply_result
    (rp ap : W16.t Array768.t) (k : int) :
    W16.t Array768.t * W64.t =
  (poly_apply_output rp ap k, poly_block_status ap k).

op poly_pair_output
    (rp ap : W16.t Array768.t) (i : int) : W16.t Array768.t =
  if poly_block_status ap (2 * i) = W64.of_int 1 then rp
  else
    poly_apply_output
      (poly_apply_output rp ap (2 * i)) ap (2 * i + 1).

op poly_pair_status (ap : W16.t Array768.t) (i : int) : W64.t =
  if poly_block_status ap (2 * i) = W64.of_int 1 then W64.of_int 1
  else poly_block_status ap (2 * i + 1).

op poly_pair_result
    (rp ap : W16.t Array768.t) (i : int) :
    W16.t Array768.t * W64.t =
  (poly_pair_output rp ap i, poly_pair_status ap i).

op poly_blocks_succeed (ap : W16.t Array768.t) (upto : int) : bool =
  forall k, 0 <= k < upto =>
    poly_block_status ap k = W64.of_int 0.

op poly_blocks_written
    (ap rp : W16.t Array768.t) (upto : int) : bool =
  forall k, 0 <= k < upto =>
    block4 rp k = poly_block_output ap k.

op poly_has_failed (ap : W16.t Array768.t) (upto : int) : bool =
  exists k, 0 <= k < upto /\
    poly_block_status ap k = W64.of_int 1.

op poly_baseinv_exact_post
    (ap rp : W16.t Array768.t) (status : W64.t) : bool =
  (status = W64.of_int 0 /\
   poly_blocks_succeed ap 192 /\
   poly_blocks_written ap rp 192) \/
  (status = W64.of_int 1 /\
   poly_has_failed ap 192 /\
   rp = poly_zero).

op zero_prefix (p : W16.t Array768.t) (upto : int) : W16.t Array768.t =
  Array768.init (fun j => if j < upto then W16.zero else p.[j]).

lemma poly_zetas96_eq :
  NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96 =
  NTRUPlus768PolyBasemul.nTRUPLUS_ZETAS96.
proof.
  by rewrite /NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96
             /NTRUPlus768PolyBasemul.nTRUPLUS_ZETAS96.
qed.

lemma poly_block_zeta_eq (k : int) :
  poly_block_zeta k = block_zeta k.
proof. by rewrite /poly_block_zeta /block_zeta poly_zetas96_eq. qed.

lemma poly_block_zeta_even (i : int) :
  0 <= i < 96 =>
  poly_block_zeta (2 * i) =
    NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[i].
proof.
  move=> Hi.
  rewrite /poly_block_zeta.
  have -> : (2 * i) %% 2 = 0 by smt().
  have -> : (2 * i) %/ 2 = i by smt().
  done.
qed.

lemma poly_block_zeta_odd (i : int) :
  0 <= i < 96 =>
  poly_block_zeta (2 * i + 1) =
    -NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[i].
proof.
  move=> Hi.
  rewrite /poly_block_zeta.
  have -> : (2 * i + 1) %% 2 = 1 by smt().
  have -> : (2 * i + 1) %/ 2 = i by smt().
  done.
qed.

lemma poly_baseinv_w64_zero_neq_one :
  W64.of_int 0 <> W64.of_int 1.
proof. by rewrite W64.to_uint_eq !W64.of_uintK /=. qed.

lemma poly_block_status_cases (ap : W16.t Array768.t) (k : int) :
  poly_block_status ap k = W64.of_int 0 \/
  poly_block_status ap k = W64.of_int 1.
proof.
  rewrite /poly_block_status /exact_status.
  by case (exact_state5 (block4 ap k) (poly_block_zeta k) = W16.zero).
qed.

lemma poly_block_status_not_one_zero
    (ap : W16.t Array768.t) (k : int) :
  poly_block_status ap k <> W64.of_int 1 =>
  poly_block_status ap k = W64.of_int 0.
proof.
  move=> Hnot.
  have Hcases := poly_block_status_cases ap k.
  smt().
qed.

lemma poly_pair_status_cases (ap : W16.t Array768.t) (i : int) :
  poly_pair_status ap i = W64.of_int 0 \/
  poly_pair_status ap i = W64.of_int 1.
proof.
  move: (poly_block_status_cases ap (2 * i)) => [Heven0 | Heven1].
  + have Hevennot : poly_block_status ap (2 * i) <> W64.of_int 1
      by smt(poly_baseinv_w64_zero_neq_one).
    rewrite /poly_pair_status Hevennot.
    exact (poly_block_status_cases ap (2 * i + 1)).
  right.
  by rewrite /poly_pair_status Heven1.
qed.

lemma poly_pair_status_not_one_zero
    (ap : W16.t Array768.t) (i : int) :
  poly_pair_status ap i <> W64.of_int 1 =>
  poly_pair_status ap i = W64.of_int 0.
proof.
  move=> Hnot.
  have Hcases := poly_pair_status_cases ap i.
  smt().
qed.

lemma exact_output_status_zero_irrelevant
    (out1 out2 a : W16.t Array4.t) (zeta_word : W16.t) :
  exact_status a zeta_word = W64.of_int 0 =>
  exact_output out1 a zeta_word = exact_output out2 a zeta_word.
proof.
  rewrite /exact_status /exact_output.
  case (exact_state5 a zeta_word = W16.zero) => Hzero /=.
  + smt(poly_baseinv_w64_zero_neq_one).
  done.
qed.

lemma array4_zero_fill (a : W16.t Array4.t) :
  a.[0 <- W16.zero]
   .[1 <- W16.zero]
   .[2 <- W16.zero]
   .[3 <- W16.zero] =
  Array4.init (fun _ => W16.zero).
proof.
  apply Array4.tP => i Hi.
  have Hcases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 by smt().
  elim Hcases => [-> | [-> | [-> | ->]]];
    by rewrite Array4.initiE 1:/# !Array4.get_setE.
qed.

lemma array4_slice_zero (a : W16.t Array4.t) :
  Array4.init (fun i => a.[0 + i]) = a.
proof.
  apply Array4.tP => i Hi.
  by rewrite Array4.initiE 1:Hi /=.
qed.

lemma poly_blocks_succeed_zero (ap : W16.t Array768.t) :
  poly_blocks_succeed ap 0.
proof. by rewrite /poly_blocks_succeed; smt(). qed.

lemma poly_blocks_written_zero (ap rp : W16.t Array768.t) :
  poly_blocks_written ap rp 0.
proof. by rewrite /poly_blocks_written; smt(). qed.

lemma poly_has_failed_zero (ap : W16.t Array768.t) :
  !poly_has_failed ap 0.
proof. by rewrite /poly_has_failed; smt(). qed.

lemma poly_blocks_succeed_extend
    (ap : W16.t Array768.t) (k : int) :
  0 <= k < 192 =>
  poly_blocks_succeed ap k =>
  poly_block_status ap k = W64.of_int 0 =>
  poly_blocks_succeed ap (k + 1).
proof.
  move=> Hk Hprefix Hstatus k' Hk'.
  case (k' = k) => [-> | Hneq].
  + exact Hstatus.
  apply Hprefix; smt().
qed.

lemma poly_blocks_written_extend
    (ap rp : W16.t Array768.t) (k : int) :
  0 <= k < 192 =>
  poly_blocks_written ap rp k =>
  poly_blocks_written ap
    (write_block4 rp k (poly_block_output ap k)) (k + 1).
proof.
  move=> Hk Hprefix k' Hk'.
  case (k' = k) => [-> | Hneq].
  + rewrite block4_write_same 1:Hk.
    done.
  have Hsame :
      block4 (write_block4 rp k (poly_block_output ap k)) k' =
      block4 rp k'.
  + apply block4_write_other; smt().
  rewrite Hsame.
  apply Hprefix; smt().
qed.

lemma poly_has_failed_current
    (ap : W16.t Array768.t) (k upto : int) :
  0 <= k < upto =>
  poly_block_status ap k = W64.of_int 1 =>
  poly_has_failed ap upto.
proof. by move=> Hk Hstatus; exists k. qed.

lemma poly_pair_success_extend
    (ap rp : W16.t Array768.t) (i : int) :
  0 <= i < 96 =>
  poly_blocks_succeed ap (2 * i) =>
  poly_blocks_written ap rp (2 * i) =>
  poly_pair_status ap i = W64.of_int 0 =>
  poly_blocks_succeed ap (2 * (i + 1)) /\
  poly_blocks_written ap (poly_pair_output rp ap i) (2 * (i + 1)).
proof.
  move=> Hi Hsuccess Hwritten Hpair.
  have Heven0 : poly_block_status ap (2 * i) = W64.of_int 0.
  + have Hcases := poly_block_status_cases ap (2 * i).
    rewrite /poly_pair_status in Hpair.
    smt(poly_baseinv_w64_zero_neq_one).
  rewrite /poly_pair_status in Hpair.
  have Hodd0 : poly_block_status ap (2 * i + 1) = W64.of_int 0
    by smt(poly_baseinv_w64_zero_neq_one).
  have Hsuccess1 := poly_blocks_succeed_extend ap (2 * i) _ Hsuccess Heven0;
    first smt().
  have Hsuccess2 := poly_blocks_succeed_extend ap (2 * i + 1) _ Hsuccess1 Hodd0;
    first smt().
  have Hwritten1 := poly_blocks_written_extend ap rp (2 * i) _ Hwritten;
    first smt().
  have Hwritten2 := poly_blocks_written_extend ap
      (write_block4 rp (2 * i) (poly_block_output ap (2 * i)))
      (2 * i + 1) _ Hwritten1;
    first smt().
  split; first by have -> : 2 * (i + 1) = 2 * i + 2 by ring.
  rewrite /poly_pair_output /poly_apply_output Heven0 Hodd0 /=
          poly_baseinv_w64_zero_neq_one.
  have -> : 2 * (i + 1) = 2 * i + 2 by ring.
  exact Hwritten2.
qed.

lemma poly_pair_failure
    (ap : W16.t Array768.t) (i : int) :
  0 <= i < 96 =>
  poly_pair_status ap i = W64.of_int 1 =>
  poly_has_failed ap 192.
proof.
  move=> Hi Hpair.
  move: (poly_block_status_cases ap (2 * i)) => [Heven0 | Heven1].
  + rewrite /poly_pair_status in Hpair.
    have Hodd : poly_block_status ap (2 * i + 1) = W64.of_int 1
      by smt(poly_baseinv_w64_zero_neq_one).
    have HoddRange : 0 <= 2 * i + 1 < 192 by smt().
    exact (poly_has_failed_current ap (2 * i + 1) 192 HoddRange Hodd).
  have HevenRange : 0 <= 2 * i < 192 by smt().
  exact (poly_has_failed_current ap (2 * i) 192 HevenRange Heven1).
qed.

lemma poly_blocks_succeed_no_failure
    (ap : W16.t Array768.t) (upto : int) :
  poly_blocks_succeed ap upto => !poly_has_failed ap upto.
proof.
  move=> Hsuccess.
  rewrite /poly_blocks_succeed in Hsuccess.
  rewrite /poly_has_failed.
  smt(poly_baseinv_w64_zero_neq_one).
qed.

lemma poly_no_failure_blocks_succeed
    (ap : W16.t Array768.t) (upto : int) :
  !poly_has_failed ap upto => poly_blocks_succeed ap upto.
proof.
  move=> Hnone.
  rewrite /poly_has_failed in Hnone.
  move=> k Hk.
  have Hcases := poly_block_status_cases ap k.
  move: Hcases => [Hzero | Hone]; first exact Hzero.
  smt().
qed.

lemma poly_baseinv_exact_status_zero_iff
    (ap rp : W16.t Array768.t) (status : W64.t) :
  poly_baseinv_exact_post ap rp status =>
  (status = W64.of_int 0 <=> poly_blocks_succeed ap 192).
proof.
  move=> Hpost.
  move: Hpost => [[Hstatus [Hsuccess Hwritten]] |
                  [Hstatus [Hfailed Hzero]]].
  + split => //.
  split.
  + smt(poly_baseinv_w64_zero_neq_one).
  move=> Hsuccess.
  have Hnone := poly_blocks_succeed_no_failure ap 192 Hsuccess.
  smt().
qed.

lemma poly_baseinv_exact_status_one_iff
    (ap rp : W16.t Array768.t) (status : W64.t) :
  poly_baseinv_exact_post ap rp status =>
  (status = W64.of_int 1 <=> poly_has_failed ap 192).
proof.
  move=> Hpost.
  move: Hpost => [[Hstatus [Hsuccess Hwritten]] |
                  [Hstatus [Hfailed Hzero]]].
  + split.
    - smt(poly_baseinv_w64_zero_neq_one).
    move=> Hfailed.
    have Hnone := poly_blocks_succeed_no_failure ap 192 Hsuccess.
    smt().
  split => //.
qed.

lemma poly_baseinv_exact_failure_zero
    (ap rp : W16.t Array768.t) (status : W64.t) :
  poly_baseinv_exact_post ap rp status =>
  status = W64.of_int 1 =>
  rp = poly_zero.
proof.
  move=> Hpost Hone.
  move: Hpost => [[Hzero [Hsuccess Hwritten]] |
                  [Hstatus [Hfailed Hzero]]].
  + smt(poly_baseinv_w64_zero_neq_one).
  exact Hzero.
qed.

lemma zero_prefix_zero (p : W16.t Array768.t) :
  zero_prefix p 0 = p.
proof.
  apply Array768.tP => j Hj.
  rewrite /zero_prefix Array768.initiE 1:Hj /=.
  smt().
qed.

lemma zero_prefix_step (p : W16.t Array768.t) (upto : int) :
  0 <= upto < 768 =>
  (zero_prefix p upto).[upto <- W16.zero] = zero_prefix p (upto + 1).
proof.
  move=> Hupto.
  apply Array768.tP => j Hj.
  rewrite /zero_prefix Array768.initiE 1:Hj.
  case (j = upto) => [-> | Hneq].
  + rewrite Array768.get_setE 1:/# Array768.initiE 1:/#.
    smt().
  rewrite Array768.get_setE 1:/# Array768.initiE 1:Hj.
  smt().
qed.

lemma zero_prefix_full (p : W16.t Array768.t) :
  zero_prefix p 768 = poly_zero.
proof.
  apply Array768.tP => j Hj.
  by rewrite /zero_prefix /poly_zero !Array768.initiE 1,2:Hj /=; smt().
qed.

lemma poly_baseinv_pretrace_eq :
  equiv [
    NTRUPlus768PolyBaseInv.M.baseInv____baseinv_pretrace ~
    NTRUPlus768BaseInv.M.__baseinv_pretrace :
    ={arg} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma poly_baseinv_pretrace_functional
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  hoare [NTRUPlus768PolyBaseInv.M.baseInv____baseinv_pretrace :
    a0 = a.[0] /\ a1 = a.[1] /\ a2 = a.[2] /\ a3 = a.[3] /\
    zeta_0 = zeta_word ==>
    res = exact_pretrace_result a zeta_word].
proof.
  conseq poly_baseinv_pretrace_eq
    (baseinv_pretrace_functional a zeta_word).
  + smt().
  smt().
qed.

lemma poly_baseinv_success_eq :
  equiv [
    NTRUPlus768PolyBaseInv.M.baseInv____baseinv_success ~
    NTRUPlus768BaseInv.M.__baseinv_success :
    ={arg} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma poly_baseinv_success_functional
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  hoare [NTRUPlus768PolyBaseInv.M.baseInv____baseinv_success :
    a0 = a.[0] /\ a1 = a.[1] /\ a2 = a.[2] /\ a3 = a.[3] /\
    t0 = exact_state2 a zeta_word /\
    t1 = exact_state3 a zeta_word /\
    t2 = exact_state4 a zeta_word /\
    determinant = exact_state5 a zeta_word ==>
    res = exact_success_raw_result a zeta_word].
proof.
  conseq poly_baseinv_success_eq
    (baseinv_success_functional a zeta_word).
  + smt().
  smt().
qed.

lemma poly_baseinv_scalar_functional
    (rp0 ap0 : W16.t Array4.t) (z0 : W16.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_block :
    tr = rp0 /\ ta = ap0 /\ zeta_0 = z0 ==>
    res = exact_result rp0 ap0 z0].
proof.
  proc.
  seq 1 : (t0 = exact_state2 ap0 z0 /\
           t1 = exact_state3 ap0 z0 /\
           t2 = exact_state4 ap0 z0 /\
           t3 = exact_state5 ap0 z0 /\
           tr = rp0 /\ ta = ap0).
  + call (poly_baseinv_pretrace_functional ap0 z0).
    auto => />.
  if.
  + auto => /> Hzero.
    by rewrite /exact_result /exact_output /exact_status Hzero.
  wp.
  call (poly_baseinv_success_functional ap0 z0).
  auto => /> Hnonzero.
  rewrite /exact_result /exact_output /exact_status Hnonzero
          /exact_success_raw_result.
  rewrite (exact_success_store_eq rp0 ap0 z0).
  done.
qed.

lemma poly_baseinv_scalar_lossless :
  islossless NTRUPlus768PolyBaseInv.M.__poly_baseinv_block.
proof.
  proc; islossless.
qed.

lemma poly_baseinv_apply_functional
    (rp0 ap0 : W16.t Array768.t) (block0 : W64.t) (z0 : W16.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_apply :
    rp = rp0 /\ ap = ap0 /\ block = block0 /\ zeta_0 = z0 /\
    0 <= W64.to_uint block0 < 192 /\
    z0 = poly_block_zeta (W64.to_uint block0) ==>
    res = poly_apply_result rp0 ap0 (W64.to_uint block0)].
proof.
  proc.
  seq 14 :
    (rp = rp0 /\ ap = ap0 /\
     block = block0 /\ zeta_0 = z0 /\
     z0 = poly_block_zeta (W64.to_uint block0) /\
     W64.to_uint off = 4 * W64.to_uint block0 /\
     W64.to_uint (off + W64.one) = 4 * W64.to_uint block0 + 1 /\
     W64.to_uint (off + W64.of_int 2) = 4 * W64.to_uint block0 + 2 /\
     W64.to_uint (off + W64.of_int 3) = 4 * W64.to_uint block0 + 3 /\
     ta = block4 ap0 (W64.to_uint block0) /\
     trp = Array4.init (fun _ => W16.zero)).
  + wp; skip => &hr [#] /= -> -> -> -> Hblock Hzeta.
    have Hoff :
        W64.to_uint (block0 `<<` W8.of_int 2) =
        4 * W64.to_uint block0.
    + rewrite /(`<<`) /= W64.to_uint_shl 1:/# /=.
      rewrite modz_small 1:/#.
      ring.
    have HoffN : forall n,
        0 <= n <= 3 =>
        W64.to_uint ((block0 `<<` W8.of_int 2) + W64.of_int n) =
        4 * W64.to_uint block0 + n.
    + move=> n Hn.
      rewrite W64.to_uintD_small.
      - rewrite Hoff W64.of_uintK modz_small 1:/#.
        smt().
      by rewrite Hoff W64.of_uintK modz_small 1:/#.
    have Hoff1 := HoffN 1 _; first smt().
    have Hoff2 := HoffN 2 _; first smt().
    have Hoff3 := HoffN 3 _; first smt().
    have Hload : forall (dst : W16.t Array4.t),
        dst.[0 <- ap0.[4 * W64.to_uint block0]]
           .[1 <- ap0.[4 * W64.to_uint block0 + 1]]
           .[2 <- ap0.[4 * W64.to_uint block0 + 2]]
           .[3 <- ap0.[4 * W64.to_uint block0 + 3]] =
        block4 ap0 (W64.to_uint block0).
    + move=> dst.
      rewrite load4_updates.
      apply load4_eq_block4; smt().
    rewrite Hoff Hoff1 Hoff2 Hoff3 !Hload array4_zero_fill
            array4_slice_zero.
    done.
  seq 1 :
    (rp = rp0 /\ ap = ap0 /\
     W64.to_uint off = 4 * W64.to_uint block0 /\
     W64.to_uint (off + W64.one) = 4 * W64.to_uint block0 + 1 /\
     W64.to_uint (off + W64.of_int 2) = 4 * W64.to_uint block0 + 2 /\
     W64.to_uint (off + W64.of_int 3) = 4 * W64.to_uint block0 + 3 /\
     status = poly_block_status ap0 (W64.to_uint block0) /\
     (status = W64.of_int 0 =>
       trp = poly_block_output ap0 (W64.to_uint block0))).
  + call (poly_baseinv_scalar_functional
      (Array4.init (fun _ => W16.zero))
      (block4 ap0 (W64.to_uint block0)) z0).
    auto => />.
  if.
  + auto => /> &hr Hoff Hoff1 Hoff2 Hoff3 Hstatus Houtput.
    rewrite /poly_apply_result /poly_apply_output /write_block4 Houtput /=.
    rewrite (Hstatus Houtput).
    rewrite Hoff Hoff1 Hoff2 Hoff3.
    done.
  skip => &hrf [Hpref Hnotf].
  move: Hpref => [Hrpf Hrest1f].
  move: Hrest1f => [Hapf Hrest2f].
  move: Hrest2f => [Hofff Hrest3f].
  move: Hrest3f => [Hoff1f Hrest4f].
  move: Hrest4f => [Hoff2f Hrest5f].
  move: Hrest5f => [Hoff3f Hrest6f].
  move: Hrest6f => [Hstatf Himpf].
  rewrite /poly_apply_result /poly_apply_output /=.
  smt().
qed.

lemma poly_baseinv_pair_functional
    (rp0 ap0 : W16.t Array768.t) (i0 : W64.t) (z0 : W16.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_pair :
    rp = rp0 /\ ap = ap0 /\ i = i0 /\ zeta_0 = z0 /\
    0 <= W64.to_uint i0 < 96 /\
    z0 = NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[W64.to_uint i0] ==>
    res = poly_pair_result rp0 ap0 (W64.to_uint i0)].
proof.
  proc.
  seq 3 :
    (ap = ap0 /\
     0 <= W64.to_uint i0 < 96 /\
     z0 = NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[W64.to_uint i0] /\
     block = (i0 `<<` W8.of_int 1) /\
     W64.to_uint block = 2 * W64.to_uint i0 /\
     rp = (poly_apply_result rp0 ap0 (2 * W64.to_uint i0)).`1 /\
     status = (poly_apply_result rp0 ap0 (2 * W64.to_uint i0)).`2 /\
     zeta_0 = z0).
  + call (poly_baseinv_apply_functional rp0 ap0
      (i0 `<<` W8.of_int 1) z0).
    wp; skip => &hr [#] /= -> -> -> -> Hi Hzeta.
    have Hshift :
        W64.to_uint (i0 `<<` W8.of_int 1) = 2 * W64.to_uint i0.
    + rewrite /(`<<`) /= W64.to_uint_shl 1:/# /=.
      rewrite modz_small 1:/#.
      ring.
    rewrite Hshift poly_block_zeta_even 1:Hi.
    done.
    auto => />.
    smt().
  if.
  + seq 2 :
      (ap = ap0 /\
       0 <= W64.to_uint i0 < 96 /\
       z0 = NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[W64.to_uint i0] /\
       rp = (poly_apply_result rp0 ap0 (2 * W64.to_uint i0)).`1 /\
       status = (poly_apply_result rp0 ap0 (2 * W64.to_uint i0)).`2 /\
       status <> W64.of_int 1 /\
       block = ((i0 `<<` W8.of_int 1) + W64.one) /\
       W64.to_uint block = 2 * W64.to_uint i0 + 1 /\
       zeta_0 = -z0 /\
       -z0 = poly_block_zeta (2 * W64.to_uint i0 + 1)).
    + wp; skip => &hr [Hpre Hcond].
      move: Hpre => [Hap [Hi [Hztable [Hblock [Hoff
        [Hrp [Hstatus Hzeta]]]]]]].
      have Hnext :
          W64.to_uint (block{hr} + W64.one) =
          W64.to_uint block{hr} + 1.
      + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
      have Hnot1 :
          (poly_apply_result rp0 ap0 (2 * W64.to_uint i0)).`2 <>
          W64.one.
      + rewrite -Hstatus.
        exact Hcond.
      have Hoff1 :
          W64.to_uint ((i0 `<<` W8.of_int 1) + W64.one) =
          2 * W64.to_uint i0 + 1.
      + rewrite -Hblock Hnext Hoff.
        done.
      rewrite Hap Hrp Hstatus Hblock Hzeta.
      rewrite poly_block_zeta_odd 1:Hi.
      rewrite Hztable.
      by rewrite /= Hi Hnot1 Hoff1.
    call (poly_baseinv_apply_functional
      (poly_apply_result rp0 ap0 (2 * W64.to_uint i0)).`1
      ap0 ((i0 `<<` W8.of_int 1) + W64.one) (-z0)).
    auto => />.
  auto => /> &hr Hrp Hstatus Hone.
  rewrite /poly_apply_result in Hstatus.
  rewrite /poly_pair_result /poly_pair_output /poly_pair_status
          /poly_apply_result Hone Hstatus /=.
  smt().
  auto => />.
  rewrite /poly_pair_result /poly_pair_output /poly_pair_status
          /poly_apply_result /poly_apply_output.
  smt(poly_baseinv_w64_zero_neq_one).
qed.

lemma poly_baseinv_zero_functional (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_zero :
    rp = rp0 ==> res = poly_zero].
proof.
  proc.
  seq 1 : (rp = zero_prefix rp0 0 /\ j = W64.of_int 0).
  + auto => />.
    by rewrite zero_prefix_zero.
  while (0 <= W64.to_uint j <= 768 /\
         rp = zero_prefix rp0 (W64.to_uint j)); last first.
  + skip => &hr [Hj Hrp].
    split.
    - split.
      + by rewrite Hrp W64.to_uint0; smt().
      by rewrite Hrp W64.to_uint0; exact Hj.
    move=> j1 rp1 Hexit [Hj1 Hrp1].
    rewrite W64.ultE /= in Hexit.
    have Hjend : W64.to_uint j1 = 768 by smt().
    by rewrite Hrp1 Hjend zero_prefix_full.
  auto => /> &hr HjLow HjHigh Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hj : 0 <= W64.to_uint j{hr} < 768 by smt().
  have Hnext :
      W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  split; first by rewrite Hnext; smt().
  rewrite Hnext.
  exact (zero_prefix_step rp0 (W64.to_uint j{hr}) Hj).
qed.

lemma poly_baseinv_functional
    (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = ap0 ==>
    poly_baseinv_exact_post ap0 res.`1 res.`2].
proof.
  proc.
  seq 5 :
    (ap = ap0 /\
     zetasp = Array96.init (fun j =>
       NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[0 + j]) /\
     i = W64.of_int 0 /\ status = W64.of_int 0 /\
     poly_blocks_succeed ap0 0 /\
     poly_blocks_written ap0 rp 0).
  + auto => />.
    split; first exact (poly_blocks_succeed_zero ap0).
    exact (poly_blocks_written_zero ap0 rp0).
  seq 1 :
    (ap = ap0 /\
     ((status = W64.of_int 0 /\
       poly_blocks_succeed ap0 192 /\
       poly_blocks_written ap0 rp 192) \/
      (status = W64.of_int 1 /\
       poly_has_failed ap0 192))).
  + while
      (0 <= W64.to_uint i <= 96 /\
       ap = ap0 /\
       zetasp = Array96.init (fun j =>
         NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[0 + j]) /\
       ((status = W64.of_int 0 /\
         poly_blocks_succeed ap0 (2 * W64.to_uint i) /\
         poly_blocks_written ap0 rp (2 * W64.to_uint i)) \/
        (status = W64.of_int 1 /\
         W64.to_uint i = 96 /\
         poly_has_failed ap0 192))); last first.
    + skip => &hr [Hap [Hzet [Hi0 [Hstatus [Hsuccess Hwritten]]]]].
      split.
      - split.
        + by rewrite Hi0 W64.to_uint0; smt().
        split; first exact Hap.
        split; first exact Hzet.
        left.
        rewrite Hi0 W64.to_uint0 /=.
        done.
      move=> i1 rp1 status1 Hexit
        [Hi [Hap1 [Hzet1 Hstate]]].
      rewrite W64.ultE /= in Hexit.
      split; first exact Hap1.
      move: Hstate => [[Hzero [Hsuccess1 Hwritten1]] |
                      [Hone [Hi96Fail Hfailed]]].
      - left.
        split; first exact Hzero.
        have Hsuccess192 : poly_blocks_succeed ap0 192.
        + move=> k Hk.
          apply Hsuccess1; smt().
        have Hwritten192 : poly_blocks_written ap0 rp1 192.
        + move=> k Hk.
          apply Hwritten1; smt().
        split; first exact Hsuccess192.
        exact Hwritten192.
      right.
      split; first exact Hone.
      exact Hfailed.
  wp.
  ecall (poly_baseinv_pair_functional rp ap0 i
    (Array96.init (fun j =>
      NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[0 + j])).[
        W64.to_uint i]).
  wp.
  auto => /> &hr HiLow HiHigh Hstate Hcond.
  have Hi96 : 0 <= W64.to_uint i{hr} < 96.
  + rewrite W64.ultE /= in Hcond.
    smt().
  have Hzeta :
      (Array96.init (fun j =>
        NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[0 + j])).[
          W64.to_uint i{hr}] =
      NTRUPlus768PolyBaseInv.nTRUPLUS_ZETAS96.[W64.to_uint i{hr}].
  + by rewrite Array96.initiE 1:Hi96 /=.
  rewrite Hzeta /=.
  have Hactive :
      status{hr} = W64.of_int 0 /\
      poly_blocks_succeed ap0 (2 * W64.to_uint i{hr}) /\
      poly_blocks_written ap0 rp{hr} (2 * W64.to_uint i{hr}).
  + move: Hstate => [Hactive | [Hone [Hiend Hfailed]]].
    - exact Hactive.
    smt().
  move: Hactive => [Hstatus [Hsuccess Hwritten]].
  split; first smt().
  move=> Hlt.
  split.
  + move=> Hpair1.
    right.
    exact (poly_pair_failure ap0 (W64.to_uint i{hr}) Hi96 Hpair1).
  move=> HpairNot1.
  have Hpair0 :
      poly_pair_status ap0 (W64.to_uint i{hr}) = W64.of_int 0.
  + apply poly_pair_status_not_one_zero.
    exact HpairNot1.
  have Hnext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have [Hsuccess' Hwritten'] :=
    poly_pair_success_extend ap0 rp{hr} (W64.to_uint i{hr})
      Hi96 Hsuccess Hwritten Hpair0.
  split; first by rewrite Hnext; smt().
  left.
  rewrite Hnext /=.
  split; [exact Hsuccess' | exact Hwritten'].
  if.
  + ecall (poly_baseinv_zero_functional rp).
    auto => /> &hr Hstate.
    have Hfailed : poly_has_failed ap0 192.
    + move: Hstate => [[Honezero _] | Hfailed].
      - smt(poly_baseinv_w64_zero_neq_one).
      exact Hfailed.
    rewrite /poly_baseinv_exact_post.
    right.
    split; first done.
    split; first exact Hfailed.
    done.
  auto => /> &hr Hstate Hcond.
  move: Hstate => [[Hzero [Hsuccess Hwritten]] |
                  [Hone Hfailed]].
  + rewrite /poly_baseinv_exact_post.
    left.
    split; first exact Hzero.
    split; first exact Hsuccess.
    exact Hwritten.
  smt().
qed.

lemma poly_exact_success_implies_poly_baseinv_success
    (ap rp : W16.t Array768.t) :
  in_qrange768 ap =>
  poly_blocks_succeed ap 192 =>
  poly_blocks_written ap rp 192 =>
  poly_baseinv_success ap rp.
proof.
  move=> Hap Hsucceed Hwritten.
  rewrite /poly_baseinv_success.
  move=> k Hk.
  have Hak :
      NTRUPlus768BasemulAlgebra.in_qrange4 (block4 ap k).
  + exact (in_qrange768_block4 ap k Hap Hk).
  have Hzeta : in_qrange (poly_block_zeta k).
  + rewrite poly_block_zeta_eq.
    exact (block_zeta_in_qrange k Hk).
  have Hterminal :
      zeta_decode (poly_block_zeta k) = terminal_value k.
  + rewrite poly_block_zeta_eq.
    by move: (block_zeta_math_terminal_value k Hk);
       rewrite /block_zeta_math.
  have Hzrel := zeta_decode_relation (poly_block_zeta k) Hzeta.
  rewrite Hterminal in Hzrel.
  have Hstatus := Hsucceed k Hk.
  rewrite /poly_block_status in Hstatus.
  have Hdet :
      inverse_determinant (block4 ap k) (terminal_value k) %% q <> 0.
  + have Hiff := exact_status_determinant_nonzero_iff
      (block4 ap k) (poly_block_zeta k) (terminal_value k)
      Hak Hzeta Hzrel.
    move: Hiff.
    rewrite Hstatus.
    smt().
  have Hinv := exact_success_block_inverse
    (Array4.init (fun _ => W16.zero))
    (block4 ap k) (poly_block_zeta k) (terminal_value k)
    Hak Hzeta Hzrel Hdet.
  rewrite (Hwritten k Hk) /poly_block_output.
  exact Hinv.
qed.

lemma poly_baseinv_exact_success_semantic
    (ap rp : W16.t Array768.t) (status : W64.t) :
  in_qrange768 ap =>
  poly_baseinv_exact_post ap rp status =>
  status = W64.of_int 0 =>
  poly_baseinv_success ap rp.
proof.
  move=> Hap Hpost Hzero.
  move: Hpost => [[_ [Hsucceed Hwritten]] |
                  [Hone [Hfailed Hrp]]].
  + exact (poly_exact_success_implies_poly_baseinv_success
      ap rp Hap Hsucceed Hwritten).
  smt(poly_baseinv_w64_zero_neq_one).
qed.

lemma poly_baseinv_success_bridge
    (rp0 ap0 : W16.t Array768.t) :
  in_qrange768 ap0 =>
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = ap0 ==>
    res.`2 = W64.of_int 0 => poly_baseinv_success ap0 res.`1].
proof.
  move=> Hap.
  conseq (poly_baseinv_functional rp0 ap0) => />
    &hr HapEq result Hexact Hstatus.
  have Hrange : in_qrange768 ap{hr} by rewrite HapEq.
  have Hsucc := poly_baseinv_exact_success_semantic
    ap{hr} result.`1 result.`2 Hrange Hexact Hstatus.
  exact Hsucc.
qed.

lemma poly_baseinv_output_qrange_on_success
    (rp0 ap0 : W16.t Array768.t) :
  in_qrange768 ap0 =>
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = ap0 ==>
    res.`2 = W64.of_int 0 => in_qrange768 res.`1].
proof.
  move=> Hap.
  conseq (poly_baseinv_functional rp0 ap0) => />
    &hr HapEq result Hexact Hstatus.
  have Hrange : in_qrange768 ap{hr} by rewrite HapEq.
  have Hsucc := poly_baseinv_exact_success_semantic
    ap{hr} result.`1 result.`2 Hrange Hexact Hstatus.
  apply (poly_baseinv_success_output_qrange ap{hr} result.`1).
  exact Hsucc.
qed.

lemma poly_baseinv_product_identity_on_success
    (rp0 ap0 : W16.t Array768.t) :
  in_qrange768 ap0 =>
  hoare [NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :
    rp = rp0 /\ ap = ap0 ==>
    res.`2 = W64.of_int 0 =>
    poly_basemul_qring ap0 res.`1 ntt_block_identity 192].
proof.
  move=> Hap.
  conseq (poly_baseinv_functional rp0 ap0) => />
    &hr HapEq result Hexact Hstatus.
  have Hrange : in_qrange768 ap{hr} by rewrite HapEq.
  have Hsucc := poly_baseinv_exact_success_semantic
    ap{hr} result.`1 result.`2 Hrange Hexact Hstatus.
  apply (poly_baseinv_success_product_identity ap{hr} result.`1).
  exact Hsucc.
qed.
