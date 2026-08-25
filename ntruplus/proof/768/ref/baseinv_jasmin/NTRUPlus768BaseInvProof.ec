require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array4.
require import NTRUPlus768BaseInv.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768BaseInvAlgebra.
require import NTRUPlus768BaseInvWordAlgebra.
require import NTRUPlus768FqInvAlgebra.
require import NTRUPlus768FqInvProof.

(* Scope: this theory proves the freshly extracted Jasmin __baseinv_core
   procedure against the exact scalar word trace.  Production-C semantics and
   C/Jasmin program equivalence remain executable source/differential seams;
   the export wrapper is not extracted here.  The determinant branch is
   secret-dependent, so this milestone makes no CT or SCT claim.  It also
   makes no poly_baseinv or downstream keygen/decapsulation claim. *)

op exact_state0 (a : W16.t Array4.t) : W16.t =
  mred_word_spec
    (coeff a.[2] * coeff a.[2] - 2 * coeff a.[1] * coeff a.[3]).

op exact_state1 (a : W16.t Array4.t) : W16.t =
  mred_word_spec (coeff a.[3] * coeff a.[3]).

op exact_state2 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff a.[0] * coeff a.[0] + coeff (exact_state0 a) * coeff zeta_word).

op exact_state3 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff a.[1] * coeff a.[1] + coeff (exact_state1 a) * coeff zeta_word -
     2 * coeff a.[0] * coeff a.[2]).

op exact_state4 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec (coeff (exact_state3 a zeta_word) * coeff zeta_word).

op exact_state5 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff (exact_state2 a zeta_word) * coeff (exact_state2 a zeta_word) -
     coeff (exact_state3 a zeta_word) * coeff (exact_state4 a zeta_word)).

op exact_invword (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  fqinv_concrete_spec (exact_state5 a zeta_word).

op exact_state6 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff a.[0] * coeff (exact_state2 a zeta_word) +
     coeff a.[2] * coeff (exact_state4 a zeta_word)).

op exact_state7 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff a.[3] * coeff (exact_state4 a zeta_word) +
     coeff a.[1] * coeff (exact_state2 a zeta_word)).

op exact_state8 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff a.[2] * coeff (exact_state2 a zeta_word) +
     coeff a.[0] * coeff (exact_state3 a zeta_word)).

op exact_state9 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff a.[1] * coeff (exact_state3 a zeta_word) +
     coeff a.[3] * coeff (exact_state2 a zeta_word)).

op exact_state10 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff (exact_state6 a zeta_word) * coeff (exact_invword a zeta_word)).

op exact_state11 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff (exact_state7 a zeta_word) * coeff (exact_invword a zeta_word)).

op exact_state12 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff (exact_state8 a zeta_word) * coeff (exact_invword a zeta_word)).

op exact_state13 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  mred_word_spec
    (coeff (exact_state9 a zeta_word) * coeff (exact_invword a zeta_word)).

op exact_state
    (a : W16.t Array4.t, zeta_word : W16.t, i : int) : W16.t =
  if i = 0 then exact_state0 a else
  if i = 1 then exact_state1 a else
  if i = 2 then exact_state2 a zeta_word else
  if i = 3 then exact_state3 a zeta_word else
  if i = 4 then exact_state4 a zeta_word else
  if i = 5 then exact_state5 a zeta_word else
  if i = 6 then exact_state6 a zeta_word else
  if i = 7 then exact_state7 a zeta_word else
  if i = 8 then exact_state8 a zeta_word else
  if i = 9 then exact_state9 a zeta_word else
  if i = 10 then exact_state10 a zeta_word else
  if i = 11 then exact_state11 a zeta_word else
  if i = 12 then exact_state12 a zeta_word else
  if i = 13 then exact_state13 a zeta_word else
  W16.zero.

op exact_output
    (rp a : W16.t Array4.t, zeta_word : W16.t) : W16.t Array4.t =
  if exact_state5 a zeta_word = W16.zero then rp
  else baseinv_signed_output (exact_state a zeta_word).

op exact_status
    (a : W16.t Array4.t, zeta_word : W16.t) : W64.t =
  if exact_state5 a zeta_word = W16.zero then W64.of_int 1 else W64.of_int 0.

op exact_result
    (rp a : W16.t Array4.t, zeta_word : W16.t) : W16.t Array4.t * W64.t =
  (exact_output rp a zeta_word, exact_status a zeta_word).

op exact_pretrace_result
    (a : W16.t Array4.t, zeta_word : W16.t) :
    W16.t * W16.t * W16.t * W16.t =
  (exact_state2 a zeta_word,
   exact_state3 a zeta_word,
   exact_state4 a zeta_word,
   exact_state5 a zeta_word).

op word_state0 (a : W16.t Array4.t) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce
    (NTRUPlus768BasemulProof.mul_i16 a.[2] a.[2] -
     (NTRUPlus768BasemulProof.mul_i16 a.[1] a.[3] +
      NTRUPlus768BasemulProof.mul_i16 a.[1] a.[3])).

op word_state1 (a : W16.t Array4.t) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce
    (NTRUPlus768BasemulProof.mul_i16 a.[3] a.[3]).

op word_state2 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce
    (NTRUPlus768BasemulProof.mul_i16 a.[0] a.[0] +
     NTRUPlus768BasemulProof.mul_i16 (word_state0 a) zeta_word).

op word_state3 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce
    (NTRUPlus768BasemulProof.mul_i16 a.[1] a.[1] +
     NTRUPlus768BasemulProof.mul_i16 (word_state1 a) zeta_word -
     (NTRUPlus768BasemulProof.mul_i16 a.[0] a.[2] +
      NTRUPlus768BasemulProof.mul_i16 a.[0] a.[2])).

op word_state4 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce
    (NTRUPlus768BasemulProof.mul_i16 (word_state3 a zeta_word) zeta_word).

op word_state5 (a : W16.t Array4.t, zeta_word : W16.t) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce
    (NTRUPlus768BasemulProof.mul_i16
       (word_state2 a zeta_word) (word_state2 a zeta_word) -
     NTRUPlus768BasemulProof.mul_i16
       (word_state3 a zeta_word) (word_state4 a zeta_word)).

op word_pretrace_result
    (a : W16.t Array4.t, zeta_word : W16.t) :
    W16.t * W16.t * W16.t * W16.t =
  (word_state2 a zeta_word,
   word_state3 a zeta_word,
   word_state4 a zeta_word,
   word_state5 a zeta_word).

op exact_success_raw_result
    (a : W16.t Array4.t, zeta_word : W16.t) :
    W16.t * W16.t * W16.t * W16.t =
  (exact_state10 a zeta_word,
   exact_state11 a zeta_word,
   exact_state12 a zeta_word,
   exact_state13 a zeta_word).

lemma baseinv_w64_zero_neq_one : W64.of_int 0 <> W64.of_int 1.
proof. by rewrite W64.to_uint_eq !W64.of_uintK /=. qed.

lemma exact_invword_final_step
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  fqmul_word_spec fq_rinv_word
    (fqinv_state (exact_state5 a zeta_word) 15) =
  exact_invword a zeta_word.
proof.
  by rewrite /exact_invword /fqinv_concrete_spec /fqinv_state /=.
qed.

lemma mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768BaseInv.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = NTRUPlus768BasemulProof.mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768BaseInv.M.__montgomery_reduce :
    a = a0 ==> res = NTRUPlus768BasemulProof.montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

lemma fqmul_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768BaseInv.M.__fqmul :
    a = a0 /\ b = b0 ==> res = fqmul_word_spec a0 b0].
proof.
  proc.
  seq 1 : (c = NTRUPlus768BasemulProof.mul_i16 a0 b0).
  + inline NTRUPlus768BaseInv.M.__mul_i16.
    auto => />.
  inline NTRUPlus768BaseInv.M.__montgomery_reduce.
  auto => />.
qed.

lemma fqinv_functional (a0 : W16.t) :
  hoare [NTRUPlus768BaseInv.M.__fqinv :
    a = a0 ==> res = fqinv_concrete_spec a0].
proof.
  proc.
  call (fqmul_functional (W16.of_int (-682)) (fqinv_state15 a0)).
  call (fqmul_functional (fqinv_state14 a0) (fqinv_state8 a0)).
  call (fqmul_functional (fqinv_state13 a0) (fqinv_state13 a0)).
  call (fqmul_functional (fqinv_state12 a0) (fqinv_state12 a0)).
  call (fqmul_functional (fqinv_state11 a0) (fqinv_state11 a0)).
  call (fqmul_functional (fqinv_state10 a0) (fqinv_state10 a0)).
  call (fqmul_functional (fqinv_state9 a0) (fqinv_state9 a0)).
  call (fqmul_functional (fqinv_state7 a0) (fqinv_state7 a0)).
  call (fqmul_functional (fqinv_state4 a0) (fqinv_state7 a0)).
  call (fqmul_functional (fqinv_state6 a0) a0).
  call (fqmul_functional (fqinv_state5 a0) (fqinv_state5 a0)).
  call (fqmul_functional (fqinv_state4 a0) (fqinv_state3 a0)).
  call (fqmul_functional (fqinv_state0 a0) (fqinv_state2 a0)).
  call (fqmul_functional (fqinv_state2 a0) (fqinv_state2 a0)).
  call (fqmul_functional (fqinv_state1 a0) (fqinv_state1 a0)).
  call (fqmul_functional (fqinv_state0 a0) (fqinv_state0 a0)).
  call (fqmul_functional a0 a0).
  auto => />.
qed.

lemma word_state0_exact (a : W16.t Array4.t) :
  word_state0 a = exact_state0 a.
proof.
  rewrite /word_state0 /exact_state0 /mred_word_spec.
  rewrite (_ : 2 * coeff a.[1] * coeff a.[3] =
      coeff a.[1] * coeff a.[3] + coeff a.[1] * coeff a.[3]); first ring.
  by rewrite !mul_i16E !W32.of_intD' !W32.of_intS'.
qed.

lemma word_state1_exact (a : W16.t Array4.t) :
  word_state1 a = exact_state1 a.
proof. by rewrite /word_state1 /exact_state1 /mred_word_spec mul_i16E. qed.

lemma word_state2_exact
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  word_state2 a zeta_word = exact_state2 a zeta_word.
proof.
  by rewrite /word_state2 /exact_state2 word_state0_exact /mred_word_spec
             !mul_i16E !W32.of_intD'.
qed.

lemma word_state3_exact
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  word_state3 a zeta_word = exact_state3 a zeta_word.
proof.
  rewrite /word_state3 /exact_state3 word_state1_exact /mred_word_spec.
  rewrite (_ : 2 * coeff a.[0] * coeff a.[2] =
      coeff a.[0] * coeff a.[2] + coeff a.[0] * coeff a.[2]); first ring.
  by rewrite !mul_i16E !W32.of_intD' !W32.of_intS'.
qed.

lemma word_state4_exact
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  word_state4 a zeta_word = exact_state4 a zeta_word.
proof.
  by rewrite /word_state4 /exact_state4 word_state3_exact /mred_word_spec
             mul_i16E.
qed.

lemma word_state5_exact
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  word_state5 a zeta_word = exact_state5 a zeta_word.
proof.
  by rewrite /word_state5 /exact_state5 word_state2_exact word_state3_exact
             word_state4_exact /mred_word_spec !mul_i16E !W32.of_intS'.
qed.

lemma word_pretrace_result_exact
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  word_pretrace_result a zeta_word = exact_pretrace_result a zeta_word.
proof.
  by rewrite /word_pretrace_result /exact_pretrace_result word_state2_exact
             word_state3_exact word_state4_exact word_state5_exact.
qed.

lemma baseinv_pretrace_word_functional
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  hoare [NTRUPlus768BaseInv.M.__baseinv_pretrace :
    a0 = a.[0] /\ a1 = a.[1] /\ a2 = a.[2] /\ a3 = a.[3] /\
    zeta_0 = zeta_word ==>
    res = word_pretrace_result a zeta_word].
proof.
  proc.
  inline NTRUPlus768BaseInv.M.__mul_i16
         NTRUPlus768BaseInv.M.__montgomery_reduce.
  auto => />.
qed.

lemma baseinv_pretrace_functional
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  hoare [NTRUPlus768BaseInv.M.__baseinv_pretrace :
    a0 = a.[0] /\ a1 = a.[1] /\ a2 = a.[2] /\ a3 = a.[3] /\
    zeta_0 = zeta_word ==>
    res = exact_pretrace_result a zeta_word].
proof.
  rewrite -(word_pretrace_result_exact a zeta_word).
  exact (baseinv_pretrace_word_functional a zeta_word).
qed.

lemma baseinv_success_functional
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  hoare [NTRUPlus768BaseInv.M.__baseinv_success :
    a0 = a.[0] /\ a1 = a.[1] /\ a2 = a.[2] /\ a3 = a.[3] /\
    t0 = exact_state2 a zeta_word /\
    t1 = exact_state3 a zeta_word /\
    t2 = exact_state4 a zeta_word /\
    determinant = exact_state5 a zeta_word ==>
    res = exact_success_raw_result a zeta_word].
proof.
  proc.
  inline NTRUPlus768BaseInv.M.__mul_i16
         NTRUPlus768BaseInv.M.__montgomery_reduce.
  wp.
  call (fqinv_functional (exact_state5 a zeta_word)).
  auto => />.
qed.

lemma exact_pretrace_eq
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  forall i, 0 <= i < 10 =>
    exact_state a zeta_word i =
      mred_word_spec
        (baseinv_trace_expr a zeta_word (exact_state a zeta_word) i).
proof.
  move=> i Hi.
  have Hcases :
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
    i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 by smt().
  move: Hcases => [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    by rewrite /exact_state /baseinv_trace_expr /=.
qed.

lemma exact_fulltrace_eq
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  forall i, 0 <= i < 14 =>
    exact_state a zeta_word i =
      mred_word_spec
        (baseinv_full_trace_expr
          a zeta_word (exact_invword a zeta_word)
          (exact_state a zeta_word) i).
proof.
  move=> i Hi.
  have Hcases :
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/
    i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 by smt().
  move: Hcases => [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
    [-> | [-> | [-> | ->]]]]]]]]]]]]];
    by rewrite /exact_state /baseinv_full_trace_expr /baseinv_trace_expr
               /baseinv_final_mul_expr /=.
qed.

lemma exact_status_trace5_zero
    (a : W16.t Array4.t) (zeta_word : W16.t) :
  exact_status a zeta_word = W64.of_int 1 <=>
  exact_state5 a zeta_word = W16.zero.
proof.
  rewrite /exact_status.
  case (exact_state5 a zeta_word = W16.zero) => Hzero /=;
    smt(baseinv_w64_zero_neq_one).
qed.

lemma exact_output_fail_unchanged
    (rp a : W16.t Array4.t) (zeta_word : W16.t) :
  exact_state5 a zeta_word = W16.zero =>
  exact_output rp a zeta_word = rp.
proof.
  move=> Hzero.
  rewrite /exact_output Hzero.
  done.
qed.

lemma exact_output_success_value
    (rp a : W16.t Array4.t) (zeta_word : W16.t) :
  exact_state5 a zeta_word <> W16.zero =>
  exact_output rp a zeta_word =
    baseinv_signed_output (exact_state a zeta_word).
proof.
  move=> Hnz.
  rewrite /exact_output.
  by case (exact_state5 a zeta_word = W16.zero); smt().
qed.

lemma signed_word_word_neg (w : W16.t) :
  -w = signed_word w.
proof.
  have Hof_sint : W16.of_int (W16.to_sint w) = w.
  + apply W16.to_uint_eq.
    rewrite W16.of_uintK W16.to_sintE /W16.smod.
    case (2 ^ (16 - 1) <= W16.to_uint w) => Hsign.
    - rewrite (_ : (W16.to_uint w - W16.modulus) %% W16.modulus =
                   W16.to_uint w %% W16.modulus) 1:/#.
      by rewrite W16.to_uint_mod.
    by rewrite W16.to_uint_mod.
  by rewrite /signed_word /coeff -W16.of_intN' Hof_sint.
qed.

lemma exact_success_store_eq
    (rp a : W16.t Array4.t) (zeta_word : W16.t) :
  rp.[0 <- exact_state10 a zeta_word]
    .[1 <- -exact_state11 a zeta_word]
    .[2 <- exact_state12 a zeta_word]
    .[3 <- -exact_state13 a zeta_word] =
  baseinv_signed_output (exact_state a zeta_word).
proof.
  apply Array4.tP => i Hi.
  have Hcases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 by smt().
  elim Hcases => [-> | [-> | [-> | ->]]];
    by rewrite /baseinv_signed_output Array4.initiE 1:/#
               !Array4.get_setE /exact_state ?signed_word_word_neg.
qed.

lemma exact_status_determinant_zero_iff
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (exact_status a zeta_word = W64.of_int 1) <=>
  inverse_determinant a z %% q = 0.
proof.
  move=> Ha Hzeta Hz.
  rewrite (exact_status_trace5_zero a zeta_word).
  rewrite -(determinant_zero_iff_trace5_zero
    a zeta_word z (exact_state a zeta_word)
    Ha Hzeta Hz (exact_pretrace_eq a zeta_word)).
  done.
qed.

lemma exact_status_determinant_nonzero_iff
    (a : W16.t Array4.t) (zeta_word : W16.t) (z : int) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  (exact_status a zeta_word = W64.of_int 0) <=>
  inverse_determinant a z %% q <> 0.
proof.
  move=> Ha Hzeta Hz.
  rewrite /exact_status.
  have Hiff := determinant_zero_iff_trace5_zero
    a zeta_word z (exact_state a zeta_word)
    Ha Hzeta Hz (exact_pretrace_eq a zeta_word).
  rewrite /exact_state /= in Hiff.
  case (exact_state5 a zeta_word = W16.zero) => Hzero.
  + move: Hiff; rewrite Hzero => Hiff.
    split => //; smt().
  move: Hiff; rewrite Hzero => Hiff.
  split => //; smt().
qed.

lemma exact_success_inverse_relation
    (rp a : W16.t Array4.t) (zeta_word : W16.t) (z : int) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  inverse_determinant a z %% q <> 0 =>
  inverse_coeff_relation
    a (exact_output rp a zeta_word) z
    (coeff (exact_invword a zeta_word) * exp Rinv 3).
proof.
  move=> Ha Hzeta Hz Hdet.
  have Hnz := determinant_nonzero_implies_trace5_nonzero
    a zeta_word z (exact_state a zeta_word)
    Ha Hzeta Hz (exact_pretrace_eq a zeta_word) Hdet.
  rewrite (exact_output_success_value rp a zeta_word Hnz).
  exact (baseinv_word_trace_inverse_relation
    a zeta_word (exact_invword a zeta_word) z
    (exact_state a zeta_word) (fqinv_state (exact_state5 a zeta_word))
    Ha Hzeta Hz (exact_fulltrace_eq a zeta_word)
    (fqinv_state_step (exact_state5 a zeta_word))
    (exact_invword_final_step a zeta_word)
    Hdet).
qed.

lemma exact_success_block_inverse
    (rp a : W16.t Array4.t) (zeta_word : W16.t) (z : int) :
  in_qrange4 a =>
  in_qrange zeta_word =>
  zeta_mont_relation zeta_word z =>
  inverse_determinant a z %% q <> 0 =>
  block_inverse_qring a (exact_output rp a zeta_word) z.
proof.
  move=> Ha Hzeta Hz Hdet.
  have Hnz := determinant_nonzero_implies_trace5_nonzero
    a zeta_word z (exact_state a zeta_word)
    Ha Hzeta Hz (exact_pretrace_eq a zeta_word) Hdet.
  rewrite (exact_output_success_value rp a zeta_word Hnz).
  exact (baseinv_word_trace_block_inverse
    a zeta_word (exact_invword a zeta_word) z
    (exact_state a zeta_word) (fqinv_state (exact_state5 a zeta_word))
    Ha Hzeta Hz (exact_fulltrace_eq a zeta_word)
    (fqinv_state_step (exact_state5 a zeta_word))
    (exact_invword_final_step a zeta_word)
    Hdet).
qed.

lemma baseinv_functional
    (rp0 input0 : W16.t Array4.t) (z0 : W16.t) :
  hoare [NTRUPlus768BaseInv.M.__baseinv_core :
    rp = rp0 /\ ap = input0 /\ zeta_0 = z0 ==>
    res = exact_result rp0 input0 z0].
proof.
  proc.
  seq 6 : (rp = rp0 /\
           a0 = input0.[0] /\ a1 = input0.[1] /\
           a2 = input0.[2] /\ a3 = input0.[3] /\
           t0 = exact_state2 input0 z0 /\
           t1 = exact_state3 input0 z0 /\
           t2 = exact_state4 input0 z0 /\
           t3 = exact_state5 input0 z0).
  + call (baseinv_pretrace_functional input0 z0).
    auto => />.
  if.
  + auto => /> Hzero.
    rewrite /exact_result /exact_output /exact_status Hzero.
    done.
  wp.
  call (baseinv_success_functional input0 z0).
  auto => /> Hnonzero.
  rewrite /exact_result /exact_output /exact_status Hnonzero
          /exact_success_raw_result.
  rewrite (exact_success_store_eq rp0 input0 z0).
  done.
qed.

lemma baseinv_lossless :
  islossless NTRUPlus768BaseInv.M.__baseinv_core.
proof.
  proc; islossless.
qed.

lemma baseinv_correct
    (rp0 input0 : W16.t Array4.t) (z0 : W16.t) :
  phoare [NTRUPlus768BaseInv.M.__baseinv_core :
    rp = rp0 /\ ap = input0 /\ zeta_0 = z0 ==>
    res = exact_result rp0 input0 z0] = 1%r.
proof.
  by conseq baseinv_lossless (baseinv_functional rp0 input0 z0).
qed.
