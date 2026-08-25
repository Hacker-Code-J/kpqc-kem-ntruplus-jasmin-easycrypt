require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import NTRUPlus768FqInv.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768FqInvAlgebra.

(* Scope: exact extracted Jasmin word trace for fqinv and the power relation
   consumed by the existing nonzero inverse corollary.  This theory does not
   claim production-C formal semantics or procedure equivalence, does not
   provide an inverse contract for fqinv(0), and does not lift any result to
   baseinv or poly_baseinv. *)

op fqinv_state0 (a : W16.t) : W16.t = fqmul_word_spec a a.
op fqinv_state1 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state0 a) (fqinv_state0 a).
op fqinv_state2 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state1 a) (fqinv_state1 a).
op fqinv_state3 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state2 a) (fqinv_state2 a).
op fqinv_state4 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state0 a) (fqinv_state2 a).
op fqinv_state5 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state4 a) (fqinv_state3 a).
op fqinv_state6 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state5 a) (fqinv_state5 a).
op fqinv_state7 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state6 a) a.
op fqinv_state8 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state4 a) (fqinv_state7 a).
op fqinv_state9 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state7 a) (fqinv_state7 a).
op fqinv_state10 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state9 a) (fqinv_state9 a).
op fqinv_state11 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state10 a) (fqinv_state10 a).
op fqinv_state12 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state11 a) (fqinv_state11 a).
op fqinv_state13 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state12 a) (fqinv_state12 a).
op fqinv_state14 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state13 a) (fqinv_state13 a).
op fqinv_state15 (a : W16.t) : W16.t =
  fqmul_word_spec (fqinv_state14 a) (fqinv_state8 a).

op fqinv_state (a : W16.t) (i : int) : W16.t =
  if i = 0 then fqinv_state0 a else
  if i = 1 then fqinv_state1 a else
  if i = 2 then fqinv_state2 a else
  if i = 3 then fqinv_state3 a else
  if i = 4 then fqinv_state4 a else
  if i = 5 then fqinv_state5 a else
  if i = 6 then fqinv_state6 a else
  if i = 7 then fqinv_state7 a else
  if i = 8 then fqinv_state8 a else
  if i = 9 then fqinv_state9 a else
  if i = 10 then fqinv_state10 a else
  if i = 11 then fqinv_state11 a else
  if i = 12 then fqinv_state12 a else
  if i = 13 then fqinv_state13 a else
  if i = 14 then fqinv_state14 a else
  if i = 15 then fqinv_state15 a else
  W16.zero.

op fqinv_concrete_spec (a : W16.t) : W16.t =
  fqmul_word_spec fq_rinv_word (fqinv_state15 a).

lemma fqinv_mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768FqInv.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = NTRUPlus768BasemulProof.mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma fqinv_montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768FqInv.M.__montgomery_reduce :
    a = a0 ==> res = NTRUPlus768BasemulProof.montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

lemma fqinv_fqmul_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768FqInv.M.__fqmul :
    a = a0 /\ b = b0 ==> res = fqmul_word_spec a0 b0].
proof.
  proc.
  seq 1 : (c = NTRUPlus768BasemulProof.mul_i16 a0 b0).
  + inline NTRUPlus768FqInv.M.__mul_i16.
    auto => />.
  inline NTRUPlus768FqInv.M.__montgomery_reduce.
  auto => />.
qed.

lemma fqinv_state_step (a : W16.t) (i : int) :
  0 <= i < 16 =>
  fqmul_word_spec (fqinv_word_left a (fqinv_state a) i)
    (fqinv_word_right a (fqinv_state a) i) = fqinv_state a i.
proof.
  move=> Hi.
  have Hcases :
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
    i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15
    by smt().
  move: Hcases => [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
    [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]];
    by rewrite /fqinv_state /fqinv_word_left /fqinv_word_right /=.
qed.

lemma fqinv_concrete_spec_power_relation (a : W16.t) :
  in_qrange a =>
  in_qrange (fqinv_concrete_spec a) /\
  power_relation a (fqinv_concrete_spec a) peinv reinv.
proof.
  move=> Ha.
  have Hsteps :
      forall i, 0 <= i < 16 =>
        fqmul_word_spec (fqinv_word_left a (fqinv_state a) i)
          (fqinv_word_right a (fqinv_state a) i) = fqinv_state a i.
  + move=> i Hi.
    exact (fqinv_state_step a i Hi).
  have Hout :
      fqmul_word_spec fq_rinv_word (fqinv_state a 15) =
      fqinv_concrete_spec a.
  + by rewrite /fqinv_concrete_spec.
  exact (fqinv_word_spec_power_relation
    a (fqinv_concrete_spec a) (fqinv_state a)
    Ha Hsteps Hout).
qed.

lemma fqinv_functional (a0 : W16.t) :
  hoare [NTRUPlus768FqInv.M.jade_ntruplus_ntruplus768_amd64_ref_fqinv :
    a = a0 ==> res = fqinv_concrete_spec a0].
proof.
  proc.
  call (fqinv_fqmul_functional (W16.of_int (-682)) (fqinv_state15 a0)).
  call (fqinv_fqmul_functional (fqinv_state14 a0) (fqinv_state8 a0)).
  call (fqinv_fqmul_functional (fqinv_state13 a0) (fqinv_state13 a0)).
  call (fqinv_fqmul_functional (fqinv_state12 a0) (fqinv_state12 a0)).
  call (fqinv_fqmul_functional (fqinv_state11 a0) (fqinv_state11 a0)).
  call (fqinv_fqmul_functional (fqinv_state10 a0) (fqinv_state10 a0)).
  call (fqinv_fqmul_functional (fqinv_state9 a0) (fqinv_state9 a0)).
  call (fqinv_fqmul_functional (fqinv_state7 a0) (fqinv_state7 a0)).
  call (fqinv_fqmul_functional (fqinv_state4 a0) (fqinv_state7 a0)).
  call (fqinv_fqmul_functional (fqinv_state6 a0) a0).
  call (fqinv_fqmul_functional (fqinv_state5 a0) (fqinv_state5 a0)).
  call (fqinv_fqmul_functional (fqinv_state4 a0) (fqinv_state3 a0)).
  call (fqinv_fqmul_functional (fqinv_state0 a0) (fqinv_state2 a0)).
  call (fqinv_fqmul_functional (fqinv_state2 a0) (fqinv_state2 a0)).
  call (fqinv_fqmul_functional (fqinv_state1 a0) (fqinv_state1 a0)).
  call (fqinv_fqmul_functional (fqinv_state0 a0) (fqinv_state0 a0)).
  call (fqinv_fqmul_functional a0 a0).
  auto => />.
qed.
