require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTStage1Algebra.
require import NTRUPlus768Crepmod3.
require import NTRUPlus768Crepmod3Proof.
require import NTRUPlus768Crepmod3Algebra.

import Ring.IntID IntOrder.

(* An integer witness identifies the centered representative of each inverse
   output coefficient.  Its interval is the explicit no-wrap premise. *)
op centered_integer_witness
    (a : W16.t Array768.t) (v : int Array768.t) : bool =
  NTRUPlus768NTTStage1Algebra.input_qrange a /\
  forall j, 0 <= j < 768 =>
    -1728 <= v.[j] <= 1728 /\
    v.[j] %% q = coeff a.[j] %% q.

op message_mod3_witness
    (v : int Array768.t) (m : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    is_trit (coeff m.[j]) /\ v.[j] %% 3 = coeff m.[j] %% 3.

lemma centered_representative_unique (x y : int) :
  -1728 <= x <= 1728 =>
  -1728 <= y <= 1728 =>
  x %% q = y %% q => x = y.
proof.
  rewrite /q.
  smt().
qed.

lemma centered_q_input_unique_witness (x v : int) :
  -q <= x < q =>
  -1728 <= v <= 1728 =>
  v %% q = x %% q => centered_q_input x = v.
proof.
  move=> Hx Hv Hmod.
  apply centered_representative_unique.
  + exact (centered_q_input_range x Hx).
  + exact Hv.
  have Hcongr := centered_q_input_congr x Hx.
  smt().
qed.

lemma trit_mod3_unique (x y : int) :
  is_trit x => is_trit y => x %% 3 = y %% 3 => x = y.
proof.
  rewrite /is_trit.
  smt().
qed.

lemma crepmod3_int_exact_recovery (x v m : int) :
  -q <= x < q =>
  -1728 <= v <= 1728 =>
  v %% q = x %% q =>
  v %% 3 = m %% 3 =>
  is_trit m => crepmod3_int x = m.
proof.
  move=> Hx Hv Hq H3 Hm.
  apply trit_mod3_unique.
  + exact (crepmod3_int_trit x Hx).
  + exact Hm.
  rewrite (crepmod3_int_mod3 x Hx).
  rewrite (centered_q_input_unique_witness x v Hx Hv Hq).
  exact H3.
qed.

lemma crepmod3_word_exact_recovery (a m : W16.t) (v : int) :
  in_qrange a =>
  -1728 <= v <= 1728 =>
  v %% q = coeff a %% q =>
  v %% 3 = coeff m %% 3 =>
  is_trit (coeff m) => crepmod3_word a = m.
proof.
  move=> Ha Hv Hq H3 Hm.
  rewrite (crepmod3_word_qrangeE a Ha).
  rewrite (crepmod3_int_exact_recovery (coeff a) v (coeff m)
    Ha Hv Hq H3 Hm).
  by rewrite -word_from_coeff.
qed.

lemma centered_integer_witness_coefficient
    (a : W16.t Array768.t) (v : int Array768.t) (j : int) :
  centered_integer_witness a v =>
  0 <= j < 768 => centered_q_input (coeff a.[j]) = v.[j].
proof.
  move=> [Ha Hv] Hj.
  have Haj := Ha j Hj.
  have [Hbound Hmod] := Hv j Hj.
  exact (centered_q_input_unique_witness (coeff a.[j]) v.[j]
    Haj Hbound Hmod).
qed.

lemma poly_crepmod3_exact_recovery_coefficient
    (a m : W16.t Array768.t) (v : int Array768.t) (j : int) :
  centered_integer_witness a v =>
  message_mod3_witness v m =>
  0 <= j < 768 =>
  (poly_crepmod3_spec a).[j] = m.[j].
proof.
  move=> [Ha Hv] Hm Hj.
  have Haj := Ha j Hj.
  have [Hbound Hmodq] := Hv j Hj.
  have [Htrit Hmod3] := Hm j Hj.
  rewrite /poly_crepmod3_spec Array768.initiE 1:Hj.
  exact (crepmod3_word_exact_recovery a.[j] m.[j] v.[j]
    Haj Hbound Hmodq Hmod3 Htrit).
qed.

lemma poly_crepmod3_exact_recovery
    (a m : W16.t Array768.t) (v : int Array768.t) :
  centered_integer_witness a v =>
  message_mod3_witness v m => poly_crepmod3_spec a = m.
proof.
  move=> Ha Hm.
  apply Array768.tP => j Hj.
  exact (poly_crepmod3_exact_recovery_coefficient a m v j Ha Hm Hj).
qed.

lemma poly_crepmod3_exact_recovery_functional
    (rp0 a m : W16.t Array768.t) (v : int Array768.t) :
  centered_integer_witness a v =>
  message_mod3_witness v m =>
  hoare [NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    rp = rp0 /\ ap = a ==> res = m].
proof.
  move=> Ha Hm.
  have Hspec := poly_crepmod3_exact_recovery a m v Ha Hm.
  by conseq (NTRUPlus768Crepmod3Proof.poly_crepmod3_functional rp0 a) => />.
qed.

lemma poly_crepmod3_exact_recovery_correct
    (rp0 a m : W16.t Array768.t) (v : int Array768.t) :
  centered_integer_witness a v =>
  message_mod3_witness v m =>
  phoare [NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    rp = rp0 /\ ap = a ==> res = m] = 1%r.
proof.
  move=> Ha Hm.
  by conseq NTRUPlus768Crepmod3Proof.poly_crepmod3_lossless
    (poly_crepmod3_exact_recovery_functional rp0 a m v Ha Hm).
qed.
