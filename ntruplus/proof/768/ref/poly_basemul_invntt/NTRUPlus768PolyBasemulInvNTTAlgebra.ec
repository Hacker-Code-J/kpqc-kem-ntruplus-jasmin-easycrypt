require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemul.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768InvNTTRadix2_4Algebra.
require import NTRUPlus768InvNTTAlgebra.

import Ring.IntID IntOrder.

op poly_basemul_invntt_ready
    (ap bp rp : W16.t Array768.t) : bool =
  poly_basemul_qring ap bp rp 192 /\
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape rp.

lemma in_qrange4_nth
    (a : W16.t Array4.t) (j : int) :
  in_qrange4 a =>
  0 <= j < 4 =>
  in_qrange a.[j].
proof.
  move=> Ha Hj.
  move: Ha => [Ha0 [Ha1 [Ha2 Ha3]]].
  have Hcases : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
  elim Hcases => [-> | [-> | [-> | ->]]].
  + exact Ha0.
  + exact Ha1.
  + exact Ha2.
  exact Ha3.
qed.

lemma block4_nthE
    (p : W16.t Array768.t) (k j : int) :
  0 <= k < 192 =>
  0 <= j < 4 =>
  (block4 p k).[j] = p.[4 * k + j].
proof.
  move=> Hk Hj.
  by rewrite /block4 Array4.initiE 1:/#.
qed.

lemma qring_block_output_qrange
    (ap bp rp : W16.t Array768.t) (k : int) :
  poly_basemul_qring ap bp rp 192 =>
  0 <= k < 192 =>
  in_qrange4 (block4 rp k).
proof.
  move=> Hqring Hk.
  have Hblock := Hqring k Hk.
  by move: Hblock => [Hrange _].
qed.

lemma blockwise_qrange4_implies_invntt_input_shape
    (p : W16.t Array768.t) :
  (forall k, 0 <= k < 192 => in_qrange4 (block4 p k)) =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape p.
proof.
  move=> Hblocks j Hj.
  have Hk : 0 <= j %/ 4 < 192 by smt().
  have Hj4 : 0 <= j %% 4 < 4 by smt().
  have Hblock : in_qrange4 (block4 p (j %/ 4)).
  + exact (Hblocks (j %/ 4) Hk).
  have Hnth : in_qrange (block4 p (j %/ 4)).[j %% 4].
  + exact (in_qrange4_nth (block4 p (j %/ 4)) (j %% 4) Hblock Hj4).
  have -> : p.[j] = (block4 p (j %/ 4)).[j %% 4].
  + rewrite (block4_nthE p (j %/ 4) (j %% 4) Hk Hj4).
    have -> : 4 * (j %/ 4) + (j %% 4) = j by smt(edivzP).
    done.
  exact Hnth.
qed.

lemma in_qrange768_implies_invntt_input_shape
    (p : W16.t Array768.t) :
  in_qrange768 p =>
  NTRUPlus768InvNTTRadix2_4Algebra.qrange_input_shape p.
proof.
  move=> Hp.
  apply blockwise_qrange4_implies_invntt_input_shape.
  exact Hp.
qed.

lemma poly_basemul_qring_implies_invntt_ready
    (ap bp rp : W16.t Array768.t) :
  poly_basemul_qring ap bp rp 192 =>
  poly_basemul_invntt_ready ap bp rp.
proof.
  move=> Hqring.
  split; first exact Hqring.
  apply blockwise_qrange4_implies_invntt_input_shape.
  by move=> k Hk; exact (qring_block_output_qrange ap bp rp k Hqring Hk).
qed.

lemma poly_basemul_qring_inverse_invntt_spec_algebra
    (ap bp rp : W16.t Array768.t) :
  poly_basemul_qring ap bp rp 192 =>
  NTRUPlus768InvNTTAlgebra.inverse_invntt_algebra rp
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec rp).
proof.
  move=> Hqring.
  have Hready := poly_basemul_qring_implies_invntt_ready ap bp rp Hqring.
  move: Hready => [_ Hshape].
  exact (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec_algebra rp Hshape).
qed.

lemma poly_basemul_qring_inverse_invntt_output_qrange
    (ap bp rp : W16.t Array768.t) (j : int) :
  poly_basemul_qring ap bp rp 192 =>
  0 <= j < 768 =>
  -q <= coeff (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec rp).[j] < q.
proof.
  move=> Hqring Hj.
  have Hready := poly_basemul_qring_implies_invntt_ready ap bp rp Hqring.
  move: Hready => [_ Hshape].
  exact (NTRUPlus768InvNTTAlgebra.inverse_invntt_output_qrange rp j Hshape Hj).
qed.

lemma poly_basemul_correct_invntt_ready
    (rp0 ap0 bp0 : W16.t Array768.t) :
  in_s12range768 ap0 =>
  in_s12range768 bp0 =>
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    poly_basemul_invntt_ready ap0 bp0 res] = 1%r.
proof.
  move=> Hap Hbp.
  conseq poly_basemul_lossless (poly_basemul_functional rp0 ap0 bp0).
  move=> &hr _ result; split.
  + move=> [_ Hword].
    split.
    + trivial.
    exact Hword.
  move=> [_ Hword]; split.
  + have Hqring :=
      poly_basemul_word_to_qring_s12 ap0 bp0 result Hap Hbp Hword.
    exact (poly_basemul_qring_implies_invntt_ready ap0 bp0 result Hqring).
  exact Hword.
qed.

lemma poly_basemul_correct_invntt_ready_qrange
    (rp0 ap0 bp0 : W16.t Array768.t) :
  in_qrange768 ap0 =>
  in_qrange768 bp0 =>
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    poly_basemul_invntt_ready ap0 bp0 res] = 1%r.
proof.
  move=> Hap Hbp.
  exact (poly_basemul_correct_invntt_ready rp0 ap0 bp0
    (in_qrange768_in_s12range768 ap0 Hap)
    (in_qrange768_in_s12range768 bp0 Hbp)).
qed.
