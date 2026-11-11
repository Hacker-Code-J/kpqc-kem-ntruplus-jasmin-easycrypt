require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array96 Array192 Array768 NTRUPlus768PolySOTPEncodeChecked.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PolyCBD1CheckedProof.
require import NTRUPlus768PolySOTPEncodeAlgebra.

(* Actual extracted encoder: no scratch buffer or incoming output reads.
   Its result equals the independent SOTP/CBD1 value specification. *)

lemma poly_sotp_encode_coeff_int msg pad k :
  0 <= k < 768 =>
  poly_cbd1_coeff_int (poly_sotp_encode_input msg pad) k =
    poly_cbd1_bit (pad.[k %/ 8] +^ msg.[k %/ 8]) (k %% 8) -
    poly_cbd1_bit pad.[96 + k %/ 8] (k %% 8).
proof.
  move=> hk.
  have hi : 0 <= k %/ 8 < 96 by smt().
  rewrite /poly_cbd1_coeff_int /poly_cbd1_head_bit /poly_cbd1_tail_bit.
  by rewrite poly_sotp_encode_input_head_byte 1:hi poly_sotp_encode_input_tail_byte 1:hi.
qed.

lemma poly_sotp_encode_functional (rp0 : W16.t Array768.t) (msg0 : W8.t Array96.t) (buf0 : W8.t Array192.t) :
  hoare [NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode :
    rp = rp0 /\ msg = msg0 /\ buf = buf0 ==> res = poly_sotp_encode_spec msg0 buf0].
proof.
  proc.
  seq 2 : (msg = msg0 /\ buf = buf0 /\ k = W64.of_int 0 /\ poly_cbd1_prefix (poly_sotp_encode_input msg0 buf0) rp 0).
  + auto => />; rewrite /poly_cbd1_prefix; smt().
  while (0 <= W64.to_uint k <= 768 /\ msg = msg0 /\ buf = buf0 /\
         poly_cbd1_prefix (poly_sotp_encode_input msg0 buf0) rp (W64.to_uint k)); last first.
  + skip => &hr [hmsg [hbuf [hk0 hp0]]].
    split.
    - split; first by rewrite hk0 W64.to_uint0; smt().
      split; first exact hmsg.
      split; first exact hbuf.
      by rewrite hk0 W64.to_uint0.
    move=> k1 rp1 hexit [hk [hmsg1 [hbuf1 hp1]]].
    rewrite W64.ultE /= in hexit.
    apply poly_cbd1_prefix_full.
    have hend : W64.to_uint k1 = 768 by smt().
    by rewrite -hend.
  auto => /> &hr hklo hkhi hp hloop.
  rewrite W64.ultE /= in hloop.
  have hk : 0 <= W64.to_uint k{hr} < 768 by smt().
  have hnext : W64.to_uint (k{hr} + W64.one) = W64.to_uint k{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have hbyte : 0 <= W64.to_uint k{hr} %/ 8 < 96 by smt().
  have hbit : 0 <= W64.to_uint k{hr} %% 8 < 8 by smt(modz_cmp).
  have htail : W64.to_uint ((k{hr} `>>` W8.of_int 3) + W64.of_int 96) =
      W64.to_uint k{hr} %/ 8 + 96.
  + rewrite W64.to_uintD_small /= cbd1_byte_index; smt(W64.to_uint_cmp).
  rewrite hnext cbd1_byte_index htail cbd1_bit_index !cbd1_shift_bit 1,2:hbit -W16.of_intS.
  split; first smt().
  rewrite (_ : W64.to_uint k{hr} %/ 8 + 96 = 96 + W64.to_uint k{hr} %/ 8) 1:/#.
  rewrite -(poly_sotp_encode_coeff_int msg0 buf0 (W64.to_uint k{hr}) hk).
  apply poly_cbd1_prefix_extend; first exact hk.
  exact hp.
qed.

lemma poly_sotp_encode_lossless :
  islossless NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode.
proof.
  proc.
  while (0 <= W64.to_uint k <= 768) (768 - W64.to_uint k); last first.
  + auto => /> k0 hk hdone; rewrite W64.ultE /=; smt().
  auto => /> &hr hk hhigh hloop.
  rewrite W64.ultE /= in hloop.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
qed.

lemma poly_sotp_encode_correct (rp0 : W16.t Array768.t) (msg0 : W8.t Array96.t) (buf0 : W8.t Array192.t) :
  phoare [NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode :
    rp = rp0 /\ msg = msg0 /\ buf = buf0 ==> res = poly_sotp_encode_spec msg0 buf0] = 1%r.
proof. by conseq poly_sotp_encode_lossless (poly_sotp_encode_functional rp0 msg0 buf0). qed.

lemma poly_sotp_encode_correct_trits
    (rp0 : W16.t Array768.t) (msg0 : W8.t Array96.t) (buf0 : W8.t Array192.t) :
  phoare [NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode :
    rp = rp0 /\ msg = msg0 /\ buf = buf0 ==>
    res = poly_sotp_encode_spec msg0 buf0 /\ poly_cbd1_trit_output res /\
    NTRUPlus768NTTStage1Algebra.input_qrange res] = 1%r.
proof.
  conseq (poly_sotp_encode_correct rp0 msg0 buf0) => />.
  rewrite /poly_sotp_encode_spec.
  smt(poly_cbd1_spec_trit_output poly_cbd1_spec_input_qrange).
qed.
