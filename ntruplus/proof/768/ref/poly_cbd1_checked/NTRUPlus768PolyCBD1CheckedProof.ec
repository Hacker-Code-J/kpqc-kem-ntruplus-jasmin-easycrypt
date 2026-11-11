require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array192 Array768 NTRUPlus768PolyCBD1Checked.
require import NTRUPlus768PolyCBD1Algebra.

(* The actual extracted sampler overwrites all 768 coefficients.  Its value
   result is the independent bit-difference specification, for every input
   byte array and every initial output array. *)

lemma cbd1_shr_value (x : W16.t) (j : W8.t) :
  (SHR_16 x j).`6 = x `>>>` (W8.to_uint j %% 32).
proof.
  rewrite /W16.SHIFT.SHR_16 /W16.shift_mask /=.
  case (W8.to_uint j %% 32 = 0) => hj.
  + rewrite hj /flags_w /=; apply W16.to_uint_eq; by rewrite W16.to_uint_shr 1:// /=.
  by rewrite /W16.SHIFT.rflags_OF /=.
qed.

lemma cbd1_shift_bit (b : W8.t) (j : int) :
  0 <= j < 8 =>
  (SHR_16 (zeroextu16 b) (W8.of_int j)).`6 `&` W16.one =
    W16.of_int (poly_cbd1_bit b j).
proof.
  move=> hj.
  rewrite (W16.and_mod 1) 1:// /= cbd1_shr_value W8.of_uintK /=.
  have h256 : j %% 256 = j by rewrite modz_small; smt().
  have h32 : j %% 32 = j by rewrite modz_small; smt().
  rewrite h256 h32 W16.to_uint_shr 1:/#.
  by rewrite W2u8.to_uint_zeroextu16 /poly_cbd1_bit /NTRUPlus768PolySOTPDecodeAlgebra.poly_sotp_bit.
qed.

lemma cbd1_byte_index (k : W64.t) :
  W64.to_uint (k `>>` W8.of_int 3) = W64.to_uint k %/ 8.
proof. by rewrite /W64.(`>>`) /= W64.to_uint_shr 1:// /=. qed.

lemma cbd1_bit_index (k : W64.t) :
  (truncateu8 k) `&` W8.of_int 7 = W8.of_int (W64.to_uint k %% 8).
proof.
  rewrite (W8.and_mod 3) 1:// /=.
  rewrite /truncateu8 W8.of_uintK /=.
  by rewrite (modz_dvd _ 256 8) 1://.
qed.

op poly_cbd1_prefix (buf : W8.t Array192.t) (rp : W16.t Array768.t)
    (upto : int) : bool =
  forall k, 0 <= k < upto => rp.[k] = W16.of_int (poly_cbd1_coeff_int buf k).

lemma poly_cbd1_prefix_extend buf rp k :
  0 <= k < 768 => poly_cbd1_prefix buf rp k =>
  poly_cbd1_prefix buf (rp.[k <- W16.of_int (poly_cbd1_coeff_int buf k)]) (k + 1).
proof.
  move=> hk hp j hj.
  case (j = k) => [-> | hne].
  + by rewrite Array768.get_setE.
  have hjold : 0 <= j < k by smt().
  have hkeep : (rp.[k <- W16.of_int (poly_cbd1_coeff_int buf k)]).[j] = rp.[j].
  + smt(Array768.get_setE).
  rewrite hkeep.
  exact (hp j hjold).
qed.

lemma poly_cbd1_prefix_full buf rp :
  poly_cbd1_prefix buf rp 768 => rp = poly_cbd1_spec buf.
proof.
  move=> hp; apply Array768.tP => k hk.
  by rewrite poly_cbd1_spec_word 1:hk (hp k hk).
qed.

lemma poly_cbd1_functional (rp0 : W16.t Array768.t) (buf0 : W8.t Array192.t) :
  hoare [NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1 :
    rp = rp0 /\ buf = buf0 ==> res = poly_cbd1_spec buf0].
proof.
  proc.
  seq 2 : (buf = buf0 /\ k = W64.of_int 0 /\ poly_cbd1_prefix buf0 rp 0).
  + auto => />; rewrite /poly_cbd1_prefix; smt().
  while (0 <= W64.to_uint k <= 768 /\ buf = buf0 /\
         poly_cbd1_prefix buf0 rp (W64.to_uint k)); last first.
  + skip => &hr [hbuf [hk0 hp0]].
    split.
    - split; first by rewrite hk0 W64.to_uint0; smt().
      split; first exact hbuf.
      by rewrite hk0 W64.to_uint0.
    move=> k1 rp1 hexit [hk [hbuf1 hp1]].
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
  rewrite -/poly_cbd1_head_bit -/poly_cbd1_tail_bit -/poly_cbd1_coeff_int.
  apply poly_cbd1_prefix_extend; first exact hk.
  exact hp.
qed.

lemma poly_cbd1_lossless :
  islossless NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1.
proof.
  proc.
  while (0 <= W64.to_uint k <= 768) (768 - W64.to_uint k); last first.
  + auto => /> k0 hk hdone; rewrite W64.ultE /=; smt().
  auto => /> &hr hk hhigh hloop.
  rewrite W64.ultE /= in hloop.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
qed.

lemma poly_cbd1_correct (rp0 : W16.t Array768.t) (buf0 : W8.t Array192.t) :
  phoare [NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1 :
    rp = rp0 /\ buf = buf0 ==> res = poly_cbd1_spec buf0] = 1%r.
proof. by conseq poly_cbd1_lossless (poly_cbd1_functional rp0 buf0). qed.

lemma poly_cbd1_correct_trits (rp0 : W16.t Array768.t) (buf0 : W8.t Array192.t) :
  phoare [NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1 :
    rp = rp0 /\ buf = buf0 ==>
    res = poly_cbd1_spec buf0 /\ poly_cbd1_trit_output res /\
    NTRUPlus768NTTStage1Algebra.input_qrange res] = 1%r.
proof.
  conseq (poly_cbd1_correct rp0 buf0) => />.
  smt(poly_cbd1_spec_trit_output poly_cbd1_spec_input_qrange).
qed.
