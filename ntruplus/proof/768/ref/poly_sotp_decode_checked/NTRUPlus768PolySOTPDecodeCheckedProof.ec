require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array96 Array192 Array768 NTRUPlus768PolySOTPDecodeChecked.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolySOTPDecodeWords.
require import NTRUPlus768PolySOTPDecodeFlag NTRUPlus768PolySOTPDecodeBitProof.
require import NTRUPlus768PolySOTPDecodeCheckedLossless.

op sotp_msg_prefix a buf (msg : W8.t Array96.t) n =
  forall k, 0 <= k < n => msg.[k] = (poly_sotp_raw_msg_spec a buf).[k].

lemma sotp_offset8 (i : W64.t) j : 0 <= W64.to_uint i < 96 => 0 <= j < 8 =>
  W64.to_uint ((i `<<` W8.of_int 3) + W64.of_int j) = 8*W64.to_uint i+j.
proof.
  move=> hi hj.
  rewrite W64.to_uintD W64.to_uint_shl 1:// !W64.of_uintK /= !modz_small; smt().
qed.

lemma sotp_raw_byte_truncate a buf i : 0 <= i < 96 =>
  truncateu8 (W16.of_int (sotp_packed a buf i 8)) = (poly_sotp_raw_msg_spec a buf).[i].
proof.
  move=> hi.
  rewrite sotp_packed8 /truncateu8 /= W16.of_uintK.
  rewrite /poly_sotp_raw_msg_spec Array96.initiE //.
  apply W8.to_uint_eq; rewrite !W8.of_uintK /=.
  exact (modz_dvd _ 65536 256 _); done.
qed.

lemma poly_sotp_decode_functional (msg0 : W8.t Array96.t) (a : W16.t Array768.t) (buf0 : W8.t Array192.t) :
  hoare [NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode :
    msg = msg0 /\ ap = a /\ buf = buf0 /\ poly_sotp_trit_input a ==>
    res = (poly_sotp_decode_msg_spec a buf0,W32.of_int (b2i (poly_sotp_decode_fail_spec a buf0)))].
proof.
  proc.
  seq 4 : (ap=a /\ buf=buf0 /\ msg=poly_sotp_raw_msg_spec a buf0 /\
    W32.to_uint r < 65536 /\ (W32.to_uint r <= 1 <=> !poly_sotp_decode_fail_spec a buf0)).
  + while (ap=a /\ buf=buf0 /\ poly_sotp_trit_input a /\
      0 <= W64.to_uint i <= 96 /\ sotp_msg_prefix a buf0 msg (W64.to_uint i) /\
      W32.to_uint r < 65536 /\ (W32.to_uint r <= 1 <=> sotp_valid_until a buf0 (8*W64.to_uint i))); last first.
    - auto => /> &hr.
      split; first by rewrite /sotp_msg_prefix sotp_valid_until0 /=; smt().
      move=> i1 msg1 r1 hdone hlo hhi hprefix hrange hvalid.
      rewrite W64.ultE /= in hdone.
      have hi : W64.to_uint i1 = 96 by smt().
      split.
      * apply Array96.tP => k hk; apply hprefix; smt().
      have hf := sotp_valid_until_full a buf0.
      smt().
    seq 13 : (ap=a /\ buf=buf0 /\ poly_sotp_trit_input a /\
      0 <= W64.to_uint i < 96 /\ sotp_msg_prefix a buf0 msg (W64.to_uint i) /\
      sotp_partial a buf0 (W64.to_uint i) 8 t1 t2 t3 r).
    - ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 7).
      ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 6).
      ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 5).
      ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 4).
      ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 3).
      ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 2).
      ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 1).
      ecall (sotp_decode_bit_partial a buf0 (W64.to_uint i) 0).
      auto => /> &hr ht hlo hhi hprefix hrange hvalid hloop.
      rewrite W64.ultE /= in hloop.
      have hoff : forall j, 0 <= j < 8 => W64.to_uint ((i{hr} `<<` W8.of_int 3)+W64.of_int j) = 8*W64.to_uint i{hr}+j.
      * move=> j hj; apply sotp_offset8; smt().
      have hadd : W64.to_uint (i{hr}+W64.of_int 96) = W64.to_uint i{hr}+96.
      * rewrite W64.to_uintD_small /=; smt().
      have hz : forall (w : W8.t), w `>>>` 0 = w.
      * move=> w; apply W8.to_uint_eq; by rewrite W8.to_uint_shr 1:// /=.
      have hoff0 : W64.to_uint (i{hr} `<<` W8.of_int 3) = 8*W64.to_uint i{hr}.
      * have h := hoff 0 _; first done. move: h; by simplify.
      rewrite hadd sotp_packed0 /= !hz hoff0.
      rewrite (hoff 1 _) 1:// (hoff 2 _) 1:// (hoff 3 _) 1:// (hoff 4 _) 1://
        (hoff 5 _) 1:// (hoff 6 _) 1:// (hoff 7 _) 1://.
      smt().
    auto => /> &hr ht hlo hhi hprefix hrange hvalid.
    have hn : W64.to_uint (i{hr}+W64.one) = W64.to_uint i{hr}+1.
    - rewrite W64.to_uintD_small /=; smt().
    rewrite hn (sotp_raw_byte_truncate a buf0 (W64.to_uint i{hr}) _) 1:/#.
    split; first smt().
    split.
    - rewrite /sotp_msg_prefix => k hk.
      rewrite Array96.get_setE 1:/# /=; smt().
    smt().
  wp.
  while (ap=a /\ buf=buf0 /\ r=W32.of_int (b2i (poly_sotp_decode_fail_spec a buf0)) /\
    mask=(if poly_sotp_decode_fail_spec a buf0 then W8.zero else W8.onew) /\
    0<=W64.to_uint i<=96 /\
    forall k, 0<=k<96 => msg.[k] =
      if k<W64.to_uint i then (poly_sotp_decode_msg_spec a buf0).[k] else (poly_sotp_raw_msg_spec a buf0).[k]); last first.
  + auto => /> &hr hrange hvalid.
    have hn := sotp_normalize r{hr} hrange.
    have hb : (1 < W32.to_uint r{hr}) = poly_sotp_decode_fail_spec a buf0 by smt().
    move: hn; rewrite /sotp_norm /= => hn.
    rewrite hn hb sotp_mask /=.
    split; first smt().
    move=> i1 msg1 hdone hlo hhi hp.
    rewrite W64.ultE /= in hdone.
    apply Array96.tP => k hk; have h := hp k hk; smt().
  auto => /> &hr hlo hhi hp hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr}+W64.one) = W64.to_uint i{hr}+1.
  + rewrite W64.to_uintD_small /=; smt().
  rewrite hn; split; first smt().
  move=> k hklo hkhi.
  rewrite Array96.get_setE 1:/# /=.
  have hcur := hp (W64.to_uint i{hr}) _; first smt().
  have hk := hp k _; first smt().
  have hm := sotp_raw_mask a buf0 (W64.to_uint i{hr}) _; first smt().
  smt().
qed.

lemma poly_sotp_decode_correct (msg0 : W8.t Array96.t) (a : W16.t Array768.t) (buf0 : W8.t Array192.t) :
  phoare [NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode :
    msg = msg0 /\ ap = a /\ buf = buf0 /\ poly_sotp_trit_input a ==>
    res = (poly_sotp_decode_msg_spec a buf0,W32.of_int (b2i (poly_sotp_decode_fail_spec a buf0)))] = 1%r.
proof. by conseq poly_sotp_decode_lossless (poly_sotp_decode_functional msg0 a buf0). qed.
