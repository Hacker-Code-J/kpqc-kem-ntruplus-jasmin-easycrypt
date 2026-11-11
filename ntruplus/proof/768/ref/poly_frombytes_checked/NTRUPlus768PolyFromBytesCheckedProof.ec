require import AllCore IntDiv List Distr Ring StdOrder.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 NTRUPlus768PolyFromBytesChecked.
require import NTRUPlus768CanonicalDecoder NTRUPlus768PolyFromBytesCheckedWords.
require NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra.

(* Theorems in this file target the generated Jasmin procedure, including
   output values on rejected inputs. They do not assert full-KEM security. *)
lemma poly_frombytes_checked_functional (rp0 : W16.t Array768.t) (ap0 : W8.t Array1152.t) :
  hoare [NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = rp0 /\ ap = ap0 ==>
    res = (decoded_poly ap0, canonical_acc ap0 384 `>>>` 31)].
proof.
  proc; wp.
  seq 3 : (ap = ap0 /\ i = W64.zero /\ fail_0 = W32.zero /\ checked_prefix ap0 rp 0).
  + auto => />; rewrite /checked_prefix; smt().
  while (0 <= W64.to_uint i <= 384 /\ ap = ap0 /\
    checked_prefix ap0 rp (W64.to_uint i) /\ fail_0 = canonical_acc ap0 (W64.to_uint i)); last first.
  + skip => &hr [Hap [Hi0 [Hfail0 Hprefix0]]].
    split.
    - split; first by rewrite Hi0 W64.to_uint0; smt().
      split; first exact Hap.
      split; first by rewrite Hi0 W64.to_uint0.
      by rewrite Hi0 W64.to_uint0 canonical_acc0.
    move=> fail1 i1 rp1 Hexit [Hi [Hap1 [Hprefix1 Hacc1]]].
    rewrite W64.ultE /= in Hexit.
    have Hiend : W64.to_uint i1 = 384 by smt().
    have Hrp : rp1 = decoded_poly ap0.
    - apply checked_prefix_full; by rewrite -Hiend.
    by rewrite Hrp Hacc1 Hiend /W32.(`>>`) /=.
  auto => /> &hr HiLow HiHigh Hprefix Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hi384 : 0 <= W64.to_uint i{hr} < 384 by smt().
  have HiLt : W64.to_uint i{hr} < 384 by smt().
  have Hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite Hnext.
  split; first smt().
  rewrite (NTRUPlus768PolyToBytesProof.poly_tobytes_offset3E i{hr} HiLt).
  rewrite (NTRUPlus768PolyToBytesProof.poly_tobytes_offset3_addE i{hr} 1 HiLt _) 1:/#.
  rewrite (NTRUPlus768PolyToBytesProof.poly_tobytes_offset3_addE i{hr} 2 HiLt _) 1:/#.
  rewrite (NTRUPlus768PolyToBytesProof.poly_tobytes_index2E i{hr} HiLt).
  rewrite (NTRUPlus768PolyToBytesProof.poly_tobytes_index2_add1E i{hr} HiLt).
  have H0 := checked_even_wordE ap0.[3 * W64.to_uint i{hr}] ap0.[3 * W64.to_uint i{hr} + 1].
  have H1 := checked_odd_wordE ap0.[3 * W64.to_uint i{hr} + 1] ap0.[3 * W64.to_uint i{hr} + 2].
  rewrite /checked_even_word in H0; rewrite /checked_odd_word in H1.
  rewrite !H0 !H1.
  rewrite -/NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int
    -/NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int.
  split.
  + exact (checked_prefix_extend ap0 rp{hr} (W64.to_uint i{hr}) Hi384 Hprefix).
  have He := NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int_range ap0 (W64.to_uint i{hr}) Hi384.
  have Ho := NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int_range ap0 (W64.to_uint i{hr}) Hi384.
  rewrite (checked_zeroext32_of_int _ He) (checked_zeroext32_of_int _ Ho).
  by rewrite canonical_accS 1:HiLow /canonical_sub.
qed.

lemma poly_frombytes_checked_lossless :
  islossless NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes.
proof.
  proc; wp.
  while (0 <= W64.to_uint i <= 384) (384 - W64.to_uint i); last first.
  + auto => /> i0 Hi Hdone; rewrite W64.ultE /=; smt().
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
qed.

lemma poly_frombytes_checked_correct rp0 ap0 :
  phoare [NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = rp0 /\ ap = ap0 ==>
    res = (decoded_poly ap0, canonical_acc ap0 384 `>>>` 31)] = 1%r.
proof.
  by conseq poly_frombytes_checked_lossless (poly_frombytes_checked_functional rp0 ap0).
qed.

lemma poly_frombytes_checked_canonical rp0 ap0 :
  phoare [NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = rp0 /\ ap = ap0 ==>
    res.`1 = decoded_poly ap0 /\
    (W32.to_uint res.`2 = 0 <=> forall j, 0 <= j < 768 => W16.to_uint res.`1.[j] < 3457) /\
    (W32.to_uint res.`2 = 0 \/ W32.to_uint res.`2 = 1)] = 1%r.
proof.
  conseq poly_frombytes_checked_lossless (poly_frombytes_checked_functional rp0 ap0) => /> &hr.
  rewrite -/canonical_return.
  split; last exact (canonical_return_binary ap{hr}).
  split.
  + move=> hz j hj0 hj768.
    have hall := iffLR _ _ (canonical_return_success_iff ap{hr}) hz.
    apply hall; by split.
  exact (iffRL _ _ (canonical_return_success_iff ap{hr})).
qed.

lemma poly_frombytes_checked_tobytes_roundtrip rp0 p :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  phoare [NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = rp0 /\ ap = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p ==>
    res.`1 = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec p /\ res.`2 = W32.zero] = 1%r.
proof.
  move=> hp.
  have [hr hs] := canonical_tobytes_roundtrip p hp.
  conseq poly_frombytes_checked_lossless
    (poly_frombytes_checked_functional rp0 (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p)) => />.
  move=> &m _.
  apply W32.to_uint_eq; rewrite W32.to_uint0 -/canonical_return; exact hs.
qed.
