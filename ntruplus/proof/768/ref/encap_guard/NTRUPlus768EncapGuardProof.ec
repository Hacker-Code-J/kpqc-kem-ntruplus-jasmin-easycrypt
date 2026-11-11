require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array32 NTRUPlus768EncapGuard.
require import NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.

lemma encap_guard_decoder_equiv :
  equiv [NTRUPlus768EncapGuard.M.checkedDecoder__jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes ~
    NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    ={rp,ap} ==> ={res}].
proof. by proc; sim. qed.

lemma encap_guard_decoder_functional hp0 pk0 :
  hoare [NTRUPlus768EncapGuard.M.checkedDecoder__jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = hp0 /\ ap = pk0 ==> res = (decoded_poly pk0, encap_status pk0)].
proof.
  conseq encap_guard_decoder_equiv (poly_frombytes_checked_functional hp0 pk0).
  + smt().
  by rewrite encap_decoder_status.
qed.

lemma encap_guard_decoder_lossless :
  islossless NTRUPlus768EncapGuard.M.checkedDecoder__jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes.
proof.
  conseq encap_guard_decoder_equiv poly_frombytes_checked_lossless; smt().
qed.

lemma encap_guard_canonical_functional hp0 ct0 ss0 pk0 :
  encap_key_canonical pk0 =>
  hoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = (decoded_poly pk0, ct0, ss0, W32.zero)].
proof.
  move=> hk; proc.
  seq 4 : (hp = decoded_poly pk0 /\ ct = ct0 /\ ss = ss0 /\ status = W32.zero).
  + wp; call (encap_guard_decoder_functional hp0 pk0); auto => />.
    by rewrite /encap_status hk /=.
  rcondf 1; first by auto.
  by auto.
qed.

lemma encap_guard_reject_functional hp0 ct0 ss0 pk0 :
  ! (encap_key_canonical pk0) =>
  hoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = (decoded_poly pk0, encap_zero_ct, encap_zero_ss, W32.one)].
proof.
  move=> hk; proc.
  seq 4 : (hp = decoded_poly pk0 /\ ct = ct0 /\ ss = ss0 /\ status = W32.one).
  + wp; call (encap_guard_decoder_functional hp0 pk0); auto => />.
    by rewrite /encap_status hk /=.
  rcondt 1; first by auto => />; smt(W32.to_uint0 W32.to_uint1).
  seq 2 : (hp = decoded_poly pk0 /\ ct = encap_zero_ct /\ ss = ss0 /\ status = W32.one).
  + while (hp = decoded_poly pk0 /\ ss = ss0 /\ status = W32.one /\
      0 <= W64.to_uint i <= 1152 /\ encap_ct_zero_prefix ct (W64.to_uint i)).
    - auto => /> &hr hlo hhi hpref hguard.
      rewrite W64.ultE /= in hguard.
      have hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
      + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
      rewrite hnext; split; first smt().
      apply encap_ct_zero_step; smt().
    auto => />; split; first by rewrite /encap_ct_zero_prefix; smt().
    move=> ct1 i1 hexit hlo hhi hpref.
    rewrite W64.ultE /= in hexit.
    have hi : W64.to_uint i1 = 1152 by smt().
    apply encap_ct_zero_full; by rewrite -hi.
  while (hp = decoded_poly pk0 /\ ct = encap_zero_ct /\ status = W32.one /\
    0 <= W64.to_uint i <= 32 /\ encap_ss_zero_prefix ss (W64.to_uint i)).
  + auto => /> &hr hlo hhi hpref hguard.
    rewrite W64.ultE /= in hguard.
    have hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
    - rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    rewrite hnext; split; first smt().
    apply encap_ss_zero_step; smt().
  auto => />; split; first by rewrite /encap_ss_zero_prefix; smt().
  move=> i1 ss1 hexit hlo hhi hpref.
  rewrite W64.ultE /= in hexit.
  have hi : W64.to_uint i1 = 32 by smt().
  apply encap_ss_zero_full; by rewrite -hi.
qed.

lemma encap_guard_functional hp0 ct0 ss0 pk0 :
  hoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = encap_guard_spec ct0 ss0 pk0].
proof.
  case (encap_key_canonical pk0) => hk.
  + conseq (encap_guard_canonical_functional hp0 ct0 ss0 pk0 hk) => /> &hr ->.
    by rewrite /encap_guard_spec /encap_status hk.
  conseq (encap_guard_reject_functional hp0 ct0 ss0 pk0 hk) => /> &hr ->.
  by rewrite /encap_guard_spec /encap_status hk.
qed.

lemma encap_guard_lossless :
  islossless NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard.
proof.
  proc.
  seq 4 : true; first by auto.
  + wp; call encap_guard_decoder_lossless; by auto.
  if; last by auto.
  while (0 <= W64.to_uint i <= 32) (32 - W64.to_uint i); last first.
  + wp.
    while (0 <= W64.to_uint i <= 1152) (1152 - W64.to_uint i); last first.
    - auto => /> &hr _ i0; split.
      + rewrite W64.ultE /=; smt().
      move=> _ _ _ i1; rewrite W64.ultE /=; smt().
    auto => /> &hr hlo hhi hguard.
    rewrite W64.ultE /= in hguard.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> &hr hlo hhi hguard.
  rewrite W64.ultE /= in hguard.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  by hoare; auto.
  by auto.
qed.

lemma encap_guard_correct hp0 ct0 ss0 pk0 :
  phoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = encap_guard_spec ct0 ss0 pk0] = 1%r.
proof. by conseq encap_guard_lossless (encap_guard_functional hp0 ct0 ss0 pk0). qed.

lemma encap_guard_canonical_success hp0 ct0 ss0 pk0 :
  encap_key_canonical pk0 =>
  phoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = (decoded_poly pk0, ct0, ss0, W32.zero)] = 1%r.
proof. move=> hk; by conseq encap_guard_lossless (encap_guard_canonical_functional hp0 ct0 ss0 pk0 hk). qed.

lemma encap_guard_noncanonical_reject hp0 ct0 ss0 pk0 :
  ! (encap_key_canonical pk0) =>
  phoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = (decoded_poly pk0, encap_zero_ct, encap_zero_ss, W32.one)] = 1%r.
proof. move=> hk; by conseq encap_guard_lossless (encap_guard_reject_functional hp0 ct0 ss0 pk0 hk). qed.
