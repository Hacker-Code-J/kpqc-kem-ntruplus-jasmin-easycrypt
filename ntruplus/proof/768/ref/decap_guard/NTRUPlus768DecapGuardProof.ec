require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array2304 Array32 NTRUPlus768DecapGuard.
require import NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768PolyFromBytesChecked NTRUPlus768PolyFromBytesCheckedProof.

lemma decap_guard_decoder_equiv :
  equiv [NTRUPlus768DecapGuard.M.checkedDecoder__jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes ~
    NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    ={rp,ap} ==> ={res}].
proof. by proc; sim. qed.

lemma decap_guard_decoder_functional rp0 ap0 :
  hoare [NTRUPlus768DecapGuard.M.checkedDecoder__jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
    rp = rp0 /\ ap = ap0 ==> res = (decoded_poly ap0, encap_status ap0)].
proof.
  conseq decap_guard_decoder_equiv (poly_frombytes_checked_functional rp0 ap0).
  + smt().
  by rewrite encap_decoder_status.
qed.

lemma decap_guard_decoder_lossless :
  islossless NTRUPlus768DecapGuard.M.checkedDecoder__jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes.
proof.
  conseq decap_guard_decoder_equiv poly_frombytes_checked_lossless; smt().
qed.

lemma decap_guard_functional cp0 fp0 hp0 ss0 ct0 sk0 :
  hoare [NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard :
    cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = decap_guard_spec fp0 hp0 ss0 ct0 (decap_fbytes sk0) (decap_hbytes sk0)].
proof.
  proc.
  seq 9 : (cp = decoded_poly ct0 /\
    fp = (if encap_key_canonical ct0 then decoded_poly (decap_fbytes sk0) else fp0) /\
    hp = (if encap_key_canonical ct0 /\ encap_key_canonical (decap_fbytes sk0)
          then decoded_poly (decap_hbytes sk0) else hp0) /\
    ss = ss0 /\ status = decap_guard_status ct0 (decap_fbytes sk0) (decap_hbytes sk0)).
  + seq 8 : (cp = decoded_poly ct0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\
      fbytes = decap_fbytes sk0 /\ hbytes = decap_hbytes sk0 /\ status = encap_status ct0).
    - wp; call (decap_guard_decoder_functional cp0 ct0); auto => />.
    if.
    - seq 3 : (cp = decoded_poly ct0 /\ fp = decoded_poly (decap_fbytes sk0) /\ hp = hp0 /\ ss = ss0 /\
        hbytes = decap_hbytes sk0 /\ encap_key_canonical ct0 /\ status = encap_status (decap_fbytes sk0)).
      + wp; call (decap_guard_decoder_functional fp0 (decap_fbytes sk0)); auto => />.
        by rewrite encap_status_zero.
      if.
      + wp; call (decap_guard_decoder_functional hp0 (decap_hbytes sk0)); auto => />.
        rewrite /decap_guard_status /decap_guard_accepts /decap_key_encoding_valid /encap_status.
        smt(W32.to_uint0 W32.to_uint1).
      auto => />; rewrite /decap_guard_status /decap_guard_accepts /decap_key_encoding_valid /encap_status.
      smt(W32.to_uint0 W32.to_uint1).
    auto => />; rewrite /decap_guard_status /decap_guard_accepts /decap_key_encoding_valid /encap_status.
    smt(W32.to_uint0 W32.to_uint1).
  if; last first.
  + auto => />; rewrite /decap_guard_spec /decap_guard_status.
    smt(W32.to_uint0 W32.to_uint1).
  while (cp = decoded_poly ct0 /\
    fp = (if encap_key_canonical ct0 then decoded_poly (decap_fbytes sk0) else fp0) /\
    hp = (if encap_key_canonical ct0 /\ encap_key_canonical (decap_fbytes sk0)
          then decoded_poly (decap_hbytes sk0) else hp0) /\
    ! decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) /\
    status = W32.one /\ 0 <= W64.to_uint i <= 32 /\ encap_ss_zero_prefix ss (W64.to_uint i)).
  + auto => /> &hr hbad hlo hhi hpref hguard.
    rewrite W64.ultE /= in hguard.
    have hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
    - rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    rewrite hnext; split; first smt().
    apply encap_ss_zero_step; smt().
  auto => /> hreject; split.
  + rewrite /decap_guard_status /encap_ss_zero_prefix; smt(W32.to_uint0 W32.to_uint1).
  move=> i1 ss1 hnot hbad hst hl hu hpref.
  rewrite W64.ultE /= in hnot.
  have hi : W64.to_uint i1 = 32 by smt().
  have hz : ss1 = encap_zero_ss.
  + apply encap_ss_zero_full; by rewrite -hi.
  rewrite /decap_guard_spec /decap_guard_status.
  smt().
qed.

lemma decap_guard_lossless :
  islossless NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard.
proof.
  proc.
  seq 9 : true; first by auto.
  + seq 8 : true; first by auto.
    - wp; call decap_guard_decoder_lossless; by auto.
    if; last by auto.
    seq 3 : true; first by auto.
    - wp; call decap_guard_decoder_lossless; by auto.
    if; last by auto.
    wp; call decap_guard_decoder_lossless; by auto.
    by hoare; auto.
    by auto.
    by hoare; auto.
    by auto.
  if; last by auto.
  while (0 <= W64.to_uint i <= 32) (32 - W64.to_uint i); last first.
  + auto => /> &hr _ i0; rewrite W64.ultE /=; smt().
  auto => /> &hr hlo hhi hguard.
  rewrite W64.ultE /= in hguard.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  by hoare; auto.
  by auto.
qed.

lemma decap_guard_correct cp0 fp0 hp0 ss0 ct0 sk0 :
  phoare [NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard :
    cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = decap_guard_spec fp0 hp0 ss0 ct0 (decap_fbytes sk0) (decap_hbytes sk0)] = 1%r.
proof. by conseq decap_guard_lossless (decap_guard_functional cp0 fp0 hp0 ss0 ct0 sk0). qed.
