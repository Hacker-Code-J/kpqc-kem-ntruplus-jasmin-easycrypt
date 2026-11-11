"""Pinned proof identities and direct semantic endpoint guards for replay."""

PROOF_PINS = {
    "NTRUPlus768DecapGuardSpec.ec": "a13ad72cb04a3dbb73cc756185036b29b02d33d9d8e436426de6c567fe42b862",
    "NTRUPlus768DecapGuardProof.ec": "34a8e8d3f04a6aad2c02f2a56451958b3099978dfb8482c35ccf689ab5ab4808",
    "NTRUPlus768DecapGuardCaller.ec": "0898a1cd134c1563baed95d0e2570038d30bde6590f011fdf4801f278ab4c432"
}

SENTINELS = {
    'NTRUPlus768DecapGuardSpec.ec': r"""
lemma __decap_spec_eof ct f1 h1 f2 h2 :
  decap_key_encoding_valid f1 h1 => decap_key_encoding_valid f2 h2 =>
  decap_guard_status ct f1 h1 = decap_guard_status ct f2 h2.
proof. exact (decap_valid_keys_guard_status_equal ct f1 h1 f2 h2). qed.
lemma __decap_keybits_eof fbytes hbytes :
  decap_key_encoding_valid fbytes hbytes =>
  encap_status fbytes = W32.zero /\ encap_status hbytes = W32.zero.
proof. exact (decap_key_validation_bits_zero fbytes hbytes). qed.
""",
    'NTRUPlus768DecapGuardProof.ec': r"""
lemma __decap_guard_eof cp0 fp0 hp0 ss0 ct0 sk0 :
  phoare [NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard :
    cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = decap_guard_spec fp0 hp0 ss0 ct0 (decap_fbytes sk0) (decap_hbytes sk0)] = 1%r.
proof. exact (decap_guard_correct cp0 fp0 hp0 ss0 ct0 sk0). qed.
lemma __decap_guard_lossless_eof :
  islossless NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard.
proof. exact decap_guard_lossless. qed.
""",
    'NTRUPlus768DecapGuardCaller.ec': r"""
lemma __decap_caller_reject_eof (Body <: DecapBody) cp0 fp0 hp0 ss0 ct0 sk0 &m :
  ! (decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0)) =>
  phoare [DecapGuardedCaller(Body).run :
    cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 /\
    (glob Body) = (glob Body){m} ==>
    res = decap_guard_spec fp0 hp0 ss0 ct0 (decap_fbytes sk0) (decap_hbytes sk0) /\
    (glob Body) = (glob Body){m}] = 1%r.
proof. exact (decap_caller_rejection_preserves_body Body cp0 fp0 hp0 ss0 ct0 sk0 &m). qed.
lemma __decap_caller_valid_eof (Body <: DecapBody) :
  equiv [DecapGuardedCaller(Body).run ~ DecapDirectCaller(Body).run :
    ={cp,fp,hp,ss,ct,skpoly,glob Body} /\
    decap_guard_accepts ct{1} (decap_fbytes skpoly{1}) (decap_hbytes skpoly{1}) ==>
    ={res,glob Body}].
proof. exact (decap_caller_valid_dispatch Body). qed.
""",
}
