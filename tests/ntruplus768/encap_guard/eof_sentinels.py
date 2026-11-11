"""Reviewed proof identities and direct semantic endpoint guards for replay."""

# All three mains passed with these exact semantic guards before pinning.
PROOF_PINS = {
    "NTRUPlus768EncapGuardSpec.ec": "030837a27ec5aad6b680c960e0dc44962ab2ceaac63bd8b830e679b6e545b7a6",
    "NTRUPlus768EncapGuardProof.ec": "54d1bea581516b767cdc090f4149b4a56a766e7b1a7a5fefd9fcb91b7482680d",
    "NTRUPlus768EncapGuardCaller.ec": "991f7d0a753d39ccce8952a5f2d2f2ba41747ea482ebef01ac43b1e64efbc7f7",
}

SENTINELS = {
    "NTRUPlus768EncapGuardSpec.ec": r"""
lemma __encap_spec_eof pk : encap_status pk = W32.zero <=> encap_key_canonical pk.
proof. exact (encap_status_zero pk). qed.
""",
    "NTRUPlus768EncapGuardProof.ec": r"""
lemma __encap_guard_eof_correct hp0 ct0 ss0 pk0 :
  phoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = encap_guard_spec ct0 ss0 pk0] = 1%r.
proof. exact (encap_guard_correct hp0 ct0 ss0 pk0). qed.
lemma __encap_guard_eof_canonical hp0 ct0 ss0 pk0 :
  encap_key_canonical pk0 =>
  phoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = (decoded_poly pk0, ct0, ss0, W32.zero)] = 1%r.
proof. exact (encap_guard_canonical_success hp0 ct0 ss0 pk0). qed.
lemma __encap_guard_eof_reject hp0 ct0 ss0 pk0 :
  ! (encap_key_canonical pk0) =>
  phoare [NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 ==>
    res = (decoded_poly pk0, encap_zero_ct, encap_zero_ss, W32.one)] = 1%r.
proof. exact (encap_guard_noncanonical_reject hp0 ct0 ss0 pk0). qed.
""",
    "NTRUPlus768EncapGuardCaller.ec": r"""
lemma __encap_caller_eof_reject (Body <: EncapBody) hp0 ct0 ss0 pk0 &m :
  ! (encap_key_canonical pk0) =>
  phoare [EncapGuardedCaller(Body).run :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 /\ (glob Body) = (glob Body){m} ==>
    res = (decoded_poly pk0, encap_zero_ct, encap_zero_ss, W32.one) /\
    (glob Body) = (glob Body){m}] = 1%r.
proof. exact (encap_caller_rejection_preserves_body Body hp0 ct0 ss0 pk0 &m). qed.
lemma __encap_caller_eof_valid (Body <: EncapBody) :
  equiv [EncapGuardedCaller(Body).run ~ EncapDirectCaller(Body).run :
    ={hp,ct,ss,pk,glob Body} /\ encap_key_canonical pk{1} ==>
    ={res,glob Body}].
proof. exact (encap_caller_valid_dispatch Body). qed.
""",
}
