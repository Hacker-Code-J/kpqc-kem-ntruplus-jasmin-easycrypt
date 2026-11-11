"""Meaningful EOF references with an explicit reviewed binder inventory."""

SENTINELS = {
    'kem_rom_oracle/NTRUPlus768ROMDistributions.ec': r'''
lemma __rom_distributions_eof (x : W8.t Array32.t) :
  mu1 uniform32 x = (1%r / 256%r)^32.
proof. exact (uniform32_point x). qed.
''',
    'kem_rom_oracle/NTRUPlus768ROMDomains.ec': r'''
lemma __rom_domains_eof : injective raw_query.
proof. exact raw_query_inj. qed.
''',
    'kem_rom_oracle/NTRUPlus768ROMOracles.ec': r'''
lemma __rom_oracles_eof m0 pk0 y0 : hoare [SHAKEFROM.shake :
  ROF.m=m0 /\ input=encode_f pk0 /\ m0.[pk0]=Some y0 ==> res=y0 /\ ROF.m=m0].
proof. exact (ro_f_shake_cached m0 pk0 y0). qed.
''',
    'kem_rom_bridge/NTRUPlus768KEMPayloadSpec.ec': r'''
lemma __rom_payload_spec_eof pk coins hout pad : encap_key_canonical pk =>
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange (payload_cipher pk coins hout pad).
proof. exact (payload_cipher_serializer pk coins hout pad). qed.
''',
    'kem_rom_bridge/NTRUPlus768KEMPayloadAlgebra.ec': r'''
lemma __rom_payload_algebra_eof fbuf gbuf finv ginv h hinv pk sk r m c :
  payload_key_relation fbuf gbuf finv ginv h hinv pk sk =>
  input_qrange r => poly_cbd1_trit_output m =>
  poly_basemul_add_qring (decoded_poly pk) (forward_ntt_spec r) (forward_ntt_spec m) c 192 =>
  sampled_m1_no_wrap fbuf gbuf r m =>
  let ct=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec c in
  complete_entry_accepts ct sk /\
  message_candidate ct (complete_sk_poly sk)=m /\
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (message_r2 ct (complete_sk_poly sk)) =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec (forward_ntt_spec r).
proof. exact (payload_actual_prefix_recovery fbuf gbuf finv ginv h hinv pk sk r m c). qed.
''',
    'kem_rom_bridge/NTRUPlus768ROMPayloadHash.ec': r'''
lemma __rom_payload_hash_eof coins0 suffix0 hout0 hm0 : hm0.[(coins0,suffix0)]=Some hout0 =>
  hoare[SHAKEHROM.shake : input=hash_h_prepare_spec coins0 suffix0 /\ ROH.m=hm0 ==>
    res=hout0 /\ ROH.m=hm0].
proof. exact (rom_h_cached coins0 suffix0 hout0 hm0). qed.
''',
    'kem_rom_bridge/NTRUPlus768ROMKeygen.ec': r'''
lemma __rom_keygen_eof (R <: KeygenSeedRNG {-ROF}) (E <: KeygenExpand {-ROF}) :
  hoare[Keygen(R,E,SHAKEFROM).run:true ==>
    exists (w:keygen_witness), rom_key_relation w ROF.m /\ res=(w.`kg_pk,w.`kg_sk)].
proof. exact (rom_keygen_public R E). qed.
''',
    'kem_rom_bridge/NTRUPlus768ROMEncap.ec': r'''
lemma __rom_encap_eof (Q <: EncapRNG {-ROF,-ROG,-ROH}) pk0 suffix0 fm0 :
  encap_key_canonical pk0 => fm0.[pk0]=Some suffix0 =>
  hoare[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,Q).run:
    pk=pk0 /\ ROF.m=fm0 ==>
    rom_encap_relation pk0 res.`2 suffix0 ROF.m ROG.m ROH.m (res.`1.`1,res.`1.`2,res.`1.`3) /\
    res.`1.`4=encap_clear_zero_spec /\ res.`1.`5=encap_clear_coins_zero_spec /\ ROF.m=fm0].
proof. exact (rom_encap_instrumented Q pk0 suffix0 fm0). qed.
''',
    'kem_rom_bridge/NTRUPlus768ROMDecap.ec': r'''
lemma __rom_decap_eof (w:keygen_witness) coins0 hout0 pad0 gm0 hm0 ws0 :
  payload_key_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk =>
  gm0.[payload_serialized hout0]=Some pad0 =>
  hm0.[(coins0,complete_sk_suffix w.`kg_sk)]=Some hout0 =>
  sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf (payload_r hout0) (payload_m coins0 pad0) =>
  hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run:
    ct=NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec(payload_cipher w.`kg_pk coins0 hout0 pad0) /\
    sk=w.`kg_sk /\ workspace=ws0 /\ ROG.m=gm0 /\ ROH.m=hm0 ==>
    res=(payload_shared_key hout0,W32.zero,clear_zero_spec) /\ ROG.m=gm0 /\ ROH.m=hm0].
proof. exact (rom_decap_success w coins0 hout0 pad0 gm0 hm0 ws0). qed.
''',
    'kem_rom_bridge/NTRUPlus768ROMCorrectness.ec': r'''
lemma __rom_correctness_eof (B <: KEMRNG {-ROE,-ROF,-ROG,-ROH}) &m :
  Pr[KEMROMCorrectness(B).run() @ &m:res] <= Pr[KEMROMPrivate(B).run() @ &m:res.`2].
proof. exact (rom_failure_probability B &m). qed.
''',
    'kem_rom_collision/NTRUPlus768ROMSeedObserver.ec': r'''
lemma __rom_seed_observer_eof (A <: SeedContext {-SeedObserver})
    &m (d:seed distr) qb ab prior (p:real) :
  0 <= qb => 0 <= ab => (forall x, mu1 d x <= p) =>
  Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r*p + (qb*(qb-1))%r/2%r*p +
    Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof. exact(seed_unrestricted_collision A &m d qb ab prior p). qed.
''',
    'kem_rom_collision/NTRUPlus768ROMSeedCollision.ec': r'''
lemma __rom_seed_collision_eof (A <: SeedContext {-SeedObserver})
    &m qb ab prior :
  0 <= qb => 0 <= ab =>
  Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) +
    Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof. exact(uniform_seed_unrestricted_collision A &m qb ab prior). qed.
''',
    'kem_rom_collision/NTRUPlus768ROMKeygenObserver.ec': r'''
lemma __rom_keygen_observer_eof &m qb ab :
  0 <= qb => 0 <= ab =>
  Pr[ObservedActualKeygen.run(qb,ab) @ &m : SeedObserver.fullbad] <=
    (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) +
    Pr[ObservedActualKeygen.run(qb,ab) @ &m :
      qb < size SeedObserver.draws \/ ab < size SeedObserver.known].
proof. exact (actual_keygen_completed_seed_collision &m qb ab). qed.
''',
    'kem_rom_sampling/NTRUPlus768ROMSOTPMaskLaw.ec': r'''
lemma __rom_sotp_mask_law_eof (coins : W8.t Array96.t) :
  dmap uniform192 (poly_sotp_encode_spec coins) =
  dmap uniform192 poly_cbd1_spec.
proof. exact (sotp_encode_uniform_law coins). qed.
''',
    'kem_rom_sampling/NTRUPlus768ROMSOTPSampling.ec': r'''
lemma __rom_sotp_sampling_eof &m rp0 coins0 serialized0 (event : W16.t Array768.t -> bool) :
  serialized0 \notin ROG.m{m} =>
  Pr[SOTPPadSampling.g_encode(rp0, coins0, serialized0) @ &m : event res] =
  mu (dmap uniform192 poly_cbd1_spec) event.
proof. exact (sotp_g_fresh_event &m rp0 coins0 serialized0 event). qed.
''',
}

SEMANTIC_TARGETS = {
    'kem_rom_oracle/NTRUPlus768ROMDistributions.ec': 'uniform32_point',
    'kem_rom_oracle/NTRUPlus768ROMDomains.ec': 'raw_query_inj',
    'kem_rom_oracle/NTRUPlus768ROMOracles.ec': 'ro_f_shake_cached',
    'kem_rom_bridge/NTRUPlus768KEMPayloadSpec.ec': 'payload_cipher_serializer',
    'kem_rom_bridge/NTRUPlus768KEMPayloadAlgebra.ec': 'payload_actual_prefix_recovery',
    'kem_rom_bridge/NTRUPlus768ROMPayloadHash.ec': 'rom_h_cached',
    'kem_rom_bridge/NTRUPlus768ROMKeygen.ec': 'rom_keygen_public',
    'kem_rom_bridge/NTRUPlus768ROMEncap.ec': 'rom_encap_instrumented',
    'kem_rom_bridge/NTRUPlus768ROMDecap.ec': 'rom_decap_success',
    'kem_rom_bridge/NTRUPlus768ROMCorrectness.ec': 'rom_failure_probability',
    'kem_rom_collision/NTRUPlus768ROMSeedObserver.ec': 'seed_unrestricted_collision',
    'kem_rom_collision/NTRUPlus768ROMSeedCollision.ec': 'uniform_seed_unrestricted_collision',
    'kem_rom_collision/NTRUPlus768ROMKeygenObserver.ec': 'actual_keygen_completed_seed_collision',
    'kem_rom_sampling/NTRUPlus768ROMSOTPMaskLaw.ec': 'sotp_encode_uniform_law',
    'kem_rom_sampling/NTRUPlus768ROMSOTPSampling.ec': 'sotp_g_fresh_event',
}

MODULE_BINDERS = {name: () for name in SENTINELS}
MODULE_BINDERS.update({
    'kem_rom_bridge/NTRUPlus768ROMKeygen.ec': ('R', 'E'),
    'kem_rom_bridge/NTRUPlus768ROMEncap.ec': ('Q',),
    'kem_rom_bridge/NTRUPlus768ROMCorrectness.ec': ('B',),
    'kem_rom_collision/NTRUPlus768ROMSeedObserver.ec': ('A',),
    'kem_rom_collision/NTRUPlus768ROMSeedCollision.ec': ('A',),
})

NEGATIVE_PROOFS = tuple(SENTINELS)
