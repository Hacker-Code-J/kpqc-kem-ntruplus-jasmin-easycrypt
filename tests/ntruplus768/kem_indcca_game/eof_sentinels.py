"""Reviewed literal semantic EOF declarations for the twelve frozen mains."""
SENTINELS = {
    'kem_indcca_game/NTRUPlus768CCAQueryCodec.ec': r'''

lemma __kem_indcca_eof_0 s q : decode_typed s=Some q <=> s=raw_query q.
proof. exact (decode_typed_exact s q). qed.
''',
    'kem_indcca_game/NTRUPlus768CCAOraclePorts.ec': r'''

lemma __kem_indcca_eof_1 m0 x0 y0 : hoare[SharedCCAOracles.h :
 ROH.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==> res=y0 /\ ROH.m=m0].
proof. exact (cca_oracle_ports_eof m0 x0 y0). qed.
''',
    'kem_indcca_game/NTRUPlus768CCAStatusAdapter.ec': r'''

lemma __kem_indcca_eof_2 :
 equiv[CCAStatusAdapter.run ~ CompleteDecaps(SHAKEGROM,SHAKEHROM).run :
 ={ct,sk,glob ROG,glob ROH} /\ workspace{2}=witness ==>
 res{1}=cca_status_result res.`1{2} res.`2{2} /\ ={glob ROG,glob ROH}].
proof. exact (cca_status_adapter_projection). qed.
''',
    'kem_indcca_game/NTRUPlus768CCADecapOracle.ec': r'''

lemma __kem_indcca_eof_3 n0 :
 equiv[CCADecapOracle.decap ~ CompleteDecaps(SHAKEGROM,SHAKEHROM).run :
 ={ct,glob ROG,glob ROH} /\ CCADecapOracle.sk{1}=sk{2} /\
 workspace{2}=witness /\ CCADecapOracle.cstar{1}<>Some ct{1} /\
 CCADecapOracle.count{1}=n0 ==>
 res{1}=cca_status_result res.`1{2} res.`2{2} /\
 ={glob ROG,glob ROH} /\ CCADecapOracle.count{1}=n0+1].
proof. exact (cca_decap_actual_projection n0). qed.
''',
    'kem_indcca_game/NTRUPlus768CCAProbability.ec': r'''

lemma __kem_indcca_eof_4 (B<:PartialCCABody) &m qf0 qg0 :
 Pr[CompleteFallback(B).run(qf0,qg0) @ &m:res]-
   Pr[B.run(qf0,qg0) @ &m:true]/2%r =
 (Pr[B.run(qf0,qg0) @ &m:res=Some true]-
  Pr[B.run(qf0,qg0) @ &m:res=Some false])/2%r.
proof. exact (cca_fallback_centered_return B &m qf0 qg0). qed.
''',
    'kem_indcca_game/NTRUPlus768RawXOFSampling.ec': r'''

lemma __kem_indcca_eof_5 i j s : 0<=i<=j<=224 =>
 size(raw_xof_output i s)=i /\ take i(raw_xof_output j s)=raw_xof_output i s.
proof. exact (raw_xof_sampling_eof i j s). qed.
''',
    'kem_indcca_game/NTRUPlus768RawXOFStreams.ec': r'''

lemma __kem_indcca_eof_6 m0 x0 y0 : phoare[RawXOFStreams.untyped :
 RawXOFStreams.other=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0]=(mu1 uniform224 y0).
proof. exact (raw_stream_untyped_fresh m0 x0 y0). qed.
''',
    'kem_indcca_game/NTRUPlus768RawXOF.ec': r'''

lemma __kem_indcca_eof_7 : hoare[BudgetRawXOF.get :
 0<=BudgetRawXOF.forwarded<=BudgetRawXOF.attempts /\
 BudgetRawXOF.forwarded<=BudgetRawXOF.limit ==>
 0<=BudgetRawXOF.forwarded<=BudgetRawXOF.attempts /\
 BudgetRawXOF.forwarded<=BudgetRawXOF.limit].
proof. exact (budget_raw_forwarded_bound). qed.
''',
    'kem_indcca_game/NTRUPlus768CCASetup.ec': r'''

lemma __kem_indcca_eof_8 (R<:EncapRNG) (F<:EncapSHAKEF) (G<:MessageSHAKE) (H<:CompleteSHAKEH) :
 hoare[EncapRandom(F,G,H,R).run : encap_key_canonical pk ==> res.`3=W32.zero].
proof. exact (cca_encap_random_status_any R F G H). qed.
''',
    'kem_indcca_game/NTRUPlus768CCAGame.ec': r'''

lemma __kem_indcca_eof_9
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) :
 equiv[CCAFiniteOriginalGame(A).run ~ CCAFiniteGame(A).run : ={qf,qg,glob A} ==>
 ={res,glob A,glob ROE,glob ROF,glob ROG,glob ROH,glob CCADecapOracle,glob RawXOFStreams}].
proof. exact (cca_finite_original_option A). qed.
''',
    'kem_indcca_game/NTRUPlus768RawXOFLaws.ec': r'''

lemma __kem_indcca_eof_10
 (A <: RawQueryAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams}) x0 s0 :
 hoare[A(SharedCCAExtendedOracles).run : raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==> raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof. exact (raw_query_adversary_preserves A x0 s0). qed.
''',
    'kem_indcca_game/NTRUPlus768CCARawStateFrame.ec': r'''

lemma __kem_indcca_eof_11
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-CCADecapOracle,-RawXOFStreams}) x0 s0 :
 hoare[A(SharedCCAExtendedOracles,CCADecapOracle).guess :
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other ==>
 raw_stored x0 s0 ROE.m ROF.m ROG.m ROH.m
 RawXOFStreams.es RawXOFStreams.fs RawXOFStreams.gs RawXOFStreams.other].
proof. exact (cca_adversary_preserves_raw_known A x0 s0). qed.
''',
}
SEMANTIC_TARGETS = {
    'kem_indcca_game/NTRUPlus768CCAQueryCodec.ec': 'decode_typed_exact',
    'kem_indcca_game/NTRUPlus768CCAOraclePorts.ec': 'cca_oracle_ports_eof',
    'kem_indcca_game/NTRUPlus768CCAStatusAdapter.ec': 'cca_status_adapter_projection',
    'kem_indcca_game/NTRUPlus768CCADecapOracle.ec': 'cca_decap_actual_projection',
    'kem_indcca_game/NTRUPlus768CCAProbability.ec': 'cca_fallback_centered_return',
    'kem_indcca_game/NTRUPlus768RawXOFSampling.ec': 'raw_xof_sampling_eof',
    'kem_indcca_game/NTRUPlus768RawXOFStreams.ec': 'raw_stream_untyped_fresh',
    'kem_indcca_game/NTRUPlus768RawXOF.ec': 'budget_raw_forwarded_bound',
    'kem_indcca_game/NTRUPlus768CCASetup.ec': 'cca_encap_random_status_any',
    'kem_indcca_game/NTRUPlus768CCAGame.ec': 'cca_finite_original_option',
    'kem_indcca_game/NTRUPlus768RawXOFLaws.ec': 'raw_query_adversary_preserves',
    'kem_indcca_game/NTRUPlus768CCARawStateFrame.ec': 'cca_adversary_preserves_raw_known',
}
MODULE_BINDERS = {
    'kem_indcca_game/NTRUPlus768CCAQueryCodec.ec': (),
    'kem_indcca_game/NTRUPlus768CCAOraclePorts.ec': (),
    'kem_indcca_game/NTRUPlus768CCAStatusAdapter.ec': (),
    'kem_indcca_game/NTRUPlus768CCADecapOracle.ec': (),
    'kem_indcca_game/NTRUPlus768CCAProbability.ec': ('B',),
    'kem_indcca_game/NTRUPlus768RawXOFSampling.ec': (),
    'kem_indcca_game/NTRUPlus768RawXOFStreams.ec': (),
    'kem_indcca_game/NTRUPlus768RawXOF.ec': (),
    'kem_indcca_game/NTRUPlus768CCASetup.ec': ('R', 'F', 'G', 'H'),
    'kem_indcca_game/NTRUPlus768CCAGame.ec': ('A',),
    'kem_indcca_game/NTRUPlus768RawXOFLaws.ec': ('A',),
    'kem_indcca_game/NTRUPlus768CCARawStateFrame.ec': ('A',),
}
NEGATIVE_PROOFS = (
    'kem_indcca_game/NTRUPlus768CCAQueryCodec.ec',
    'kem_indcca_game/NTRUPlus768CCAOraclePorts.ec',
    'kem_indcca_game/NTRUPlus768CCAStatusAdapter.ec',
    'kem_indcca_game/NTRUPlus768CCADecapOracle.ec',
    'kem_indcca_game/NTRUPlus768CCAProbability.ec',
    'kem_indcca_game/NTRUPlus768RawXOFSampling.ec',
    'kem_indcca_game/NTRUPlus768RawXOFStreams.ec',
    'kem_indcca_game/NTRUPlus768RawXOF.ec',
    'kem_indcca_game/NTRUPlus768CCASetup.ec',
    'kem_indcca_game/NTRUPlus768CCAGame.ec',
    'kem_indcca_game/NTRUPlus768RawXOFLaws.ec',
    'kem_indcca_game/NTRUPlus768CCARawStateFrame.ec',
)
