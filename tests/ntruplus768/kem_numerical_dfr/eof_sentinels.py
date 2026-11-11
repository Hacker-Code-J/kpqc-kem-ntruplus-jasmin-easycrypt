"""Reviewed semantic targets with literal full theorem declarations."""
SENTINELS = {
    'kem_numerical_dfr/NTRUPlus768NumericalDFRModel.ec': r'''
lemma __numerical_dfr_0_eof f g r m :
 dfr_bad f g r m = !sampled_m1_no_wrap f g (poly_cbd1_spec r) (poly_cbd1_spec m).
proof. exact (dfr_badE f g r m). qed.
''',
    'kem_numerical_dfr/NTRUPlus768CBDTensor.ec': r'''
lemma __numerical_dfr_1_eof ['a] (d:'a distr) (x0:'a) n (perm:int -> int) :
  0 <= n => is_lossless d =>
  (forall i j,0 <= i < n => 0 <= j < n => perm i=perm j => i=j) =>
  (forall i,0 <= i < n => 0 <= perm i < n) =>
  dmap (dlist d (2*n) `*` dlist d (2*n)) (paired_halves_tensor x0 n perm) =
  dlist ((d `*` d) `*` (d `*` d)) n.
proof. exact (paired_halves_tensor_law d x0 n perm). qed.
''',
    'kem_numerical_dfr/NTRUPlus768CBDDistribution.ec': r'''
lemma __numerical_dfr_2_eof perm :
 (forall i j,0<=i<384=>0<=j<384=>perm i=perm j=>i=j) =>
 (forall i,0<=i<384=>0<=perm i<384) =>
 dmap ((uniform192 `*` uniform192) `*` (uniform192 `*` uniform192))
  (cbd_four_blocks perm)=dlist dcbd_quad 768.
proof. exact (cbd_four_blocks_uniform perm). qed.
''',
    'kem_numerical_dfr/NTRUPlus768NoiseDecomposition.ec': r'''
lemma __numerical_dfr_3_eof a b c d k : 0<=k<768 =>
 (integer_add(integer_product a b)(integer_product c d)).[k]=
 noise_product_blocks a b k+noise_product_blocks c d k.
proof. exact (two_integer_products_noise_blocks a b c d k). qed.
''',
    'kem_numerical_dfr/NTRUPlus768NoiseNoWrap.ec': r'''
lemma __numerical_dfr_4_eof fbuf gbuf r m :
 (forall k,0<=k<768 => -1<=coeff m.[k]<=1) =>
 !sampled_m1_no_wrap fbuf gbuf r m =>
 exists k,0<=k<768 /\
 576<=`|noise_product_blocks (integer_coefficients(poly_cbd1_spec gbuf))
   (integer_coefficients r) k +
 noise_product_blocks (integer_coefficients m)
   (integer_coefficients(poly_cbd1_spec fbuf)) k|.
proof. exact (no_wrap_violation_blocks576 fbuf gbuf r m). qed.
''',
    'kem_numerical_dfr/NTRUPlus768NoiseIndependentBlocks.ec': r'''
lemma __numerical_dfr_5_eof ['a 'b 'c]
    (d:'a distr) (f:int -> 'a -> 'b) (g:'b list -> 'c) n :
  0 <= n =>
  dmap (dlist d n) (fun xs => g (mapi f xs)) =
  dmap (djoin (map (fun i => dmap d (f i)) (range 0 n))) g.
proof. exact (independent_blocks_observation d f g n). qed.
''',
    'kem_numerical_dfr/NTRUPlus768NoiseMGF.ec': r'''
lemma __numerical_dfr_6_eof kind s : s=1 \/ s= -1 =>
 noise_mgf s (noise_kind_distr kind)=
   (if kind=0 then 289%r/256%r else 1237%r/1024%r).
proof. exact (noise_kind_mgf_exact kind s). qed.
''',
    'kem_numerical_dfr/NTRUPlus768NoiseTail.ec': r'''
lemma __numerical_dfr_7_eof : mu raw_four_law four_buffers_bad<1%r/(2%r^356).
proof. exact raw_four_bad_numerical. qed.
''',
    'kem_numerical_dfr/NTRUPlus768ConditionalBufferLaw.ec': r'''
lemma __numerical_dfr_8_eof :
 mu accepted_four_law four_buffers_bad <=
 (64%r/25%r)*mu raw_four_law four_buffers_bad.
proof. exact accepted_bad_event_bound. qed.
''',
    'kem_numerical_dfr/NTRUPlus768HashPayloadSampling.ec': r'''
lemma __numerical_dfr_9_eof coins :
 dmap (uniform224 `*` uniform192)
   (fun hp:W8.t Array224.t*W8.t Array192.t =>
     (complete_hash_tail hp.`1,poly_sotp_encode_input coins hp.`2)) =
 (uniform192 `*` uniform192).
proof. exact (fresh_payload_buffer_pair_law coins). qed.
''',
    'kem_numerical_dfr/NTRUPlus768KEMProposalContext.ec': r'''
lemma __numerical_dfr_10_eof (E<:KeygenExpand {-ROF}) &m (event:kem_keygen_observation -> bool) :
 Pr[KeygenThenUniform(E).run() @ &m : event res] =
 Pr[ReifiedKeygenThenUniform.run(mk(fun z=>Pr[KeygenSource(E).guess(witness) @ &m : res=z]))
   @ &m : event res].
proof. exact (keygen_then_uniform_reified E &m event). qed.
''',
    'kem_numerical_dfr/NTRUPlus768EncapFreshBridge.ec': r'''
lemma __numerical_dfr_11_eof w0 fm0 :
 equiv[EncapBufferObservation.run ~ UniformPayloadBuffers.sample :
 w{1}=w0 /\ ROF.m{1}=fm0 /\ rom_key_relation w0 fm0 /\
 ROG.m{1}=empty /\ ROH.m{1}=empty ==> ={res}].
proof. exact (encap_observation_uniform w0 fm0). qed.
''',
    'kem_numerical_dfr/NTRUPlus768KEMROMTransfer.ec': r'''
lemma __numerical_dfr_12_eof &m :
 ROE.m{m}=empty =>
 Pr[KeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res] +
 (1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : true]) <=
 Pr[KeygenThenUniform(FreshExpand).run() @ &m : !honest_no_wrap res] + keygen_observer_error.
proof. exact (keygen_uniform_bad_or_missing &m). qed.
''',
    'kem_numerical_dfr/NTRUPlus768KEMIdealObservation.ec': r'''
lemma __numerical_dfr_13_eof &m :
 Pr[KeygenThenUniform(FreshExpand).run() @ &m : !honest_no_wrap res]=
 mu accepted_four_law four_buffers_bad.
proof. exact (fresh_keygen_no_wrap_ideal &m). qed.
''',
    'kem_numerical_dfr/NTRUPlus768ROMDFRObservation.ec': r'''
lemma __numerical_dfr_14_eof :
 equiv[KEMROMPrivate(UniformKEMRNG).run ~ InitializedKeygenThenUniform(ExpandROM).run :
 true ==> res.`2{1}= !honest_no_wrap res{2}].
proof. exact rom_private_uniform_observation. qed.
''',
    'kem_numerical_dfr/NTRUPlus768NumericalDFR.ec': r'''
lemma __numerical_dfr_15_eof &m :
 Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res] +
 (1%r-Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true]) <
 1%r/(2%r^238).
proof. exact (numerical_rom_dfr_total &m). qed.
''',
}

SEMANTIC_TARGETS = {
    'kem_numerical_dfr/NTRUPlus768NumericalDFRModel.ec': 'dfr_badE',
    'kem_numerical_dfr/NTRUPlus768CBDTensor.ec': 'paired_halves_tensor_law',
    'kem_numerical_dfr/NTRUPlus768CBDDistribution.ec': 'cbd_four_blocks_uniform',
    'kem_numerical_dfr/NTRUPlus768NoiseDecomposition.ec': 'two_integer_products_noise_blocks',
    'kem_numerical_dfr/NTRUPlus768NoiseNoWrap.ec': 'no_wrap_violation_blocks576',
    'kem_numerical_dfr/NTRUPlus768NoiseIndependentBlocks.ec': 'independent_blocks_observation',
    'kem_numerical_dfr/NTRUPlus768NoiseMGF.ec': 'noise_kind_mgf_exact',
    'kem_numerical_dfr/NTRUPlus768NoiseTail.ec': 'raw_four_bad_numerical',
    'kem_numerical_dfr/NTRUPlus768ConditionalBufferLaw.ec': 'accepted_bad_event_bound',
    'kem_numerical_dfr/NTRUPlus768HashPayloadSampling.ec': 'fresh_payload_buffer_pair_law',
    'kem_numerical_dfr/NTRUPlus768KEMProposalContext.ec': 'keygen_then_uniform_reified',
    'kem_numerical_dfr/NTRUPlus768EncapFreshBridge.ec': 'encap_observation_uniform',
    'kem_numerical_dfr/NTRUPlus768KEMROMTransfer.ec': 'keygen_uniform_bad_or_missing',
    'kem_numerical_dfr/NTRUPlus768KEMIdealObservation.ec': 'fresh_keygen_no_wrap_ideal',
    'kem_numerical_dfr/NTRUPlus768ROMDFRObservation.ec': 'rom_private_uniform_observation',
    'kem_numerical_dfr/NTRUPlus768NumericalDFR.ec': 'numerical_rom_dfr_total',
}

MODULE_BINDERS = {
    'kem_numerical_dfr/NTRUPlus768NumericalDFRModel.ec': (),
    'kem_numerical_dfr/NTRUPlus768CBDTensor.ec': (),
    'kem_numerical_dfr/NTRUPlus768CBDDistribution.ec': (),
    'kem_numerical_dfr/NTRUPlus768NoiseDecomposition.ec': (),
    'kem_numerical_dfr/NTRUPlus768NoiseNoWrap.ec': (),
    'kem_numerical_dfr/NTRUPlus768NoiseIndependentBlocks.ec': (),
    'kem_numerical_dfr/NTRUPlus768NoiseMGF.ec': (),
    'kem_numerical_dfr/NTRUPlus768NoiseTail.ec': (),
    'kem_numerical_dfr/NTRUPlus768ConditionalBufferLaw.ec': (),
    'kem_numerical_dfr/NTRUPlus768HashPayloadSampling.ec': (),
    'kem_numerical_dfr/NTRUPlus768KEMProposalContext.ec': ('E',),
    'kem_numerical_dfr/NTRUPlus768EncapFreshBridge.ec': (),
    'kem_numerical_dfr/NTRUPlus768KEMROMTransfer.ec': (),
    'kem_numerical_dfr/NTRUPlus768KEMIdealObservation.ec': (),
    'kem_numerical_dfr/NTRUPlus768ROMDFRObservation.ec': (),
    'kem_numerical_dfr/NTRUPlus768NumericalDFR.ec': (),
}
NEGATIVE_PROOFS = tuple(SENTINELS)
