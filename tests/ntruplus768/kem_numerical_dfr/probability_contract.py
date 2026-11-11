"""Distribution, numeric-tail and postprocessing boundaries."""
PREFIX='ntruplus/proof/768/ref/kem_numerical_dfr/'
CONDITIONAL=PREFIX+'NTRUPlus768ConditionalBufferLaw.ec'
NOWRAP=PREFIX+'NTRUPlus768NoiseNoWrap.ec'
TAIL=PREFIX+'NTRUPlus768NoiseTail.ec'
PAYLOAD=PREFIX+'NTRUPlus768HashPayloadSampling.ec'
IDEAL=PREFIX+'NTRUPlus768KEMIdealObservation.ec'
TRANSFER=PREFIX+'NTRUPlus768KEMROMTransfer.ec'


def check_probability(read,require):
    def has(code,token,label):
        wanted=''.join(token.split()).replace('op[opaque]','op')
        require(wanted in code.replace('op[opaque]','op'),label)
    conditional=read(CONDITIONAL)
    has(conditional,'keygen_f_accept bs.`1.`1 /\\ keygen_g_accept bs.`1.`2.','conditioning must retain both whole-key inverse predicates')
    has(conditional,'accepted_four_law = dcond raw_four_law four_buffers_accept.','accepted joint law is conditioning of the full raw four-buffer law')
    declaration=conditional.split('lemmaaccepted_four_probability',1)[1].split('proof.',1)[0]
    has(declaration,'mu accepted_four_law event = mu raw_four_law (fun bs=>four_buffers_accept bs /\\ event bs) / (fresh_f_accept_mass*fresh_g_accept_mass).','conditioning density must retain both acceptance masses and joint event')
    has(conditional,'25%r/64%r <= fresh_f_accept_mass*fresh_g_accept_mass.','conditioning denominator is bounded from both actual acceptance results')
    declaration=conditional.split('lemmaaccepted_four_event_bound',1)[1].split('proof.',1)[0]
    has(declaration,'mu accepted_four_law event <= (64%r/25%r)*mu raw_four_law event.','no accepted-coefficient iid shortcut may replace the conditioning cost')
    nowrap=read(NOWRAP)
    declaration=nowrap.split('lemmano_wrap_violation_noise576',1)[1].split('proof.',1)[0]
    has(declaration,'(forall k,0<=k<768 => -1<=coeff m.[k]<=1) =>','tail inclusion needs the actual CBD message range')
    has(declaration,'!sampled_m1_no_wrap fbuf gbuf r m => exists k,0<=k<768 /\\ 576<=`|(sampled_m1_noise fbuf gbuf r m).[k]|.','no-wrap failure must reach an inclusive 576 absolute-value tail for some actual coefficient')
    tail=read(TAIL)
    has(tail,'op noise_coefficient_bound = 2%r*noise_mgf_base^768/(2%r^576).','coefficient tail includes two signs and all 768 four-trit blocks')
    has(tail,'op noise_unconditional_bound = 1536%r*noise_mgf_base^768/(2%r^576).','union bound includes both signs of all 768 coefficients')
    declaration=tail.split('lemmaindependent_noise_tail',1)[1].split('proof.',1)[0]
    has(declaration,'size ds=768 =>','independent sum must contain all 768 blocks')
    has(declaration,'noise_mgf 1 d<=noise_mgf_base /\\ noise_mgf (-1) d<=noise_mgf_base','two-sided tail requires both MGF signs')
    has(declaration,'mu (djoin ds) (fun xs=>576<=`|noise_sum xs|)<=noise_coefficient_bound.','tail must measure the actual signed sum of independent blocks')
    has(tail,'lemma noise_union_numerical : noise_unconditional_bound<1%r/(2%r^356).','unconditioned exact numerical target')
    has(tail,'(64%r/25%r)*noise_unconditional_bound<1%r/(2%r^354).','conditioned target must retain the full conditioning factor')
    payload=read(PAYLOAD)
    has(payload,'Array224.init(fun i=>if i<32 then p.`1.[i] else p.`2.[i-32])','H output split preserves 32-byte key head and full 192-byte tail')
    has(payload,'dmap uniform224 complete_hash_tail=uniform192.','fresh H tail must have the full uniform192 law')
    declaration=payload.split('lemmafresh_payload_buffer_pair_law',1)[1].split('proof.',1)[0]
    has(declaration,'dmap (uniform224 `*` uniform192) (fun hp:W8.t Array224.t*W8.t Array192.t => (complete_hash_tail hp.`1,poly_sotp_encode_input coins hp.`2)) = (uniform192 `*` uniform192).','r and message buffer product law must retain actual H tail and coins-dependent SOTP mask')
    ideal=read(IDEAL)
    has(ideal,'((x.`1.`1.`kg_fbuf,x.`1.`1.`kg_gbuf),(x.`2,x.`3)).','ideal event projection must preserve actual accepted f/g and fresh r/m buffers')
    has(ideal,'call{1} keygen_clear_lossless. call{1}(keygen_finish_lossless SHAKEFROM ro_f_shake_ll). call fresh_retry_g_accepted_buffer; call fresh_retry_f_accepted_buffer;','ideal accepted-buffer coupling must discharge actual old clear, finish and both retry calls')
    has(ideal,'Pr[KeygenThenUniform(FreshExpand).run() @ &m : !honest_no_wrap res]= mu accepted_four_law four_buffers_bad.','ideal bad probability must be the actual whole-key conditioned law')
    transfer=read(TRANSFER)
    declaration=transfer.split('lemmakeygen_uniform_no_wrap_transfer',1)[1].split('proof.',1)[0]
    has(declaration,'ROE.m{m}=empty =>','postprocessing distance requires the original empty E cache premise')
    has(declaration,'`|Pr[KeygenThenUniform(ExpandROM).run() @ &m : honest_no_wrap res] - Pr[KeygenThenUniform(FreshExpand).run() @ &m : honest_no_wrap res]| <= keygen_observer_error.','postprocessing theorem must target the explicit stateless observer')
    identity=transfer.split('lemmakeygen_uniform_bad_missing_identity',1)[1].split('proof.',1)[0]
    has(identity,'Pr[KeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res] + (1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : true]) = 1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : honest_no_wrap res].','good/bad complement identity must retain nonreturning mass')
    declaration=transfer.split('lemmakeygen_uniform_bad_or_missing',1)[1].split('proof.',1)[0]
    has(declaration,'Pr[KeygenThenUniform(ExpandROM).run() @ &m : !honest_no_wrap res] + (1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : true]) <= Pr[KeygenThenUniform(FreshExpand).run() @ &m : !honest_no_wrap res] + keygen_observer_error.','bad-event transfer must retain real-ROM nonreturning mass')
    require('islosslessKeygenThenUniform(ExpandROM).run' not in transfer,'real-ROM postprocessing must not assume keygen termination')
