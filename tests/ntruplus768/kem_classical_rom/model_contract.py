"""Independent structural checks for cache, domain, caller and observer boundaries."""
import re
PREFIX = 'ntruplus/proof/768/ref/'
DOMAINS = PREFIX + 'kem_rom_oracle/NTRUPlus768ROMDomains.ec'
LAWS = PREFIX + 'kem_rom_oracle/NTRUPlus768ROMDistributions.ec'
ORACLES = PREFIX + 'kem_rom_oracle/NTRUPlus768ROMOracles.ec'
OBSERVER = PREFIX + 'kem_rom_collision/NTRUPlus768ROMSeedObserver.ec'
COLLISION = PREFIX + 'kem_rom_collision/NTRUPlus768ROMSeedCollision.ec'
KEYGENOBSERVER = PREFIX + 'kem_rom_collision/NTRUPlus768ROMKeygenObserver.ec'
KEYGEN = PREFIX + 'kem_rom_bridge/NTRUPlus768ROMKeygen.ec'
PAYLOADSPEC = PREFIX + 'kem_rom_bridge/NTRUPlus768KEMPayloadSpec.ec'
PAYLOADALGEBRA = PREFIX + 'kem_rom_bridge/NTRUPlus768KEMPayloadAlgebra.ec'
ENCAP = PREFIX + 'kem_rom_bridge/NTRUPlus768ROMEncap.ec'
DECAP = PREFIX + 'kem_rom_bridge/NTRUPlus768ROMDecap.ec'
GAME = PREFIX + 'kem_rom_bridge/NTRUPlus768ROMCorrectness.ec'
HASH = PREFIX + 'kem_rom_bridge/NTRUPlus768ROMPayloadHash.ec'
SOTPMASK = PREFIX + 'kem_rom_sampling/NTRUPlus768ROMSOTPMaskLaw.ec'
SOTPDEF = PREFIX + 'poly_sotp_roundtrip/NTRUPlus768PolySOTPEncodeAlgebra.ec'
SAMPLING = PREFIX + 'kem_rom_sampling/NTRUPlus768ROMSOTPSampling.ec'
FAILURE = PREFIX + 'kem_failure_bound/NTRUPlus768KEMFailureModel.ec'


def check_model(read, ordered, require):
    domains = read(DOMAINS)
    for token in (
        'Array1153.init (fun i => if i = 0 then W8.zero else pk.[i-1])',
        'Array1153.init (fun i => if i = 0 then W8.one else serialized.[i-1])',
        'Array129.init (fun i => if i = 0 then W8.of_int 2 else if i <= 96 then coins.[i-1] else pkhash.[i-97])',
        'H of (W8.t Array96.t * W8.t Array32.t)',
        'with q = E seed => Array32.to_list seed',
        'with q = F pk => Array1153.to_list (encode_f pk)',
        'with q = G serialized => Array1153.to_list (encode_g serialized)',
        'with q = H payload => Array129.to_list (encode_h payload.`1 payload.`2)',
        'lemma raw_query_inj : injective raw_query',
        'lemma encode_h_inj coins pkhash coins\' pkhash\'',
        'lemma encode_f_g_disjoint pk serialized : encode_f pk <> encode_g serialized',
    ):
        require(''.join(token.split()) in domains, 'ROM domain definition/injection drift: ' + token)
    laws = read(LAWS)
    require('abstracttheory' not in laws and 'clone' not in laws,
            'concrete laws must not rely on unresolved clone obligations')
    for size in (32, 96, 192, 224):
        require(f'opuniform{size}=dmap(dlistW8.dword{size})(Array{size}.of_listW8.zero).' in laws,
                'concrete array distribution definition')
        for lemma in ('ll', 'uni', 'point', 'fu'):
            require(f'lemmauniform{size}_{lemma}' in laws, 'concrete distribution law inventory')
        require(f'lemmauniform{size}_point(x:W8.tArray{size}.t):mu1uniform{size}x=(1%r/256%r)^{size}' in laws,
                'exact output point law')
    require('lemmabyte_uniform_point' in laws and 'lemmabyte_list_uniform_point' in laws,
            'finite byte and list laws must be locally proved')
    oracles = read(ORACLES)
    port_data = (
        ('E', 'W8.t Array32.t', 'W8.t Array192.t', 192),
        ('F', 'W8.t Array1152.t', 'W8.t Array32.t', 32),
        ('G', 'W8.t Array1152.t', 'W8.t Array192.t', 192),
        ('H', 'W8.t Array96.t * W8.t Array32.t', 'W8.t Array224.t', 224),
    )
    declared = re.findall(r'module(?:type)?([A-Z]\w*)[(:={]', oracles)
    expected = {f'RO{p}{s}' for p, _, _, _ in port_data for s in ('', 'Port')}
    expected.update(('ExpandROM', 'SHAKEFROM', 'SHAKEGROM', 'SHAKEHROM', 'ROMInit'))
    require(set(declared) == expected and len(declared) == len(expected), 'oracle module inventory/state boundary')
    for port, input_type, output_type, size in port_data:
        input_type, output_type = ''.join(input_type.split()), ''.join(output_type.split())
        body = (f'moduleRO{port}:RO{port}Port={{varm:({input_type},{output_type})fmap'
                f'procinit()={{m<-empty;}}procget(input:{input_type}):{output_type}='
                f'{{varr;if(input\\notinm){{r<$uniform{size};m.[input]<-r;}}returnogetm.[input];}}}}.')
        require(body in oracles, 'oracle must sample only fresh keys, preserve cache and own only its table: ' + port)
        lower = port.lower()
        for lemma in ('init_empty', 'init_ll', 'get_ll', 'get_value', 'get_cached', 'get_preserves', 'get_fresh'):
            require(f'lemmaro{lower}_{lemma}' in oracles, 'oracle contract inventory: ' + port + '/' + lemma)
        require(f'RO{port}.m=m0/\\input=x0/\\x0\\notinm0==>res=y0]=(mu1uniform{size}y0)' in oracles,
                'fresh law needs an explicit absent-key premise: ' + port)
        require(f'RO{port}.m=m0/\\input=x0/\\m0.[x0]=Somey0==>res=y0/\\RO{port}.m=m0' in oracles,
                'cached law must preserve both response and table: ' + port)
    for name, input_type, output_type, call in (
        ('ExpandROM', 'seed:W8.t Array32.t', 'W8.t Array192.t', 'ROE.get(seed)'),
        ('SHAKEFROM', 'input:W8.t Array1153.t', 'W8.t Array32.t', 'ROF.get(peel1153 input)'),
        ('SHAKEGROM', 'input:W8.t Array1153.t', 'W8.t Array192.t', 'ROG.get(peel1153 input)'),
        ('SHAKEHROM', 'input:W8.t Array129.t', 'W8.t Array224.t', 'ROH.get(peel_h input)'),
    ):
        body = f'module{name}={{procshake({input_type}):{output_type}={{varr;r<@{call};returnr;}}}}.'
        require(''.join(body.split()) in oracles, 'raw shake adapter must use matching typed cache: ' + name)
    require('moduleROMInit={procinit()={ROE.init();ROF.init();ROG.init();ROH.init();}}.' in oracles,
            'initialization must clear exactly the four independent tables')
    keygen, encap, hashes, decap, game = read(KEYGEN), read(ENCAP), read(HASH), read(DECAP), read(GAME)
    payload = read(PAYLOADSPEC)
    for token in (
        'op [opaque] payload_r (hout:W8.t Array224.t) = poly_cbd1_spec (complete_hash_tail hout)',
        'op [opaque] payload_m (coins:W8.t Array96.t) (pad:W8.t Array192.t) = poly_sotp_encode_spec coins pad',
        'op [opaque] payload_shared_key (hout:W8.t Array224.t) = Array32.init (fun i => hout.[i])',
    ):
        require(''.join(token.split()) in payload, 'realized H tail/SOTP coins/shared-key prefix drift: ' + token)
    for name, text in (('KeyGen', keygen), ('Encap', encap), ('Hash', hashes), ('Decap', decap),
                       ('Game', game), ('PayloadSpec', read(PAYLOADSPEC)),
                       ('PayloadAlgebra', read(PAYLOADALGEBRA)), ('Sampling', read(SAMPLING))):
        require(all(token not in text for token in (
            'encap_shake_f_spec', 'message_shake_spec', 'complete_shake_h_spec',
            'keygen_seed_expansion', 'encap_derand_spec', 'complete_spec')) and
                'shake256' not in text.lower(),
            'ROM bridge must not apply fixed SHAKE contracts: ' + name)
    for token in (
        'payload_key_relation w.`kg_fbuf w.`kg_gbuf w.`kg_finv w.`kg_ginv w.`kg_h w.`kg_hinv w.`kg_pk w.`kg_sk',
        'fm.[w.`kg_pk]=Some (complete_sk_suffix w.`kg_sk)',
        'hoare[KeygenInstrumented(R,E,SHAKEFROM).run:true ==> rom_key_relation res.`1 ROF.m /\\ res.`2=keygen_clear_zero_spec]',
        'hoare[Keygen(R,E,SHAKEFROM).run:true ==> exists (w:keygen_witness), rom_key_relation w ROF.m /\\ res=(w.`kg_pk,w.`kg_sk)]',
        'call(keygen_retry_g_accepted R E); call(keygen_retry_f_accepted R E)',
    ):
        require(''.join(token.split()) in keygen, 'actual accepted KeyGen/cached F boundary drift: ' + token)
    for lemma in ('rom_keygen_instrumented', 'rom_keygen_public'):
        declaration = keygen.split('lemma' + lemma, 1)[1].split('proof.', 1)[0]
        require('(R<:KeygenSeedRNG{-ROF})(E<:KeygenExpand{-ROF})' in declaration,
                'KeyGen seed/expand modules must be separated from cached F: ' + lemma)
    for token in (
        'hoare[EncapBody(SHAKEGROM).run:',
        'let pad0=oget ROG.m.[payload_serialized hout0] in ROG.m.[payload_serialized hout0]=Some pad0',
        'let hout=oget hm.[(coins,suffix)] in let pad=oget gm.[payload_serialized hout] in',
        'fm.[pk]=Some suffix /\\ hm.[(coins,suffix)]=Some hout /\\ gm.[payload_serialized hout]=Some pad',
        'hoare[EncapDerand(SHAKEFROM,SHAKEGROM,SHAKEHROM).run:',
        'hoare[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,Q).run:',
        '(Q<:EncapRNG {-ROF,-ROG,-ROH})',
        'ecall(poly_sotp_encode_functional witness coins0 pad)',
    ):
        require(''.join(token.split()) in encap, 'actual Encaps/realized cached payload boundary drift: ' + token)
    for token in (
        'encap_hash_f_input_spec pk=encode_f pk',
        'message_hash_input bs=encode_g bs',
        'hash_h_prepare_spec coins suffix=encode_h coins suffix',
        'hm0.[(coins0,suffix0)]=Some hout0',
        'ROH.m=hm0 ==> res=hout0 /\\ ROH.m=hm0',
    ):
        require(''.join(token.split()) in hashes, 'actual old-array preparation/cache contract drift: ' + token)
    for token in (
        'hm0.[(coins0,complete_sk_suffix w.`kg_sk)]=Some hout0',
        'sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf (payload_r hout0) (payload_m coins0 pad0)',
        'hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run:',
        'res=(payload_shared_key hout0,W32.zero,clear_zero_spec) /\\ ROG.m=gm0 /\\ ROH.m=hm0',
        'call(poly_sotp_decode_functional witness (payload_m coins0 pad0) pad0)',
        'call(rom_g_cached',
        'call(rom_h_cached coins0 suffix0 hout0 hm0 hc)',
    ):
        require(''.join(token.split()) in decap, 'actual CompleteDecaps/cached recovery boundary drift: ' + token)
    public = game.split('moduleKEMROMCorrectness(', 1)[1].split('moduleKEMROMPrivate(', 1)[0]
    private = game.split('moduleKEMROMPrivate(', 1)[1].split('lemmarom_decap_from_relation', 1)[0]
    require(public.count('<@') == 1 and public.count('return') == 1,
            'public ROM game must forward exactly one actual failure experiment')
    require(private.count('<@') == 3 and private.count('return') == 1,
            'private ROM game must forward exactly three actual callers')
    for body in (public, private):
        require('var' not in body.split('proc', 1)[0], 'game must not add global observation state')
        require('<$' not in body and 'while(' not in body and 'if(' not in body,
                'game must not replace caller sampling or branching')
    ordered(public, ('ROE.init(); ROF.init(); ROG.init(); ROH.init();',
                     'failed <@ KEMCorrectness(KeygenRNGPort(B),ExpandROM,SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run();',
                     'return failed;'))
    ordered(private, ('ROE.init(); ROF.init(); ROG.init(); ROH.init();',
                      '(w,cleared) <@ KeygenInstrumented(KeygenRNGPort(B),ExpandROM,SHAKEFROM).run(witness);',
                      '(er,coins) <@ EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run(w.`kg_pk,witness);',
                      'suffix <- complete_sk_suffix w.`kg_sk;',
                      'hout <- oget ROH.m.[(coins,suffix)];',
                      'pad <- oget ROG.m.[payload_serialized hout];',
                      'bad <- !sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf (payload_r hout) (payload_m coins pad);',
                      'dr <@ CompleteDecaps(SHAKEGROM,SHAKEHROM).run(er.`1,w.`kg_sk,witness);',
                      'return (kem_failure er dr,bad);'))
    for lemma in ('rom_public_projection', 'rom_failure_implies_bad', 'rom_failure_probability'):
        declaration = game.split('lemma' + lemma + '(', 1)[1].split('proof.', 1)[0]
        require('B<:KEMRNG{-ROE,-ROF,-ROG,-ROH}' in declaration,
                'common RNG must be independent of every oracle table: ' + lemma)
    require('Pr[KEMROMCorrectness(B).run()@&m:res]<=Pr[KEMROMPrivate(B).run()@&m:res.`2]' in game,
            'ROM probability theorem must bound the actual public failure by actual private Bad')
    projection = game.split('lemmarom_public_projection(', 1)[1].split('proof.', 1)[0]
    require('={globB,globROE,globROF,globROG,globROH}==>res{1}=res{2}.`1/\\={globB,globROE,globROF,globROG,globROH}' in projection,
            'public/private projection must preserve shared RNG state and all caches')
    require('op[opaque]kem_failure(er:encap_result)(dr:decap_result)=er.`3<>W32.zero\\/dr.`2<>W32.zero\\/er.`2<>dr.`1.' in read(FAILURE),
            'failure must include both statuses and shared-key mismatch')
    mask = read(SOTPMASK)
    for token in (
        'lemma sotp_xor_byte_involution (byte mask : W8.t) : (byte +^ mask) +^ mask = byte',
        'lemma sotp_xor_head_bijection (coins : W8.t Array96.t) : bijective (poly_sotp_encode_input coins)',
        'dmap uniform192 (poly_sotp_encode_input coins) = uniform192',
        'op cbd1_uniform = dmap uniform192 poly_cbd1_spec',
        'lemma sotp_encode_uniform_law (coins : W8.t Array96.t) : dmap uniform192 (poly_sotp_encode_spec coins) = cbd1_uniform',
    ):
        require(''.join(token.split()) in mask, 'arbitrary-coins SOTP uniform-pad law drift: ' + token)
    require('op poly_sotp_encode_input (msg : W8.t Array96.t) (pad : W8.t Array192.t) : W8.t Array192.t = Array192.init (fun k => if 0 <= k < 96 then pad.[k] +^ msg.[k] else pad.[k])'.replace(' ', '') in read(SOTPDEF),
            'actual SOTP mask must XOR only the 96-byte head and preserve the tail')
    sampling = read(SAMPLING)
    require(sampling.count('module') == 1 and sampling.count('proc') >= 5,
            'component sampler module inventory')
    actual_name = 'NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(rp,coins,pad)'
    require('pad<@SHAKEGROM.shake(encode_gserialized);rp<@' + actual_name + ';returnrp;' in sampling,
            'fresh G component must call actual old-array SOTP encoder')
    require('pad<$uniform192;rp<@' + actual_name + ';returnrp;' in sampling,
            'component uniform pad must have the full 192-byte law and actual encoder')
    fresh = sampling.split('lemmasotp_g_fresh_event', 1)[1].split('proof.', 1)[0]
    require('serialized0\\notinROG.m{m}=>' in fresh,
            'component CBD distribution equality needs an absent G-key premise')
    require('Pr[SOTPPadSampling.g_encode(rp0,coins0,serialized0)@&m:eventres]=mucbd1_uniformevent' in fresh,
            'component fresh-G equality must measure actual encoder output')
    coupling = sampling.split('lemmasotp_g_fresh_uniform', 1)[1].split('proof.', 1)[0]
    require('={rp,coins}/\\serialized{1}=serialized0/\\serialized0\\notinROG.m{1}==>={res}' in coupling,
            'fresh component coupling must retain the initial absent G-key condition')
    cached = sampling.split('lemmasotp_g_cached_value', 1)[1].split('proof.', 1)[0]
    require('ROG.m=m0/\\m0.[serialized0]=Somepad0==>res=poly_sotp_encode_speccoins0pad0/\\ROG.m=m0' in cached,
            'cached component must use its realized response and preserve its table')
    observer = read(OBSERVER)
    seed = observer.split('procseed32():seed={', 1)[1].split('procmark(', 1)[0]
    require(seed.startswith('varx;x<$law;if(sizeprefix<q)'), 'draw must precede every budget branch')
    ordered(seed, ('x <$ law;', 'if (size prefix < q)',
                   'prefixbad <- prefixbad \\/ (size known <= a /\\ (x \\in known \\/ x \\in prefix));',
                   'prefix <- x::prefix;', 'fullbad <- fullbad \\/ (x \\in known \\/ x \\in draws);',
                   'draws <- x::draws;', 'return x;'))
    require(seed.count('<$') == 1 and seed.count('return') == 1, 'observer must always draw once')
    require('procmark(x:seed):unit={if(!(x\\indraws)/\\!(x\\inknown))known<-x::known;}' in observer,
            'mark must retain every external E input not covered by draws or known')
    ordered(observer, ('law <- d; q <- q0; a <- a0;',
                       'draws <- []; prefix <- []; known <- undup prior;',
                       'fullbad <- false; prefixbad <- false;'))
    collision_decl = observer.split('lemmaseed_prefix_collision(', 1)[1].split('proof.', 1)[0]
    require('(forallx,mu1dx<=p)=>' in collision_decl, 'adaptive prefix bound must retain its point premise')
    full_decl = observer.split('lemmaseed_unrestricted_collision(', 1)[1].split('proof.', 1)[0]
    require('+Pr[SeedExperiment(A).run(d,qb,ab,prior)@&m:qb<sizeSeedObserver.draws\\/ab<sizeSeedObserver.known]' in full_decl,
            'unrestricted collision bound must retain the budget tail probability')
    for formula in (
        '(b => pb \\/ q < size ds \\/ a < size ks)',
        'Bigreal.BRA.bigi predT (fun c => (a0+c)%r*p) 0 q0 = (a0*q0)%r*p + (q0*(q0-1))%r/2%r*p',
        'Pr[SeedExperiment(A).run(d,q0,a0,prior) @ &m : SeedObserver.prefixbad] <= (a0*q0)%r*p + (q0*(q0-1))%r/2%r*p',
        '0 <= q0 => 0 <= a0 =>',
        '(forall x, mu1 d x <= p) =>',
        'Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : SeedObserver.fullbad] <= (ab*qb)%r*p + (qb*(qb-1))%r/2%r*p + Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : qb < size SeedObserver.draws \\/ ab < size SeedObserver.known]',
    ):
        require(''.join(formula.split()) in observer, 'observer collision/budget premise drift: ' + formula)
    collision = read(COLLISION)
    require('opseed_probability=(1%r/256%r)^32.' in collision,
            'seed collision point law must be exactly the 32-byte uniform domain')
    uniform_decl = collision.split('lemmauniform_seed_unrestricted_collision(', 1)[1].split('proof.', 1)[0]
    for token in (
        '0 <= qb => 0 <= ab =>',
        'Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m : SeedObserver.fullbad] <= (ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) + Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m : qb < size SeedObserver.draws \\/ ab < size SeedObserver.known]',
    ):
        require(''.join(token.split()) in uniform_decl, 'uniform collision law/budget/tail drift: ' + token)
    observed = read(KEYGENOBSERVER)
    for token in (
        'module ObserverSeedPort(O:SeedQueryOracle) = { proc sample() : seed = { var x; x <@ O.seed32(); return x; } }.',
        'O.mark(seed); y <@ ROE.get(seed); return y;',
        'result <@ Keygen(ObserverSeedPort(O),ObservedExpand(O),SHAKEFROM).run();',
        'SeedObserver.init(uniform32,q0,a0,elems(fdom ROE.m));',
        '(pk,sk) <@ Keygen(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run();',
        'PlainSeedOracle.law <- uniform32;',
        '(pk,sk) <@ Keygen(ObserverSeedPort(PlainSeedOracle),ExpandROM,SHAKEFROM).run();',
        'forall x, x \\in m => x \\in ds \\/ x \\in ks',
        'lemma observer_initial_cache_covered m : observer_cache_covers m [] (undup(elems(fdom m)))',
        'lemma observed_expand_cache_covered : hoare[ObservedExpand(SeedObserver).shake : observer_cache_covers ROE.m SeedObserver.draws SeedObserver.known ==> observer_cache_covers ROE.m SeedObserver.draws SeedObserver.known]',
        'forall x, x \\in m <=> x \\in ds \\/ x \\in ks',
        'observer_cache_covers m ds ks /\\ forall x, x \\in ds \\/ x \\in ks => x \\in m \\/ x=pending',
        'lemma observer_seed_cache_pending : hoare[ObserverSeedPort(SeedObserver).sample : observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known ==> observer_cache_pending ROE.m SeedObserver.draws SeedObserver.known res]',
        'lemma observed_expand_cache_exact : hoare[ObservedExpand(SeedObserver).shake : observer_cache_pending ROE.m SeedObserver.draws SeedObserver.known seed ==> observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known]',
        'lemma actual_keygen_observer_cache_exact : hoare[ObservedActualKeygen.run : true ==> observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known]',
        'call observed_retry_g_cache_exact; call observed_retry_f_cache_exact;',
        'lemma observed_expand_erases (O <: SeedQueryOracle {-ROE}) : islossless O.mark => equiv[ObservedExpand(O).shake ~ ExpandROM.shake : ={seed,ROE.m} ==> ={res,ROE.m}]',
        'lemma actual_keygen_observer_projects : equiv[ObservedActualKeygen.run ~ PlainActualKeygen.run : ={q0,a0,ROE.m,ROF.m} ==> ={res,ROE.m,ROF.m}]',
        'lemma actual_keygen_observer_matches_context : equiv[ObservedActualKeygen.run ~ SeedExperiment(ActualKeygenSeedContext).run : ={q0,a0,ROE.m,ROF.m} /\\ d{2}=uniform32 /\\ prior{2}=elems(fdom ROE.m{1}) ==> ={glob SeedObserver,ROE.m,ROF.m} /\\ res{1}=ActualKeygenSeedContext.result{2}]',
    ):
        require(''.join(token.split()) in observed, 'actual KeyGen observer/projection/cache union drift: ' + token)
    for wrapper in ('ObservedActualKeygen', 'PlainActualKeygen'):
        body = observed.split('module' + wrapper + '={', 1)[1].split('}.', 1)[0]
        require(body.count('<@') == 1 and body.count('return') == 1 and
                all(t not in body for t in ('<$', 'while(', 'if(', 'ROE.init()')),
                'KeyGen observer wrapper must preserve actual retries and prior cache: ' + wrapper)
    bound = observed.split('lemmaactual_keygen_completed_seed_collision', 1)[1].split('proof.', 1)[0]
    require('0<=qb=>0<=ab=>' in bound and
            'Pr[ObservedActualKeygen.run(qb,ab)@&m:SeedObserver.fullbad]<=(ab*qb)%r/(2%r^256)+(qb*(qb-1))%r/(2%r*(2%r^256))+Pr[ObservedActualKeygen.run(qb,ab)@&m:qb<sizeSeedObserver.draws\\/ab<sizeSeedObserver.known]' in bound,
            'actual completed KeyGen collision bound must retain both budget tails')
    require(all(t not in observed for t in ('islosslessObservedActualKeygen.run',
                                            'islosslessPlainActualKeygen.run')),
            'observer projection must not assert unconditional ROM retry termination')
