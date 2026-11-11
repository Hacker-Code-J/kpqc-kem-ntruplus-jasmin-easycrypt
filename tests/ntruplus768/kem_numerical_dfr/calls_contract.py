"""Actual encapsulation, cached F and fresh H/G boundaries."""
PREFIX='ntruplus/proof/768/ref/kem_numerical_dfr/'
ENCAP=PREFIX+'NTRUPlus768EncapFreshBridge.ec'
TENSOR=PREFIX+'NTRUPlus768CBDTensor.ec'
BLOCKS=PREFIX+'NTRUPlus768NoiseIndependentBlocks.ec'


def check_calls(read,ordered,require):
    def has(code,token,label):
        wanted=''.join(token.split()).replace('op[opaque]','op')
        require(wanted in code.replace('op[opaque]','op'),label)
    encap=read(ENCAP)
    observation=encap.split('moduleEncapBufferObservation=',1)[1].split('moduleFreshEncapCore=',1)[0]
    ordered(observation,('(er,coins) <@ EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(w.`kg_pk,witness);',
        'h <- oget ROH.m.[(coins,complete_sk_suffix w.`kg_sk)];',
        'p <- oget ROG.m.[payload_serialized h];',
        'return(complete_hash_tail h,poly_sotp_encode_input coins p);'))
    require(observation.count('<@')==1 and '<$' not in observation,'actual Encaps observer must not resample or skip its old caller')
    h=encap.split('lemmaencap_seed_fresh',1)[1].split('proof.',1)[0]
    has(h,'fm0.[pk0]=Some suffix0 =>','F must reuse the key-generation cached suffix')
    has(h,'equiv[EncapSeed(SHAKEFROM,SHAKEHROM).run ~ FreshHDraw.sample','fresh-H coupling must reference the actual seed/hash caller')
    has(h,'ROF.m{1}=fm0 /\\ ROH.m{1}=empty ==>','fresh H requires an empty H table while retaining F')
    has(h,'ROH.m{1}.[(coins0,suffix0)]=Some res{2}','H reply must be stored under actual coins and cached suffix')
    g=encap.split('lemmaencap_body_fresh',1)[1].split('proof.',1)[0]
    has(g,'equiv[EncapBody(SHAKEGROM).run ~ FreshGDraw.sample','fresh-G coupling must reference the actual body caller')
    has(g,'hashout{1}=h0 /\\ ROG.m{1}=empty ==>','fresh G requires an empty G table for the adaptive H-derived query')
    has(g,'ROG.m{1}.[payload_serialized h0]=Some res{2}','G pad must be stored at the actual serialized-r query')
    has(encap,'call{1} encap_clear_lossless.','actual encapsulation workspace clearing must be discharged')
    has(encap,'call{1} encap_clear_coins_lossless.','actual encapsulation coins clearing must be discharged')
    instrumented=encap.split('lemmaencap_instrumented_fresh',1)[1].split('proof.',1)[0]
    has(instrumented,'equiv[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run ~ FreshEncapRandom.run','instrumented coupling must preserve the old randomized caller')
    has(instrumented,'ROG.m{1}=empty /\\ ROH.m{1}=empty ==>','both freshness premises must reach the randomized caller')
    has(instrumented,'res.`2{1}=res.`1{2} /\\ ROF.m{1}=fm0','retained actual original coins and F cache must agree')
    observed=encap.split('lemmaencap_observation_fresh',1)[1].split('proof.',1)[0]
    has(observed,'rom_key_relation w0 fm0 /\\ ROG.m{1}=empty /\\ ROH.m{1}=empty ==> ={res}','final Encaps sampling bridge requires a generated key and fresh downstream caches')
    tensor=read(TENSOR)
    halves=tensor.split('lemmacbd_tensor_halves_law',1)[1].split('proof.',1)[0]
    has(halves,'dmap (dlist d (2*n)) (cbd_tensor_halves x0 n) = dlist (d `*` d) n.','pairing halves must start with twice as many unconditioned iid coordinates')
    has(tensor,'(nth x0 ab.`1 i,nth x0 ab.`1 (i+n))','tensor left pair must use different halves')
    has(tensor,'(nth x0 ab.`2 (perm i),nth x0 ab.`2 (perm i+n))','tensor right pair must preserve the same block permutation across distinct halves')
    blocks=read(BLOCKS)
    has(blocks,'dmap (dlist d n) (mapi f) = djoin (map (fun i => dmap d (f i)) (range 0 n)).','independent-block tensor identity cannot replace a conditioned joint law by iid coordinates')
    for name,code in (('encap',encap),('tensor',tensor),('blocks',blocks)):
        require('shake256' not in code.lower() and 'keygen_seed_expansion' not in code,'new distribution bridge must not substitute fixed SHAKE: '+name)
