"""Semantic boundaries for integer noise, conditioning and actual-call seams."""
import re

PREFIX='ntruplus/proof/768/ref/kem_numerical_dfr/'
MODEL=PREFIX+'NTRUPlus768NumericalDFRModel.ec'
DECOMPOSITION=PREFIX+'NTRUPlus768NoiseDecomposition.ec'
CBD=PREFIX+'NTRUPlus768CBDDistribution.ec'
MGF=PREFIX+'NTRUPlus768NoiseMGF.ec'
CONTEXT=PREFIX+'NTRUPlus768KEMProposalContext.ec'
CONVOLUTION='ntruplus/proof/768/ref/valid_key_m1_recovery/NTRUPlus768IntegerConvolution.ec'
RECOVERY='ntruplus/proof/768/ref/valid_key_m1_recovery/NTRUPlus768ValidKeyM1Recovery.ec'
FAILURE='ntruplus/proof/768/ref/kem_failure_bound/NTRUPlus768KEMFailureModel.ec'
ORACLES='ntruplus/proof/768/ref/kem_rom_oracle/NTRUPlus768ROMOracles.ec'
ROM_GAME='ntruplus/proof/768/ref/kem_rom_bridge/NTRUPlus768ROMCorrectness.ec'


def check_model(read,ordered,require):
    def has(code,token,label):
        wanted=''.join(token.split()).replace('op[opaque]','op')
        require(wanted in code.replace('op[opaque]','op'),label)
    convolution=read(CONVOLUTION)
    has(convolution,'if s < 768 then integer_unit s else if s < 1152 then integer_add (integer_unit (s - 384)) (integer_scale (-1) (integer_unit (s - 768))) else integer_scale (-1) (integer_unit (s - 1152)).','integer product must use exact X^768-X^384+1 reduction signs')
    product=convolution.split('opinteger_product',1)[1].split('lemmainteger_zero_get',1)[0]
    require('%%' not in product,'integer noise must never reduce coefficients modulo q')
    recovery=read(RECOVERY)
    has(recovery,'integer_add (integer_product (integer_coefficients (poly_cbd1_spec gbuf)) (integer_coefficients r)) (integer_product (integer_coefficients m) (integer_coefficients (poly_cbd1_spec fbuf)))','actual noise must include both gr and mf products')
    has(recovery,'integer_add (integer_coefficients m) (integer_scale 3 (sampled_m1_noise fbuf gbuf r m))','actual lift must retain correlated message coefficient and factor three')
    has(recovery,'-1728 <= (sampled_m1_integer_lift fbuf gbuf r m).[j] <= 1728','no-wrap interval is inclusive and integer-valued')
    decomposition=read(DECOMPOSITION)
    has(decomposition,'op noise_partner (k i:int) : int = (k-i) %%384.','partner permutation must be modulo the 384 block length')
    has(decomposition,'if s<768 then b2i(k=s) else if s<1152 then b2i(k=s-384)-b2i(k=s-768) else -b2i(k=s-1152).','new monomial weights must retain all signed reduction branches')
    has(decomposition,'op noise_block (k i a c b d:int) : int = if k<384 then if i<=k then a*b-c*d else -(a*d+c*b+c*d) else if i<=k-384 then a*d+c*b+c*d else a*b+a*d+c*b.','all four signed block cases and carry boundaries must be preserved')
    has(decomposition,'noise_block k i a.[i] a.[i+384] b.[noise_partner k i] b.[noise_partner k i+384]) 0 384.','each product must use 384 blocks with four distinct indexed coordinates')
    cbd=read(CBD)
    has(cbd,'op [opaque] dcbd : int distr = dmap (duniform [0;1;2;3]) (fun u=>if u=0 then -1 else if u=3 then 1 else 0).','CBD trit weights must be 1/4,1/2,1/4')
    has(cbd,'op cbd_interleave_index (i:int) = if i %% 2=0 then i %/ 2 else 768+i %/ 2.','CBD pairing must combine distinct head/tail source bits')
    has(cbd,'lemma cbd_coeff_list_uniform : dmap uniform192 cbd_coeff_list=dlist dcbd 768.','iid coefficient law must be proved only for unconditioned uniform buffers')
    require(not re.search(r'dmap\(dconduniform192keygen_[fg]_accept\)cbd_coeff_list=dlistdcbd768',cbd),'accepted key coefficients must not be asserted iid')
    has(cbd,'cbd_pair_blocks perm (bs.`1.`2,bs.`2.`1) ++ cbd_pair_blocks perm (bs.`2.`2,bs.`1.`1).','four-buffer tensor must pair g/r and m/f without dropping or duplicating a buffer')
    full_cbd=cbd.split('lemmacbd_four_blocks_uniform',1)[1].split('proof.',1)[0]
    has(full_cbd,'(forall i j,0<=i<384=>0<=j<384=>perm i=perm j=>i=j) =>','independent block law requires an injective coordinate permutation')
    has(full_cbd,'(forall i,0<=i<384=>0<=perm i<384) =>','independent block law requires an in-range coordinate permutation')
    has(full_cbd,'dmap ((uniform192 `*` uniform192) `*` (uniform192 `*` uniform192)) (cbd_four_blocks perm)=dlist dcbd_quad 768.','four-buffer iid block law applies only before key acceptance and includes both convolutions')
    mgf=read(MGF)
    has(mgf,'op noise_mgf_base = 1237%r/1024%r.','MGF base must be the exact four-trit path value')
    has(mgf,'op noise_mgf (s:int) (d:int distr) = E d (fun x=>2%r^(s*x)).','MGF must include the signed whole block exponent')
    declaration=mgf.split('lemmaindependent_noise_mgf_product',1)[1].split('proof.',1)[0]
    has(declaration,'E (djoin ds) (fun xs=>2%r^(s*noise_sum xs))= Bigreal.BRM.big predT (noise_mgf s) ds.','MGF multiplication must apply to an explicit independent join of full block laws')
    model=read(MODEL)
    has(model,'op [opaque] dfr_bad (f g r m:W8.t Array192.t) : bool = !sampled_m1_no_wrap f g (poly_cbd1_spec r) (poly_cbd1_spec m).','numerical bad event must be the actual no-wrap violation')
    has(model,'op accepted_four_law = (((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept)) `*` (uniform192 `*` uniform192)).','accepted keys must retain whole-buffer conditioning on both actual predicates')
    has(model,'f <$ dcond uniform192 keygen_f_accept; g <$ dcond uniform192 keygen_g_accept; r <$ uniform192; m <$ uniform192; return ((f,g),(r,m));','accepted comparison experiment must sample whole conditional keys and independent fresh r/m buffers')
    has(model,'proc seed32() : W8.t Array32.t = { var x; x <$ uniform32; return x; }','honest KEM seed port law must be concrete uniform32')
    has(model,'proc coins96() : W8.t Array96.t = { var x; x <$ uniform96; return x; }','honest KEM coins port law must be concrete uniform96')
    context=read(CONTEXT)
    has(context,'op honest_no_wrap (x:kem_keygen_observation) = sampled_m1_no_wrap x.`1.`1.`kg_fbuf x.`1.`1.`kg_gbuf (poly_cbd1_spec x.`2) (poly_cbd1_spec x.`3).','postprocessor predicate must use actual returned key buffers and both fresh samples')
    has(context,'out <@ KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(witness); rbuf <$ uniform192; mbuf <$ uniform192; return(out,rbuf,mbuf);','post-KeyGen ideal observation must retain the actual caller before fresh r/m sampling')
    has(context,'module NoWrapObserver = { proc guess(x:keygen_output) : bool = { var rbuf,mbuf:W8.t Array192.t; rbuf <$ uniform192; mbuf <$ uniform192; return honest_no_wrap(x,rbuf,mbuf); } }.','postprocessor may read only returned witness and its own fresh randomness, not ROM state')
    has(context,'op keygen_observer_error = 130818%r/(2%r^256).','context transfer must include the full previously certified KeyGen error')
    has(context,'(E<:KeygenExpand {-ROG,-ROH})','hash framing must exclude both downstream caches from key expansion')
    has(context,'ROG.m=gm /\\ ROH.m=hm ==> ROG.m=gm /\\ ROH.m=hm','key generation must preserve both downstream cache states')
    failure=read(FAILURE)
    has(failure,'op [opaque] kem_failure (er:encap_result) (dr:decap_result) = er.`3 <> W32.zero \\/ dr.`2 <> W32.zero \\/ er.`2 <> dr.`1.','actual failure includes both API statuses and shared-key disagreement')
    ordered(failure,('coins <@ Q.sample();','original <- coins;','(ct,ss,status,workspace) <@ EncapDerand(F,G,H).run(pk,coins,workspace);','coins <@ NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins);','return((ct,ss,status,workspace,coins),original);'))
    ordered(failure,('(pk,sk) <@ Keygen(R,E,F).run();','er <@ EncapRandom(F,G,H,Q).run(pk,witness);','dr <@ CompleteDecaps(G,H).run(er.`1,sk,witness);','return kem_failure er dr;'))
    game=read(ROM_GAME)
    ordered(game,('ROE.init(); ROF.init(); ROG.init(); ROH.init();','failed <@ KEMCorrectness(KeygenRNGPort(B),ExpandROM,SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run();','return failed;'))
    oracles=read(ORACLES)
    for port,size in (('G',192),('H',224)):
        has(oracles,f'RO{port}.m=m0 /\\ input=x0 /\\ x0 \\notin m0 ==> res=y0]=(mu1 uniform{size} y0)','fresh '+port+' distribution must require an absent query')
        has(oracles,f'm0.[x0]=Some y0 ==> res=y0 /\\ RO{port}.m=m0','cached '+port+' answer must stay fixed rather than redraw')
    for name,code in (('model',model),('CBD',cbd),('MGF',mgf),('decomposition',decomposition),('context',context)):
        require('shake256' not in code.lower() and 'keygen_seed_expansion' not in code,'fresh/ROM bridge must not substitute fixed SHAKE: '+name)
        require(not re.search(r'islossless(?:CountedKeygen|KeygenInstrumented|Keygen)\([^)]*ExpandROM',code),'numerical DFR must not assume unlimited real-ROM losslessness: '+name)

    from probability_contract import check_probability
    check_probability(read,require)

    from calls_contract import check_calls
    check_calls(read,ordered,require)

    from final_contract import check_final
    check_final(read,ordered,require)
