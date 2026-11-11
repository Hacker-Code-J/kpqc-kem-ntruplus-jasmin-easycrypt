"""Independent boundaries for concrete acceptance certificates and aggregation."""
import re
from test_reference import inputs, certify_roots

PREFIX='ntruplus/proof/768/ref/keygen_acceptance/'
ROOTS=PREFIX+'NTRUPlus768AcceptanceRoots.ec'
ORBIT=PREFIX+'NTRUPlus768UniformOrbitBound.ec'
ALGEBRA=PREFIX+'NTRUPlus768AcceptanceAlgebra.ec'
INPUT=PREFIX+'NTRUPlus768AcceptanceInput.ec'
COVER=PREFIX+'NTRUPlus768AcceptanceCover.ec'
HEAD=PREFIX+'NTRUPlus768AcceptanceHeadReduction.ec'
SLICES=PREFIX+'NTRUPlus768AcceptanceSlices.ec'
MASKS=PREFIX+'NTRUPlus768AcceptanceMasks.ec'
ROMBOUND=PREFIX+'NTRUPlus768AcceptanceROMBound.ec'
PROBABILITY=PREFIX+'NTRUPlus768AcceptanceProbability.ec'
BUDGET=PREFIX+'NTRUPlus768AcceptanceBudget.ec'
SHAPING='ntruplus/proof/768/ref/keygen_sampler/NTRUPlus768KeygenSamplerAlgebra.ec'
ACCEPT='ntruplus/proof/768/ref/keygen_complete/NTRUPlus768KeygenCompleteSpec.ec'
COLLISION='ntruplus/proof/768/ref/kem_stopped_rom/NTRUPlus768ProposalSwitch.ec'


def check_model(read,ordered,require):
    def has(code,token,label):
        require(''.join(token.split()) in code,label)
    roots=read(ROOTS)
    match=re.search(r'op(?:\[opaque\])?acceptance_roots:intlist=\[(.*?)\]\.',roots)
    require(match is not None,'concrete root certificate is missing')
    claimed=[int(x) for x in re.findall(r'-?\d+',match.group(1))]
    _,_,actual=certify_roots(inputs())
    require(claimed==actual,'root certificate differs from old actual signed terminal table')
    has(roots,'acceptance_euler_mod x = x^1728 %%3457','Euler certificate exponent and field modulus')
    has(roots,'all (fun r=>acceptance_euler_mod r=3456) acceptance_roots','all roots must be certified nonsquares')
    has(roots,'acceptance_root(2*k+1)=(-acceptance_root(2*k)) %%3457','roots must include both signs')
    root_square=roots.split('lemmaacceptance_root_square',1)[1].split('proof.',1)[0]
    has(root_square,'k (b:bool) : 0<=k<192 => (acceptance_root(2*k+b2i b)^2) %%3457=terminal_value k.','both signed roots must match actual terminal z')
    orbit=read(ORBIT)
    has(orbit,'Array192.init (fun i=>buf.[i] +^ mask.[i])','orbit transforms use full-byte XOR')
    has(orbit,'dmap uniform192 (uniform192_xor mask)=uniform192','orbit measure-preservation is proved for actual uniform192')
    declaration=orbit.split('lemmafinite_uniform_orbit_bound',1)[1].split('proof.',1)[0]
    has(declaration,'0<n =>','orbit division requires positive finite size')
    has(declaration,'(forall i, 0<=i<n => dmap uniform192 (transforms i)=uniform192) =>','orbit bound requires every transform to preserve the measure')
    has(declaration,'bad(transforms i buf) => bad(transforms j buf) => i=j','orbit bound requires pointwise disjoint translated events')
    has(declaration,'mu uniform192 bad<=1%r/n%r','orbit bound target must be inverse orbit size')
    declaration=orbit.split('lemmauniform192_acceptance_from_384_bad',1)[1].split('proof.',1)[0]
    has(declaration,'(forall i, 0<=i<384 => mu uniform192 (bad i)<=1%r/1024%r) =>','union requires all 384 root-event bounds')
    has(declaration,'(forall buf, !accept buf => indexed_event_union 384 bad buf) =>','union requires actual rejection to be covered')
    has(declaration,'5%r/8%r<=mu uniform192 accept','acceptance target must be five eighths')
    require('independent' not in declaration,'union bound must not assume independent roots')
    algebra=read(ALGEBRA)
    has(algebra,'forall (x:CycloFq.cyclocoeff), x*x<>r','nonsquare means no field square root')
    has(algebra,'op quadratic_modulus (r:CycloFq.cyclocoeff) : NTRUPoly.poly = NTRUPoly.PolyComRing.exp NTRUPoly.X 2-NTRUPoly.polyC r','quadratic factor must be X^2-r')
    has(algebra,'field_nonsquare r => a*a-r*(b*b)=CycloFq.zero => a=CycloFq.zero /\\ b=CycloFq.zero','norm-zero reasoning requires nonsquare coefficient')
    failed=algebra.split('lemmafailed_block_determinant',1)[1].split('proof.',1)[0]
    has(failed,'in_qrange768 a => 0<=k<192 => poly_block_status a k=W64.of_int 1 => inverse_determinant (block4 a k) (terminal_value k) %% q=0.','failed old word status must imply determinant zero at decoded terminal z')
    has(algebra,'zeta_decode(poly_block_zeta k)=terminal_value k','algebraic bridge must decode the actual Montgomery twiddle')
    has(algebra,'lift_int(inverse_determinant a z)=block_norm a r*block_norm a (-r)','quartic determinant must factor over both signed quadratic roots')
    for phase in ('f','g'):
        decl=algebra.split('lemmakeygen_'+phase+'_rejected_cover',1)[1].split('proof.',1)[0]
        has(decl,'!keygen_'+phase+'_accept buf => exists j,0<=j<384 /\\ quadratic_divides(roots j)(input_poly(keygen_'+phase+'_pre_ntt_spec buf)).','old '+phase+' inverse rejection must reach its actual input polynomial')
    budget=read(BUDGET)
    pair_budget=budget.split('lemmaacceptance_retry_pair_256',1)[1].split('proof.',1)[0]
    has(pair_budget,'5%r/8%r <= pf <= 1%r => 5%r/8%r <= pg <= 1%r =>','numeric retry helper needs both useful probability bounds')
    has(pair_budget,'(1%r-pf)^256+(1%r-pg)^256 <= 2%r/(2%r^256)','numeric retry helper includes both separate 256-attempt tails')
    has(budget,'proposal_delta a 512 = (512%r*a%r+130816%r)/(2%r^256)','birthday sum must count all 512 queries and prior cache')
    has(budget,'proposal_delta a 512 + ((1%r-pf)^256+(1%r-pg)^256) <= (512%r*a%r+130818%r)/(2%r^256)','numeric error retains collision and retry terms')
    has(budget,'130818%r/(2%r^256) < 1%r/(2%r^239)','empty-cache exact strict numerical comparison')
    shaping=read(SHAPING)
    shape_f=shaping.split('opkeygen_f_pre_ntt_spec',1)[1].split('opkeygen_g_pre_ntt_spec',1)[0]
    triple=shaping.split('oppoly_triple_spec',1)[1].split('opkeygen_f_pre_ntt_spec',1)[0]
    has(shape_f,'3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k + keygen_delta0 k','actual f rescaling and delta term')
    has(triple,'W16.of_int (3 * coeff p.[k])','actual g and common sampler rescaling')
    accept=read(ACCEPT)
    for phase in ('f','g'):
        has(accept,'op keygen_'+phase+'_accept (buf : W8.t Array192.t) = poly_blocks_succeed (keygen_'+phase+'_ntt_spec buf) 192','acceptance must use actual all-192-block inverse status: '+phase)
    has(read(COLLISION),'(ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256))','imported collision expression cannot reset between retry phases')
    for name,code in (('roots',roots),('orbit',orbit),('algebra',algebra),('budget',budget)):
        require('shake256' not in code.lower() and 'keygen_seed_expansion' not in code,'uniform-buffer theorem cannot substitute fixed SHAKE: '+name)

    input_model=read(INPUT)
    has(input_model,'if is_f then keygen_f_pre_ntt_spec buf else keygen_g_pre_ntt_spec buf','input model must retain actual f/g pre-NTT shaping')
    has(input_model,'op acceptance_input (is_f:bool) (buf:W8.t Array192.t) = input_poly (acceptance_shape is_f buf).','input model must use full actual coefficient polynomial')
    has(input_model,'op acceptance_same_tail (b c:W8.t Array192.t) = forall i, 2<=i<192 => b.[i]=c.[i].','slice context must fix every byte except the first two')
    has(input_model,'PCA.bigi predT (fun k=>polyC(lift_int(3*acceptance_head_bit buf k))*exp X k) 0 16.','head polynomial must preserve three-times CBD scaling and all sixteen head bits')
    has(input_model,'acceptance_same_tail b c => acceptance_input is_f b-acceptance_input is_f c= acceptance_head_poly b-acceptance_head_poly c.','full polynomial difference requires fixed remainder context')
    probability=read(PROBABILITY)
    has(probability,'op acceptance_bad (is_f:bool) (j:int) (buf:W8.t Array192.t) = quadratic_divides (lift_int(acceptance_root j)) (acceptance_input is_f buf).','root bad event must use actual shaped input and actual root')
    for phase,flag in (('f','true'),('g','false')):
        declaration=probability.split('lemmafresh_'+phase+'_accept_lower',1)[1].split('proof.',1)[0]
        require(declaration==':5%r/8%r<=fresh_'+phase+'_accept_mass.',
                'actual acceptance lower bound must be unconditional: '+phase)
        has(probability,'!keygen_'+phase+'_accept buf => indexed_event_union 384 (acceptance_bad '+flag+') buf.',
            'actual '+phase+' rejection must be covered by all quadratic events')
        has(probability,'apply(uniform192_acceptance_from_384_bad keygen_'+phase+'_accept (acceptance_bad '+flag+'))',
            'actual '+phase+' probability proof must instantiate the union bound')
    has(probability,'islossless Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run.','new unlimited losslessness theorem must use the ideal fresh expansion')
    require(not re.search(r'islossless(?:CountedKeygen|ResumedKeygen|KeygenInstrumented|Keygen)\([^)]*ExpandROM',probability),
            'positive ideal acceptance must not assert actual unlimited ROM losslessness')
    for name,code in (('input',input_model),('probability',probability)):
        require('shake256' not in code.lower() and 'keygen_seed_expansion' not in code,
                'acceptance family must not substitute fixed SHAKE: '+name)

    slices=read(SLICES)
    has(slices,r'op slice_exponents (rho:int) : int list = [0;1;2;3;if rho \in [252;974;2483;3205] then 5 else 4].','five-bit selection must handle all four exceptional roots')
    has(slices,'all (fun rho=>uniq(map(slice_weighted_sum rho)(iota_ 0 32))) acceptance_roots.','injectivity certificate covers all 384 roots and all 32 assignments')
    masks=read(MASKS)
    has(masks,'op acceptance_digit m p = if p=0 then m %% 32 else m %/ 32.','ten-bit masks must split into two distinct five-bit digits')
    has(masks,'op acceptance_mask_bit rho m k = if 0<=k<8 then slice_bit (acceptance_digit m (k %% 2)) (k %/ 2) else if k=2*acceptance_last rho then slice_bit (acceptance_digit m 0) 4 else if k=2*acceptance_last rho+1 then slice_bit (acceptance_digit m 1) 4 else false.','mask support must preserve parity and exceptional fifth positions')
    has(masks,'Array192.init (fun i=>if 0<=i<2 then W8.init(fun j=>acceptance_mask_bit rho m (8*i+j)) else W8.zero).','masks must touch only the first two bytes')
    has(masks,'op acceptance_position rho t p = 2*nth 0 (slice_exponents rho) t+p.','selected positions must use even/odd polynomial exponents')
    bound=read(ROMBOUND)
    declaration=bound.split('lemmacertified_keygen_public_distance_256',1)[1].split('proof.',1)[0]
    expected='&m a m0 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) : 0<=a => fsize m0<=a => ROE.m{m}=m0 => `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] - Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]| <= (512%r*a%r+130818%r)/(2%r^256).'
    require(declaration==''.join(expected.split()),'public numerical theorem must retain actual APIs and initial-cache assumptions, with no positivity hypothesis')
    empty=bound.split('lemmacertified_keygen_empty_cache_distance',1)[1].split('proof.',1)[0]
    expected='&m (event:W8.t Array1152.t * W8.t Array2336.t -> bool) : ROE.m{m}=empty => `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] - Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]| < 1%r/(2%r^239).'
    require(empty==''.join(expected.split()),'empty-cache bound must refer to actual public-KeyGen events, without new hidden assumptions')
    late=bound.split('lemmacertified_keygen_late_or_missing_256',1)[1].split('proof.',1)[0]
    has(late,'!counted_within 256 256 res] + (1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true])','late-return bound must also include nonreturning mass')
    require(not re.search(r'islossless(?:CountedKeygen|ResumedKeygen|KeygenInstrumented|Keygen)\([^)]*ExpandROM',bound),'numerical approximation must not assume actual unlimited-ROM losslessness')
    for name,code in (('slices',slices),('masks',masks),('final_bound',bound)):
        require('shake256' not in code.lower() and 'keygen_seed_expansion' not in code,
                'acceptance family must not substitute fixed SHAKE: '+name)

    cover=read(COVER)
    for phase in ('f','g'):
        decl=cover.split('lemmakeygen_'+phase+'_rejected_quadratic',1)[1].split('proof.',1)[0]
        expected='(buf:W8.t Array192.t) : !keygen_'+phase+'_accept buf => exists j,0<=j<384 /\\ quadratic_divides(lift_int(acceptance_root j))(input_poly(keygen_'+phase+'_pre_ntt_spec buf)).'
        require(decl==''.join(expected.split()),'concrete '+phase+' rejection cover must discharge root assumptions')
    has(cover,'apply field_euler_nonsquare; exact(acceptance_root_euler j hj)','field nonsquare must be derived from the concrete Euler certificate')
    head=read(HEAD)
    has(head,'NTRUPoly.polyC(lift_int 3*acceptance_weight8 r buf 0) + NTRUPoly.polyC(lift_int 3*acceptance_weight8 r buf 1)*NTRUPoly.X.','quadratic remainder must retain both rescaled parity components')
    equal=head.split('lemmaacceptance_head_divisors_equal',1)[1].split('proof.',1)[0]
    has(equal,'acceptance_same_tail b c =>','selected equality requires fixed full-byte remainder')
    has(equal,'(forall k,8<=k<16 => k<>2*nth 0 (slice_exponents rho) 4 => k<>2*nth 0 (slice_exponents rho) 4+1 => acceptance_head_bit b k=acceptance_head_bit c k) =>','selected equality requires all unselected head bits fixed')
    has(equal,'forall p,0<=p<2 => acceptance_selected_weight rho b p=acceptance_selected_weight rho c p.','selected equality must cover both even and odd slices')
