"""Boundary checks for actual bounded adapters and subdistribution transfer."""
PREFIX='ntruplus/proof/768/ref/kem_stopped_rom/'
BRIDGE=PREFIX+'NTRUPlus768ProposalKeygenBridge.ec'
GAMES=PREFIX+'NTRUPlus768StoppedROMGames.ec'
TRANSFER=PREFIX+'NTRUPlus768SubdistributionTransfer.ec'
PAIR_LAW=PREFIX+'NTRUPlus768FreshKeyPairLaw.ec'
BOUND=PREFIX+'NTRUPlus768StoppedROMBound.ec'
TOP_HEADER='lemma keygen_rom_fresh_distance &m qf0 qg0 ab m0 (event:keygen_output -> bool) :'
TOP_PREMISES='0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>'
TOP_POSITIVE='0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>'



def check_final_models(read, ordered, require):
    def has(code, token, label):
        require(''.join(token.split()) in code,label)
    bridge=read(BRIDGE)
    has(bridge, '''module StoppedKeygenContext(P:ProposalPort) = {
      var event:stopped_output -> bool
      proc run(qf:int,qg:int) : bool = {
        var result;
        result <@ StoppedKeygen(PairPorts(P),PairPorts(P)).run(qf,qg,witness);
        return event result;
      }
    }.''','proposal caller must invoke actual stopped KeyGen with the same shared ports')
    for oracle in ('ROM','Fresh'):
        decl=bridge.split('lemmastopped_'+oracle.lower()+'_proposal_bridge',1)[1].split('proof.',1)[0]
        has(decl,'StoppedKeygen(PairPorts('+oracle+'Proposal),PairPorts('+oracle+'Proposal)).run',
            'paired endpoint must use actual KeyGen: '+oracle)
        has(decl,oracle+'Proposal.n{2}=0 /\\ '+oracle+'Proposal.q{2}=qf{1}+qg{1}',
            'shared proposal budget must include all attempts of both phases: '+oracle)
        has(decl,'0<=qf{1} /\\ 0<=qg{1}', 'actual proposal bridge budget premises: '+oracle)
    decl=bridge.split('lemmastopped_rom_proposal_bridge',1)[1].split('proof.',1)[0]
    has(decl,'equiv[StoppedKeygen(UniformSeedRNG,ExpandROM).run ~', 'ROM endpoint must use real old cache adapter')
    has(decl,'==> ={res,glob ROE,glob ROF}]','ROM bridge preserves full result and E/F caches')
    for phase in ('f','g'):
        has(bridge,'call(keygen_attempt_'+phase+'_realized_equiv E)',
            'reference retry replacement must be proved from realized old attempt: '+phase)
    has(bridge,'ecall(result_rom_g_bridge fv.`rs_count{2} (qf{1}+qg{1}) qg{1})',
        'ROM g bridge must retain f count in shared proposal budget')
    has(bridge,'ecall(result_fresh_g_bridge fv.`rs_count{2} (qf{1}+qg{1}) qg{1})',
        'fresh g bridge must retain f count in shared proposal budget')
    games=read(GAMES)
    has(games,'''module DirectROMStopped = {
      proc run(qf:int,qg:int,m0:(W8.t Array32.t,W8.t Array192.t) fmap) : stopped_output = {
        var result; ROE.m <- m0;
        result <@ StoppedKeygen(UniformSeedRNG,ExpandROM).run(qf,qg,witness);
        return result;
      }
    }.''','direct stopped ROM must retain prior E cache and actual caller')
    has(games,'''module DirectFreshStopped = {
      proc run(qf:int,qg:int) : stopped_output = {
        var result; result <@ StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf,qg,witness);
        return result;
      }
    }.''','direct stopped fresh must use actual caller')
    require('ROF.init(' not in games and 'ROF.m<-' not in games,
            'direct stopped games must retain current F table')
    for oracle in ('ROM','Fresh'):
        has(games,'StoppedKeygenContext.event <- event; result <@ '+oracle+
            'ProposalExperiment(StoppedKeygenContext).run(qf,qg,qf+qg,m0); return result;',
            'configured event must cover both phase budgets: '+oracle)
    distance=games.split('lemmastopped_rom_fresh_distance',1)[1].split('proof.',1)[0]
    has(distance,'0<=qf => 0<=qg => 0<=ab => fsize m0<=ab =>','actual distance retains prior/cache/budget premises')
    has(distance,'`|Pr[DirectROMStopped.run(qf,qg,m0) @ &mem : event res] - Pr[DirectFreshStopped.run(qf,qg) @ &mem : event res]| <= proposal_delta ab (qf+qg)',
        'actual stopped distance must cover every result event and all attempts')
    transfer=read(TRANSFER)
    has(transfer,'x+xc <= 1%r => y+yc=1%r =>',
        'actual events must remain a subdistribution; only ideal is total')
    has(transfer,'y-epsilon <= x => yc-epsilon <= xc => `|x-y| <= epsilon',
        'bidirectional event bound must use event and complement lower bounds')
    has(transfer,'mass<=1%r => good<=mass => 1%r-epsilon<=good => 0%r<=1%r-mass<=epsilon',
        'missing mass must be bounded from below by stopped good mass')
    for name,code in (('bridge',bridge),('games',games),('transfer',transfer)):
        require('shake256' not in code.lower() and 'keygen_seed_expansion' not in code,
                'fixed SHAKE must not replace the actual ROM/fresh boundary: '+name)

    bound=read(BOUND)
    declaration=bound.split('lemmakeygen_rom_fresh_distance',1)[1].split('proof.',1)[0]
    has(declaration,TOP_PREMISES,'final actual theorem retains nonnegative budgets and initial E cache premise')
    has(declaration,TOP_POSITIVE,'final ideal unlimited comparison retains both positive acceptance premises')
    has(declaration, '`|Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : event res] - Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(witness) @ &m : event res]| <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0',
        'final delta plus tail applies to unchanged actual KeyGen and ideal fresh KeyGen')
    require('islossless' not in declaration,'final actual theorem cannot assume unlimited ROM losslessness')
    missing=bound.split('lemmakeygen_rom_missing_mass',1)[1].split('proof.',1)[0]
    has(missing,'0%r <= 1%r-Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : true] <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0',
        'missing mass bound must refer to actual old unlimited KeyGen')
    late=bound.split('lemmarom_counted_late_or_divergent',1)[1].split('proof.',1)[0]
    has(late,'Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : !counted_within qf0 qg0 res] + (1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true])',
        'late return event must include separate nonreturning mass')
    require('shake256' not in bound.lower() and 'keygen_seed_expansion' not in bound,
            'final bound must not substitute deterministic SHAKE')
    import re
    require(not re.search(r'islossless(?:CountedKeygen|ResumedKeygen|KeygenInstrumented|Keygen)\([^)]*ExpandROM',bound),
            'no unlimited real-ROM termination premise in final proof family')

    public=bound.split('lemmakeygen_public_rom_fresh_distance',1)[1].split('proof.',1)[0]
    has(public,TOP_PREMISES,'public actual theorem retains initial cache and budget premises')
    has(public,TOP_POSITIVE,'public ideal comparison retains both positivity premises')
    has(public,'`|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] - Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]| <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0',
        'public theorem must measure actual pk/sk return events with delta plus tail')
    projection=bound.split('lemmakeygen_public_instrumented_probability',1)[1].split('proof.',1)[0]
    has(projection,'Pr[Keygen(UniformSeedRNG,E,SHAKEFROM).run() @ &m : event res] = Pr[KeygenInstrumented(UniformSeedRNG,E,SHAKEFROM).run(witness) @ &m : event (res.`1.`kg_pk,res.`1.`kg_sk)]',
        'public projection retains actual public and secret key outputs')

    expected_instrumented = (
        '&m qf0 qg0 ab m0 (event:keygen_output -> bool) :' + TOP_PREMISES + TOP_POSITIVE +
        '`|Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : event res] - '
        'Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(witness) @ &m : event res]| '
        '<= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.')
    expected_public = (
        '&m qf0 qg0 ab m0 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :' + TOP_PREMISES + TOP_POSITIVE +
        '`|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] - '
        'Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]| '
        '<= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.')
    require(declaration==''.join(expected_instrumented.split()),
            'final actual theorem must have exactly the reviewed premises and conclusion')
    require(public==''.join(expected_public.split()),
            'public theorem must have exactly the reviewed premises and conclusion')

    pair_law=read(PAIR_LAW)
    has(pair_law,'op fresh_accepted_pair_law = ((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept)).',
        'accepted f/g independence is the product of two whole-buffer conditioned laws')
    has(pair_law,'call{1} keygen_clear_lossless. call{1}(keygen_finish_lossless SHAKEFROM ro_f_shake_ll). call fresh_retry_g_direct_buffer. call fresh_retry_f_direct_buffer.',
        'accepted pair law must retain actual f/g retries, finish and clear')
    pair_declaration=pair_law.split('lemmafresh_keygen_buffer_pair_probability',1)[1].split('proof.',1)[0]
    has(pair_declaration,'Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(workspace) @ &m : event(res.`1.`kg_fbuf,res.`1.`kg_gbuf)] = mu (((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))) event.',
        'joint law must apply to the actual returned f and g buffers and arbitrary events')
    require('shake256' not in pair_law.lower() and 'keygen_seed_expansion' not in pair_law,
            'fresh joint law must not substitute fixed SHAKE')
