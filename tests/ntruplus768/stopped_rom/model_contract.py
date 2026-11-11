"""Source boundary controls, separate from the EasyCrypt proof checks."""
import re

PREFIX = 'ntruplus/proof/768/ref/kem_stopped_rom/'
MODEL = PREFIX + 'NTRUPlus768StoppedKeygenModel.ec'
PAIR = PREFIX + 'NTRUPlus768ProposalModel.ec'
SWITCH = PREFIX + 'NTRUPlus768ProposalSwitch.ec'
ATTEMPT = PREFIX + 'NTRUPlus768AttemptRealized.ec'
BUFFER = PREFIX + 'NTRUPlus768BufferRejection.ec'
BOUNDED = PREFIX + 'NTRUPlus768BoundedBufferRejection.ec'
FRESH_BOUNDED = PREFIX + 'NTRUPlus768FreshBoundedLaw.ec'
FRESH = PREFIX + 'NTRUPlus768FreshRetryLaw.ec'
PREFIX_PROOF = PREFIX + 'NTRUPlus768StoppedKeygenPrefix.ec'
ORACLE = 'ntruplus/proof/768/ref/kem_rom_oracle/NTRUPlus768ROMOracles.ec'


def check_model(read, ordered, require):
    def has(code, token, label):
        require(''.join(token.split()) in code, label)

    pair = read(PAIR)
    has(pair, 'module type ProposalPort = { proc draw() : W8.t Array32.t * W8.t Array192.t }.',
        'proposal capability must expose draw only')
    has(pair, '''module PairPorts(P:ProposalPort) = {
      var pending : W8.t Array192.t
      proc sample() : W8.t Array32.t = {
        var v:W8.t Array32.t * W8.t Array192.t;
        v <@ P.draw(); pending <- v.`2; return v.`1;
      }
      proc shake(seed:W8.t Array32.t) : W8.t Array192.t = { return pending; }
    }.''', 'shared pending adapter must neither redraw nor recompute expansion')

    model = read(MODEL)
    has(model, '{|rs_buf=witness;rs_ntt=witness;rs_inv=witness;rs_ok=false;rs_count=0|}',
        'initial retry state must not accept and has count zero')
    has(model, 'r.`1 <> None /\\ event (oget r.`1)', 'stopped event must exclude exhausted runs')
    has(model, 'r.`2 <= max 0 qf /\\ r.`3 <= max 0 qg', 'budget event must count f and g separately')
    for family, guard in (('Bounded', 'status <> W64.zero /\\ count < max 0 limit'),
                          ('Counted', 'status <> W64.zero')):
        body = model.split('module'+family+'Retry(', 1)[1].split('}.', 1)[0]
        for phase in ('f', 'g'):
            fragment = body.split('proc'+phase+'_from(', 1)[1].split('return', 1)[0]
            has(fragment, '''buf <- start.`rs_buf; ntt <- start.`rs_ntt; inverse <- start.`rs_inv;
              status <- if start.`rs_ok then W64.zero else W64.one; count <- start.`rs_count;''',
                family+' '+phase+' must resume full prior state')
            has(fragment, 'while ('+guard+') { seed <@ R.sample(); '
                '(buf,ntt,inverse,status) <@ KeygenAttempt(E).'+phase+'(seed); count <- count+1; }',
                family+' '+phase+' must call actual old attempt once per counted draw')
            require(fragment.count('<@') == 2, 'extra or missing retry call: '+family+'/'+phase)
            require('<$' not in fragment, 'retry must use the supplied actual RNG and expansion')
    for forbidden in ('ROE.init(', 'ROF.init(', 'ROE.m<-', 'ROF.m<-'):
        require(forbidden not in model, 'actual phases must preserve shared oracle tables')
    has(model, '''module StoppedKeygen(R:KeygenSeedRNG,E:KeygenExpand) = {
      proc run(qf:int,qg:int,workspace:W8.t Array14466.t) : stopped_output = {
        var fv,gv:retry_state; var result:keygen_output option; var out:keygen_output;
        result <- None; gv <- retry_initial;
        fv <@ BoundedRetry(R,E).f(qf);
        if (fv.`rs_ok) { gv <@ BoundedRetry(R,E).g(qg);
          if (gv.`rs_ok) { out <@ ObservedFinish.run(fv,gv,workspace); result <- Some out; }
        }
        return(result,fv.`rs_count,gv.`rs_count);
      }
    }.''', 'stopped phases must preserve accepted f and finish only after both accepts')
    has(model, '''fv <@ CountedRetry(R,E).f(); gv <@ CountedRetry(R,E).g();
      out <@ ObservedFinish.run(fv,gv,workspace); return(out,fv.`rs_count,gv.`rs_count);''',
        'unlimited observer must use actual uncapped loops and both counts')
    ordered(model, ('(pk,sk,h,hinv) <@ KeygenFinish(SHAKEFROM).run(fv.`rs_ntt,fv.`rs_inv,gv.`rs_ntt,gv.`rs_inv);',
        'workspace <@ NTRUPlus768KeygenClear.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_clear(workspace);',
        'return ({|kg_pk=pk;kg_sk=sk;kg_fbuf=fv.`rs_buf;kg_gbuf=gv.`rs_buf;'))

    switch = read(SWITCH)
    has(switch, 'module type ProposalContext(P:ProposalPort) = { proc run(qf:int,qg:int) : bool }.',
        'adversarial caller must access only capped draw')
    rom = switch.split('moduleROMProposal={', 1)[1].split('moduleFreshProposal=', 1)[0]
    fresh = switch.split('moduleFreshProposal={', 1)[1].split('moduleROMProposalExperiment', 1)[0]
    for name, code, table in (('ROM', rom, 'ROE.m'), ('Fresh', fresh, 'm')):
        has(code, f'n <- 0; q <- q0; bad <- false; {table} <- m0;', name+' must retain provided prior table')
        ordered(code, ('x <- witness; y <- witness;', 'if (n < q) {', 'x <$ uniform32;',
            'bad <- bad \\/ x \\in '+table+';', 'n <- n+1;', 'return (x,y);'))
        require(code.count('if(') == 1, name+' must have exactly one cap gate')
    has(rom, 'bad <- bad \\/ x \\in ROE.m; y <@ ROE.get(x); n <- n+1;',
        'real ROM must call existing lazy cache without fresh-on-hit overwrite')
    require(rom.count('<$') == 1 and rom.count('<@') == 1, 'real ROM must sample seeds only directly')
    has(fresh, 'bad <- bad \\/ x \\in m; y <$ uniform192; m.[x] <- y; n <- n+1;',
        'fresh proposal must draw full independent buffer even on repeat')
    require(fresh.count('<$') == 2 and '<@' not in fresh, 'fresh proposal draws exactly seed and buffer')
    has(switch, '(ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256))',
        'birthday delta must include prior size and triangle over full seed domain')
    for theorem in ('fresh_proposal_birthday',):
        decl = switch.split('lemma'+theorem, 1)[1].split('proof.', 1)[0]
        has(decl, '(A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE})',
            'caller must not change cap, tables or bad: '+theorem)
        has(decl, '0<=qb => 0<=ab => fsize m0<=ab =>', 'birthday requires prior table bound')
    for name in ('rom_proposal_cap','fresh_proposal_cap'):
        decl=switch.split('lemma'+name,1)[1].split('proof.',1)[0]
        has(decl, 'q0<=n0 ==> res=(witness,witness)', 'capped draw must return without further draws')
    distance = switch.split('lemmaproposal_switch_distance',1)[1].split('proof.',1)[0]
    has(distance, '(forall (P <: ProposalPort {-A}), islossless P.draw => islossless A(P).run) =>',
        'distance across bad requires termination of the bounded context')
    has(distance, '0<=qb => 0<=ab => fsize m0<=ab =>', 'proposal distance retains budget and prior cache premise')
    has(distance, '`|Pr[ROMProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res] - Pr[FreshProposalExperiment(A).run(qf,qg,qb,m0) @ &mem : res]| <= proposal_delta ab qb',
        'proposal distance measures the unnormalized actual result event')
    oracle = read(ORACLE)
    has(oracle, '''module ROE : ROEPort = { var m : (W8.t Array32.t,W8.t Array192.t) fmap
      proc init() = { m <- empty; }
      proc get(input:W8.t Array32.t) : W8.t Array192.t = {
        var r; if (input \\notin m) { r <$ uniform192; m.[input] <- r; }
        return oget m.[input];
      }
    }.''', 'imported real cache must never overwrite on hit')

    attempt = read(ATTEMPT)
    for phase in ('f','g'):
        has(attempt, 'equiv [KeygenAttempt(E).'+phase+' ~ AttemptResult(E).'+phase+
            ' : ={seed,glob E} ==> ={res,glob E}]', 'realized attempt preserves actual output and expansion state')
        has(attempt, 'hoare [KeygenAttempt(E).'+phase+' : true ==> res=keygen_'+phase+'_attempt_result res.`1].',
            'actual attempt law must refer to realized buffer')
    buffer = read(BUFFER)
    has(buffer, 'is_lossless d0 => 0%r < mu d0 accept0 =>', 'ideal unlimited losslessness needs positive acceptance')
    has(buffer, 'mu d (fun buffer => accept buffer /\\ event buffer) / mu d accept',
        'accepted whole-buffer conditional law must retain dependencies')
    bounded = read(BOUNDED)
    has(bounded, 'while (count < q /\\ !success) { buffer <$ d; success <- accept buffer; count <- count + 1; }',
        'finite rejection must stop at zero budget and preserve first success')
    bounded_tail = bounded.split('lemmabounded_buffer_rejection_tail',1)[1].split('proof.',1)[0]
    has(bounded_tail, 'is_lossless d0 => 0<=q0 =>', 'finite tail requires lossless source and nonnegative count')
    has(bounded_tail, '(1%r-mu d0 accept0)^q0', 'finite rejection tail must include all q rejections')
    fresh = read(FRESH)
    has(fresh, 'op fresh_f_accept_mass = mu uniform192 keygen_f_accept.', 'fresh f acceptance uses actual predicate')
    has(fresh, 'op fresh_g_accept_mass = mu uniform192 keygen_g_accept.', 'fresh g acceptance uses actual predicate')
    has(fresh, '(1%r-fresh_f_accept_mass)^qf + (1%r-fresh_g_accept_mass)^qg',
        'fresh retry tail retains both separate budgets')
    for phase in ('f','g'):
        decl = fresh.split('lemmafresh_retry_'+phase+'_ll',1)[1].split('proof.',1)[0]
        has(decl, '0%r < fresh_'+phase+'_accept_mass => islossless KeygenRetry(UniformSeedRNG,FreshExpand).'+phase,
            'unlimited ideal retry requires its own positive acceptance: '+phase)
    for phase in ('f','g'):
        decl = fresh.split('lemmafresh_retry_'+phase+'_buffer_law',1)[1].split('proof.',1)[0]
        has(decl, 'phoare[KeygenRetry(UniformSeedRNG,FreshExpand).'+phase+' : true ==> event res.`1] = (mu (dcond uniform192 keygen_'+phase+'_accept) event)',
            'actual accepted buffer follows full-buffer conditional law: '+phase)
    fresh_bounded = read(FRESH_BOUNDED)
    for phase in ('f','g'):
        decl = fresh_bounded.split('lemmafresh_bounded_'+phase+'_tail',1)[1].split('proof.',1)[0]
        has(decl, '0<=q0 => phoare[BoundedRetry(UniformSeedRNG,FreshExpand).'+phase+' : limit=q0 ==> !res.`rs_ok] = ((1%r-fresh_'+phase+'_accept_mass)^q0)',
            'actual finite fresh tail preserves phase acceptance and full budget: '+phase)
        require('0%r<' not in decl, 'finite tail must not require positive acceptance')
    has(fresh_bounded, 'Pr[StoppedKeygen(UniformSeedRNG,FreshExpand).run(qf0,qg0,workspace0) @ &m : !stopped_success res] <= fresh_retry_tail qf0 qg0',
        'fresh exhaustion bound must apply to the actual stopped KeyGen result')
    prefix = read(PREFIX_PROOF)
    resume = prefix.split('lemmaresumed_prefix_upto',1)[1].split('proof.',1)[0]
    has(resume, 'Pr[ResumedKeygen(R,E).run(qf,qg,w) @ &m : event res.`1 /\\ !PrefixBad.bad] = Pr[PrefixOnlyKeygen(R,E).run(qf,qg,w) @ &m : event res.`1 /\\ !PrefixBad.bad]',
        'prefix comparison must use unnormalized same returned event before bad')
    require('islossless' not in resume, 'prefix comparison must not assume unlimited termination')
    declaration = prefix.split('lemmacounted_stopped_prefix_nonnegative',1)[1].split('proof.',1)[0]
    has(declaration, '(R<:KeygenSeedRNG {-ROF,-PrefixBad}) (E<:KeygenExpand {-ROF,-PrefixBad,-R})',
        'prefix theorem retains RNG/expansion/cache state boundaries')
    has(declaration, '0<=qf0 => 0<=qg0 => islossless R.sample => islossless E.shake =>',
        'prefix theorem requires only per-call losslessness and finite budget premises')
    has(declaration, 'Pr[CountedKeygen(R,E).run(w) @ &m : (res.`2<=qf0 /\\ res.`3<=qg0) /\\ event res.`1] = Pr[StoppedKeygen(R,E).run(qf0,qg0,w) @ &m : res.`1<>None /\\ event (oget res.`1)]',
        'prefix equality must retain both counts and actual stopped event')
    require(declaration.count('islossless') == 2, 'prefix equality cannot assume unlimited losslessness')
    for phase in ('f','g'):
        has(prefix, 'lemma counted_'+phase+'_erasure', 'both counted phases require old-loop erasure')
    for name, code in (('model',model), ('pair',pair), ('switch',switch), ('attempt',attempt),
                        ('fresh',fresh), ('fresh_bounded',fresh_bounded), ('prefix',prefix), ('buffer',buffer), ('bounded',bounded)):
        require('shake256' not in code.lower() and 'keygen_seed_expansion' not in code,
                'fixed SHAKE cannot replace the ROM/fresh expansion: '+name)
        require(not re.search(r'islossless(?:CountedKeygen|ResumedKeygen|Keygen)\([^)]*ExpandROM', code),
                'unlimited real-ROM losslessness must not be assumed: '+name)

    from final_contract import check_final_models
    check_final_models(read, ordered, require)
