#!/usr/bin/env python3
"""Mutations of independent semantic/source guards and EOF diagnostic regressions."""
import json
import sys
sys.dont_write_bytecode = True
import check_stopped_rom as policy
import eof_sentinels as eof
from model_contract import MODEL, PAIR, SWITCH, ATTEMPT, BUFFER, BOUNDED, FRESH, FRESH_BOUNDED, PREFIX_PROOF, ORACLE
from final_contract import BRIDGE, GAMES, TRANSFER, BOUND, TOP_HEADER, TOP_PREMISES, TOP_POSITIVE, PAIR_LAW
from verify_stopped_rom import check_negative_diagnostic, check_sentinel

MUTATIONS = (
    ('g-rejected-attempt-not-counted',MODEL,'KeygenAttempt(E).g(seed); count <- count+1;','KeygenAttempt(E).g(seed); if(status=W64.zero){count <- count+1;}'),
    ('ideal-f-positive-mass-omitted',FRESH,'0%r < fresh_f_accept_mass => islossless KeygenRetry(UniformSeedRNG,FreshExpand).f','islossless KeygenRetry(UniformSeedRNG,FreshExpand).f'),
    ('ideal-g-positive-mass-omitted',FRESH,'0%r < fresh_g_accept_mass => islossless KeygenRetry(UniformSeedRNG,FreshExpand).g','islossless KeygenRetry(UniformSeedRNG,FreshExpand).g'),
    ('unlimited-loop-capped',MODEL,'while (status <> W64.zero) {','while (status <> W64.zero /\\ count<1) {'),
    ('prefix-good-event-omitted',PREFIX_PROOF,'event res.`1 /\\ !PrefixBad.bad','event res.`1'),
    ('prefix-termination-assumed',PREFIX_PROOF,'(event:keygen_output -> bool) &m :','(event:keygen_output -> bool) &m : islossless ResumedKeygen(R,E).run =>'),
    ('distance-bounded-context-LL-omitted',SWITCH,'lemma proposal_switch_distance (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE}) &mem qf qg qb ab m0 : (forall (P <: ProposalPort {-A}), islossless P.draw => islossless A(P).run) =>','lemma proposal_switch_distance (A <: ProposalContext {-FreshProposal,-ROMProposal,-ROE}) &mem qf qg qb ab m0 :'),
    ('distance-bound-zeroed',SWITCH,'res]| <= proposal_delta ab qb','res]| <= 0%r'),
    ('prefix-final-f-count-omitted',PREFIX_PROOF,'(res.`2<=qf0 /\\ res.`3<=qg0) /\\ event res.`1','res.`3<=qg0 /\\ event res.`1'),
    ('prefix-final-g-count-omitted',PREFIX_PROOF,'(res.`2<=qf0 /\\ res.`3<=qg0) /\\ event res.`1','res.`2<=qf0 /\\ event res.`1'),
    ('prefix-final-failure-included',PREFIX_PROOF,'res.`1<>None /\\ event (oget res.`1)','event (oget res.`1)'),
    ('fresh-actual-f-tail-shifted',FRESH_BOUNDED,'((1%r-fresh_f_accept_mass)^q0)','((1%r-fresh_f_accept_mass)^(q0+1))'),
    ('fresh-actual-g-tail-shifted',FRESH_BOUNDED,'((1%r-fresh_g_accept_mass)^q0)','((1%r-fresh_g_accept_mass)^(q0+1))'),
    ('fresh-actual-abort-event-negated',FRESH_BOUNDED,'!stopped_success res] <= fresh_retry_tail','stopped_success res] <= fresh_retry_tail'),
    ('actual-proposal-caller-substituted',BRIDGE,'StoppedKeygen(PairPorts(P),PairPorts(P)).run(qf,qg,witness)','ReferenceKeygen(P).run(qf,qg,witness)'),
    ('ROM-g-counter-reset',BRIDGE,'ecall(result_rom_g_bridge fv.`rs_count{2}','ecall(result_rom_g_bridge 0'),
    ('fresh-g-counter-reset',BRIDGE,'ecall(result_fresh_g_bridge fv.`rs_count{2}','ecall(result_fresh_g_bridge 0'),
    ('direct-game-loses-prior-E-table',GAMES,'ROE.m <- m0','ROE.m <- empty'),
    ('direct-game-clears-F-table',GAMES,'ROE.m <- m0;','ROE.m <- m0; ROF.init();'),
    ('configured-ROM-omits-g-budget',GAMES,'ROMProposalExperiment(StoppedKeygenContext).run(qf,qg,qf+qg,m0)','ROMProposalExperiment(StoppedKeygenContext).run(qf,qg,qf,m0)'),
    ('configured-fresh-omits-f-budget',GAMES,'FreshProposalExperiment(StoppedKeygenContext).run(qf,qg,qf+qg,m0)','FreshProposalExperiment(StoppedKeygenContext).run(qf,qg,qg,m0)'),
    ('transfer-assumes-real-total',TRANSFER,'x+xc <= 1%r','x+xc = 1%r'),
    ('transfer-forgets-ideal-total',TRANSFER,'y+yc=1%r','y+yc<=1%r'),
    ('transfer-omits-complement-bound',TRANSFER,'yc-epsilon <= xc =>',''),
    ('transfer-forgets-nonreturn-mass',TRANSFER,'0%r<=1%r-mass<=epsilon','0%r<=epsilon'),
    ('fresh-f-conditioning-omitted',FRESH,'lemma fresh_retry_f_buffer_law (event:W8.t Array192.t -> bool) : phoare[KeygenRetry(UniformSeedRNG,FreshExpand).f : true ==> event res.`1] = (mu (dcond uniform192 keygen_f_accept) event)','lemma fresh_retry_f_buffer_law (event:W8.t Array192.t -> bool) : phoare[KeygenRetry(UniformSeedRNG,FreshExpand).f : true ==> event res.`1] = (mu uniform192 event)'),
    ('fresh-g-conditioning-wrong-predicate',FRESH,'lemma fresh_retry_g_buffer_law (event:W8.t Array192.t -> bool) : phoare[KeygenRetry(UniformSeedRNG,FreshExpand).g : true ==> event res.`1] = (mu (dcond uniform192 keygen_g_accept) event)','lemma fresh_retry_g_buffer_law (event:W8.t Array192.t -> bool) : phoare[KeygenRetry(UniformSeedRNG,FreshExpand).g : true ==> event res.`1] = (mu (dcond uniform192 keygen_f_accept) event)'),
    ('final-prior-table-premise-omitted',BOUND,TOP_HEADER+TOP_PREMISES,TOP_HEADER+'0<=qf0 => 0<=qg0 => 0<=ab => ROE.m{m}=m0 =>'),
    ('final-initial-cache-premise-omitted',BOUND,TOP_HEADER+TOP_PREMISES,TOP_HEADER+'0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab =>'),
    ('final-ideal-f-positivity-omitted',BOUND,TOP_HEADER+TOP_PREMISES+TOP_POSITIVE,TOP_HEADER+TOP_PREMISES+'0%r<fresh_g_accept_mass =>'),
    ('final-ideal-g-positivity-omitted',BOUND,TOP_HEADER+TOP_PREMISES+TOP_POSITIVE,TOP_HEADER+TOP_PREMISES+'0%r<fresh_f_accept_mass =>'),
    ('final-assumes-unlimited-ROM-LL',BOUND,TOP_HEADER,TOP_HEADER+'islossless KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run =>'),
    ('final-tail-of-nonreturn-omitted',BOUND,'!counted_within qf0 qg0 res] + (1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true])','!counted_within qf0 qg0 res] + 0%r'),
    ('public-key-output-substituted',BOUND,'event (res.`1.`kg_pk,res.`1.`kg_sk)','event (witness,res.`1.`kg_sk)'),
    ('public-secret-key-output-substituted',BOUND,'event (res.`1.`kg_pk,res.`1.`kg_sk)','event (res.`1.`kg_pk,witness)'),
    ('public-actual-ROM-substituted',BOUND,'Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run()','Pr[ReferenceKeygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run()'),
    ('public-fresh-ideal-substituted',BOUND,'Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run()','Pr[ReferenceKeygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run()'),
    ('final-hidden-total-return-premise',BOUND,TOP_HEADER,TOP_HEADER+'Pr[KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness) @ &m : true]=1%r =>'),
    ('pair-law-f-conditioning-omitted',PAIR_LAW,'op fresh_accepted_pair_law = ((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))','op fresh_accepted_pair_law = (uniform192 `*` (dcond uniform192 keygen_g_accept))'),
    ('pair-law-g-conditioning-omitted',PAIR_LAW,'op fresh_accepted_pair_law = ((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))','op fresh_accepted_pair_law = ((dcond uniform192 keygen_f_accept) `*` uniform192)'),
    ('pair-law-actual-finish-skipped',PAIR_LAW,'call{1}(keygen_finish_lossless SHAKEFROM ro_f_shake_ll).',''),
    ('pair-law-actual-clear-skipped',PAIR_LAW,'call{1} keygen_clear_lossless.',''),
    ('initial-count-wrong',MODEL,'rs_ok=false;rs_count=0','rs_ok=false;rs_count=1'),
    ('initial-success-forged',MODEL,'rs_ok=false;rs_count=0','rs_ok=true;rs_count=0'),
    ('f-budget-omitted',MODEL,'r.`2 <= max 0 qf /\\ r.`3 <= max 0 qg','true /\\ r.`3 <= max 0 qg'),
    ('g-budget-omitted',MODEL,'r.`2 <= max 0 qf /\\ r.`3 <= max 0 qg','r.`2 <= max 0 qf /\\ true'),
    ('negative-budget-not-clamped',MODEL,'count < max 0 limit','count < limit'),
    ('zero-budget-extra-draw',MODEL,'count < max 0 limit','count <= max 0 limit'),
    ('f-attempt-substituted-spec',MODEL,'KeygenAttempt(E).f(seed)','KeygenAttemptSpec(E).f(seed)'),
    ('g-attempt-substituted-spec',MODEL,'KeygenAttempt(E).g(seed)','KeygenAttemptSpec(E).g(seed)'),
    ('f-rejected-attempt-not-counted',MODEL,'count <- count+1','if(status=W64.zero){count <- count+1;}'),
    ('resume-count-reset',MODEL,'count <- start.`rs_count','count <- 0'),
    ('resume-buffer-reset',MODEL,'buf <- start.`rs_buf','buf <- witness'),
    ('stopped-g-restarts-f',MODEL,'gv <@ BoundedRetry(R,E).g(qg);','fv <@ BoundedRetry(R,E).f(qf); gv <@ BoundedRetry(R,E).g(qg);'),
    ('stopped-g-wrong-budget',MODEL,'gv <@ BoundedRetry(R,E).g(qg);','gv <@ BoundedRetry(R,E).g(qf);'),
    ('stopped-f-budget-swapped',MODEL,'fv <@ BoundedRetry(R,E).f(qf);','fv <@ BoundedRetry(R,E).f(qg);'),
    ('finish-before-g-accepted',MODEL,'if (gv.`rs_ok) {','if (true) {'),
    ('finish-substituted-reference',MODEL,'KeygenFinish(SHAKEFROM).run','ReferenceFinish.run'),
    ('workspace-clear-substituted',MODEL,'NTRUPlus768KeygenClear.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_clear(workspace)','ClearReference.run(workspace)'),
    ('cache-reset-between-phases',MODEL,'gv <@ BoundedRetry(R,E).g(qg);','ROE.init(); gv <@ BoundedRetry(R,E).g(qg);'),
    ('exhaustion-counted-as-event',MODEL,'r.`1 <> None /\\ event (oget r.`1)','event (oget r.`1)'),
    ('counted-g-skipped',MODEL,'gv <@ CountedRetry(R,E).g();','gv <- retry_initial;'),
    ('counted-f-skipped',MODEL,'fv <@ CountedRetry(R,E).f();','fv <- retry_initial;'),
    ('proposal-fresh-on-expand',PAIR,'return pending;','pending <$ uniform192; return pending;'),
    ('proposal-loses-pending',PAIR,'pending <- v.`2','pending <- witness'),
    ('proposal-seed-detached',PAIR,'return v.`1','return witness'),
    ('proposal-extra-capability',PAIR,'proc draw() : W8.t Array32.t * W8.t Array192.t','proc init():unit proc draw() : W8.t Array32.t * W8.t Array192.t'),
    ('real-prior-cache-discarded',SWITCH,'ROE.m <- m0','ROE.m <- empty'),
    ('real-hit-overwrites-cache',SWITCH,'y <@ ROE.get(x);','y <$ uniform192; ROE.m.[x] <- y;'),
    ('real-cap-off-by-one',SWITCH,'if (n < q)','if (n <= q)'),
    ('real-bad-nonmonotone',SWITCH,'bad <- bad \\/ x \\in ROE.m','bad <- x \\in ROE.m'),
    ('real-count-omitted',SWITCH,'n <- n+1;',''),
    ('fresh-not-full-buffer',SWITCH,'y <$ uniform192','y <$ uniform96'),
    ('fresh-cache-discarded',SWITCH,'bad <- false; m <- m0','bad <- false; m <- empty'),
    ('fresh-does-not-store-query',SWITCH,'m.[x] <- y;',''),
    ('caller-can-mutate-real-cache',SWITCH,'ProposalContext {-FreshProposal,-ROMProposal,-ROE}','ProposalContext {-FreshProposal,-ROMProposal}'),
    ('prior-table-bound-omitted',SWITCH,'0<=qb => 0<=ab => fsize m0<=ab =>','0<=qb => 0<=ab =>'),
    ('birthday-initial-query-term-omitted',SWITCH,'(ab*qb)%r/(2%r^256) +',''),
    ('birthday-triangle-off-by-one',SWITCH,'(qb*(qb-1))%r','(qb*(qb-2))%r'),
    ('birthday-seed-width-shortened',SWITCH,'2%r^256','2%r^128'),
    ('imported-ROM-hit-redraws',ORACLE,'if (input \\notin m)','if (true)'),
    ('realized-f-law-uses-fixed-buffer',ATTEMPT,'res=keygen_f_attempt_result res.`1','res=keygen_f_attempt_result witness'),
    ('realized-g-law-uses-fixed-buffer',ATTEMPT,'res=keygen_g_attempt_result res.`1','res=keygen_g_attempt_result witness'),
    ('realized-f-state-forgotten',ATTEMPT,'={seed,glob E} ==> ={res,glob E}','={seed,glob E} ==> ={res}'),
    ('ideal-positivity-omitted',BUFFER,'is_lossless d0 => 0%r < mu d0 accept0 =>','is_lossless d0 =>'),
    ('ideal-conditional-normalizer-omitted',BUFFER,'/ mu d accept',''),
    ('finite-rejection-extra-zero-draw',BOUNDED,'count < q /\\ !success','count <= q /\\ !success'),
    ('finite-rejection-keeps-drawing-after-accept',BOUNDED,'count < q /\\ !success','count < q'),
    ('finite-rejection-tail-off-by-one',BOUNDED,'(1%r-mu d0 accept0)^q0','(1%r-mu d0 accept0)^(q0+1)'),
    ('fresh-f-mass-fixed-SHAKE',FRESH,'mu uniform192 keygen_f_accept','mu uniform192 (fun b=>keygen_f_accept(keygen_seed_expansion witness))'),
    ('fresh-g-mass-wrong-predicate',FRESH,'mu uniform192 keygen_g_accept','mu uniform192 keygen_f_accept'),
    ('fresh-g-tail-omitted',FRESH,'+ (1%r-fresh_g_accept_mass)^qg',''),
    ('old-g-erasure-omitted',PREFIX_PROOF,'lemma counted_g_erasure','lemma irrelevant_g_erasure'),
    ('actual-unlimited-LL-injected',PREFIX_PROOF,'require import AllCore','lemma forbidden : islossless CountedKeygen(UniformSeedRNG,ExpandROM).run. proof. auto. qed. require import AllCore'),
)


def main():
    controls=[]
    policy.check_structure()
    for inventory in (eof.SENTINELS, eof.SEMANTIC_TARGETS, eof.MODULE_BINDERS, eof.NEGATIVE_PROOFS):
        policy.require(set(inventory)==set(policy.MAINS),'semantic EOF inventory drift')
    for name,sentinel in eof.SENTINELS.items():
        check_sentinel(name,sentinel,eof.SEMANTIC_TARGETS[name],eof.MODULE_BINDERS[name])
    def rejects(label, action):
        try:
            action()
        except (ValueError,AssertionError,IndexError):
            controls.append({'label':label,'result':'EXPECTED_REJECTION'})
            return
        raise AssertionError('accepted negative control: '+label)
    for label, relative, old, new in MUTATIONS:
        text=policy.compact((policy.ROOT/relative).read_text())
        old,new=policy.compact(old),policy.compact(new)
        policy.require(old in text,'absent mutation target: '+label)
        altered=text.replace(old,new,1)
        policy.require(altered!=text,'ineffective mutation: '+label)
        rejects(label,lambda relative=relative,altered=altered:policy.check_structure({relative:altered}))
    for label, text in (
        ('admitted-proof','lemma forged : false. proof. admit. qed.'),
        ('local-axiom','axiom forged : false.'),
        ('disabled-checker','pragma -check.'),
        ('abstract-local-law','op arbitrary_uniform : int distr.'),
        ('unclosed-comment','(* mask the final proof'),
    ):
        rejects(label,lambda text=text:policy.check_proof_text(text))
    own='/isolated/0/Main.ec'
    valid='[critical] ['+own+': line 80] cannot process [axiom] inside a proof script'
    check_negative_diagnostic(valid,own)
    rejects('eof-wrong-main',lambda:check_negative_diagnostic(valid,'/isolated/1/Other.ec'))
    rejects('eof-import-contamination',lambda:check_negative_diagnostic(
        '[critical] ['+own+': line 4] In external theory Broken: cannot process [axiom] inside a proof script',own))
    rejects('eof-unrelated-error',lambda:check_negative_diagnostic(
        '[critical] ['+own+': line 80] unknown type',own))
    rejects('eof-wrong-command-inside-proof',lambda:check_negative_diagnostic(
        '[critical] ['+own+': line 80] cannot process [module] inside a proof script',own))
    sentinel='lemma __test (P <: ProposalPort) : islossless P.draw => islossless PairPorts(P).sample. proof. exact (pair_ports_sample_lossless P). qed.'
    def validates(s):
        check_sentinel('test',s,'pair_ports_sample_lossless',('P',))
    validates(sentinel)
    rejects('eof-implicit-module-binder',lambda:validates(sentinel.replace('P <: ProposalPort','P : ProposalPort')))
    rejects('eof-wrong-semantic-target',lambda:validates(sentinel.replace('exact (pair_ports_sample_lossless','exact (irrelevant')))
    rejects('eof-target-suffix-forgery',lambda:validates(sentinel.replace('exact (pair_ports_sample_lossless','exact (pair_ports_sample_lossless_unreviewed')))
    rejects('eof-open-sentinel',lambda:validates(sentinel.replace('qed.','')))
    rejects('eof-constant-proposition',lambda:validates('lemma __test (P <: ProposalPort) : true. proof. exact pair_ports_sample_lossless. qed.'))
    pair_name='kem_stopped_rom/NTRUPlus768ProposalModel.ec'
    malformed=eof.SENTINELS[pair_name].replace('PairPorts.pending','PairPorts(P).pending')
    rejects('eof-functor-global-instantiation',lambda:check_sentinel(
        pair_name,malformed,eof.SEMANTIC_TARGETS[pair_name],eof.MODULE_BINDERS[pair_name]))
    policy.require(len(controls)==len(MUTATIONS)+15,'mutation inventory drift')
    print(json.dumps({'status':'PASS','declared':len(MUTATIONS)+15,'count':len(controls),'controls':controls}))


if __name__=='__main__':
    main()
