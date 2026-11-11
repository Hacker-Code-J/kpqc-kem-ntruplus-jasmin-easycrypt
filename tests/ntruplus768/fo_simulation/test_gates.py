#!/usr/bin/env python3
"""Narrow source mutations and strict EOF/negative diagnostic regressions."""
import json
import sys
sys.dont_write_bytecode=True
import check_fo_simulation as policy
import eof_sentinels as eof
from model_contract import MUTATIONS
from verify_fo_simulation import check_negative_diagnostic,check_sentinel,unfinished_proof_text,completed_proof_text


def main():
    controls=[]
    policy.check_structure()
    for inventory in (eof.SENTINELS,eof.SEMANTIC_TARGETS,eof.MODULE_BINDERS,eof.NEGATIVE_PROOFS):
        policy.require(set(inventory)==set(policy.MAINS),'semantic EOF inventory drift')
    for name,sentinel in eof.SENTINELS.items():
        check_sentinel(name,sentinel,eof.SEMANTIC_TARGETS[name],eof.MODULE_BINDERS[name])
    def rejects(label,action):
        try:action()
        except (ValueError,AssertionError,IndexError):
            controls.append({'label':label,'result':'EXPECTED_REJECTION'});return
        raise AssertionError('accepted negative control: '+label)
    for label,relative,old,new in MUTATIONS:
        text=policy.compact((policy.ROOT/relative).read_text()).replace('op[opaque]','op')
        old,new=(policy.compact(value).replace('op[opaque]','op') for value in (old,new))
        policy.require(old in text,'absent mutation target: '+label)
        altered=text.replace(old,new,1)
        policy.require(altered!=text,'ineffective mutation: '+label)
        rejects(label,lambda relative=relative,altered=altered:policy.check_structure({relative:altered}))
    for label,text in (
        ('admitted-proof','lemma forged : false. proof. admit. qed.'),
        ('local-proof-axiom','axiom forged_recovery : false.'),
        ('disabled-checker','pragma -check.'),
        ('abstract-local-law','op arbitrary_recovery : bool.'),
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
    def validates(s):check_sentinel('fixture',s,'pair_ports_sample_lossless',('P',))
    validates(sentinel)
    rejects('eof-implicit-module-binder',lambda:validates(sentinel.replace('P <: ProposalPort','P : ProposalPort')))
    rejects('eof-wrong-semantic-target',lambda:validates(sentinel.replace('exact (pair_ports_sample_lossless','exact (irrelevant')))
    rejects('eof-target-suffix-forgery',lambda:validates(sentinel.replace('exact (pair_ports_sample_lossless','exact (pair_ports_sample_lossless_unreviewed')))
    rejects('eof-open-sentinel',lambda:validates(sentinel.replace('qed.','')))
    rejects('eof-constant-proposition',lambda:validates('lemma __test (P <: ProposalPort) : true. proof. exact pair_ports_sample_lossless. qed.'))
    source='lemma pair_value (P <: ProposalPort) : hoare[PairPorts(P).shake : true ==> res=PairPorts.pending]. proof. proc; auto. qed.'
    valid_sentinel='lemma __test (P <: ProposalPort) : hoare[PairPorts(P).shake : true ==> res=PairPorts.pending]. proof. exact (pair_value P). qed.'
    check_sentinel('fixture',valid_sentinel,'pair_value',('P',),source_text=source)
    rejects('eof-functor-global-instantiation',lambda:check_sentinel('fixture',
        valid_sentinel.replace('PairPorts.pending','PairPorts(P).pending'),'pair_value',('P',),source_text=source))
    source_with_tail = 'lemma closed : true. proof. trivial. qed.\nmodule Tail = {}.\n(* outer (* qed. *) qed. *)\n'
    marker = '\nlemma __unfinished_probe : true. proof. trivial. qed.\n'
    prepared = unfinished_proof_text(source_with_tail, marker)
    policy.require(prepared == source_with_tail.replace('qed.', marker, 1),
                   'negative must retain trailing modules and ignore comment closers')
    rejects('unfinished-proof-comment-only-closer',
            lambda:unfinished_proof_text('(* outer (* qed. *) qed. *)', marker))
    hybrid_name='kem_fo_simulation/NTRUPlus768SimHybrid.ec'
    selected_name='kem_fo_simulation/NTRUPlus768SimSelected.ec'
    hybrid=(policy.BASE/hybrid_name).read_text()
    selected=(policy.BASE/selected_name).read_text()
    policy.check_proof_text(hybrid,hybrid_name)
    policy.check_proof_text(selected,selected_name)
    rejects('clone-parameter-wrong-file',lambda:policy.check_proof_text(hybrid,'kem_fo_simulation/Other.ec'))
    rejects('clone-parameter-wrong-scope',lambda:policy.check_proof_text(
        hybrid.replace('SimHybridBudget','WrongScope'),hybrid_name))
    rejects('clone-budget-wrong-type',lambda:policy.check_proof_text(
        hybrid.replace('op budget : int.','op budget : real.'),hybrid_name))
    rejects('clone-unrelated-abstract-op',lambda:policy.check_proof_text(
        hybrid.replace('end SimHybridBudget.','op security_distance : real.\nend SimHybridBudget.'),hybrid_name))
    rejects('clone-unrelated-abstract-type',lambda:policy.check_proof_text(
        hybrid.replace('end SimHybridBudget.','type assumed_law.\nend SimHybridBudget.'),hybrid_name))
    rejects('clone-negative-budget-not-normalized',lambda:policy.check_proof_text(
        hybrid.replace('op q <- max 0 budget','op q <- budget'),hybrid_name))
    rejects('clone-nonnegative-obligation-skipped',lambda:policy.check_proof_text(
        hybrid.replace('proof q_ge0 by smt()',''),hybrid_name))
    rejects('selected-budget-not-forwarded',lambda:policy.check_proof_text(
        selected.replace('op budget <- budget.','op budget <- 0.'),selected_name))
    rejects('selected-scope-must-be-concrete',lambda:policy.check_proof_text(
        selected.replace('theory SimSelectedBudget.','abstract theory SimSelectedBudget.'),selected_name))
    scoped='abstract theory Probe.\nlemma closed : true. proof. trivial. qed.\nend Probe.\n'
    policy.require(completed_proof_text(scoped,marker).endswith(marker+'\nend Probe.\n'),
                   'positive semantic EOF must remain inside the source theory')
    policy.require(unfinished_proof_text(scoped,marker).endswith(marker+'\nend Probe.\n'),
                   'unfinished proof must preserve the trailing theory end')
    policy.require(len(controls)==len(MUTATIONS)+25,'control inventory drift')
    print(json.dumps({'status':'PASS','declared':len(MUTATIONS)+25,'count':len(controls),'controls':controls,
                      'main_inventory':'FROZEN' if (policy.TEST/'source-pins.json').is_file() else 'DECLARED_NOT_PINNED' if policy.MAINS else 'PENDING_FREEZE',
                      'semantic_eof_count':len(eof.SENTINELS)}))


if __name__=='__main__':main()
