#!/usr/bin/env python3
"""Narrow source mutations and strict EOF/negative diagnostic regressions."""
import json
import sys
sys.dont_write_bytecode=True
import check_linear_rrec as policy
import eof_sentinels as eof
from model_contract import MUTATIONS
from verify_linear_rrec import check_negative_diagnostic,check_sentinel


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
    policy.require(len(controls)==len(MUTATIONS)+15,'control inventory drift')
    print(json.dumps({'status':'PASS','declared':len(MUTATIONS)+15,'count':len(controls),'controls':controls,
                      'main_inventory':'FROZEN' if (policy.TEST/'source-pins.json').is_file() else 'DECLARED_NOT_PINNED' if policy.MAINS else 'PENDING_FREEZE',
                      'semantic_eof_count':len(eof.SENTINELS)}))


if __name__=='__main__':main()
