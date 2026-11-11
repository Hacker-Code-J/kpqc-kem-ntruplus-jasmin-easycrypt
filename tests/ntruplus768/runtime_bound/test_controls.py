#!/usr/bin/env python3
"""Negative controls for trust, own-proof diagnostics, scope and source calibration."""
import json,copy,re
from pathlib import Path
import policy, model_contract, scope_controls, manual_calibration, calibration_policy


def main():
    records=[]
    def rejects(name,action):
        try:action()
        except (ValueError,AssertionError,IndexError,KeyError):
            records.append({'label':name,'result':'EXPECTED_REJECTION'});return
        raise AssertionError('accepted negative control: '+name)
    for label,text in (
        ('admit','lemma x:false. proof. admit. qed.'),('new-axiom','axiom x:false.'),
        ('checkoff','pragma -check.'),('abstract-op','op hidden:real.'),
        ('abstract-type','type hidden.'),('native-proof','lemma x:true. proof. coq check "x" (). qed.'),
        ('section-hidden-axiom','section.\naxiom x:false.\nend section.'),
        ('unclosed-section','section.\nlemma x:true. proof. trivial. qed.'),
        ('unclosed-comment','(* unfinished'),('abort','lemma x:false. proof. abort.')):
        rejects(label,lambda text=text:policy.check_proof_text(text))
    own='/isolated/Own.ec'
    message='[critical] ['+own+': line 9] cannot process [axiom] inside a proof script'
    policy.check_negative_diagnostic(message,own)
    rejects('negative-other-main',lambda:policy.check_negative_diagnostic(message,'/isolated/Other.ec'))
    rejects('negative-import',lambda:policy.check_negative_diagnostic(message+' in external theory Other',own))
    rejects('negative-unrelated-parse',lambda:policy.check_negative_diagnostic(message.replace('cannot process [axiom] inside a proof script','parse error'),own))
    source='lemma final (A<:Port):islossless A.run. proof. proc;auto. qed.'
    sentinel='\nlemma __runtime_bound_eof(A<:Port):islossless A.run. proof. exact(final A). qed.\n'
    valid=lambda text:policy.check_sentinel('test',text,'final',['A'],source_text=source)
    valid(sentinel)
    for label,text in [('target-forged',sentinel.replace('exact(final','exact(other')),
                       ('eof-weakened',sentinel.replace('islossless A.run','true')),
                       ('implicit-module',sentinel.replace('A<:Port','A:Port')),
                       ('unfinished-sentinel',sentinel.replace('qed.',''))]:
        rejects(label,lambda text=text:valid(text))
    scope_controls.fixture_manifest()
    # These controls intentionally do not inspect any source pin. Even when
    # a caller reseals a modified file and its bound, charge rules reject it.
    for name in ('suffix','cipher','key','word_equal','copy768'):
        good=manual_calibration.expected_primitive(name)
        manual_calibration.check_body('RTPrimitive.'+name,good)
        rejects('manual-tick-and-bound-shrink-'+name,lambda name=name,good=good:manual_calibration.check_body('RTPrimitive.'+name,good.replace('work<-work+2;','work<-work+1;',1)))
        rejects('manual-omitted-charge-'+name,lambda name=name,good=good:manual_calibration.check_body('RTPrimitive.'+name,good.replace('work<-work+2;','',1)))
        rejects('manual-unsupported-source-op-'+name,lambda name=name,good=good:manual_calibration.check_body('RTPrimitive.'+name,'unchecked();'+good))
    scale=manual_calibration.expected_scale();manual_calibration.check_body('RTWordScale3.measure',scale)
    rejects('manual-array-size-shape-drift',lambda:manual_calibration.check_header('RTPrimitive.suffix','proc suffix(x y:W8.t Array1152.t):bool*int='))
    for label,altered in [('scale-copy-fee-omission',scale.replace('steps<-steps+2304;','',1)),
                          ('scale-fixed-loop-changed',scale.replace('i<768','i<767')),
                          ('scale-tick-and-bound-shrink',scale.replace('steps<-steps+4;','steps<-steps+1;',1))]:
        rejects(label,lambda altered=altered:manual_calibration.check_body('RTWordScale3.measure',altered))
    sample='module M={proc f(x:int):int={x<-x+1;return x;}}.'
    calibration_policy.compare_body(sample,sample,'M.f')
    rejects('regenerated-body-drift-with-resealed-pin',lambda:calibration_policy.compare_body(sample.replace('x+1','x+0'),sample,'M.f'))
    cost={'name':'tiny','source':'x','source_sha256':'pin','generated_source':'y','procedures':[{'cost':3,'ast':[{'fee':3}]}]}
    lowered={**cost,'procedures':[{'cost':1,'ast':[{'fee':1}]}]}
    rejects('joint-counter-bound-metadata-shrink',lambda:calibration_policy.compare_cost_record(lowered,cost))
    rejects('word-polynomial-reification',lambda:model_contract.check_executable('x<-ow_coeff_words p;',{},word=True))
    rejects('word-hidden-choice-helper',lambda:model_contract.check_executable('x<-wrapper y;',{'wrapper':'hidden y','hidden':'choice predT'},word=True))
    rejects('word-hidden-exists-helper',lambda:model_contract.check_executable('x<-tag y;',{'tag':'exists x,x=y'},word=True))
    for adapter in ('RTPolyNTRUAdapter','RTPolyRLWEAdapter'):
        sources={'RTWordGames':'module '+adapter+'={proc run():int={return 0;}}.',
                 'RTWordClient':'module RTWordClient={proc run():int={var x:int;x<@'+adapter+'.run();return x;}}.'}
        rejects('word-calls-ghost-adapter-'+adapter,lambda sources=sources:model_contract.word_closure(sources,{}))
    for source,label,old,new in model_contract.MUTATIONS:
        text=(policy.PROOF/('NTRUPlus768'+source+'.ec')).read_text()
        compact=policy.compact(text);policy.require(policy.compact(old) in compact,'mutation anchor missing')
        rejects('actual-source-'+label,lambda source=source,compact=compact,old=old,new=new:
                policy.shared.ordered(compact.replace(policy.compact(old),policy.compact(new),1),model_contract.ORDERED[source]))
    import fee_checker
    rejects('unpriced-division',lambda:fee_checker.expression_fee('a <- a / b;',{'a':'int','b':'int'}))
    rejects('unpriced-logical-combination',lambda:fee_checker.expression_fee('a <- b /\\ c;',{'a':'bool','b':'bool','c':'bool'}))
    for label,expression,types in (
      ('unpriced-list-cons','xs<-x::xs;',{'x':'int','xs':'int list'}),
      ('unpriced-variable-function','z<-f x;',{'z':'int','x':'int','f':'int->int'}),
      ('unpriced-variable-call','z<-f(x);',{'z':'int','x':'int','f':'int->int'}),
      ('uncalibrated-array-tuple-copy','(a,b)<-(c,d);',{x:'W16.t Array768.t' for x in 'abcd'})):
        rejects(label,lambda expression=expression,types=types:fee_checker.assignment_fee(expression,types))
    for qualified in ('RTFixedWordChecks.normalize','RTFixedWordChecks.trit','RTPsiSampler.measure','RTKey32Sampler.measure'):
        good=manual_calibration.expected_wordcheck(qualified.split('.')[1]) if qualified.startswith('RTFixed') else manual_calibration.expected_sampler(qualified)
        manual_calibration.check_body(qualified,good)
        marker='rt_work<-rt_work+2;' if qualified.startswith('RTFixed') else ('work<-work+385;' if qualified.startswith('RTPsi') else 'work<-work+65;')
        rejects('manual-charge-omission-'+qualified,lambda qualified=qualified,good=good,marker=marker:manual_calibration.check_body(qualified,good.replace(marker,'',1)))
    import kernel_calibration
    for expression in ('f x','f(x)'):
        rejects('kernel-unpriced-function-'+expression,lambda expression=expression:kernel_calibration.expression_ops(expression,{'f':'int -> int','x':'int'}))
    for condition,types in (('a=b',{'a':'W16.t Array768.t','b':'W16.t Array768.t'}),
                            ('x+y=W16.of_int 0',{'x':'W16.t','y':'W16.t'}),
                            ('x=W16.of_int 0 /\\ y=W16.of_int 0',{'x':'W16.t','y':'W16.t'}),
                            ('x=W32.of_int 0',{'x':'W16.t'})):
        rejects('unsupported-guard-'+condition,lambda condition=condition,types=types:fee_checker.single_scalar_guard(condition,'if',types))
    for source in ('RTPrimitiveCost','RTWordCodec','RTFixedWordChecks','RTPsiSampler'):
        text=(policy.PROOF/('NTRUPlus768'+source+'.ec')).read_text()
        manual_calibration.check_contracts(source,text)
        mutated=re.sub(r'(\blemma\s+(?:rt_primitive_suffix_correct|rt_word_scale3_measure_cost|rt_fixed_normalize_bound_cost|rt_psi_sampler_measure_total)\b).*?\bproof\s*\.',
                       r'\1 : true. proof.',text,flags=re.S)
        rejects('manual-weakened-theorem-'+source,lambda source=source,mutated=mutated:manual_calibration.check_contracts(source,mutated))
    manifest=policy.TEST/'calibration/manifest.json'
    if manifest.is_file():
        groups=json.loads(manifest.read_text())['groups']
        for group in groups:fee_checker.check_group(group)
        lowered=copy.deepcopy(next(x for x in groups if x['name']=='PolySub'))
        lowered['generated_source_sha256']='new-approved-pin-is-not-a-fee-proof'
        lowered['procedures'][0]['cost']-=1
        lowered['procedures'][0]['ast'][0]['fee']-=1
        lowered['procedures'][0]['ast'][0]['post']-=1
        rejects('independent-resealed-counter-bound-and-AST-shrink',lambda:fee_checker.check_group(lowered))
        first=groups[0];proc=first['procedures'][0]
        original=calibration_policy.path(first['generated_source']).read_text()
        for label,replacement in (('weakened-cost-declaration','true'),('wrong-cost-endpoint','hoare[Other.run:true ==>true]')):
            mutated=re.sub(r'(\blemma\s+'+re.escape(proc['cost_lemma'])+r'\b).*?\bproof\s*\.',
                           r'\1 : '+replacement+'. proof.',original,flags=re.S)
            rejects(label,lambda mutated=mutated:calibration_policy.fixed_declarations(first,proc,mutated))
    audit={'model':calibration_policy.MODEL_ID,'required_calibration_kinds':list(calibration_policy.REQUIRED_KINDS),
           'actual_word_endpoints':list(calibration_policy.ACTUAL_WORD_ENDPOINTS),
           'source_calibration_files':list(calibration_policy.CALIBRATION_FILES),
           'calibrated_final_theorems':[{'source':str((policy.PROOF/source).relative_to(policy.ROOT)),'theorem':name,
              'expected_declaration':calibration_policy.lemma_declaration((policy.PROOF/source).read_text(),name)}
              for source,name in calibration_policy.FINAL_THEOREMS]}
    categories=dict.fromkeys(calibration_policy.REQUIRED_KINDS,True)
    observed=calibration_policy.ACTUAL_WORD_ENDPOINTS+calibration_policy.MEASURED_WORD_ENDPOINTS
    calibration_policy.validate_coverage(audit,categories,observed)
    for kind in calibration_policy.REQUIRED_KINDS:
        missing={**categories,kind:False}
        rejects('whole-path-missing-'+kind,lambda missing=missing:calibration_policy.validate_coverage(audit,missing,observed))
    weaker=copy.deepcopy(audit);weaker['calibrated_final_theorems']=[]
    rejects('weighted-only-final',lambda:calibration_policy.validate_coverage(weaker,categories,observed))
    rejects('whole-path-missing-actual-endpoint',lambda:calibration_policy.validate_coverage(audit,categories,observed[1:]))
    incomplete=copy.deepcopy(audit);incomplete['source_calibration_files'].pop()
    rejects('whole-path-missing-source-rule-input',lambda:calibration_policy.validate_coverage(incomplete,categories,observed))
    import composition_calibration
    composed={name:(policy.PROOF/('NTRUPlus768'+name+'.ec')).read_text() for name in composition_calibration.expected_operations()}
    composition_calibration.check(composed)
    for source,name in (('RTCompleteCost','rt_complete_di_charge'),('RTBounds','rtk_charge'),
                        ('RTModel','rt_call'),('RTModel','rt_visits'),('RTKernelTypes','rtk_profile')):
        altered=dict(composed)
        altered[source]=re.sub(r'(\bop\s+'+name+r'\b.*?)=(.*?)\.\s*(?=\n|$)',r'\1=0.\n',altered[source],count=1,flags=re.S)
        rejects('semantic-charge-erasure-'+name,lambda altered=altered:composition_calibration.check(altered))
    outer_path=policy.TEST/'calibration/manual-outer.json'
    if outer_path.is_file():
        import outer_calibration
        original=json.loads(outer_path.read_text())
        outer_calibration._check_record(copy.deepcopy(original),False)
        def altered_outer(label,edit):
            data=copy.deepcopy(original);edit(data)
            rejects(label,lambda:outer_calibration._check_record(data,False))
        def proc(data,key):return next(p for p in data['procedures'] if p['key']==key)
        altered_outer('outer-entry-clone-omission',lambda data:proc(data,'top_di').update(entry_fee=0))
        def drop_clone(data):
            nodes=next(n for n in proc(data,'word_inj')['body_nodes'] if n['kind']=='if')['body']
            node=next(n for n in nodes if n.get('target')=='B.run')
            node['return_cells']=0;node['fee_parts']['result_clone']=0;node['local_fee']=3
        altered_outer('outer-data-return-clone-omission',drop_clone)
        def erase_data(data):
            p=proc(data,'word_inj');p['ghost_variables'].append('win')
            node=next(n for n in p['body_nodes'] if n.get('lhs')=='win')
            node['bucket']='ghost_erasure';node['local_fee']=0
        altered_outer('outer-data-erased-as-ghost',erase_data)
        altered_outer('outer-kernel-profile-omission',lambda data:proc(data,'inj_check')['direct_kernel_profile'].__setitem__(5,0))
        altered_outer('outer-callee-closure-omission',lambda data:data['endpoints']['di']['fixed_blocks'].remove('encrypt'))
        altered_outer('outer-run-dispatcher-omission',lambda data:data['run_dispatchers'].pop())
        def drop_dispatch_clone(data):
            r=next(row for row in data['run_dispatchers'] if row['source_proc']=='RTWord_CO.run')
            r['cost']-=r['fee_parts']['return_clone'];r['fee_parts']['return_clone']=0
        altered_outer('outer-run-return-clone-and-total-shrink',drop_dispatch_clone)
    phase_path=policy.TEST/'calibration/manual-phase.json'
    if phase_path.is_file():
        import phase_calibration
        rejects('phase-unpriced-list-append',lambda:phase_calibration.validate_fragment(
            'todo<-todo++[];',{'todo':'hist_table'},'HistReverse.run'))
        original=json.loads(phase_path.read_text())
        phase_calibration._check_record(copy.deepcopy(original),False)
        def altered_phase(label,edit):
            data=copy.deepcopy(original);edit(data)
            rejects(label,lambda:phase_calibration._check_record(data,False))
        altered_phase('phase-wrapper-boundary-omission',lambda data:data['bucket_aggregation']['encrypt_wrappers'].update(total=0))
        altered_phase('phase-raw-input-length-omission',lambda data:data['raw_numeric_rules'].update(raw_input_coefficient=0))
        altered_phase('phase-missing-history-body',lambda data:data['entries'].pop(next(i for i,e in enumerate(data['entries']) if e.get('module')=='HistKeep')))
        altered_phase('phase-native-counter-cost-omission',lambda data:next(e for e in data['entries'] if e.get('module')=='FOHashG').update(entry_cost=0,fixed_local_upper=0))
    print(json.dumps({'status':'PASS','count':len(records),'controls':records,
      'scope':'Source-rule negative controls only; not a proof replay or machine-cost result.'}))

if __name__=='__main__':main()
